module Scuf {

  import Std.Collections.Seq
  import opened Subcircuit
  import opened Circ
  import opened Eval
  import opened Utils
  import opened MapFunction

  datatype Scuf = Scuf(
    sc: set<CNode>,
    mp: ScufMap,
    uf: UpdateFunction
  ) {

    ghost predicate MapValid() {
      && mp.Valid()
      && mp.InSc(sc)
      && uf.Valid()
      && ScufMapUpdateFunctionConsistent(mp, uf)
    }

    opaque predicate SomewhatValid(c: Circuit)
      requires c.Valid()
    {
      && ScValid(c, sc)
      && (AllONPs(c, sc) >= Seq.ToSet(mp.outputs) >= ConnOutputs(c, sc))
      && (Seq.ToSet(mp.state) == AllSeq(c, sc))
      && (Seq.ToSet(mp.inputs) == AllInputs(c, sc))
    }

    opaque predicate SomewhatValidRelaxInputs(c: Circuit)
      requires c.Valid()
    {
      && ScValid(c, sc)
      && (AllONPs(c, sc) >= Seq.ToSet(mp.outputs) >= ConnOutputs(c, sc))
      && (Seq.ToSet(mp.state) == AllSeq(c, sc))
      // We relax the constraint on inputs a bit.
      // This is useful if we've connected an input but still want to
      // work with properties of the scuf.
      && (AllINPs(c, sc) >= Seq.ToSet(mp.inputs) >= AllInputs(c, sc))
    }

    lemma SomewhatValidToRelaxInputs(c: Circuit)
      requires c.Valid()
      requires SomewhatValid(c) || SomewhatValidRelaxInputs(c)
      ensures SomewhatValidRelaxInputs(c)
    {
      reveal SomewhatValid();
      reveal SomewhatValidRelaxInputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal Seq.ToSet();
      assert AllInputs(c, sc) <= AllINPs(c, sc) by {
        reveal AllINPs();
        reveal NPsInSc();
        reveal INPsValid();
      }
    }

    ghost opaque predicate EvaluatesCorrectly(c: Circuit)
      requires c.Valid()
      requires ScValid(c, sc)
      requires MapValid()
      requires SomewhatValidRelaxInputs(c) || SomewhatValid(c)
    {
      reveal ScValid();
      ScufFOutputsAreValid(c, this);
      reveal Seq.ToSet();
      forall fi: FI :: FIValid(fi, mp.inputs, mp.state) ==>
        assert FICircuitValid(c, fi) by {ScufValidFiValidToFICircuitValid(c, this, fi);}
        forall np :: np in Seq.ToSet(mp.outputs) || np in StateINPs(mp.state) ==>
          Evaluate(c, np, fi) == EvalOk(MFLookup(this, fi, np))
    }

    ghost predicate Valid(c: Circuit)
      requires c.Valid()
    {
      && MapValid()
      && ScValid(c, sc)
      && SomewhatValid(c)
      && assert SomewhatValidRelaxInputs(c) by {
           SomewhatValidToRelaxInputs(c);
         }
      && EvaluatesCorrectly(c)
    }

    ghost predicate ValidRelaxInputs(c: Circuit)
      requires c.Valid()
    {
      && MapValid()
      && ScValid(c, sc)
      && SomewhatValidRelaxInputs(c)
      && EvaluatesCorrectly(c)
    }

    function f(fi: FI): (fo: FO)
      requires MapValid()
      requires FIValid(fi, mp.inputs, mp.state)
      ensures FOValid(fo, mp.outputs, mp.state)
    {
      reveal UpdateFunction.Valid();
      var si := mp.fi2si(fi);
      var so := uf.sf(si);
      var fo := mp.so2fo(so);
      fo
    }

    lemma MapNPsInSc()
      requires MapValid()
      ensures NPsInSc(sc, mp.NPs())
    {
      reveal NPsInSc();
      reveal Seq.ToSet();
    }
  }

  lemma ScufFInputsAreValid(c: Circuit, e: Scuf)
    requires c.Valid()
    requires e.SomewhatValidRelaxInputs(c) || e.SomewhatValid(c)
    ensures forall np :: np in e.mp.inputs ==> INPValid(c, np)
    ensures forall np :: np in StateONPs(e.mp.state) ==> ONPValid(c, np)
  {
    reveal Scuf.SomewhatValidRelaxInputs();
    reveal Scuf.SomewhatValid();
    reveal AllSeq();
    reveal INPsValid();
    assert INPsValid(c, AllInputs(c, e.sc));
    assert INPsValid(c, Seq.ToSet(e.mp.inputs));
    reveal Seq.ToSet();
    forall np | np in StateONPs(e.mp.state)
      ensures ONPValid(c, np)
    {
      assert np.n in e.mp.state;
      assert np.p == OUTPUT_0;
      assert np.n in AllSeq(c, e.sc);
      reveal ScValid();
      assert np.n in c.NodeKind;
    }
  }

  lemma ScufFOutputsAreValid(c: Circuit, e: Scuf)
    requires c.Valid()
    requires e.SomewhatValidRelaxInputs(c) || e.SomewhatValid(c)
    ensures forall np :: np in e.mp.outputs ==> ONPValid(c, np)
    ensures forall np :: np in StateINPs(e.mp.state) ==> INPValid(c, np)
  {
    reveal ScValid();
    reveal Scuf.SomewhatValid();
    reveal Scuf.SomewhatValidRelaxInputs();
    reveal ONPsValid();
    assert Seq.ToSet(e.mp.outputs) <= AllONPs(c, e.sc);
    reveal Seq.ToSet();
    reveal ONPsValid();
    reveal AllSeq();
    forall np | np in StateINPs(e.mp.state)
      ensures INPValid(c, np)
    {
      assert np.n in AllSeq(c, e.sc);
    }
  }


  ghost opaque predicate ScufSeqEvaluatesCorrectly(c: Circuit, e: Scuf)
    requires c.Valid()
    requires ScValid(c, e.sc)
    requires e.MapValid()
    requires e.SomewhatValidRelaxInputs(c)
  {
    reveal ScValid();
    ScufFOutputsAreValid(c, e);
    reveal Seq.ToSet();
    forall fi: FI :: FIValid(fi, e.mp.inputs, e.mp.state) ==>
      assert FICircuitValid(c, fi) by {ScufValidFiValidToFICircuitValid(c, e, fi);}
      forall np :: np in Seq.ToSet(e.mp.outputs) || np in StateINPs(e.mp.state) ==>
        Evaluate(c, np, fi) == EvalOk(MFLookup(e, fi, np))
  }

  lemma FInputsInSc(c: Circuit, e: Scuf)
    requires c.Valid()
    requires e.SomewhatValidRelaxInputs(c) || e.SomewhatValid(c)
    ensures NPsInSc(e.sc, Seq.ToSet(e.mp.inputs))
    ensures NPsInSc(e.sc, StateONPs(e.mp.state))
  {
    reveal Scuf.SomewhatValid();
    reveal Scuf.SomewhatValidRelaxInputs();
    reveal AllINPs();
    reveal NPsInSc();
    reveal Seq.ToSet();
    reveal AllSeq();
  }

  lemma FOutputsInSc(c: Circuit, e: Scuf)
    requires c.Valid()
    requires e.SomewhatValid(c) || e.SomewhatValidRelaxInputs(c)
    ensures NPsInSc(e.sc, Seq.ToSet(e.mp.outputs))
    ensures NPsInSc(e.sc, StateINPs(e.mp.state))
  {
    reveal NPsInSc();
    reveal Scuf.SomewhatValid();
    reveal Scuf.SomewhatValidRelaxInputs();
    reveal AllSeq();
    reveal Seq.ToSet();
    assert AllONPs(c, e.sc) >= Seq.ToSet(e.mp.outputs);
  }

  lemma FAllInSc(c: Circuit, e: Scuf)
    requires c.Valid()
    requires e.SomewhatValid(c)
    ensures NPsInSc(e.sc, e.mp.NPs())
  {
    FInputsInSc(c, e);
    FOutputsInSc(c, e);
    reveal NPsInSc();
  }

  lemma StateInSc(c: Circuit, e: Scuf)
    requires c.Valid()
    requires e.SomewhatValid(c)
    ensures Seq.ToSet(e.mp.state) <= e.sc
  {
    reveal Scuf.SomewhatValid();
  }

  lemma StateIsSeq(c: Circuit, s: Scuf)
    requires c.Valid()
    requires s.SomewhatValidRelaxInputs(c)
    ensures forall n :: n in s.mp.state ==> n in c.NodeKind && c.NodeKind[n].CSeq?
  {
    reveal Scuf.SomewhatValidRelaxInputs();
    assert Seq.ToSet(s.mp.state) == AllSeq(c, s.sc);
    reveal Seq.ToSet();
    reveal ScValid();
    reveal Circuit.Valid();
    reveal AllSeq();
    assert forall n :: n in s.mp.state ==> (n in s.sc) && c.NodeKind[n].CSeq?;
  }

  lemma StaysInSc(c: Circuit, e: Scuf, np: NP)
    requires c.Valid()
    requires e.SomewhatValidRelaxInputs(c)
    requires INPValid(c, np)
    requires np.n in e.sc
    requires np !in e.mp.inputs
    ensures np in c.PortSource
    ensures c.PortSource[np].n in e.sc
  {
    reveal Circuit.Valid();
    reveal Scuf.SomewhatValidRelaxInputs();
    reveal UnconnInputs();
    reveal ConnInputs();
    reveal Seq.ToSet();
    assert np !in AllInputs(c, e.sc);
  }

  predicate OutputsInFOutputs(c: Circuit, e: Scuf)
    requires c.Valid()
  {
    Seq.ToSet(e.mp.outputs) >= ConnOutputs(c, e.sc)
  }

  lemma InputsOfIslandNotInPortSource(c: Circuit, e: Scuf)
    requires c.Valid()
    requires IsIsland(c, e.sc)
    requires e.Valid(c)
    ensures SetsNoIntersection(Seq.ToSet(e.mp.inputs), c.PortSource.Keys)
  {
    reveal Seq.ToSet();
    forall np | np in e.mp.inputs
      ensures np !in c.PortSource
    {
      NPInFInputsOfIslandNotInPortSource(c, e, np);
    }
    assert forall np :: np in Seq.ToSet(e.mp.inputs) ==> np in e.mp.inputs;
  }

  lemma NPInFInputsOfIslandNotInPortSource(c: Circuit, e: Scuf, np: NP) 
    requires c.Valid()
    requires IsIsland(c, e.sc)
    requires e.Valid(c)
    requires np in e.mp.inputs
    ensures np !in c.PortSource
  {
    reveal Seq.ToSet();
    assert np in AllInputs(c, e.sc) by {
      reveal Scuf.SomewhatValid();
    }
    assert |ConnInputs(c, e.sc)| == 0 by {
      IsIslandNoInputs(c, e.sc);
    }
    assert np in UnconnInputs(c, e.sc) || np in SeqInputs(c, e.sc);
    if np in UnconnInputs(c, e.sc) {
      assert np !in c.PortSource by {
        reveal UnconnInputs();
      }
    }
    if np in SeqInputs(c, e.sc) {
      reveal ONPsValid();
      assert ONPValid(c, np) by {
        reveal SeqInputs();
      }
    }
  }

  lemma ScufValidFiValidToFICircuitValid(c: Circuit, e: Scuf, fi: FI)
    requires c.Valid()
    requires e.SomewhatValidRelaxInputs(c) || e.SomewhatValid(c)
    requires FIValid(fi, e.mp.inputs, e.mp.state)
    ensures FICircuitValid(c, fi)
  {
    reveal Scuf.SomewhatValid();
    reveal Scuf.SomewhatValidRelaxInputs();
    assert Seq.ToSet(e.mp.inputs) >= AllInputs(c, e.sc);
    assert Seq.ToSet(e.mp.inputs) == fi.inputs.Keys;
    reveal ConnInputs();
    reveal UnconnInputs();
    reveal INPsValid();
    assert fi.state.Keys == Seq.ToSet(e.mp.state);
    assert fi.state.Keys == AllSeq(c, e.sc);
    reveal AllSeq();
    reveal ONPsValid();
    reveal ScValid();
    assert (forall np :: np in fi.inputs.Keys ==> INPValid(c, np));
    assert (forall n :: n in fi.state.Keys ==> c.NodeKind[n].CSeq?);
    reveal FICircuitValid();
  }

  lemma EntitiesSeparate(c: Circuit, e1: Scuf, e2: Scuf)
    requires c.Valid()
    requires e1.SomewhatValid(c)
    requires e2.SomewhatValid(c)
    requires e1.sc !! e2.sc
    ensures e1.mp.NPs() !! e2.mp.NPs()
  {
    FAllInSc(c, e1);
    FAllInSc(c, e2);
    forall np | np in e1.mp.NPs()
      ensures np !in e2.mp.NPs()
    {
      if np in e2.mp.NPs() {
        reveal NPsInSc();
        assert np.n in e1.sc;
        assert np.n in e2.sc;
        assert np.n in e1.sc * e2.sc;
        assert false;
      }
    }
  }

  function ScufSwapUF(c: Circuit, e: Scuf, uf: UpdateFunction): (r: Scuf)
    requires c.Valid()
    requires e.Valid(c)
    requires uf.Valid()
    requires UpdateFunctionsEquiv(e.uf, uf)
    ensures r.Valid(c)
  {
    var r := Scuf(e.sc, e.mp, uf);
    assert r.SomewhatValid(c) by {
      reveal Scuf.SomewhatValid();
    }
    r.SomewhatValidToRelaxInputs(c);
    assert r.MapValid() by {
      UFConsistentEquiv(e.uf, uf, e.mp);
    }
    assert ScValid(c, r.sc);
    assert r.EvaluatesCorrectly(c) by {
      reveal Scuf.EvaluatesCorrectly();
      reveal UpdateFunctionsEquiv();
    }
    r
  }

  const NullScuf := Scuf({}, NullScufMap, NullUpdateFunction)

  lemma NullScufValid(c: Circuit)
    requires c.Valid()
    ensures NullScuf.Valid(c)
  {
    var e := NullScuf;
    assert ScValid(c, e.sc) by {
      reveal ScValid();
    }
    assert e.uf.Valid() by {
      NullUpdateFunctionValid();
    }
    assert e.MapValid() by {
      NullScufMapValid();
      reveal NPsInSc();
      reveal Seq.ToSet();
    }
    assert e.SomewhatValid(c) by {
      reveal AllONPs();
      reveal Seq.ToSet();
      reveal ConnOutputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal Scuf.SomewhatValid();
    }
    e.SomewhatValidToRelaxInputs(c);
    assert e.EvaluatesCorrectly(c) by {
      reveal Seq.ToSet();
      assert |Seq.ToSet(e.mp.outputs)| == 0;
      assert |StateINPs(e.mp.state)| == 0;
      reveal Scuf.EvaluatesCorrectly();
    }
    reveal Scuf.SomewhatValid();
  }

  function MFLookup(scuf: Scuf, fi: FI, np: NP): bool
    requires scuf.MapValid()
    requires FIValid(fi, scuf.mp.inputs, scuf.mp.state)
    requires np in scuf.mp.outputs || np in StateINPs(scuf.mp.state)
  {
    assert !((np in scuf.mp.outputs) && (np in StateINPs(scuf.mp.state))) by {
      reveal Seq.ToSet();
      StateINPsSeqSame(scuf.mp.state);
    }
    if (np in scuf.mp.outputs) then
      MFLookupOutput(scuf, fi, np)
    else
      MFLookupState(scuf, fi, np)
  }

  function MFLookupOutput(scuf: Scuf, fi: FI, np: NP): bool
    requires scuf.MapValid()
    requires FIValid(fi, scuf.mp.inputs, scuf.mp.state)
    requires np in scuf.mp.outputs
  {
    var si := scuf.mp.fi2si(fi);
    reveal UpdateFunction.Valid();
    var so := scuf.uf.sf(si);
    var fo := scuf.mp.so2fo(so);
    assert FOValid(fo, scuf.mp.outputs, scuf.mp.state);
    reveal Seq.ToSet();
    fo.outputs[np]
  }

  function MFLookupState(scuf: Scuf, fi: FI, np: NP): bool
    requires scuf.MapValid()
    requires FIValid(fi, scuf.mp.inputs, scuf.mp.state)
    requires np in StateINPs(scuf.mp.state)
  {
    reveal UpdateFunction.Valid();
    var si := scuf.mp.fi2si(fi);
    var so := scuf.uf.sf(si);
    var fo := scuf.mp.so2fo(so);
    assert FOValid(fo, scuf.mp.outputs, scuf.mp.state);
    reveal Seq.ToSet();
    fo.state[np.n]
  }



}
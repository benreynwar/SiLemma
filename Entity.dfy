module Entity {

  import Std.Collections.Seq
  import opened Subcircuit
  import opened Circ
  import opened Eval
  import opened Utils
  import opened MapFunction

  datatype Entity = Entity(
    sc: set<CNode>,
    mf: MapFunction
  )

  opaque predicate EntitySomewhatValid(c: Circuit, e: Entity)
    requires c.Valid()
  {
    && ScValid(c, e.sc)
    && (AllONPs(c, e.sc) >= Seq.ToSet(e.mf.outputs) >= ConnOutputs(c, e.sc))
    && (Seq.ToSet(e.mf.inputs) == AllInputs(c, e.sc))
    && (Seq.ToSet(e.mf.state) == AllSeq(c, e.sc))
  }

  lemma EntityFInputsAreValid(c: Circuit, e: Entity)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    ensures forall np :: np in e.mf.inputs ==> INPValid(c, np)
    ensures forall np :: np in StateONPs(e.mf.state) ==> ONPValid(c, np)
  {
    reveal EntitySomewhatValid();
    reveal AllSeq();
    reveal INPsValid();
    assert INPsValid(c, AllInputs(c, e.sc));
    assert INPsValid(c, Seq.ToSet(e.mf.inputs));
    reveal Seq.ToSet();
    forall np | np in StateONPs(e.mf.state)
      ensures ONPValid(c, np)
    {
      assert np.n in e.mf.state;
      assert np.p == OUTPUT_0;
      assert np.n in AllSeq(c, e.sc);
      reveal ScValid();
      assert np.n in c.NodeKind;
    }
  }

  lemma EntityFOutputsAreValid(c: Circuit, e: Entity)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    ensures forall np :: np in e.mf.outputs ==> ONPValid(c, np)
    ensures forall np :: np in StateINPs(e.mf.state) ==> INPValid(c, np)
  {
    reveal ScValid();
    reveal EntitySomewhatValid();
    reveal ONPsValid();
    assert Seq.ToSet(e.mf.outputs) <= AllONPs(c, e.sc);
    reveal Seq.ToSet();
    reveal ONPsValid();
    reveal AllSeq();
    forall np | np in StateINPs(e.mf.state)
      ensures INPValid(c, np)
    {
      assert np.n in AllSeq(c, e.sc);
    }
  }

  ghost opaque predicate EntityEvaluatesCorrectly(c: Circuit, e: Entity)
    requires c.Valid()
    requires ScValid(c, e.sc)
    requires e.mf.Valid()
    requires EntitySomewhatValid(c, e)
  {
    reveal ScValid();
    EntityFOutputsAreValid(c, e);
    reveal MapFunction.Valid();
    reveal Seq.ToSet();
    forall fi: FI :: FIValid(fi, e.mf.inputs, e.mf.state) ==>
      assert FICircuitValid(c, fi) by {EntityValidFiValidToFICircuitValid(c, e, fi);}
      forall np :: np in Seq.ToSet(e.mf.outputs) || np in StateINPs(e.mf.state) ==>
        Evaluate(c, np, fi) == EvalOk(MFLookup(e.mf, fi, np))
  }

  ghost opaque predicate EntitySeqEvaluatesCorrectly(c: Circuit, e: Entity)
    requires c.Valid()
    requires ScValid(c, e.sc)
    requires e.mf.Valid()
    requires EntitySomewhatValid(c, e)
  {
    reveal ScValid();
    EntityFOutputsAreValid(c, e);
    reveal MapFunction.Valid();
    reveal Seq.ToSet();
    forall fi: FI :: FIValid(fi, e.mf.inputs, e.mf.state) ==>
      assert FICircuitValid(c, fi) by {EntityValidFiValidToFICircuitValid(c, e, fi);}
      forall np :: np in Seq.ToSet(e.mf.outputs) || np in StateINPs(e.mf.state) ==>
        Evaluate(c, np, fi) == EvalOk(MFLookup(e.mf, fi, np))
  }

  ghost predicate EntityValid(c: Circuit, e: Entity)
    requires c.Valid()
  {
    && EntitySomewhatValid(c, e)
    && e.mf.Valid()
    && ScValid(c, e.sc)
    && EntityEvaluatesCorrectly(c, e)
  }

  lemma FInputsInSc(c: Circuit, e: Entity)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    ensures NPsInSc(e.sc, Seq.ToSet(e.mf.inputs))
    ensures NPsInSc(e.sc, StateONPs(e.mf.state))
  {
    reveal EntitySomewhatValid();
    reveal AllINPs();
    reveal NPsInSc();
    reveal Seq.ToSet();
    reveal AllSeq();
  }

  lemma FOutputsInSc(c: Circuit, e: Entity)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    ensures NPsInSc(e.sc, Seq.ToSet(e.mf.outputs))
    ensures NPsInSc(e.sc, StateINPs(e.mf.state))
  {
    reveal NPsInSc();
    reveal EntitySomewhatValid();
    reveal AllSeq();
    reveal Seq.ToSet();
    assert AllONPs(c, e.sc) >= Seq.ToSet(e.mf.outputs);
  }

  lemma FAllInSc(c: Circuit, e: Entity)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    ensures NPsInSc(e.sc, e.mf.NPs())
  {
    FInputsInSc(c, e);
    FOutputsInSc(c, e);
    reveal NPsInSc();
  }

  lemma StateInSc(c: Circuit, e: Entity)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    ensures Seq.ToSet(e.mf.state) <= e.sc
  {
    reveal EntitySomewhatValid();
  }

  lemma StaysInSc(c: Circuit, e: Entity, np: NP)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    requires INPValid(c, np)
    requires np.n in e.sc
    requires np !in e.mf.inputs
    ensures np in c.PortSource
    ensures c.PortSource[np].n in e.sc
  {
    reveal Circuit.Valid();
    reveal EntitySomewhatValid();
    reveal UnconnInputs();
    reveal ConnInputs();
    reveal Seq.ToSet();
    assert np !in AllInputs(c, e.sc);
  }

  predicate OutputsInFOutputs(c: Circuit, e: Entity)
    requires c.Valid()
  {
    Seq.ToSet(e.mf.outputs) >= ConnOutputs(c, e.sc)
  }

  lemma InputsOfIslandNotInPortSource(c: Circuit, e: Entity)
    requires c.Valid()
    requires IsIsland(c, e.sc)
    requires EntityValid(c, e)
    ensures SetsNoIntersection(Seq.ToSet(e.mf.inputs), c.PortSource.Keys)
  {
    reveal Seq.ToSet();
    forall np | np in e.mf.inputs
      ensures np !in c.PortSource
    {
      NPInFInputsOfIslandNotInPortSource(c, e, np);
    }
    assert forall np :: np in Seq.ToSet(e.mf.inputs) ==> np in e.mf.inputs;
  }

  lemma NPInFInputsOfIslandNotInPortSource(c: Circuit, e: Entity, np: NP) 
    requires c.Valid()
    requires IsIsland(c, e.sc)
    requires EntityValid(c, e)
    requires np in e.mf.inputs
    ensures np !in c.PortSource
  {
    reveal Seq.ToSet();
    assert np in AllInputs(c, e.sc) by {
      reveal EntitySomewhatValid();
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

  lemma EntityValidFiValidToFICircuitValid(c: Circuit, e: Entity, fi: FI)
    requires c.Valid()
    requires EntitySomewhatValid(c, e)
    requires FIValid(fi, e.mf.inputs, e.mf.state)
    ensures FICircuitValid(c, fi)
  {
    reveal EntitySomewhatValid();
    assert Seq.ToSet(e.mf.inputs) == AllInputs(c, e.sc);
    assert Seq.ToSet(e.mf.inputs) == fi.inputs.Keys;
    reveal ConnInputs();
    reveal UnconnInputs();
    reveal INPsValid();
    assert fi.state.Keys == Seq.ToSet(e.mf.state);
    assert fi.state.Keys == AllSeq(c, e.sc);
    reveal AllSeq();
    reveal ONPsValid();
    reveal ScValid();
    assert (forall np :: np in fi.inputs.Keys ==> INPValid(c, np));
    assert (forall n :: n in fi.state.Keys ==> c.NodeKind[n].CSeq?);
    reveal FICircuitValid();
  }

  lemma EntitiesSeparate(c: Circuit, e1: Entity, e2: Entity)
    requires c.Valid()
    requires EntitySomewhatValid(c, e1)
    requires EntitySomewhatValid(c, e2)
    requires e1.sc !! e2.sc
    ensures e1.mf.NPs() !! e2.mf.NPs()
  {
    FAllInSc(c, e1);
    FAllInSc(c, e2);
    forall np | np in e1.mf.NPs()
      ensures np !in e2.mf.NPs()
    {
      if np in e2.mf.NPs() {
        reveal NPsInSc();
        assert np.n in e1.sc;
        assert np.n in e2.sc;
        assert np.n in e1.sc * e2.sc;
        assert false;
      }
    }
  }

  function EntitySwapMF(c: Circuit, e: Entity, mf: MapFunction): (r: Entity)
    requires c.Valid()
    requires EntityValid(c, e)
    requires mf.Valid()
    requires MapFunctionsEquiv(e.mf, mf)
    ensures EntityValid(c, r)
  {
    var r := Entity(e.sc, mf);
    reveal MapFunctionsEquiv();
    assert EntitySomewhatValid(c, r) by {
      reveal EntitySomewhatValid();
    }
    assert r.mf.Valid();
    assert ScValid(c, r.sc);
    assert EntityEvaluatesCorrectly(c, r) by {
      reveal EntityEvaluatesCorrectly();
    }
    r
  }

  function EntitySwapRF(c: Circuit, e: Entity, rf: RFunction): (r: Entity)
    requires c.Valid()
    requires EntityValid(c, e)
    requires rf.Valid()
    requires rf.MFConsistent(e.mf)
    ensures EntityValid(c, r)
    ensures rf.MFConsistent(r.mf)
  {
    var mf := rf.ReplacementMF(e.mf);
    EntitySwapMF(c, e, mf)
  }

  const NullEntity := Entity({}, NullMF)

  lemma NullEntityValid(c: Circuit)
    requires c.Valid()
    ensures EntityValid(c, NullEntity)
  {
    var e := NullEntity;
    assert ScValid(c, e.sc) by {
      reveal ScValid();
    }
    assert e.mf.Valid() by {
      NullMFValid();
    }
    assert EntitySomewhatValid(c, e) by {
      reveal AllONPs();
      reveal Seq.ToSet();
      reveal ConnOutputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal EntitySomewhatValid();
    }
    assert EntityEvaluatesCorrectly(c, e) by {
      reveal Seq.ToSet();
      assert |Seq.ToSet(e.mf.outputs)| == 0;
      assert |StateINPs(e.mf.state)| == 0;
      reveal EntityEvaluatesCorrectly();
    }
    reveal EntitySomewhatValid();
  }

}
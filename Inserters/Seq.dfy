module Inserters.Seq {

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  function SeqSF(si: SI): (so: SO)
    requires |si.inputs| == 1
    requires |si.state| == 1
  {
    SO([si.state[0]], [si.inputs[0]])
  }

  function InsertSeqImpl(c: Circuit): (r: (Circuit, Entity))
    requires c.Valid()
    ensures r.0.Valid()
    ensures EntitySomewhatValid(r.0, r.1)
    ensures r.1.mf.Valid()
  {
    reveal Circuit.Valid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CSeq],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := [i_0];
    var outputs := [o_0];
    var state := [new_node];
    var mf := MapFunction(inputs, outputs, state, SeqSF);
    var e := Entity({new_node}, mf);
    assert EntitySomewhatValid(new_c, e) by {
      reveal EntitySomewhatValid();
      reveal Seq.ToSet();
      reveal ScValid();
      reveal ConnOutputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal AllONPs();
      reveal AllSeq();
      assert ScValid(new_c, e.sc);
      assert forall np: NP :: np.n in e.sc ==> np !in c.PortSource.Values;
    }
    assert mf.Valid() by {
      reveal MapFunction.Valid();
      reveal Seq.ToSet();
      reveal Seq.HasNoDuplicates();
    }
    (new_c, e)
  }

  lemma InsertSeqCorrect(c: Circuit)
    requires c.Valid()
    ensures
      var (new_c, e) := InsertSeqImpl(c);
      && EntityValid(new_c, e)
  {
    var (new_c, e) := InsertSeqImpl(c);
    var o := e.mf.outputs[0];
    var i_0 := e.mf.inputs[0];
    var os_0 := NP(e.mf.state[0], OUTPUT_0);
    var path := [e.mf.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert new_c.Valid();
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
      ensures
        var sv_0 := fi.state[os_0.n];
        && FICircuitValid(new_c, fi)
        && (EvaluateONP(new_c, o, fi) == EvalOk(sv_0))
    {
      var iv_0 := fi.inputs[i_0];
      var sv_0 := fi.state[os_0.n];
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, fi) by {
        reveal MapFunction.Valid();
        reveal FICircuitValid();
      }
      assert EvaluateONP(new_c, o, fi) == EvalOk(sv_0);
      reveal Seq.HasNoDuplicates();
      assert Evaluate(new_c, o, fi) == EvalOk(sv_0);
      assert Evaluate(new_c, o, fi) == EvalOk(e.mf.f(fi).outputs[o]) by {
        reveal MapMatchesSeqs();
      }
    }
    assert ScValid(new_c, e.sc) by {
      reveal EntitySomewhatValid();
    }
    assert EntityEvaluatesCorrectly(new_c, e) by {
      reveal EntityEvaluatesCorrectly();
      reveal MapMatchesSeqs();
    }
    assert EntityValid(new_c, e);
  }

  lemma InsertSeqConserves(c: Circuit)
    requires c.Valid()
    ensures CircuitConserved(c, InsertSeqImpl(c).0)
    ensures CircuitUnconnected(c, InsertSeqImpl(c).0)
    ensures
      var (new_c, e) := InsertSeqImpl(c);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertSeqImpl(c);
    reveal Circuit.Valid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  lemma InsertSeqMFConsistent(c: Circuit)
    requires c.Valid()
    ensures
      var (new_c, e) := InsertSeqImpl(c);
      SeqRF().MFConsistent(e.mf)
  {
    reveal RFunction.MFConsistent();
  }

  function InsertSeq(c: Circuit): (r: (Circuit, Entity))
    requires c.Valid()
    ensures SimpleInsertion(c, r.0, r.1)
    ensures SeqRF().MFConsistent(r.1.mf)
  {
    reveal SimpleInsertion();
    InsertSeqCorrect(c);
    InsertSeqConserves(c);
    InsertSeqMFConsistent(c);
    InsertSeqImpl(c)
  }

  const SeqRFConst := RFunction(1, 1, 1, SeqSF)

  function SeqRF(): (r: RFunction)
    ensures r.Valid()
  {
    reveal RFunction.Valid();
    SeqRFConst
  }

  const SeqInserterConst := EntityInserter(SeqRF(), InsertSeq)

  function SeqInserter(): (r: EntityInserter)
    ensures r.Valid()
  {
    reveal RFunction.Valid();
    reveal EntityInserter.Valid();
    var rf := SeqRF();
    SeqInserterConst
  }

}

module Inserters.Seq{

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Scuf
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  const SeqUFConst := UpdateFunction(
    1, 1, 1,
    (si: SI) requires |si.inputs| == 1 && |si.state| == 1 =>
      SO(si.state, si.inputs))

  function SeqUpdateFunction(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    SeqUFConst
  }

  function InsertSeqImpl(c: Circuit): (r: (Circuit, Scuf))
    requires c.Valid()
    ensures r.0.Valid()
    ensures r.1.SomewhatValid(r.0)
    ensures r.1.MapValid()
    ensures r.1.uf.Valid()
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
    var mp := ScufMap(inputs, outputs, state);
    assert mp.Valid() by {
      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
    }
    var uf := SeqUpdateFunction();
    var s := Scuf({new_node}, mp, uf);
    assert s.SomewhatValid(new_c) by {
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      reveal ScValid();
      reveal ConnOutputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal AllONPs();
      reveal AllSeq();
      assert ScValid(new_c, s.sc);
      assert forall np: NP :: np.n in s.sc ==> np !in c.PortSource.Values;
      assert (AllONPs(new_c, s.sc) >= Seq.ToSet(mp.outputs) >= ConnOutputs(new_c, s.sc));
    }
    assert s.MapValid() by {
      reveal Seq.ToSet();
      reveal NPsInSc();
    }
    (new_c, s)
  }

  lemma InsertSeqF(c: Circuit, fi: FI)
    requires c.Valid()
    requires
      var (new_c, s) := InsertSeqImpl(c);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var (new_c, s) := InsertSeqImpl(c);
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      && s.f(fi) == FO(map[s.mp.outputs[0]:=fi.state[s.mp.state[0]]], map[s.mp.state[0]:=fi.inputs[s.mp.inputs[0]]])
    {
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      reveal MapToSeq();
      reveal SeqsToMap();
    }
      
  lemma InsertSeqCorrect(c: Circuit)
    requires c.Valid()
    ensures
      var (new_c, e) := InsertSeqImpl(c);
      && e.Valid(new_c)
  {
    var (new_c, e) := InsertSeqImpl(c);
    var o := e.mp.outputs[0];
    var st := e.mp.state[0];
    var i_0 := e.mp.inputs[0];
    var path := [e.mp.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) by {
      reveal PathValid();
    }
    var os_0 := NP(e.mp.state[0], OUTPUT_0);
    LengthOneNoDuplicates(path);
    assert new_c.Valid();
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, e.mp.inputs, e.mp.state)
      ensures
        var iv_0 := fi.inputs[i_0];
        var sv_0 := fi.state[i_0.n];
        && FICircuitValid(new_c, FItoKeys(fi))
        && (EvaluateONP(new_c, o, fi) == EvalOk(sv_0))
    {
      var iv_0 := fi.inputs[i_0];
      var sv_0 := fi.state[os_0.n];
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, FItoKeys(fi)) by {
        reveal UpdateFunction.Valid();
        reveal FICircuitValid();
      }
      assert EvaluateONP(new_c, o, fi) == EvalOk(sv_0);
      reveal Seq.HasNoDuplicates();
      assert Evaluate(new_c, o, fi) == EvalOk(sv_0);
      assert Evaluate(new_c, o, fi) == EvalOk(e.f(fi).outputs[o]) by {
        reveal MapMatchesSeqs();
      }
    }
    assert ScValid(new_c, e.sc) by {
      reveal Scuf.SomewhatValid();
    }
    assert e.EvaluatesCorrectly(new_c) by {
      reveal Scuf.EvaluatesCorrectly();
      reveal MapMatchesSeqs();
    }
    assert e.Valid(new_c);
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

  function InsertSeq(c: Circuit): (r: (Circuit, Scuf))
    requires c.Valid()
    ensures
      var (new_c, e) := r;
      && r == InsertSeqImpl(c)
      && r.0.Valid()
      && e.Valid(new_c)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertSeqCorrect(c);
    InsertSeqConserves(c);
    InsertSeqImpl(c)
  }

  const SeqInserterConst := ScufInserter(SeqUpdateFunction(), InsertSeq)

  function SeqInserter(): (r: ScufInserter)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    reveal ScufInserter.Valid();
    var z := SeqInserterConst;
    assert z.Valid() by {
      reveal SimpleInsertion();
    }
    z 
  }

}

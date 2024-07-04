module Inserters.And{

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Scuf
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  const AndUFConst := UpdateFunction(
    2, 1, 0,
    (si: SI) requires |si.inputs| == 2 && |si.state| == 0 =>
      SO([si.inputs[0] && si.inputs[1]], []));

  function AndUF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    AndUFConst
  }

  function InsertAndImpl(c: Circuit): (r: (Circuit, Scuf))
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
      NodeKind := c.NodeKind[new_node := CAnd],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var i_1 := NP(new_node, INPUT_1);
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := [i_0, i_1];
    var outputs := [o_0];
    var state := [];
    var mp := ScufMap(inputs, outputs, state);
    assert mp.Valid() by {
      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
    }
    var uf := AndUF();
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
    }
    assert s.MapValid() by {
      reveal Seq.ToSet();
      reveal NPsInSc();
    }
    (new_c, s)
  }

  lemma InsertAndF(c: Circuit, fi: FI)
    requires c.Valid()
    requires
      var (new_c, s) := InsertAndImpl(c);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var (new_c, s) := InsertAndImpl(c);
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      && s.f(fi) == FO(map[s.mp.outputs[0]:=fi.inputs[s.mp.inputs[0]] && fi.inputs[s.mp.inputs[1]]], map[])
    {
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      reveal MapToSeq();
      reveal SeqsToMap();
    }
      


  lemma InsertAndCorrect(c: Circuit)
    requires c.Valid()
    ensures
      var (new_c, e) := InsertAndImpl(c);
      && e.Valid(new_c)
  {
    var (new_c, e) := InsertAndImpl(c);
    var o := e.mp.outputs[0];
    var i_0 := e.mp.inputs[0];
    var i_1 := e.mp.inputs[1];
    var path := [e.mp.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) && PathValid(new_c, [o, i_1]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert new_c.Valid();
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, e.mp.inputs, e.mp.state)
      ensures
        var iv_0 := fi.inputs[i_0];
        var iv_1 := fi.inputs[i_1];
        && FICircuitValid(new_c, fi)
        && (EvaluateONP(new_c, o, fi) == EvalOk(iv_0 && iv_1))
    {
      var iv_0 := fi.inputs[i_0];
      var iv_1 := fi.inputs[i_1];
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, fi) by {
        reveal UpdateFunction.Valid();
        reveal FICircuitValid();
      }
      assert EvaluateONP(new_c, o, fi) == EvaluateONPBinary(new_c, [o], fi);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [o, i_0], fi) == EvalOk(iv_0);
      assert EvaluateINPInner(new_c, [o, i_1], fi) == EvalOk(iv_1);
      assert EvaluateONPBinary(new_c, [o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONPInner(new_c, [o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONP(new_c, o, fi) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o, fi) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o, fi) == EvalOk(e.f(fi).outputs[o]) by {
        InsertAndF(c, fi);
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

  lemma InsertAndConserves(c: Circuit)
    requires c.Valid()
    ensures CircuitConserved(c, InsertAndImpl(c).0)
    ensures CircuitUnconnected(c, InsertAndImpl(c).0)
    ensures
      var (new_c, e) := InsertAndImpl(c);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertAndImpl(c);
    reveal Circuit.Valid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertAnd(c: Circuit): (r: (Circuit, Scuf))
    requires c.Valid()
    ensures
      var (new_c, e) := r;
      && r == InsertAndImpl(c)
      && r.0.Valid()
      && e.Valid(new_c)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertAndCorrect(c);
    InsertAndConserves(c);
    InsertAndImpl(c)
  }

  const AndInserterConst := ScufInserter(AndUF(), InsertAnd)

  function AndInserter(): (r: ScufInserter)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    reveal ScufInserter.Valid();
    var z := AndInserterConst;
    assert z.Valid() by {
      reveal SimpleInsertion();
    }
    z 
  }

}

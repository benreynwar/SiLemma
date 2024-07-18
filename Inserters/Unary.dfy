module Inserters_Unary{

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Scuf
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  function UnaryUF(nk: CNodeKind): (uf: UpdateFunction)
    requires CNodeKindIsUnary(nk)
    ensures uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      1, 1, 0,
      (si: SI) requires |si.inputs| == 1 && |si.state| == 0 =>
        SO([UnaryOp(si.inputs[0], nk)], []))
  }

  function InsertUnaryImpl(c: Circuit, nk: CNodeKind): (r: (Circuit, Scuf))
    requires c.Valid()
    requires CNodeKindIsUnary(nk)
    ensures r.0.Valid()
    ensures r.1.SomewhatValid(r.0)
    ensures r.1.MapValid()
    ensures r.1.uf.Valid()
  {
    reveal Circuit.Valid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := nk],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := [i_0];
    var outputs := [o_0];
    var state := [];
    var mp := ScufMap(inputs, outputs, state);
    assert mp.Valid() by {
      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
    }
    var uf := UnaryUF(nk);
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

  lemma InsertUnaryF(c: Circuit, nk: CNodeKind, fi: FI)
    requires c.Valid()
    requires CNodeKindIsUnary(nk)
    requires
      var (new_c, s) := InsertUnaryImpl(c, nk);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var (new_c, s) := InsertUnaryImpl(c, nk);
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      && s.f(fi) == FO(map[s.mp.outputs[0]:=UnaryOp(fi.inputs[s.mp.inputs[0]], nk)], map[])
    {
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      reveal MapToSeq();
      reveal SeqsToMap();
    }
      


  lemma InsertUnaryCorrect(c: Circuit, nk: CNodeKind)
    requires c.Valid()
    requires CNodeKindIsUnary(nk)
    ensures
      var (new_c, e) := InsertUnaryImpl(c, nk);
      && e.Valid(new_c)
  {
    var (new_c, e) := InsertUnaryImpl(c, nk);
    var o := e.mp.outputs[0];
    var i_0 := e.mp.inputs[0];
    var path := [e.mp.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert new_c.Valid();
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, e.mp.inputs, e.mp.state)
      ensures
        var iv_0 := fi.inputs[i_0];
        && FICircuitValid(new_c, FItoKeys(fi))
        && (EvaluateONP(new_c, o, fi) == EvalOk(UnaryOp(iv_0, nk)))
    {
      var iv_0 := fi.inputs[i_0];
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, FItoKeys(fi)) by {
        reveal UpdateFunction.Valid();
        reveal FICircuitValid();
      }
      assert EvaluateONP(new_c, o, fi) == EvaluateONPUnary(new_c, [o], fi);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [o, i_0], fi) == EvalOk(iv_0);
      assert EvaluateONPUnary(new_c, [o], fi) == EvalOk(UnaryOp(iv_0, nk));
      assert EvaluateONPInner(new_c, [o], fi) == EvalOk(UnaryOp(iv_0, nk));
      assert EvaluateONP(new_c, o, fi) == EvalOk(UnaryOp(iv_0, nk));
      assert Evaluate(new_c, o, fi) == EvalOk(UnaryOp(iv_0, nk));
      assert Evaluate(new_c, o, fi) == EvalOk(e.f(fi).outputs[o]) by {
        InsertUnaryF(c, nk, fi);
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

  lemma InsertUnaryConserves(c: Circuit, nk: CNodeKind)
    requires c.Valid()
    requires CNodeKindIsUnary(nk)
    ensures CircuitConserved(c, InsertUnaryImpl(c, nk).0)
    ensures CircuitUnconnected(c, InsertUnaryImpl(c, nk).0)
    ensures
      var (new_c, e) := InsertUnaryImpl(c, nk);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertUnaryImpl(c, nk);
    reveal Circuit.Valid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertUnary(c: Circuit, nk: CNodeKind): (r: (Circuit, Scuf))
    requires c.Valid()
    requires CNodeKindIsUnary(nk)
    ensures
      var (new_c, e) := r;
      && r == InsertUnaryImpl(c, nk)
      && r.0.Valid()
      && e.Valid(new_c)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertUnaryCorrect(c, nk);
    InsertUnaryConserves(c, nk);
    InsertUnaryImpl(c, nk)
  }

  function UnaryInserter(nk: CNodeKind): (r: ScufInserter)
    requires CNodeKindIsUnary(nk)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    reveal ScufInserter.Valid();
    var z := ScufInserter(
      UnaryUF(nk),
      (c: Circuit) requires c.Valid() => InsertUnary(c, nk)
      );
    assert z.Valid() by {
      reveal SimpleInsertion();
    }
    z 
  }

}

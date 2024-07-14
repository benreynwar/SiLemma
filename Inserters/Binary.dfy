module Inserters_Binary {

  import opened Circ
  import opened Scuf 
  import opened MapFunction
  import opened Subcircuit
  import opened Utils
  import opened Eval
  import opened ConservedSubcircuit

  function BinaryOp(a: bool, b: bool, nk: CNodeKind): bool
    requires CNodeKindIsBinary(nk)
  {
    match nk {
      case CAnd =>
        a && b
      case COr =>
        a || b
      case CXor =>
        Xor(a, b)
    }
  }

  function BinaryUF(nk: CNodeKind): (uf: UpdateFunction)
    requires CNodeKindIsBinary(nk)
    ensures uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      2, 1, 0,
      (si: SI) requires |si.inputs| == 2 && |si.state| == 0
        => SO([BinaryOp(si.inputs[0], si.inputs[1], nk)], [])
    )
  }

  function InsertBinaryImpl(c: Circuit, nk: CNodeKind): (r: (Circuit, Scuf))
    requires c.Valid()
    requires CNodeKindIsBinary(nk)
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
    var uf := BinaryUF(nk);
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

  lemma InsertBinaryF(c: Circuit, nk: CNodeKind, fi: FI)
    requires c.Valid()
    requires CNodeKindIsBinary(nk)
    requires
      var (new_c, s) := InsertBinaryImpl(c, nk);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var (new_c, s) := InsertBinaryImpl(c, nk);
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      && s.f(fi) == FO(map[s.mp.outputs[0]:=BinaryOp(fi.inputs[s.mp.inputs[0]], fi.inputs[s.mp.inputs[1]], nk)], map[])
    {
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      reveal MapToSeq();
      reveal SeqsToMap();
    }

  lemma InsertBinaryCorrect(c: Circuit, nk: CNodeKind)
    requires c.Valid()
    requires CNodeKindIsBinary(nk)
    ensures
      var (new_c, s) := InsertBinaryImpl(c, nk);
      && s.Valid(new_c)
  {
    var (new_c, s) := InsertBinaryImpl(c, nk);
    var o := s.mp.outputs[0];
    var i_0 := s.mp.inputs[0];
    var i_1 := s.mp.inputs[1];
    var path := [s.mp.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) && PathValid(new_c, [o, i_1]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert new_c.Valid();
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, s.mp.inputs, s.mp.state)
      ensures
        var iv_0 := fi.inputs[i_0];
        var iv_1 := fi.inputs[i_1];
        && FICircuitValid(new_c, fi)
        && (EvaluateONP(new_c, o, fi) == EvalOk(BinaryOp(iv_0, iv_1, nk)))
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
      assert EvaluateONPBinary(new_c, [o], fi) == EvalOk(BinaryOp(iv_0, iv_1, nk));
      assert EvaluateONPInner(new_c, [o], fi) == EvalOk(BinaryOp(iv_0, iv_1, nk));
      assert EvaluateONP(new_c, o, fi) == EvalOk(BinaryOp(iv_0, iv_1, nk));
      assert Evaluate(new_c, o, fi) == EvalOk(BinaryOp(iv_0, iv_1, nk));
      assert Evaluate(new_c, o, fi) == EvalOk(s.f(fi).outputs[o]) by {
        InsertBinaryF(c, nk, fi);
      }
    }
    assert ScValid(new_c, s.sc) by {
      reveal Scuf.SomewhatValid();
    }
    assert s.EvaluatesCorrectly(new_c) by {
      reveal Scuf.EvaluatesCorrectly();
      reveal MapMatchesSeqs();
    }
    assert s.Valid(new_c);
  }

  lemma InsertBinaryConserves(c: Circuit, nk: CNodeKind)
    requires c.Valid()
    requires CNodeKindIsBinary(nk)
    ensures CircuitConserved(c, InsertBinaryImpl(c, nk).0)
    ensures CircuitUnconnected(c, InsertBinaryImpl(c, nk).0)
    ensures
      var (new_c, e) := InsertBinaryImpl(c, nk);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertBinaryImpl(c, nk);
    reveal Circuit.Valid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertBinary(c: Circuit, nk: CNodeKind): (r: (Circuit, Scuf))
    requires c.Valid()
    requires CNodeKindIsBinary(nk)
    ensures
      var (new_c, e) := r;
      && r == InsertBinaryImpl(c, nk)
      && r.0.Valid()
      && e.Valid(new_c)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertBinaryCorrect(c, nk);
    InsertBinaryConserves(c, nk);
    InsertBinaryImpl(c, nk)
  }
  
  function BinaryInserter(nk: CNodeKind): (r: ScufInserter)
    requires CNodeKindIsBinary(nk)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    reveal ScufInserter.Valid();
    var z := ScufInserter(
      BinaryUF(nk),
      (c: Circuit) requires c.Valid() => InsertBinary(c, nk)
      );
    assert z.Valid() by {
      reveal SimpleInsertion();
    }
    z 
  }

}
module Build.And {

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  datatype AndPorts = AndPorts(
    i_0: NP,
    i_1: NP,
    o: NP
    )

  function AndBehav(p: AndPorts, knowns: map<NP, bool>): (r: map<NP, bool>)
    requires knowns.Keys == {p.i_0, p.i_1}
    ensures r.Keys == {p.o}
  {
    map[p.o := knowns[p.i_0] && knowns[p.i_1]]
  }

  function InsertAndImpl(c: Circuit): (r: (Circuit, AndPorts, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntitySomewhatValid(r.0, r.2)
    ensures MapFunctionValid(r.2.mf)
    ensures ScValid(r.0, r.2.sc)
  {
    reveal CircuitValid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CAnd],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var i_1 := NP(new_node, INPUT_1);
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := {i_0, i_1};
    var outputs := {o_0};
    var m := AndPorts(i_0, i_1, o_0);
    var f: FI --> FO := (fi: FI) requires fi.inputs.Keys == inputs && |fi.state.Keys| == 0 =>
      FO(AndBehav(m, fi.inputs), map[]);
    var e := Entity({new_node}, MapFunction(inputs, outputs, {}, f));
    assert forall np :: np in new_c.PortSource.Values ==> np.n !in e.sc;
    reveal ScValid();
    assert ScValid(new_c, e.sc) by {
      reveal ScValid();
    }
    assert EntitySomewhatValid(new_c, e) by {
      reveal EntitySomewhatValid();
      reveal ConnOutputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal SeqInputs();
      reveal SeqOutputs();
      reveal AllONPs();
      assert (AllONPs(new_c, e.sc) >= e.mf.outputs >= ConnOutputs(new_c, e.sc));
      assert (e.mf.inputs == AllInputs(new_c, e.sc));
    }
    assert MapFunctionValid(e.mf) by {
      reveal MapFunctionValid();
    }
    (new_c, m, e)
  }

  lemma InsertAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, m, e) := InsertAndImpl(c);
      && EntityValid(new_c, e)
  {
    var (new_c, m, e) := InsertAndImpl(c);
    var path := [m.o];
    assert PathValid(new_c, path) && PathValid(new_c, [m.o, m.i_0]) && PathValid(new_c, [m.o, m.i_1]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert CircuitValid(new_c);
    forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
      ensures
        var iv_0 := fi.inputs[m.i_0];
        var iv_1 := fi.inputs[m.i_1];
        EvaluateONP(new_c, m.o, fi) == EvalOk(iv_0 && iv_1)
    {
      var iv_0 := fi.inputs[m.i_0];
      var iv_1 := fi.inputs[m.i_1];
      assert Seq.HasNoDuplicates(path);
      assert EvaluateONP(new_c, m.o, fi) == EvaluateONPBinary(new_c, [m.o], fi);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [m.o, m.i_0], fi) == EvalOk(iv_0);
      assert EvaluateINPInner(new_c, [m.o, m.i_1], fi) == EvalOk(iv_1);
      assert EvaluateONPBinary(new_c, [m.o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONPInner(new_c, [m.o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONP(new_c, m.o, fi) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, m.o, fi) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, m.o, fi) == EvalOk(e.mf.f(fi).outputs[m.o]);
    }
    assert EntityEvaluatesCorrectly(new_c, e) by {
      reveal EntityEvaluatesCorrectly();
    }
    assert EntityValid(new_c, e);
  }

  lemma InsertAndConserves(c: Circuit)
    requires CircuitValid(c)
    ensures CircuitConserved(c, InsertAndImpl(c).0)
    ensures CircuitUnconnected(c, InsertAndImpl(c).0)
    ensures
      var (new_c, m, e) := InsertAndImpl(c);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, m, e) := InsertAndImpl(c);
    reveal CircuitValid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertAnd(c: Circuit): (r: (Circuit, AndPorts, Entity))
    requires CircuitValid(c)
    ensures
      var (new_c, m, e) := r;
      && r == InsertAndImpl(c)
      && CircuitValid(r.0)
      && EntityValid(new_c, e)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertAndCorrect(c);
    InsertAndConserves(c);
    InsertAndImpl(c)
  }

  //lemma InsertAndScOutputBoundaryEmpty(c: Circuit)
  //  requires CircuitValid(c)
  //  ensures
  //    var (new_c, p, e) := InsertAnd(c);
  //    ScOutputBoundary(new_c, e.sc) == {}
  //{
  //  var (new_c, p, e) := InsertAnd(c);
  //  reveal CircuitValid();
  //  assert forall np: NP :: np.n in e.sc ==> np !in c.PortSource.Values;
  //}

}

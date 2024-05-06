module Build.And {

  import opened Circ
  import opened Equiv
  import opened Eval
  import opened Utils
  import opened MapFunction
  import opened ConservedSubcircuit

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

  function InsertAndImpl(c: Circuit): (r: (Circuit, AndPorts, Equiv))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EquivValid(r.0, r.2)
  {
    reveal EquivValid();
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
    var f: map<NP, bool> --> map<NP, bool> := (x: map<NP, bool>) requires x.Keys == inputs =>
      AndBehav(m, x);
    var e := Equiv({new_node}, inputs, outputs, f);
    assert forall np :: np in new_c.PortSource.Values ==> np.n !in e.sc;
    reveal ScValid();
    reveal NPsValidAndInSc();
    reveal EquivScOutputsInOutputs();
    reveal MapFunctionValid();
    assert EquivValid(new_c, e);
    (new_c, m, e)
  }

  lemma InsertAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, m, e) := InsertAndImpl(c);
      && EquivValid(new_c, e)
      && EquivTrue(new_c, e)
  {
    var (new_c, m, e) := InsertAndImpl(c);
    var path := [m.o];
    assert PathValid(new_c, path) && PathValid(new_c, [m.o, m.i_0]) && PathValid(new_c, [m.o, m.i_1]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert CircuitValid(new_c);
    forall knowns: map<NP, bool> | knowns.Keys == e.inputs
      ensures
        var iv_0 := knowns[m.i_0];
        var iv_1 := knowns[m.i_1];
        EvaluateONP(new_c, m.o, knowns) == EvalOk(iv_0 && iv_1)
    {
      var iv_0 := knowns[m.i_0];
      var iv_1 := knowns[m.i_1];
      assert Seq.HasNoDuplicates(path);
      assert EvaluateONP(new_c, m.o, knowns) == EvaluateONPBinary(new_c, [m.o], knowns);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [m.o, m.i_0], knowns) == EvalOk(iv_0);
      assert EvaluateINPInner(new_c, [m.o, m.i_1], knowns) == EvalOk(iv_1);
      assert EvaluateONPBinary(new_c, [m.o], knowns) == EvalOk(iv_0 && iv_1);
      assert EvaluateONPInner(new_c, [m.o], knowns) == EvalOk(iv_0 && iv_1);
      assert EvaluateONP(new_c, m.o, knowns) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, m.o, knowns) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, m.o, knowns) == EvalOk(e.f(knowns)[m.o]);
    }
    reveal EquivTrue();
    assert EquivTrue(new_c, e);
  }

  lemma InsertAndConserves(c: Circuit)
    requires CircuitValid(c)
    ensures CircuitConserved(c, InsertAndImpl(c).0)
    ensures CircuitUnconnected(c, InsertAndImpl(c).0)
    ensures
      var (new_c, m, e) := InsertAndImpl(c);
      SubcircuitIsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, m, e) := InsertAndImpl(c);
    reveal CircuitValid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal SubcircuitIsIsland();
  }

  function InsertAnd(c: Circuit): (r: (Circuit, AndPorts, Equiv))
    requires CircuitValid(c)
    ensures
      var (new_c, m, e) := r;
      && r == InsertAndImpl(c)
      && CircuitValid(r.0)
      && EquivTrue(new_c, e)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && SubcircuitIsIsland(new_c, e.sc)
  {
    InsertAndCorrect(c);
    InsertAndConserves(c);
    InsertAndImpl(c)
  }

  lemma InsertAndScOutputBoundaryEmpty(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, p, e) := InsertAnd(c);
      ScOutputBoundary(new_c, e.sc) == {}
  {
    var (new_c, p, e) := InsertAnd(c);
    reveal CircuitValid();
    assert forall np: NP :: np.n in e.sc ==> np !in c.PortSource.Values;
  }

}

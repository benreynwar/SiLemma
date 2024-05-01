module Build {

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Compose
  import opened ComposeEval
  import opened Utils
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

  function InsertAndImpl(c: Circuit): (r: (Circuit, AndPorts, Equiv))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EquivValid(r.0, r.2)
  {
    reveal EquivValid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    //assert forall np: NP :: np in c.PortSource.Keys ==> np.n != new_node;
    //assert forall np: NP :: np in c.PortSource.Values ==> np.n != new_node;
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
    //assert ScOutputBoundary(new_c, e.sc) == {};
    (new_c, m, e)
  }

  lemma InsertAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, m, e) := InsertAndImpl(c);
      EquivTrue(new_c, e)
  {
    var (new_c, m, e) := InsertAndImpl(c);
    var path := [m.o];
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
    assert EquivTrue(new_c, e);
  }

  function InsertAnd(c: Circuit): (r: (Circuit, AndPorts, Equiv))
    requires CircuitValid(c)
    ensures
      var (new_c, m, e) := r;
      r == InsertAndImpl(c) &&
      EquivTrue(new_c, e)
  {
    InsertAndCorrect(c);
    InsertAndImpl(c)
  }

  datatype And3Ports = And3Ports(
    i_0: NP,
    i_1: NP,
    i_2: NP,
    o: NP,
    o_extra: NP
    )

  function And3Behav(p: And3Ports, knowns: map<NP, bool>): (r: map<NP, bool>)
    requires knowns.Keys == {p.i_0, p.i_1, p.i_2}
    ensures r.Keys == {p.o, p.o_extra}
  {
    map[p.o := knowns[p.i_0] && knowns[p.i_1] &&knowns[p.i_2], p.o_extra := knowns[p.i_0] && knowns[p.i_1]]
  }

  lemma And3BehavIsComposition(p1: AndPorts, p2: AndPorts, knowns: map<NP, bool>)
    requires knowns.Keys == {p1.i_0, p1.i_1, p2.i_0}
    requires SetsNoIntersection({p1.i_0, p1.i_1}, {p1.o})
    requires SetsNoIntersection({p2.i_0, p2.i_1}, {p2.o})
    requires p2.i_0 != p2.i_1
    requires SetsNoIntersection({p1.i_0, p1.i_1, p1.o}, {p2.i_0, p2.i_1, p2.o})
    ensures 
      var p := And3Ports(p1.i_0, p1.i_1, p2.i_0, p2.o, p1.o);
      var o_base := And3Behav(p, knowns);
      var input_keys_1 := {p1.i_0, p1.i_1};
      var input_keys_2 := {p2.i_0, p2.i_1};
      var mf1 := MapFunction(input_keys_1, {p1.o}, (x: map<NP, bool>) requires x.Keys == input_keys_1 => AndBehav(p1, x));
      var mf2 := MapFunction(input_keys_2, {p2.o}, (x: map<NP, bool>) requires x.Keys == input_keys_2=> AndBehav(p2, x));
      var connection := map[p2.i_1 := p1.o];
      var o_compose := ComposeMapFunction(mf1, mf2, connection, knowns);
      o_base == o_compose
  {
    var p := And3Ports(p1.i_0, p1.i_1, p2.i_0, p2.o, p1.o);
    var o_base := And3Behav(p, knowns);
    var input_keys_1 := {p1.i_0, p1.i_1};
    var input_keys_2 := {p2.i_0, p2.i_1};
    var mf1 := MapFunction(input_keys_1, {p1.o}, (x: map<NP, bool>) requires x.Keys == input_keys_1 => AndBehav(p1, x));
    var mf2 := MapFunction(input_keys_2, {p2.o}, (x: map<NP, bool>) requires x.Keys == input_keys_2=> AndBehav(p2, x));
    var connection := map[p2.i_1 := p1.o];
    var o_compose := ComposeMapFunction(mf1, mf2, connection, knowns);
    assert o_base == o_compose;
  }

  function {:vcs_split_on_every_assert} InsertAnd3Impl(c: Circuit): (r: (Circuit, And3Ports, Equiv))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EquivValid(r.0, r.2)
  {
    var (c1, a, e1) := InsertAnd(c);
    reveal EquivValid();
    var (c2, b, e2) := InsertAnd(c1);
    EquivConserved(c1, c2, e1);
    reveal ComposedValid();
    assert SetsNoIntersection(e1.sc, e2.sc);
    assert ScValid(c2, e1.sc);
    assert ScValid(c2, e2.sc);
    assert (NPBetweenSubcircuits(c2, e1.sc, e2.sc) == {});
    var c3 := Connect(c2, b.i_1, a.o);
    EquivConserved(c2, c3, e1);
    EquivConserved(c2, c3, e2);
    var e := ComposeEquiv(c3, e1, e2);
    var combined_input_keys := ComposeEquivInputs(c3, e1, e2);
    var ports := And3Ports(a.i_0, a.i_1, b.i_0, b.o, a.o);
    var f: map<NP, bool> --> map<NP, bool> := (x: map<NP, bool>) requires x.Keys == combined_input_keys =>
      And3Behav(ports, x);
    var new_e := SwapEquivF(c3, e, f);
    assert EquivValid(c3, new_e);
    (c3, ports, new_e)
  }

  lemma InsertAnd3CorrectHelper(c: Circuit, e1: Equiv, e2: Equiv, knowns: map<NP, bool>)
    requires ComposedValid(c, e1, e2)
    requires
      var combined_input_keys := ComposeEquivInputs(c, e1, e2);
      knowns.Keys == combined_input_keys
    ensures
      var e := ComposeEquiv(c, e1, e2);
      (e.f(knowns) == ComposeEquivF(c, e1, e2, knowns))
  {
    reveal ComposedValid();
    reveal EquivValid();
    var combined_input_keys := ComposeEquivInputs(c, e1, e2);
    var e := ComposeEquiv(c, e1, e2);
    assert (e.f(knowns) == ComposeEquivF(c, e1, e2, knowns));
  }

  lemma {:vcs_split_on_every_assert} InsertAnd3Correct(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, ports, e) := InsertAnd3Impl(c);
      EquivTrue(new_c, e)
  {
    var (new_c, ports, e) := InsertAnd3Impl(c);
    reveal EquivValid();
    var (c1, a, e1) := InsertAnd(c);
    var (c2, b, e2) := InsertAnd(c1);
    var p := And3Ports(a.i_0, a.i_1, b.i_0, b.o, a.o);
    var c3 := Connect(c2, b.i_1, a.o);
    reveal ComposedValid();
    EquivConserved(c1, c2, e1);
    EquivConserved(c2, c3, e1);
    EquivConserved(c2, c3, e2);
    var e_alt := ComposeEquiv(c3, e1, e2);
    ComposeEquivCorrect(c3, e1, e2);
    assert EquivTrue(c3, e_alt);
    var combined_input_keys := ComposeEquivInputs(c3, e1, e2);
    forall knowns: map<NP, bool> | knowns.Keys == combined_input_keys
      ensures e_alt.f(knowns) == e.f(knowns)
    {
      And3BehavIsComposition(a, b, knowns);
      assert e_alt.f(knowns) == ComposeEquivF(c3, e1, e2, knowns);
      assert e.f(knowns) == And3Behav(p, knowns);
      assert e_alt.f(knowns) == e.f(knowns);
    }
    assert EquivTrue(c3, e);
  }

}
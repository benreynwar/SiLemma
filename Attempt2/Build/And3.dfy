module Build.And3 {

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Compose
  import opened ComposeEval
  import opened Utils
  import opened MapFunction
  import opened Equiv
  import opened HideOutput
  import opened Connecting

  import opened And

  datatype And3Ports = And3Ports(
    i_0: NP,
    i_1: NP,
    i_2: NP,
    o: NP
    )

  function And3Behav(p: And3Ports, knowns: map<NP, bool>): (r: map<NP, bool>)
    requires knowns.Keys == {p.i_0, p.i_1, p.i_2}
    ensures r.Keys == {p.o}
  {
    map[p.o := knowns[p.i_0] && knowns[p.i_1] && knowns[p.i_2]]
  }

  lemma And3BehavIsComposition(p1: AndPorts, p2: AndPorts, knowns: map<NP, bool>)
    requires knowns.Keys == {p1.i_0, p1.i_1, p2.i_0}
    requires SetsNoIntersection({p1.i_0, p1.i_1}, {p1.o})
    requires SetsNoIntersection({p2.i_0, p2.i_1}, {p2.o})
    requires p2.i_0 != p2.i_1
    requires SetsNoIntersection({p1.i_0, p1.i_1, p1.o}, {p2.i_0, p2.i_1, p2.o})
    ensures 
      var p := And3Ports(p1.i_0, p1.i_1, p2.i_0, p2.o);
      var o_base := And3Behav(p, knowns);
      var input_keys_1 := {p1.i_0, p1.i_1};
      var input_keys_2 := {p2.i_0, p2.i_1};
      var mf1 := MapFunction(input_keys_1, {p1.o}, (x: map<NP, bool>) requires x.Keys == input_keys_1 => AndBehav(p1, x));
      var mf2 := MapFunction(input_keys_2, {p2.o}, (x: map<NP, bool>) requires x.Keys == input_keys_2=> AndBehav(p2, x));
      var connection := map[p2.i_1 := p1.o];
      var o_compose := ComposeMapFunction(mf1, mf2, connection, knowns);
      o_base == o_compose - {p1.o}
  {
    var p := And3Ports(p1.i_0, p1.i_1, p2.i_0, p2.o);
    var o_base := And3Behav(p, knowns);
    var input_keys_1 := {p1.i_0, p1.i_1};
    var input_keys_2 := {p2.i_0, p2.i_1};
    var mf1 := MapFunction(input_keys_1, {p1.o}, (x: map<NP, bool>) requires x.Keys == input_keys_1 => AndBehav(p1, x));
    var mf2 := MapFunction(input_keys_2, {p2.o}, (x: map<NP, bool>) requires x.Keys == input_keys_2=> AndBehav(p2, x));
    var connection := map[p2.i_1 := p1.o];
    var o_compose := ComposeMapFunction(mf1, mf2, connection, knowns);
    assert o_base == o_compose - {p1.o};
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
    assert forall np: NP :: np.n in e.sc ==> np !in c.PortSource.Values;
    var combined_input_keys := ComposeEquivInputs(c3, e1, e2);
    var ports := And3Ports(a.i_0, a.i_1, b.i_0, b.o);
    var f: map<NP, bool> --> map<NP, bool> := (x: map<NP, bool>) requires x.Keys == combined_input_keys =>
      And3Behav(ports, x);
    var e_h := EquivHideOutput(c3, e, {a.o});
    var e_s := SwapEquivF(c3, e_h, f);
    assert EquivValid(c3, e_s);
    (c3, ports, e_s)
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
    var p := And3Ports(a.i_0, a.i_1, b.i_0, b.o);
    var c3 := Connect(c2, b.i_1, a.o);
    ConnectPreservesSubcircuit(c2, b.i_1, a.o, e1.sc);
    ConnectPreservesSubcircuit(c2, b.i_1, a.o, e2.sc);
    reveal ComposedValid();
    assert forall np: NP :: np.n in e1.sc ==> np !in c.PortSource.Values;
    assert forall np: NP :: np.n in e2.sc ==> np !in c.PortSource.Values;
    EquivConserved(c1, c2, e1);
    EquivConserved(c2, c3, e1);
    EquivConserved(c2, c3, e2);
    var e_alt := ComposeEquiv(c3, e1, e2);
    ComposeEquivCorrect(c3, e1, e2);
    assert EquivTrue(c3, e_alt);
    var e_rem := EquivHideOutput(c3, e_alt, {a.o});
    var combined_input_keys := ComposeEquivInputs(c3, e1, e2);
    forall knowns: map<NP, bool> | knowns.Keys == combined_input_keys
      ensures e_rem.f(knowns) == e.f(knowns)
    {
      And3BehavIsComposition(a, b, knowns);
      assert e_rem.f(knowns) == ComposeEquivF(c3, e1, e2, knowns) - {a.o};
      assert e.f(knowns) == And3Behav(p, knowns);
      assert e_rem.f(knowns) == e.f(knowns);
    }
    assert EquivTrue(c3, e);
  }

}
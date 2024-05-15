module Build.And3 {

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Utils
  import opened Entity
  import opened HideOutput
  import opened MapFunction
  import opened ConnectionEval
  import opened Connection
  import opened IslandBundle
  import opened Subcircuit

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
      var mf1 := MapFunction(input_keys_1, {p1.o}, {}, (fi: FI) requires FIValid(fi, input_keys_1, {}) => FO(AndBehav(p1, fi.inputs), map[]));
      var mf2 := MapFunction(input_keys_2, {p2.o}, {}, (fi: FI) requires FIValid(fi, input_keys_2, {}) => FO(AndBehav(p2, fi.inputs), map[]));
      assert MapFunctionValid(mf1) && MapFunctionValid(mf2) by {
        reveal MapFunctionValid();
      }
      var connection := map[p2.i_1 := p1.o];
      var o_compose := ConnectMapFunctionF(mf1, mf2, connection, FI(knowns, map[]));
      o_base == o_compose.outputs - {p1.o}
  {
    var p := And3Ports(p1.i_0, p1.i_1, p2.i_0, p2.o);
    var o_base := And3Behav(p, knowns);
    var input_keys_1 := {p1.i_0, p1.i_1};
    var input_keys_2 := {p2.i_0, p2.i_1};
    var mf1 := MapFunction(input_keys_1, {p1.o}, {}, (fi: FI) requires FIValid(fi, input_keys_1, {}) => FO(AndBehav(p1, fi.inputs), map[]));
    var mf2 := MapFunction(input_keys_2, {p2.o}, {}, (fi: FI) requires FIValid(fi, input_keys_2, {}) => FO(AndBehav(p2, fi.inputs), map[]));
    assert MapFunctionValid(mf1) && MapFunctionValid(mf2) by {
      reveal MapFunctionValid();
    }
    var connection := map[p2.i_1 := p1.o];
    var o_compose := ConnectMapFunctionF(mf1, mf2, connection, FI(knowns, map[]));
    assert o_base == o_compose.outputs - {p1.o};
  }

  function {:vcs_split_on_every_assert} InsertAnd3Impl(c: Circuit): (r: (Circuit, And3Ports, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntityValid(r.0, r.2)
  {
    var eb1 := IslandBundle(c, [], map[]);
    assert IslandBundleValid(eb1) by {
      reveal IslandBundleValid();
    }
    var (c1, a, e1) := InsertAnd(c);
    var (eb2, a_ref) := AddEntity(eb1, c1, e1);
    assert e1.sc == {a.o.n};
    assert EntityValid(c1, e1);

    assert e1 == eb2.es[a_ref].value;

    var (c2, b, e2) := InsertAnd(c1);
    var (eb3, b_ref) := AddEntity(eb2, c2, e2);
    assert e2.sc == {b.o.n};

    assert e1 == eb3.es[a_ref].value;

    //assert EntityValid(c2, e1) by {
    //  reveal IslandBundleValid();
    //}
    //assert EntityValid(c2, e2);
    //reveal ScValid();
    //assert ScValid(c2, e1.sc);
    //assert ScValid(c2, e2.sc);
    //reveal CircuitValid();
    //assert (NPBetweenSubcircuits(c2, e1.sc, e2.sc) == {});
    var connection := map[b.i_1 := a.o];
    assert ConnectEntitiesRequirements(c2, e1, e2, connection) by {
      reveal IslandBundleValid();
      assert CircuitValid(c2);
      assert EntityValid(c2, e1);
      assert EntityValid(c2, e2);
      assert IsIsland(c2, e1.sc);
      assert IsIsland(c2, e2.sc);
      assert SetsNoIntersection(e1.sc, e2.sc);
      assert ConnectionValid(c2, e1, e2, connection) by {
        reveal ConnectionValid();
        reveal AllINPs();
        reveal AllONPs();
        assert (connection.Keys <= e2.mf.inputs * AllINPs(c2, e2.sc));
        assert (connection.Values <= e1.mf.outputs * AllONPs(c2, e1.sc));
        assert b.i_1 in e2.mf.inputs;
        assert IsIsland(c2, e2.sc);
        assert b.i_1 in AllInputs(c2, e2.sc) by {
          reveal EntitySomewhatValid();
        }
        assert b.i_1 !in c2.PortSource.Keys by {
          reveal UnconnInputs();
          reveal ConnInputs();
          reveal SeqInputs();
        }
        assert SetsNoIntersection(connection.Keys, c2.PortSource.Keys);
      }
    }
    var (c3, e) := ConnectEntities(c2, e1, e2, connection);
    assert e.mf.inputs == {a.i_0, a.i_1, b.i_0};
    assert e.mf.outputs == {a.o, b.o};
    var ports := And3Ports(a.i_0, a.i_1, b.i_0, b.o);
    var f: FI --> FO := (fi: FI) requires FIValid(fi, e.mf.inputs, {}) =>
      FO(And3Behav(ports, fi.inputs), map[]);
    var e_h := EntityHideOutput(c3, e, {a.o});
    var mf := MapFunction(e_h.mf.inputs, e_h.mf.outputs, {}, f);
    assert MapFunctionValid(mf) by {
      reveal MapFunctionValid();
    }
    var e_s := SwapEntityF(c3, e_h, mf);
    assert EntityValid(c3, e_s);
    (c3, ports, e_s)
  }

  //lemma {:vcs_split_on_every_assert} InsertAnd3Correct(c: Circuit)
  //  requires CircuitValid(c)
  //  ensures
  //    var (new_c, ports, e) := InsertAnd3Impl(c);
  //    EntityValid(new_c, e)
  //{
  //  var (new_c, ports, e) := InsertAnd3Impl(c);
  //  var (c1, a, e1) := InsertAnd(c);
  //  var (c2, b, e2) := InsertAnd(c1);
  //  var p := And3Ports(a.i_0, a.i_1, b.i_0, b.o);
  //  assert b.i_1 !in c2.PortSource by {reveal CircuitValid();}
  //  var c3 := Connect(c2, b.i_1, a.o);
  //  ConnectPreservesSubcircuit(c2, b.i_1, a.o, e1.sc);
  //  ConnectPreservesSubcircuit(c2, b.i_1, a.o, e2.sc);
  //  assert forall np: NP :: np.n in e1.sc + e2.sc ==> np !in c.PortSource.Values by {reveal CircuitValid();}
  //  EntityConserved(c1, c2, e1);
  //  EntityConserved(c2, c3, e1);
  //  EntityConserved(c2, c3, e2);
  //  assert ComposedValid(c3, e1, e2) by {reveal ComposedValid();}
  //  var e_alt := ComposeEntity(c3, e1, e2);
  //  ComposeEntityCorrect(c3, e1, e2);
  //  assert EntityTrue(c3, e_alt);
  //  var e_rem := EntityHideOutput(c3, e_alt, {a.o});
  //  var combined_input_keys := ComposeEntityInputs(c3, e1, e2);
  //  forall knowns: map<NP, bool> | knowns.Keys == combined_input_keys
  //    ensures e_rem.f(knowns) == e.f(knowns)
  //  {
  //    And3BehavIsComposition(a, b, knowns);
  //    assert e_rem.f(knowns) == ComposeEntityF(c3, e1, e2, knowns) - {a.o};
  //    assert e.f(knowns) == And3Behav(p, knowns);
  //    assert e_rem.f(knowns) == e.f(knowns);
  //  }
  //  assert EntityTrue(c3, e);
  //}

}
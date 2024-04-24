module Build {

  import opened Circ
  import opened Eval

  function InsertAndImpl(c: Circuit): (r: (Circuit, (NP, NP), NP, Subcircuit, map<NP,bool> --> bool))
    {
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CAnd],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var i_1 := NP(new_node, INPUT_1);
    var o_0 := NP(new_node, OUTPUT_0);
    var f: map<NP, bool> --> bool := x requires i_0 in x && i_1 in x => x[i_0] && x[i_1];
    var sc := Subcircuit({new_node}, {i_0, i_1});
    (new_c, (i_0, i_1), o_0, sc, f)
  }

  function GetBoundary(c: Circuit): set<NP>
  {
    (set np: NP | 
      np in AllNP(c) &&
      var nk := c.NodeKind[np.n];
      ((nk.CInput? && ONPValid(c, np)) || (nk.CSeq? && ONPValid(c, np)) ||
       (INPValid(c, np) && (np !in c.PortSource)))
      :: np
    )
  }

  function GetFullSubcircuit(c: Circuit): Subcircuit
  {
    Subcircuit(
      nodes := c.NodeKind.Keys,
      boundary := GetBoundary(c)
    )
  }

  lemma InsertAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, (i_0, i_1), o_0, sc, f) := InsertAndImpl(c);
      Equiv(new_c, o_0, sc.boundary, f)
  {
    var (new_c, (i_0, i_1), o_0, sc, f) := InsertAndImpl(c);
    var path := [o_0];
    LengthOneNoDuplicates(path);
    assert CircuitValid(new_c);
    forall knowns: map<NP, bool> | knowns.Keys == {i_0, i_1}
      ensures
        var iv_0 := knowns[i_0];
        var iv_1 := knowns[i_1];
        EvaluateONP(new_c, o_0, knowns) == EvalOk(iv_0 && iv_1)
    {
      var iv_0 := knowns[i_0];
      var iv_1 := knowns[i_1];
      assert Seq.HasNoDuplicates(path);
      assert EvaluateONP(new_c, o_0, knowns) == EvaluateONPBinary(new_c, [o_0], knowns);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [o_0, i_0], knowns) == EvalOk(iv_0);
      assert EvaluateINPInner(new_c, [o_0, i_1], knowns) == EvalOk(iv_1);
      assert EvaluateONPBinary(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
      assert EvaluateONPInner(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
      assert EvaluateONP(new_c, o_0, knowns) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o_0, knowns) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o_0, knowns) == EvalOk(f(knowns));
    }
    assert Equiv(new_c, o_0, {i_0, i_1}, f);
  }

  function InsertAnd(c: Circuit): (r: (Circuit, (NP, NP), NP, Subcircuit, map<NP,bool> --> bool))
    requires CircuitValid(c)
    ensures
      var (new_c, (i_0, i_1), o_0, sc, f) := r;
      r == InsertAndImpl(c) &&
      Equiv(new_c, o_0, {i_0, i_1}, f)
  {
    InsertAndCorrect(c);
    InsertAndImpl(c)
  }

  function InsertThreeAndImpl(c: Circuit): (r: (Circuit, (NP, NP, NP), NP, map<NP, bool> --> bool))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
  {
    var (c, (ai_0, ai_1), ao_0, a_sc, a_f) := InsertAnd(c);
    var (c, (bi_0, bi_1), bo_0, b_sc, b_f) := InsertAnd(c);
    var c := Connect(c, bi_1, ao_0);
    var f: map<NP, bool> --> bool := x requires ai_0 in x && ai_1 in x && bi_0 in x => x[ai_0] && x[ai_1] && x[bi_0];
    (c, (ai_0, ai_1, bi_0), bo_0, f)
  }

  // Want to prove that when you insert something everything else is unchanged.

  // Want to prove that when you make a connection an Equiv cannot change.

  function UpdateMap<T, U>(m: map<T, U>, old_keys: set<T>, new_keys: set<T>, x: T, y: T): (r: map<T, U>)
    requires y !in old_keys
    requires y in new_keys
    requires x in old_keys
    requires m.Keys == old_keys
    requires x != y
    requires (new_keys == old_keys - {x} + {y}) || (new_keys == old_keys + {y})
    ensures r.Keys == new_keys
    ensures r[y] == m[x]
  {
    var n := m[y := m[x]];
    assert n[y] == m[x];
    if x in new_keys then
      n
    else
      var o := n - {x};
      assert o[y] == m[x];
      o
  }


  lemma ShiftEquivBoundary(c: Circuit, e: Equiv2, orig_input: NP, upstream_input: NP)
    requires orig_input in e.inputs
    requires orig_input in c.PortSource
    requires c.PortSource[orig_input] == upstream_input
    requires orig_input != upstream_input
    requires CircuitValid(c)
    requires EquivValid(c, e)
    requires EquivTrue(c, e)
    ensures
      var new_inputs := e.inputs - {orig_input} + {upstream_input};
      var new_f := (x: map<NP, bool>) requires x.Keys == new_inputs =>
        assert upstream_input in x;
        assert orig_input !in x;
        e.f(UpdateMap(x, new_inputs, e.inputs, upstream_input, orig_input));
      EquivTrue(c, Equiv2(e.output, new_inputs, new_f))
  {
  }

  lemma InsertThreeAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, (i_0, i_1, i_2), o_0, f) := InsertThreeAndImpl(c);
      Equiv(new_c, o_0, {i_0, i_1, i_2}, f)
  {
    var (new_c, (i_0, i_1, i_2), o_0, f) := InsertThreeAndImpl(c);
    var (c_1, (ai_0, ai_1), ao_0, a_sc, a_f) := InsertAnd(c);
    var (c_2, (bi_0, bi_1), bo_0, b_sc, b_f) := InsertAnd(c_1);
    EquivConserved(c_1, c_2, a_sc, ao_0, a_f);
    assert Equiv(c_2, ao_0, {ai_0, ai_1}, a_f);
    assert Equiv(c_2, bo_0, {bi_0, bi_1}, b_f);
    var c_3 := Connect(c_2, bi_1, ao_0);
    EquivConserved(c_2, c_3, a_sc, ao_0, a_f);
    EquivConserved(c_2, c_3, b_sc, bo_0, b_f);
    assert c_3 == new_c;
    assert Equiv(new_c, ao_0, {ai_0, ai_1}, a_f);
    assert Equiv(new_c, bo_0, {bi_0, bi_1}, b_f);
    assert new_c.PortSource[bi_1] == ao_0;
    var new_b_f: map<NP, bool> --> bool := (x: map<NP, bool>) requires x.Keys == {bi_0, ao_0} =>
      b_f(x[bi_1 := x[ao_0]]);
    assert Equiv(new_c, bo_0, {bi_0, ao_0}, new_b_f);
    //var f: map<NP, bool> --> bool := x requires ai_0 in x && ai_1 in x && bi_0 in x => x[ai_0] && x[ai_1] && x[bi_0];
  }

}
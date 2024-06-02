module Build.IdentBuilder {

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  datatype IdentInstance = IdentInstance(
    inputs: seq<NP>,
    outputs: seq<NP>,
    state: seq<CNode>)
  {
  }

  function InsertIdentImpl(c: Circuit): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntitySomewhatValid(r.0, r.1)
    ensures r.1.mf.Valid()
  {
    reveal CircuitValid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CIden],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := [i_0];
    var outputs := [o_0];
    var state := [];
    var mf := MapFunction(inputs, outputs, state, (si: SI) requires SIValid(si, inputs, state) =>
      reveal Seq.ToSet();
      SO([si.inputs[0]], []));
    var e := Entity({new_node}, mf);
    assert EntitySomewhatValid(new_c, e) by {
      reveal EntitySomewhatValid();
      reveal Seq.ToSet();
      reveal ScValid();
      reveal ConnOutputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal AllONPs();
      reveal AllSeq();
      assert ScValid(new_c, e.sc);
      assert forall np: NP :: np.n in e.sc ==> np !in c.PortSource.Values;
    }
    assert mf.Valid() by {
      reveal MapFunction.Valid();
      reveal Seq.ToSet();
      reveal Seq.HasNoDuplicates();
    }
    (new_c, e)
  }

  lemma InsertIdentCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, e) := InsertIdentImpl(c);
      && EntityValid(new_c, e)
  {
    var (new_c, e) := InsertIdentImpl(c);
    var o := e.mf.outputs[0];
    var i_0 := e.mf.inputs[0];
    var path := [e.mf.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert CircuitValid(new_c);
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
      ensures
        var iv_0 := fi.inputs[i_0];
        && FICircuitValid(new_c, fi)
        && (EvaluateONP(new_c, o, fi) == EvalOk(iv_0))
    {
      var iv_0 := fi.inputs[i_0];
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, fi) by {
        reveal MapFunction.Valid();
        reveal FICircuitValid();
      }
      assert EvaluateONP(new_c, o, fi) == EvaluateONPUnary(new_c, [o], fi);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [o, i_0], fi) == EvalOk(iv_0);
      assert EvaluateONPUnary(new_c, [o], fi) == EvalOk(iv_0);
      assert EvaluateONPInner(new_c, [o], fi) == EvalOk(iv_0);
      assert EvaluateONP(new_c, o, fi) == EvalOk(iv_0);
      assert Evaluate(new_c, o, fi) == EvalOk(iv_0);
      assert Evaluate(new_c, o, fi) == EvalOk(e.mf.f(fi).outputs[o]) by {
        reveal MapMatchesSeqs();
      }
    }
    assert ScValid(new_c, e.sc) by {
      reveal EntitySomewhatValid();
    }
    assert EntityEvaluatesCorrectly(new_c, e) by {
      reveal EntityEvaluatesCorrectly();
      reveal MapMatchesSeqs();
    }
    assert EntityValid(new_c, e);
  }

  lemma InsertIdentConserves(c: Circuit)
    requires CircuitValid(c)
    ensures CircuitConserved(c, InsertIdentImpl(c).0)
    ensures CircuitUnconnected(c, InsertIdentImpl(c).0)
    ensures
      var (new_c, e) := InsertIdentImpl(c);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertIdentImpl(c);
    reveal CircuitValid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertIdent(c: Circuit): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures
      var (new_c, e) := r;
      && r == InsertIdentImpl(c)
      && CircuitValid(r.0)
      && EntityValid(new_c, e)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertIdentCorrect(c);
    InsertIdentConserves(c);
    InsertIdentImpl(c)
  }

}

module Inserters.Const{

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  function InsertConstImpl(c: Circuit, v: bool): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntitySomewhatValid(r.0, r.1)
    ensures r.1.mf.Valid()
  {
    reveal CircuitValid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CConst(v)],
      PortSource := c.PortSource
    );
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := [];
    var outputs := [o_0];
    var state := [];
    var mf := MapFunction(inputs, outputs, state, (si: SI) requires SIValid(si, inputs, state) =>
      reveal Seq.ToSet();
      SO([v], []));
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

  lemma InsertConstCorrect(c: Circuit, v: bool)
    requires CircuitValid(c)
    ensures
      var (new_c, e) := InsertConstImpl(c, v);
      && EntityValid(new_c, e)
  {
    var (new_c, e) := InsertConstImpl(c, v);
    assert |e.mf.inputs| == 0;
    var o := e.mf.outputs[0];
    var path := [e.mf.outputs[0]];
    LengthOneNoDuplicates(path);
    forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
      ensures
        && FICircuitValid(new_c, fi)
        && (EvaluateONP(new_c, o, fi) == EvalOk(v))
    {
      reveal e.mf.Valid();
      reveal Seq.ToSet();
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, fi) by {
        reveal MapFunction.Valid();
        reveal FICircuitValid();
      }
      reveal Seq.HasNoDuplicates();
      assert PathValid(new_c, path) by {
        reveal PathValid();
      }
      assert EvaluateONPInner(new_c, [o], fi) == EvalOk(v);
      assert EvaluateONP(new_c, o, fi) == EvalOk(v);
      assert Evaluate(new_c, o, fi) == EvalOk(v);
      assert Evaluate(new_c, o, fi) == EvalOk(e.mf.f(fi).outputs[o]) by {
        reveal MapMatchesSeqs();
      }
    }
    assert ScValid(new_c, e.sc) by {
      reveal EntitySomewhatValid();
    }
    assert EntityEvaluatesCorrectly(new_c, e) by {
      EntityFOutputsAreValid(new_c, e);
      reveal Seq.ToSet();
      reveal EntityEvaluatesCorrectly();
      reveal MapMatchesSeqs();
    }
    assert EntityValid(new_c, e);
  }

  lemma InsertConstConserves(c: Circuit, v: bool)
    requires CircuitValid(c)
    ensures CircuitConserved(c, InsertConstImpl(c, v).0)
    ensures CircuitUnconnected(c, InsertConstImpl(c, v).0)
    ensures
      var (new_c, e) := InsertConstImpl(c, v);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertConstImpl(c, v);
    reveal CircuitValid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertConst(c: Circuit, v: bool): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures
      var (new_c, e) := r;
      && r == InsertConstImpl(c, v)
      && CircuitValid(r.0)
      && EntityValid(new_c, e)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertConstCorrect(c, v);
    InsertConstConserves(c, v);
    InsertConstImpl(c, v)
  }

}

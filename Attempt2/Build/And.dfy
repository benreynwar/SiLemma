module Build.AndBuilder {

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  datatype AndInstance = AndInstance(
    inputs: seq<NP>,
    outputs: seq<NP>,
    state: seq<CNode>)
  {
  }

  function AndSF(si: SI): (so: SO)
    requires |si.inputs| == 2
    requires |si.state| == 0
  {
    SO([si.inputs[0] && si.inputs[1]], [])
  }

  ghost predicate AndMFValid(mf: MapFunction)
  {
    && mf.Valid()
    && |mf.inputs| == 2
    && |mf.state| == 0
    && |mf.outputs| == 1
    && (forall si :: SIValid(si, mf.inputs, mf.state) ==> (
      && mf.sf.requires(si)
      && mf.sf(si) == AndSF(si)
      )
    )
  }

  function InsertAndImpl(c: Circuit): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntitySomewhatValid(r.0, r.1)
    ensures r.1.mf.Valid()
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
    var inputs := [i_0, i_1];
    var outputs := [o_0];
    var state := [];
    var mf := MapFunction(inputs, outputs, state, (si: SI) requires SIValid(si, inputs, state) =>
      reveal Seq.ToSet();
      SO([si.inputs[0] && si.inputs[1]], []));
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

  lemma InsertAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, e) := InsertAndImpl(c);
      && EntityValid(new_c, e)
  {
    var (new_c, e) := InsertAndImpl(c);
    var o := e.mf.outputs[0];
    var i_0 := e.mf.inputs[0];
    var i_1 := e.mf.inputs[1];
    var path := [e.mf.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) && PathValid(new_c, [o, i_1]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert CircuitValid(new_c);
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
      ensures
        var iv_0 := fi.inputs[i_0];
        var iv_1 := fi.inputs[i_1];
        && FICircuitValid(new_c, fi)
        && (EvaluateONP(new_c, o, fi) == EvalOk(iv_0 && iv_1))
    {
      var iv_0 := fi.inputs[i_0];
      var iv_1 := fi.inputs[i_1];
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, fi) by {
        reveal MapFunction.Valid();
        reveal FICircuitValid();
      }
      assert EvaluateONP(new_c, o, fi) == EvaluateONPBinary(new_c, [o], fi);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [o, i_0], fi) == EvalOk(iv_0);
      assert EvaluateINPInner(new_c, [o, i_1], fi) == EvalOk(iv_1);
      assert EvaluateONPBinary(new_c, [o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONPInner(new_c, [o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONP(new_c, o, fi) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o, fi) == EvalOk(iv_0 && iv_1);
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

  lemma InsertAndConserves(c: Circuit)
    requires CircuitValid(c)
    ensures CircuitConserved(c, InsertAndImpl(c).0)
    ensures CircuitUnconnected(c, InsertAndImpl(c).0)
    ensures
      var (new_c, e) := InsertAndImpl(c);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertAndImpl(c);
    reveal CircuitValid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertAnd(c: Circuit): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures
      var (new_c, e) := r;
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

}

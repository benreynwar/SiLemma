module Inserters.Const{

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Scuf
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  function ConstUF(value: bool): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      0, 1, 0,
      (si: SI) requires |si.inputs| == 0 && |si.state| == 0 => SO([value], []))
  }

  function InsertConstImpl(c: Circuit, value: bool): (r: (Circuit, Scuf))
    requires c.Valid()
    ensures r.0.Valid()
    ensures r.1.SomewhatValid(r.0)
    ensures r.1.MapValid()
    ensures r.1.uf.Valid()
  {
    reveal Circuit.Valid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CConst(value)],
      PortSource := c.PortSource
    );
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := [];
    var outputs := [o_0];
    var state := [];
    var mp := ScufMap(inputs, outputs, state);
    assert mp.Valid() by {
      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
    }
    var uf := ConstUF(value);
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

  lemma InsertConstF(c: Circuit, value: bool, fi: FI)
    requires c.Valid()
    requires
      var (new_c, s) := InsertConstImpl(c, value);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var (new_c, s) := InsertConstImpl(c, value);
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      && s.f(fi) == FO(map[s.mp.outputs[0]:=value], map[])
    {
      reveal Scuf.SomewhatValid();
      reveal Seq.ToSet();
      reveal MapToSeq();
      reveal SeqsToMap();
    }
      


  lemma InsertConstCorrect(c: Circuit, value: bool)
    requires c.Valid()
    ensures
      var (new_c, e) := InsertConstImpl(c, value);
      && e.Valid(new_c)
  {
    reveal Seq.ToSet();
    var (new_c, s) := InsertConstImpl(c, value);
    var o := s.mp.outputs[0];
    forall fi: FI | FIValid(fi, s.mp.inputs, s.mp.state)
      ensures
        && FICircuitValid(new_c, FItoKeys(fi))
        && (EvaluateONP(new_c, o, fi) == EvalOk(value))
    {
      reveal FICircuitValid();
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

  lemma InsertConstConserves(c: Circuit, value: bool)
    requires c.Valid()
    ensures CircuitConserved(c, InsertConstImpl(c, value).0)
    ensures CircuitUnconnected(c, InsertConstImpl(c, value).0)
    ensures
      var (new_c, e) := InsertConstImpl(c, value);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertConstImpl(c, value);
    reveal Circuit.Valid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertConst(c: Circuit, value: bool): (r: (Circuit, Scuf))
    requires c.Valid()
    ensures
      var (new_c, e) := r;
      && r == InsertConstImpl(c, value)
      && r.0.Valid()
      && e.Valid(new_c)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertConstCorrect(c, value);
    InsertConstConserves(c, value);
    InsertConstImpl(c, value)
  }

  function InsertConstWrapper(value: bool): (fn: Circuit-->(Circuit, Scuf))
    ensures forall c: Circuit :: c.Valid() ==> fn.requires(c)
  {
    var fn: Circuit --> (Circuit, Scuf) :=
      (c: Circuit) requires c.Valid() => InsertConst(c, value);
    fn
  }

  opaque function ConstInserter(value: bool): (r: ScufInserter)
    ensures r.Valid()
    ensures r.uf == ConstUF(value)
  {
    reveal UpdateFunction.Valid();
    reveal ScufInserter.Valid();
    var fn := InsertConstWrapper(value);
    var z := ScufInserter(ConstUF(value), fn);
    assert z.Valid() by {
      reveal SimpleInsertion();
    }
    z 
  }

}

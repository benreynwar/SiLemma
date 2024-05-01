module ComposeEval {

  import Std.Collections.Seq

  import opened Circ
  import opened Eval
  import opened Compose
  import opened Utils
  import opened MapFunction

  lemma NPNotInPathHelper(np: NP, sc1: set<CNode>, sc2: set<CNode>, prepath: seq<NP>, path: seq<NP>)
    requires np.n in sc1
    requires SetsNoIntersection(sc1, sc2)
    requires forall np :: np in prepath ==> np.n in sc2
    requires forall np :: np in path ==> np.n in sc1
    ensures (np in path) == (np in (prepath + path))
  {
  }
  
  lemma {:vcs_split_on_every_assert} EvaluateONPBinaryComposed1(
      c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires forall np :: np in prepath ==> np.n in e2.sc
    requires forall np :: np in path ==> np.n in e1.sc
    requires EvaluateONPBinaryRequirements(c, path, knowns)
    requires EvaluateONPBinaryRequirements(c, prepath + path, knowns)
    ensures
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var np := Seq.Last(path);
      (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_1)) &&
      (Simpl(EvaluateONPBinary(c, path, knowns)) == Simpl(EvaluateONPBinary(c, prepath+path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 3
  {
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var head := Seq.Last(path);
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    SetsNoIntersectionFromComposedValid(c, e1, e2);
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    NPNotInPathHelper(inp_1, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
      assert (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_1));
      assert (Simpl(EvaluateONPBinary(c, path, knowns)) == Simpl(EvaluateONPBinary(c, prepath+path, knowns)));
    } else if inp_1 in path {
      assert (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_1));
      assert (Simpl(EvaluateONPBinary(c, path, knowns)) == Simpl(EvaluateONPBinary(c, prepath+path, knowns)));
    } else {
      NodesNotInPathDecreases(c, prepath + path, inp_0);
      NodesNotInPathDecreases(c, prepath + path, inp_1);
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(prepath + path, inp_0);
      assert (prepath + path) + [inp_0] == prepath + (path + [inp_0]);
      assert Seq.HasNoDuplicates(prepath + (path + [inp_0]));
      StillHasNoDuplicates(path, inp_1);
      StillHasNoDuplicates(prepath + path, inp_1);
      assert (prepath + path) + [inp_1] == prepath + (path + [inp_1]);
      assert Seq.HasNoDuplicates(prepath + (path + [inp_1]));
      EvaluateINPInnerComposed1(c, e1, e2, prepath, path + [inp_0], knowns);
      EvaluateINPInnerComposed1(c, e1, e2, prepath, path + [inp_1], knowns);
      assert (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_1));
      assert (Simpl(EvaluateONPBinary(c, path, knowns)) == Simpl(EvaluateONPBinary(c, prepath+path, knowns)));
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateONPBinaryComposed2(
      c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires forall np :: np in path ==> np.n in e2.sc
    requires EvaluateONPBinaryRequirements(c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      var np := Seq.Last(path);
      (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_2))
    decreases |NodesNotInPath(c, path)|, 3
  {
    var nk := c.NodeKind[path[|path|-1].n];
    var head := path[|path|-1];
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path {
    } else if inp_1 in path {
    } else {
      NodesNotInPathDecreases(c, path, inp_0);
      NodesNotInPathDecreases(c, path, inp_1);
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      EvaluateINPInnerComposed2(c, e1, e2, path + [inp_0], knowns);
      EvaluateINPInnerComposed2(c, e1, e2, path + [inp_1], knowns);
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateONPUnaryComposed1(
      c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires forall np :: np in prepath ==> np.n in e2.sc
    requires forall np :: np in path ==> np.n in e1.sc
    requires EvaluateONPUnaryRequirements(c, path, knowns)
    requires EvaluateONPUnaryRequirements(c, prepath+path, knowns)
    ensures
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var np := Seq.Last(path);
      (EvaluateONPUnary(c, path, knowns) == EvaluateONPUnary(c, path, knowns_1)) &&
      (Simpl(EvaluateONPUnary(c, path, knowns)) == Simpl(EvaluateONPUnary(c, prepath+path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 3
  {
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    SetsNoIntersectionFromComposedValid(c, e1, e2);
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(c, prepath + path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(prepath + path, inp_0);
      assert (prepath + path) + [inp_0] == prepath + (path + [inp_0]);
      assert Seq.HasNoDuplicates(prepath + (path + [inp_0]));
      EvaluateINPInnerComposed1(c, e1, e2, prepath, path + [inp_0], knowns);
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateONPUnaryComposed2(
      c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires forall np :: np in path ==> np.n in e2.sc
    requires EvaluateONPUnaryRequirements(c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      var np := Seq.Last(path);
      EvaluateONPUnary(c, path, knowns) == EvaluateONPUnary(c, path, knowns_2)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      EvaluateINPInnerComposed2(c, e1, e2, path + [inp_0], knowns);
    }
  }

  lemma HasNoDuplicatesMeansHeadNotInTail<T>(a: seq<T>)
    requires |a| > 0
    requires Seq.HasNoDuplicates(a)
    ensures
      var head := Seq.Last(a);
      var tail := Seq.DropLast(a);
      head !in tail
  {
    reveal Seq.HasNoDuplicates();
  }

  lemma {:vcs_split_on_every_assert} EvaluateINPInnerComposed1(c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires forall np :: np in path ==> np.n in e1.sc
    requires forall np :: np in prepath ==> np.n in e2.sc
    requires EvaluateINPInnerRequirements(c, path, knowns)
    requires EvaluateINPInnerRequirements(c, prepath + path, knowns)
    ensures
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      var np := Seq.Last(path);
      (EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1)) &&
      (Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 2
  {
    reveal ComposedValid();
    reveal EquivValid();
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var np := Seq.Last(path);
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e1.inputs {
      assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1);
      assert Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns));
    } else {
      if np in c.PortSource {
        var onp := c.PortSource[np];
        assert onp.n in e1.sc;
        if onp in path {
          assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1);
          assert Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns));
        } else {
          NodesNotInPathDecreases(c, prepath+path, onp);
          StillHasNoDuplicates(path, onp);
          StillHasNoDuplicates(prepath + path, onp);
          assert (prepath + path) + [onp] == prepath + (path + [onp]);
          assert Seq.HasNoDuplicates(prepath + (path + [onp]));
          EvaluateONPInnerComposed1(c, e1, e2, prepath, path + [onp], knowns);
          assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1);
          assert Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns));
        }
      } else {
        assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1);
        assert Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns));
      }
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateINPInnerComposed2(c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires forall np :: np in path ==> np.n in e2.sc
    requires EvaluateINPInnerRequirements(c, path, knowns)
    ensures
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      var np := Seq.Last(path);
      (EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2))
    decreases |NodesNotInPath(c, path)|, 2
  {
    reveal ComposedValid();
    reveal EquivValid();
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var np := Seq.Last(path);
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e2.inputs {
      if np in knowns {
        assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
      } else {
        var onp := c.PortSource[np];
        assert onp.n in e1.sc;
        assert onp !in path;
        NodesNotInPathDecreases(c, path, onp);
        StillHasNoDuplicates(path, onp);
        LengthOneNoDuplicates([onp]);
        EvaluateONPInnerComposed1(c, e1, e2, path, [onp], knowns);
        assert (EvaluateONPInner(c, [onp], knowns) == EvaluateONPInner(c, [onp], knowns_1)); //  (1)
        assert (EvaluateONPInner(c, path + [onp], knowns) == EvaluateONPInner(c, [onp], knowns)); // (2)
        assert EvaluateINPInner(c, path, knowns) == EvaluateONPInner(c, path + [onp], knowns); // (3)
        assert knowns_2[np] == e1.f(knowns_1)[onp]; // (4)
        assert EvaluateONPInner(c, [onp], knowns_1) == EvalOk(e1.f(knowns_1)[onp]); // (5)

        assert EvaluateINPInner(c, path, knowns_2) == EvalOk(knowns_2[np]); // by it's own def
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateONPInner(c, [onp], knowns_1); // by (4) and (5)
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateONPInner(c, [onp], knowns); // by (1)
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateONPInner(c, path + [onp], knowns); // by (2)
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateINPInner(c, path, knowns); // by (3)
      }
    } else {
      if np in c.PortSource {
        var onp := c.PortSource[np];
        assert onp.n in e2.sc;
        if onp in path {
          assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
        } else {
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          EvaluateONPInnerComposed2(c, e1, e2, path + [onp], knowns);
          assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
        }
      } else {
        assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
      }
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateONPInnerComposed1(c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires EvaluateONPInnerRequirements(c, prepath + path, knowns)
    requires EvaluateONPInnerRequirements(c, path, knowns)
    requires forall np :: np in path ==> np.n in e1.sc
    requires forall np :: np in prepath ==> np.n in e2.sc
    ensures
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      (EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_1)) &&
      (Simpl(EvaluateONPInner(c, prepath + path, knowns)) == Simpl(EvaluateONPInner(c, path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 4
  {
    reveal ComposedValid();
    reveal EquivValid();
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var np := Seq.Last(path);
    Seq.LemmaAppendLast(prepath, path);
    assert np == Seq.Last(prepath + path);
    if np in knowns {
      assert np in knowns_1;
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_1);
      assert Simpl(EvaluateONPInner(c, prepath + path, knowns)) == Simpl(EvaluateONPInner(c, path, knowns));
    } else {
      var nk := c.NodeKind[np.n];
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed1(c, e1, e2, prepath, path, knowns);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed1(c, e1, e2, prepath, path, knowns);
        }
        case CInv() => {
          EvaluateONPUnaryComposed1(c, e1, e2, prepath, path, knowns);
        }
        case CConst(b) => {}
        case CInput() => {}
        case CSeq() => {}
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_1);
      assert Simpl(EvaluateONPInner(c, prepath + path, knowns)) == Simpl(EvaluateONPInner(c, path, knowns));
    }
    assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_1);
    assert Simpl(EvaluateONPInner(c, prepath + path, knowns)) == Simpl(EvaluateONPInner(c, path, knowns));
  }

  lemma {:vcs_split_on_every_assert} EvaluateONPInnerComposed2(c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires EvaluateONPInnerRequirements(c, path, knowns)
    requires forall np :: np in path ==> np.n in e2.sc
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      var np := path[|path|-1];
      (EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2))
    decreases |NodesNotInPath(c, path)|, 4
  {
    reveal ComposedValid();
    reveal EquivValid();
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var np := Seq.Last(path);
    if np in knowns {
      assert np in knowns_2;
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);
    } else {
      var nk := c.NodeKind[np.n];
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed2(c, e1, e2, path, knowns);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed2(c, e1, e2, path, knowns);
        }
        case CInv() => {
          EvaluateONPUnaryComposed2(c, e1, e2, path, knowns);
        }
        case CConst(b) => {}
        case CInput() => {}
        case CSeq() => {}
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateComposedInner(c: Circuit, e1: Equiv, e2: Equiv, np: NP, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires ONPValid(c, np) || INPValid(c, np)
    requires np.n in (e1.sc + e2.sc)
    requires np in e1.outputs || np in e2.outputs
    ensures
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      (np.n in e1.sc ==> Evaluate(c, np, knowns_1) == Evaluate(c, np, knowns)) &&
      (np.n in e2.sc ==> Evaluate(c, np, knowns_2) == Evaluate(c, np, knowns))
  {
    var prepath: seq<NP> := [];
    var path := [np];
    assert np == path[|path|-1];
    assert PathValid(c, path);

    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);

    LengthOneNoDuplicates(path);
    LengthOneNoDuplicates(prepath + path);
    if ONPValid(c, np) {
      if np.n in e1.sc {
        EvaluateONPInnerComposed1(c, e1, e2, prepath, path, knowns);
        assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_1);
      } else {
        EvaluateONPInnerComposed2(c, e1, e2, path, knowns);
        assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);
      }
    } else {
      if np.n in e1.sc {
        EvaluateINPInnerComposed1(c, e1, e2, prepath, path, knowns);
        assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1);
      } else {
        EvaluateINPInnerComposed2(c, e1, e2, path, knowns);
        assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
      }
    }
    reveal ComposedValid();
    if np.n in e1.sc {
      assert np.n !in e2.sc;
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_1);
    } else {
      assert np.n in e2.sc;
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_2);
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateComposed(c: Circuit, e1: Equiv, e2: Equiv, np: NP, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
    requires ONPValid(c, np) || INPValid(c, np)
    requires np.n in (e1.sc + e2.sc)
    requires np in e1.outputs || np in e2.outputs
    ensures
      var e := ComposeEquiv(c, e1, e2);
      e.f.requires(knowns) &&
      np in e.f(knowns) &&
      Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np])
  {
    EvaluateComposedInner(c, e1, e2, np, knowns);
    var e := ComposeEquiv(c, e1, e2);
    assert EquivValid(c, e);
    {
      reveal EquivValid();
      assert e.f.requires(knowns);
      assert np in e.f(knowns);
    }

    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);


    //assert forall np :: np in e1.inputs + e1.outputs ==> np.n in e1.sc;
    //assert forall np :: np in e2.inputs + e2.outputs ==> np.n in e2.sc;
    //assert SetsNoIntersection(e1.inputs+e1.outputs, e2.inputs+e2.outputs);

    //var mf1 := EtoMf(e1);
    //var mf2 := EtoMf(e2);
    //EValidMfValid(c, e1);
    //EValidMfValid(c, e2);
    //var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
    //var e2_inputs_from_e1 := (map np | np in e2_inputs_from_e1_keys :: np := c.PortSource[np]);
    //assert e.f(knowns) == ComposeMapFunction(mf1, mf2, e2_inputs_from_e1, knowns);

    if np in e1.outputs {
      {
        reveal ComposedValid();
        reveal EquivValid();
        assert Evaluate(c, np, knowns_1) == EvalOk(e1.f(knowns_1)[np]);
      }
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_1);
      assert EvalOk(e1.f(knowns_1)[np]) == EvalOk(e.f(knowns)[np]);
      assert Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np]);
    } else {
      assert np in e2.outputs;
      {
        reveal ComposedValid();
        reveal EquivValid();
        assert Evaluate(c, np, knowns_2) == EvalOk(e2.f(knowns_2)[np]);
      }
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_2);
      assert EvalOk(e2.f(knowns_2)[np]) == EvalOk(e.f(knowns)[np]);
      assert Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np]);

    }
  }

  lemma {:vcs_split_on_every_assert} ComposeEquivCorrect(c: Circuit, e1: Equiv, e2: Equiv)
    requires ComposedValid(c, e1, e2)
    ensures
      var r := ComposeEquiv(c, e1, e2);
      CircuitValid(c) &&
      EquivValid(c, r) &&
      EquivTrue(c, r)
  {
    reveal ComposedValid();
    reveal EquivValid();
    var combined_input_keys := ComposeEquivInputs(c, e1, e2);
    var e := ComposeEquiv(c, e1, e2);
    assert EquivValid(c, e);
    forall knowns: map<NP, bool> | (knowns.Keys == e.inputs)
      ensures
        e.f.requires(knowns) &&
        (forall np :: np in e.outputs ==>
          np in e.f(knowns) &&
          (Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np])))
    {
      forall np | np in e.outputs
        ensures
          e.f.requires(knowns) &&
          np in e.f(knowns) &&
          (Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np]))
      {
        EvaluateComposed(c, e1, e2, np, knowns);
      }
    }
    assert EquivTrue(c, e);
  }

}
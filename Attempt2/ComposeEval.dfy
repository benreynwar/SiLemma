module ComposeEval {

  import Std.Collections.Seq

  import opened Circ
  import opened Eval
  import opened Compose
  import opened Utils
  import opened MapFunction
  import opened Equiv

  lemma NPNotInPathHelper(np: NP, sc1: set<CNode>, sc2: set<CNode>, prepath: seq<NP>, path: seq<NP>)
    requires np.n in sc1
    requires SetsNoIntersection(sc1, sc2)
    requires PathInSubcircuit(prepath, sc2)
    requires PathInSubcircuit(path, sc1)
    ensures (np in path) == (np in (prepath + path))
  {
    reveal PathInSubcircuit();
    if np.n in sc2 {
      assert np.n in sc1 * sc2;
    }
    assert np.n !in sc2;
    assert np !in prepath;
  }

  opaque predicate PathInSubcircuit(path: seq<NP>, sc: set<CNode>)
  {
    forall np :: np in path ==> np.n in sc
  }

  lemma EvaluateONPComposed1Helper(
      c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>, inp: NP)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires EvaluateONPUnaryBinaryRequirements(c, path, knowns)
    requires EvaluateONPUnaryBinaryRequirements(c, prepath + path, knowns)
    requires INPValid(c, inp)
    requires inp !in path
    requires inp.n in e1.sc
    ensures
      (forall np :: np in e1.inputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var new_path := path + [inp];
      Seq.HasNoDuplicates(new_path) &&
      Seq.HasNoDuplicates(prepath + new_path) &&
      PathValid(c, new_path) &&
      PathValid(c, prepath + new_path) &&
      EvaluateINPInner(c, new_path, knowns) == EvaluateINPInner(c, new_path, knowns_1) &&
      Simpl(EvaluateINPInner(c, new_path, knowns)) == Simpl(EvaluateINPInner(c, prepath+new_path, knowns))
    decreases |NodesNotInPath(c, prepath + path)|, 3
  {
    StillHasNoDuplicates(path, inp);
    assert inp !in prepath by {
      reveal PathInSubcircuit();
      reveal ComposedValid();
      InThisNotInThat(inp.n, e1.sc, e2.sc);
    }
    StillHasNoDuplicates(prepath + path, inp);
    AppendPathValid(c, path, inp);
    AppendPathValid(c, prepath + path, inp);
    assert forall np :: np in e1.inputs ==> np in knowns by {reveal GoodKnownKeys();}
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var new_path := path + [inp];
    NodesNotInPathDecreases(c, prepath + path, inp);
    assert PathInSubcircuit(new_path, e1.sc) by {reveal PathInSubcircuit();}
    assert (prepath + path) + [inp] == prepath + (path + [inp]);
    assert Seq.Last(prepath + new_path) == inp;
    EvaluateINPInnerComposed1(c, e1, e2, prepath, new_path, knowns);
    assert EvaluateINPInner(c, new_path, knowns) == EvaluateINPInner(c, new_path, knowns_1);
    assert Simpl(EvaluateINPInner(c, new_path, knowns)) == Simpl(EvaluateINPInner(c, prepath+new_path, knowns));
  }

  lemma EvaluateONPBinaryComposed1(
      c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires EvaluateONPBinaryRequirements(c, path, knowns)
    requires EvaluateONPBinaryRequirements(c, prepath + path, knowns)
    ensures
      (forall np :: np in e1.inputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var np := Seq.Last(path);
      (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_1)) &&
      (Simpl(EvaluateONPBinary(c, path, knowns)) == Simpl(EvaluateONPBinary(c, prepath+path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 4
  {
    assert forall np :: np in e1.inputs ==> np in knowns by {reveal GoodKnownKeys();}
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var head := Seq.Last(path);
    assert head == Seq.Last(prepath + path);
    assert head.n in e1.sc by {reveal PathInSubcircuit();}
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    assert INPValid(c, inp_0) && INPValid(c, inp_1) by {reveal CircuitValid();}
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
      EvaluateONPComposed1Helper(c, e1, e2, prepath, path, knowns, inp_0);
      EvaluateONPComposed1Helper(c, e1, e2, prepath, path, knowns, inp_1);

      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert prepath + (path + [inp_1]) == (prepath + path) + [inp_1];

      assert (Simpl(EvaluateONPBinary(c, path, knowns)) == Simpl(EvaluateONPBinary(c, prepath+path, knowns)));
    }
  }

  lemma EvaluateONPComposed2Helper(
      c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>, inp: NP)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPUnaryBinaryRequirements(c, path, knowns)
    requires INPValid(c, inp)
    requires inp !in path
    requires inp.n in e2.sc
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      var new_path := path + [inp];
      Seq.HasNoDuplicates(new_path) &&
      PathValid(c, new_path) &&
      (EvaluateINPInner(c, new_path, knowns) == EvaluateINPInner(c, new_path, knowns_2))
    decreases |NodesNotInPath(c, path)|, 4
  {
    StillHasNoDuplicates(path, inp);
    AppendPathValid(c, path, inp);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var new_path := path + [inp];
    NodesNotInPathDecreases(c, path, inp);
    reveal PathInSubcircuit();
    EvaluateINPInnerComposed2(c, e1, e2, new_path, knowns);
    assert (EvaluateINPInner(c, new_path, knowns) == EvaluateINPInner(c, new_path, knowns_2));
  }

  lemma EvaluateONPBinaryComposed2(
      c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPBinaryRequirements(c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      (Seq.Last(path) !in knowns_2) &&
      (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_2))
    decreases |NodesNotInPath(c, path)|, 5
  {
    var head := Seq.Last(path);
    assert head.n in e2.sc by {
      reveal PathInSubcircuit();
    }
    var nk := c.NodeKind[head.n];
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    assert INPValid(c, inp_0) && INPValid(c, inp_1) by {reveal CircuitValid();}
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    assert head !in knowns;
    ONPNotInKnownsNotInKnowns2(c, head, e1, e2, knowns);
    assert head !in knowns_2;
    if inp_0 in path {
      assert (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_2));
    } else if inp_1 in path {
      assert (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_2));
    } else {
      assert 
        var new_path := path + [inp_0];
        Seq.HasNoDuplicates(new_path) &&
        PathValid(c, new_path) &&
        (EvaluateINPInner(c, new_path, knowns) == EvaluateINPInner(c, new_path, knowns_2)) by {
          EvaluateONPComposed2Helper(c, e1, e2, path, knowns, inp_0);
        }
      assert 
        var new_path := path + [inp_1];
        Seq.HasNoDuplicates(new_path) &&
        PathValid(c, new_path) &&
        (EvaluateINPInner(c, new_path, knowns) == EvaluateINPInner(c, new_path, knowns_2)) by {
          EvaluateONPComposed2Helper(c, e1, e2, path, knowns, inp_1);
        }
      assert EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_2);
    }
    assert
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      (EvaluateONPBinary(c, path, knowns) == EvaluateONPBinary(c, path, knowns_2));
  }

  lemma EvaluateONPUnaryComposed1(
      c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires EvaluateONPUnaryRequirements(c, path, knowns)
    requires EvaluateONPUnaryRequirements(c, prepath+path, knowns)
    ensures
      (forall np :: np in e1.inputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var np := Seq.Last(path);
      (EvaluateONPUnary(c, path, knowns) == EvaluateONPUnary(c, path, knowns_1)) &&
      (Simpl(EvaluateONPUnary(c, path, knowns)) == Simpl(EvaluateONPUnary(c, prepath+path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 5
  {
    assert forall np :: np in e1.inputs ==> np in knowns by {reveal GoodKnownKeys();}
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var head := Seq.Last(path);
    assert head == Seq.Last(prepath + path);
    assert head.n in e1.sc by {reveal PathInSubcircuit();}
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    assert INPValid(c, inp_0) by {reveal CircuitValid();}
    SetsNoIntersectionFromComposedValid(c, e1, e2);
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
      assert (EvaluateONPUnary(c, path, knowns) == EvaluateONPUnary(c, path, knowns_1));
      assert (Simpl(EvaluateONPUnary(c, path, knowns)) == Simpl(EvaluateONPUnary(c, prepath+path, knowns)));
    } else {
      EvaluateONPComposed1Helper(c, e1, e2, prepath, path, knowns, inp_0);
      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert (Simpl(EvaluateONPUnary(c, path, knowns)) == Simpl(EvaluateONPUnary(c, prepath+path, knowns)));
    }
  }

  lemma EvaluateONPUnaryComposed2(
      c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPUnaryRequirements(c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      (Seq.Last(path) !in knowns_2) &&
      EvaluateONPUnary(c, path, knowns) == EvaluateONPUnary(c, path, knowns_2)
    decreases |NodesNotInPath(c, path)|, 4
  {
    var head := Seq.Last(path);
    assert head !in knowns;
    ONPNotInKnownsNotInKnowns2(c, head, e1, e2, knowns);
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      assert PathInSubcircuit(path + [inp_0], e2.sc) by {
        reveal PathInSubcircuit();
      }
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

  lemma EvaluateINPInnerComposed1(c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(path, e1.sc)
    requires PathInSubcircuit(prepath, e2.sc)
    requires EvaluateINPInnerRequirements(c, path, knowns)
    requires EvaluateINPInnerRequirements(c, prepath + path, knowns)
    ensures
      (forall np :: np in e1.inputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      (EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1)) &&
      (Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 2
  {
    assert forall np :: np in e1.inputs ==> np in knowns by {reveal GoodKnownKeys();}
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var np := Seq.Last(path);
    assert np.n in e1.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e1.inputs {
      assert np in knowns;
      assert np in knowns_1;
      assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1);
      assert Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns));
    } else {
      assert np !in knowns by {
        reveal ComposedValid();
        reveal ScValid();
        reveal GoodKnownKeys();
        assert knowns.Keys == (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
        InThisNotInThat(np.n, e1.sc, e2.sc);
        assert np.n !in e2.sc;
        reveal EquivValid();
        assert np !in e2.inputs;
      }
      assert np !in knowns_1;
      if np in c.PortSource {
        var onp := c.PortSource[np];
        assert ONPValid(c, onp) by {
          reveal CircuitValid();
        }
        assert onp.n in e1.sc by {
          reveal ComposedValid();
          reveal EquivValid();
          reveal PathInSubcircuit();
        }
        assert EvaluateINPInnerRequirements(c, path, knowns);
        assert EvaluateINPInnerRequirements(c, path, knowns_1);
        assert EvaluateINPInnerRequirements(c, prepath + path, knowns);
        if onp in path {
          assert EvaluateINPInner(c, path, knowns) == EvalError({}, {path + [onp]});
          assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_1);
          assert Simpl(EvaluateINPInner(c, path, knowns)) == Simpl(EvaluateINPInner(c, prepath+path, knowns));
        } else {
          assert NPValid(c, onp) by {
            reveal CircuitValid();
          }
          SetsNoIntersectionFromComposedValid(c, e1, e2);
          NPNotInPathHelper(onp, e1.sc, e2.sc, prepath, path);
          NodesNotInPathDecreases(c, prepath+path, onp);
          StillHasNoDuplicates(path, onp);
          StillHasNoDuplicates(prepath + path, onp);
          AppendPathValid(c, path, onp);
          AppendPathValid(c, prepath + path, onp);
          assert (prepath + path) + [onp] == prepath + (path + [onp]);
          assert Seq.HasNoDuplicates(prepath + (path + [onp]));
          assert PathInSubcircuit(path + [onp], e1.sc) by {
            reveal PathInSubcircuit();
          }
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

  lemma EvaluateINPInnerComposed2(c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateINPInnerRequirements(c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      (EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2))
    decreases |NodesNotInPath(c, path)|, 2
  {
    assert forall np :: np in e1.inputs ==> np in knowns by {reveal GoodKnownKeys();}
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var np := Seq.Last(path);
    assert np.n in e2.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e2.inputs {
      if np in knowns {
        assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
      } else {
        assert (np in c.PortSource) && (c.PortSource[np].n in e1.sc) by {
          reveal GoodKnownKeys();
          reveal ComposedValid();
          assert knowns.Keys == (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
          assert np in NPBetweenSubcircuits(c, e2.sc, e1.sc);
          assert c.PortSource[np].n in e1.sc;
        }
        var onp := c.PortSource[np];
        assert ONPValid(c, onp) by {
          reveal CircuitValid();
        }
        assert onp.n in e1.sc;
        assert onp !in path by {
          reveal PathInSubcircuit();
          reveal ComposedValid();
          InThisNotInThat(onp.n, e1.sc, e2.sc);
        } 
        NodesNotInPathDecreases(c, path, onp);
        StillHasNoDuplicates(path, onp);
        LengthOneNoDuplicates([onp]);
        assert PathValid(c, [onp]) by {reveal PathValid();}
        assert PathInSubcircuit([onp], e1.sc) by {reveal PathInSubcircuit();}
        EvaluateONPInnerComposed1(c, e1, e2, path, [onp], knowns);
        assert (EvaluateONPInner(c, [onp], knowns) == EvaluateONPInner(c, [onp], knowns_1)); //  (1)
        assert (Simpl(EvaluateONPInner(c, path + [onp], knowns)) == Simpl(EvaluateONPInner(c, [onp], knowns))); // (2)
        assert EvaluateINPInner(c, path, knowns) == EvaluateONPInner(c, path + [onp], knowns); // (3)
        assert onp in e1.outputs by {
          reveal ComposedValid();
          reveal EquivValid();
          reveal EquivScOutputsInOutputs();
          assert (np.n !in e1.sc) && np in c.PortSource && c.PortSource[np].n in e1.sc;
          assert onp in ScOutputBoundary(c, e1.sc);
        }
        assert (e1.f.requires(knowns_1)) && (e1.f(knowns_1).Keys == e1.outputs) && (knowns_2[np] == e1.f(knowns_1)[onp]) by { // (4)
          reveal ComposedValid();
          reveal EquivValid();
          reveal MapFunctionValid();
          assert knowns_1.Keys == e1.inputs;
          assert e1.f.requires(knowns_1);
          assert e1.f(knowns_1).Keys == e1.outputs;
        }
        assert EvaluateONPInner(c, [onp], knowns_1) == EvalOk(e1.f(knowns_1)[onp]) by { // (5)
          reveal ComposedValid();
          reveal EquivTrue();
        }

        assert EvaluateINPInner(c, path, knowns_2) == EvalOk(knowns_2[np]); // by it's own def
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateONPInner(c, [onp], knowns_1); // by (4) and (5)
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateONPInner(c, [onp], knowns); // by (1)
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateONPInner(c, path + [onp], knowns); // by (2)
        assert EvaluateINPInner(c, path, knowns_2) == EvaluateINPInner(c, path, knowns); // by (3)
      }
    } else {
      assert np !in e2.inputs;
      assert knowns_2.Keys == e2.inputs;
      assert np !in knowns_2;
      InE2ButNotE2InputsNotInKnowns(c, e1, e2, knowns, np);
      assert np !in knowns;
      if np in c.PortSource {
        var onp := c.PortSource[np];
        assert ONPValid(c, onp) by {
          reveal CircuitValid();
        }
        assert onp.n in e2.sc by {
          assert np !in e2.inputs;
          reveal ComposedValid();
          reveal EquivValid();
          assert np !in ScInputBoundary(c, e2.sc);
          assert np !in NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc);
          assert !(np.n in e2.sc && np in c.PortSource && c.PortSource[np].n !in e2.sc);
        }
        if onp in path {
          assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
        } else {
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          assert PathInSubcircuit(path + [onp], e2.sc) by {
            reveal PathInSubcircuit();
          }
          EvaluateONPInnerComposed2(c, e1, e2, path + [onp], knowns);
          assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
        }
      } else {
        assert EvaluateINPInner(c, path, knowns) == EvaluateINPInner(c, path, knowns_2);
      }
    }
  }

  lemma EvaluateONPInnerComposed1(c: Circuit, e1: Equiv, e2: Equiv, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires EvaluateONPInnerRequirements(c, prepath + path, knowns)
    requires EvaluateONPInnerRequirements(c, path, knowns)
    requires PathInSubcircuit(path, e1.sc)
    requires PathInSubcircuit(prepath, e2.sc)
    ensures
      (forall np :: np in e1.inputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      (EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_1)) &&
      (Simpl(EvaluateONPInner(c, prepath + path, knowns)) == Simpl(EvaluateONPInner(c, path, knowns)))
    decreases |NodesNotInPath(c, prepath + path)|, 6
  {
    assert forall np :: np in e1.inputs ==> np in knowns by {reveal GoodKnownKeys();}
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var np := Seq.Last(path);
    assert (np.n in e1.sc) && (np.n !in e2.sc) by {
      reveal PathInSubcircuit();
      reveal ComposedValid();
      InThisNotInThat(np.n, e1.sc, e2.sc);
    }
    Seq.LemmaAppendLast(prepath, path);
    assert np == Seq.Last(prepath + path);
    if np in knowns {
      assert np in knowns_1 by {
        reveal GoodKnownKeys();
        reveal ComposedValid();
        reveal EquivValid();
        reveal NPsValidAndInSc();
        assert forall x :: x in e2.inputs ==> x.n in e2.sc;
        assert np !in e2.inputs;
      }
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

  lemma EvaluateONPInnerComposed2(c: Circuit, e1: Equiv, e2: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires EvaluateONPInnerRequirements(c, path, knowns)
    requires PathInSubcircuit(path, e2.sc)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      var np := Seq.Last(path);
      (EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2))
    decreases |NodesNotInPath(c, path)|, 6
  {
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var np := Seq.Last(path);
    assert (np.n in e2.sc) && (np.n !in e1.sc) by {
      reveal PathInSubcircuit();
      reveal ComposedValid();
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    if np in knowns {
      assert np in knowns_2 by {
        reveal GoodKnownKeys();
        reveal ComposedValid();
        reveal EquivValid();
        reveal NPsValidAndInSc();
        assert np !in e1.inputs;
      }
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);
    } else {
      assert np !in e2.inputs by {
        reveal GoodKnownKeys();
        reveal ComposedValid();
        reveal EquivValid();
        reveal NPsValidAndInSc();
        reveal CircuitValid();
        assert knowns.Keys == (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
        assert np !in NPBetweenSubcircuits(c, e2.sc, e1.sc);
      }
      var nk := c.NodeKind[np.n];
      assert !nk.CInput? && !nk.CSeq? by {
        reveal GoodKnownKeys();
        reveal EquivValid();
        if (nk.CInput? || nk.CSeq?) {
          reveal ComposedValid();
          assert np in InternalInputs(c, e2.sc);
          assert np in e2.inputs;
        }
      }
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed2(c, e1, e2, path, knowns);
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed2(c, e1, e2, path, knowns);
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);
        }
        case CInv() => {
          EvaluateONPUnaryComposed2(c, e1, e2, path, knowns);
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);
        }
        case CConst(b) => {
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);

        }
        case CInput() => {}
        case CSeq() => {}
      assert EvaluateONPInner(c, path, knowns) == EvaluateONPInner(c, path, knowns_2);
    }
  }

  lemma EvaluateComposedInner(c: Circuit, e1: Equiv, e2: Equiv, np: NP, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires ONPValid(c, np) || INPValid(c, np)
    requires np.n in (e1.sc + e2.sc)
    requires np in e1.outputs || np in e2.outputs
    ensures
      (forall np :: np in e1.inputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.inputs);
      var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
      (np.n in e1.sc ==> Evaluate(c, np, knowns_1) == Evaluate(c, np, knowns)) &&
      (np.n in e2.sc ==> Evaluate(c, np, knowns_2) == Evaluate(c, np, knowns))
  {
    var prepath: seq<NP> := [];
    var path := [np];
    assert np == Seq.Last(path);
    assert PathValid(c, path) && PathValid(c, prepath + path) by {
      reveal PathValid();
    }

    assert forall np :: np in e1.inputs ==> np in knowns by {reveal GoodKnownKeys();}
    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);

    LengthOneNoDuplicates(path);
    LengthOneNoDuplicates(prepath + path);
    if np.n in e1.sc {
      assert PathInSubcircuit(prepath, e2.sc) by { reveal PathInSubcircuit(); }
      assert PathInSubcircuit(path, e1.sc) by { reveal PathInSubcircuit(); }
    } else {
      assert PathInSubcircuit(path, e2.sc) by { reveal PathInSubcircuit(); }
    }

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
      InThisNotInThat(np.n, e1.sc, e2.sc);
      assert np.n !in e2.sc;
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_1);
    } else {
      assert np.n in e2.sc;
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_2);
    }
  }

  lemma EvaluateComposed(c: Circuit, e1: Equiv, e2: Equiv, np: NP, knowns: map<NP, bool>)
    requires CircuitValid(c)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
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

    var knowns_1 := ExtractMap(knowns, e1.inputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);

    assert e1.f.requires(knowns_1) && (e1.f(knowns_1).Keys == e1.outputs) &&
           e2.f.requires(knowns_2) && (e2.f(knowns_2).Keys == e2.outputs) &&
           e.f.requires(knowns) && (e.f(knowns).Keys == e.outputs) by {
      reveal ComposedValid();
      reveal EquivValid();
      reveal MapFunctionValid();
      reveal GoodKnownKeys();
      assert EquivValid(c, e1);
      assert EquivValid(c, e2);
      assert EquivValid(c, e);
      assert e.f.requires(knowns);
      assert (e.f(knowns).Keys == e.outputs);
    }
    if np in e1.outputs {
      assert np.n in e1.sc by {
        reveal ComposedValid();
        reveal EquivValid();
        reveal NPsValidAndInSc();
      }
      assert Evaluate(c, np, knowns_1) == EvalOk(e1.f(knowns_1)[np]) by {
        reveal ComposedValid();
        assert EquivTrue(c, e1);
        reveal EquivTrue();
      }
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_1);
      assert EvalOk(e1.f(knowns_1)[np]) == EvalOk(e.f(knowns)[np]) by {
        reveal GoodKnownKeys();
        reveal ComposedValid(); reveal EquivTrue();
      }
      assert Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np]);
    } else {
      assert np in e2.outputs;
      assert np.n in e2.sc by {
        reveal ComposedValid();
        reveal EquivValid();
        reveal NPsValidAndInSc();
      }
      assert Evaluate(c, np, knowns_2) == EvalOk(e2.f(knowns_2)[np]) by {
        reveal ComposedValid();
        reveal EquivTrue();
      }
      assert EvalOk(e2.f(knowns_2)[np]) == EvalOk(e.f(knowns)[np]) by {
        reveal GoodKnownKeys();
        reveal ComposedValid();
        reveal EquivTrue();
      }
      assert Evaluate(c, np, knowns) == Evaluate(c, np, knowns_2);
      assert EvalOk(e2.f(knowns_2)[np]) == EvalOk(e.f(knowns)[np]);
      assert Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np]);

    }
  }

  lemma ComposeEquivCorrect(c: Circuit, e1: Equiv, e2: Equiv)
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
          NPValid(c, np) &&
          (Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np])))
    {
      forall np | np in e.outputs
        ensures
          e.f.requires(knowns) &&
          np in e.f(knowns) &&
          NPValid(c, np) &&
          (Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np]))
      {
        reveal ComposedValid();
        reveal GoodKnownKeys();
        reveal EquivValid();
        reveal NPsValidAndInSc();
        EvaluateComposed(c, e1, e2, np, knowns);
      }
    }
    reveal EquivTrue();
    assert EquivTrue(c, e);
  }

}
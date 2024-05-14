module ConnectionEval {

  import Std.Collections.Seq

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Connection
  import opened Subcircuit

  lemma Knowns2FromKnowns1(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, knowns: map<NP, bool>, np: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires np in connection
    ensures
      && var new_c := ConnectEntitiesImpl(c, e1, e2, connection).0;
      && np in new_c.PortSource
      && var onp := new_c.PortSource[np];
      && var knowns_1 := ExtractMap(knowns, e1.finputs);
      && var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      && (np in knowns_2)
      && (e1.f.requires(knowns_1))
      && (onp in e1.f(knowns_1))
      && (knowns_2[np] == e1.f(knowns_1)[onp])
  {
    var new_c := ConnectEntitiesImpl(c, e1, e2, connection).0;
    ConnectCircuitReqFromConnectEntitiesReq(c, e1, e2, connection);
    assert new_c == ConnectCircuit(c, connection) by {
      reveal ConnectEntitiesImpl();
    }
    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
    var onp := connection[np];
    assert onp == new_c.PortSource[np] by {
      reveal ConnectEntitiesImpl();
      reveal ConnectionValid();
    }
    assert np !in e1.finputs by {
      ConnectionKeysInE2(c, e1, e2, connection);
      FInputsInSc(c, e1);
      reveal NPsInSc();
      SetsNoIntersectionSymm(e1.sc, e2.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    assert np !in knowns;

    var inputs_1 := ExtractMap(knowns, e1.finputs);
    reveal EntityFValid();
    var outputs_1 := e1.f(inputs_1);
    assert outputs_1.Keys == e1.foutputs;
    reveal ConnectionValid();
    assert connection.Values <= e1.foutputs;
    var connected := (map np | np in connection :: np := outputs_1[connection[np]]);
    assert connected.Keys == connection.Keys;
    assert knowns.Keys == e1.finputs + (e2.finputs - connection.Keys);
    RearrangeKnownKeys(c, e1, e2, connection, knowns);
    assert knowns.Keys == (e1.finputs + e2.finputs) - connection.Keys;
    var combined_map := AddMaps(knowns, connected);
    var inputs_2 := ExtractMap(combined_map, e2.finputs);
    assert inputs_2 == knowns_2;

    assert np in connected;
    assert np in knowns_2;
  }

  lemma ONPNotInKnownsNotInKnowns2(c: Circuit, onp: NP, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires onp !in knowns
    requires ONPValid(new_c, onp)
    ensures onp !in CalculateE2Inputs(c, e1, e2, connection, knowns)
  {
    assert onp !in e1.finputs + (e2.finputs - connection.Keys);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
    assert knowns_2.Keys == e2.finputs;
    ConnectionKeysINPs(c, e1, e2, connection);
    reveal INPsValid();
  }

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

  lemma EvaluateONPComposed1Helper(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>, inp: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires inp !in path
    requires inp.n in e1.sc
    requires INPValid(new_c, inp)
    requires EvaluateONPUnaryBinaryRequirements(new_c, path, knowns)
    requires EvaluateONPUnaryBinaryRequirements(new_c, prepath + path, knowns)
    ensures forall np :: np in e1.finputs ==> np in knowns
    ensures
      && var new_path := path + [inp];
      && Seq.HasNoDuplicates(new_path)
      && Seq.HasNoDuplicates(prepath + new_path)
      && PathValid(new_c, new_path)
      && PathValid(new_c, prepath + new_path)
      && var knowns_1 := ExtractMap(knowns, e1.finputs);
      && EvaluateINPInner(new_c, new_path, knowns) == EvaluateINPInner(new_c, new_path, knowns_1)
      && Simpl(EvaluateINPInner(new_c, new_path, knowns)) == Simpl(EvaluateINPInner(new_c, prepath+new_path, knowns))
    decreases
      |NodesNotInPath(new_c, prepath + path)|, 3
  {
    StillHasNoDuplicates(path, inp);
    assert inp !in prepath by {
      reveal PathInSubcircuit();
      InThisNotInThat(inp.n, e1.sc, e2.sc);
    }
    StillHasNoDuplicates(prepath + path, inp);
    AppendPathValid(new_c, path, inp);
    AppendPathValid(new_c, prepath + path, inp);
    assert forall np :: np in e1.finputs ==> np in knowns;
    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var new_path := path + [inp];
    NodesNotInPathDecreases(new_c, prepath + path, inp);
    assert PathInSubcircuit(new_path, e1.sc) by {reveal PathInSubcircuit();}
    assert (prepath + path) + [inp] == prepath + (path + [inp]);
    assert Seq.Last(prepath + new_path) == inp;
    EvaluateINPInnerComposed1(c, e1, e2, connection, new_c, prepath, new_path, knowns);
    assert EvaluateINPInner(new_c, new_path, knowns) == EvaluateINPInner(new_c, new_path, knowns_1);
    assert Simpl(EvaluateINPInner(new_c, new_path, knowns)) == Simpl(EvaluateINPInner(new_c, prepath+new_path, knowns));
  }

  lemma EvaluateONPBinaryComposed1(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires EvaluateONPBinaryRequirements(new_c, path, knowns)
    requires EvaluateONPBinaryRequirements(new_c, prepath + path, knowns)
    ensures
      (forall np :: np in e1.finputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.finputs);
      var np := Seq.Last(path);
      && (EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_1))
      && (Simpl(EvaluateONPBinary(new_c, path, knowns)) == Simpl(EvaluateONPBinary(new_c, prepath+path, knowns)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 4
  {
    assert forall np :: np in e1.finputs ==> np in knowns;
    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var head := Seq.Last(path);
    assert head == Seq.Last(prepath + path);
    assert head.n in e1.sc by {reveal PathInSubcircuit();}
    assert NodeValid(new_c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    assert INPValid(new_c, inp_0) && INPValid(new_c, inp_1) by {reveal CircuitValid();}
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    NPNotInPathHelper(inp_1, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
      assert (EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_1));
      assert (Simpl(EvaluateONPBinary(new_c, path, knowns)) == Simpl(EvaluateONPBinary(new_c, prepath+path, knowns)));
    } else if inp_1 in path {
      assert (EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_1));
      assert (Simpl(EvaluateONPBinary(new_c, path, knowns)) == Simpl(EvaluateONPBinary(new_c, prepath+path, knowns)));
    } else {
      EvaluateONPComposed1Helper(c, e1, e2, connection, new_c, prepath, path, knowns, inp_0);
      EvaluateONPComposed1Helper(c, e1, e2, connection, new_c, prepath, path, knowns, inp_1);

      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert prepath + (path + [inp_1]) == (prepath + path) + [inp_1];

      assert (Simpl(EvaluateONPBinary(new_c, path, knowns)) == Simpl(EvaluateONPBinary(new_c, prepath+path, knowns)));
    }
  }

  lemma EvaluateONPComposed2Helper(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, knowns: map<NP, bool>, inp: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPUnaryBinaryRequirements(new_c, path, knowns)
    requires INPValid(new_c, inp)
    requires inp !in path
    requires inp.n in e2.sc
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      var new_path := path + [inp];
      Seq.HasNoDuplicates(new_path) &&
      PathValid(new_c, new_path) &&
      (EvaluateINPInner(new_c, new_path, knowns) == EvaluateINPInner(new_c, new_path, knowns_2))
    decreases |NodesNotInPath(new_c, path)|, 4
  {
    StillHasNoDuplicates(path, inp);
    AppendPathValid(new_c, path, inp);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
    var new_path := path + [inp];
    NodesNotInPathDecreases(new_c, path, inp);
    reveal PathInSubcircuit();
    EvaluateINPInnerComposed2(c, e1, e2, connection, new_c, new_path, knowns);
    assert (EvaluateINPInner(new_c, new_path, knowns) == EvaluateINPInner(new_c, new_path, knowns_2));
  }

  lemma EvaluateONPBinaryComposed2(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPBinaryRequirements(new_c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      (Seq.Last(path) !in knowns_2) &&
      (EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_2))
    decreases |NodesNotInPath(new_c, path)|, 5
  {
    var head := Seq.Last(path);
    assert head.n in e2.sc by {
      reveal PathInSubcircuit();
    }
    var nk := new_c.NodeKind[head.n];
    assert NodeValid(new_c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    assert INPValid(new_c, inp_0) && INPValid(new_c, inp_1) by {reveal CircuitValid();}
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
    assert head !in knowns;
    ONPNotInKnownsNotInKnowns2(c, head, e1, e2, connection, new_c, knowns);
    assert head !in knowns_2;
    if inp_0 in path {
      assert (EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_2));
    } else if inp_1 in path {
      assert (EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_2));
    } else {
      assert 
        var new_path := path + [inp_0];
        && Seq.HasNoDuplicates(new_path)
        && PathValid(new_c, new_path)
        && (EvaluateINPInner(new_c, new_path, knowns) == EvaluateINPInner(new_c, new_path, knowns_2)) by {
          //AppendPathValid(new_path, inp_0);
          EvaluateONPComposed2Helper(c, e1, e2, connection, new_c, path, knowns, inp_0);
        }
      assert 
        var new_path := path + [inp_1];
        && Seq.HasNoDuplicates(new_path)
        && PathValid(new_c, new_path)
        && (EvaluateINPInner(new_c, new_path, knowns) == EvaluateINPInner(new_c, new_path, knowns_2)) by {
          //AppendPathValid(new_path, inp_0);
          EvaluateONPComposed2Helper(c, e1, e2, connection, new_c, path, knowns, inp_1);
        }
      assert EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_2);
    }
    assert
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      (EvaluateONPBinary(new_c, path, knowns) == EvaluateONPBinary(new_c, path, knowns_2));
  }

  lemma EvaluateONPUnaryComposed1(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires EvaluateONPUnaryRequirements(new_c, path, knowns)
    requires EvaluateONPUnaryRequirements(new_c, prepath+path, knowns)
    ensures
      (forall np :: np in e1.finputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.finputs);
      var np := Seq.Last(path);
      (EvaluateONPUnary(new_c, path, knowns) == EvaluateONPUnary(new_c, path, knowns_1)) &&
      (Simpl(EvaluateONPUnary(new_c, path, knowns)) == Simpl(EvaluateONPUnary(new_c, prepath+path, knowns)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 5
  {
    assert forall np :: np in e1.finputs ==> np in knowns;
    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var head := Seq.Last(path);
    assert head == Seq.Last(prepath + path);
    assert head.n in e1.sc by {reveal PathInSubcircuit();}
    assert NodeValid(new_c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    assert INPValid(new_c, inp_0) by {reveal CircuitValid();}
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
      assert (EvaluateONPUnary(new_c, path, knowns) == EvaluateONPUnary(new_c, path, knowns_1));
      assert (Simpl(EvaluateONPUnary(new_c, path, knowns)) == Simpl(EvaluateONPUnary(new_c, prepath+path, knowns)));
    } else {
      EvaluateONPComposed1Helper(c, e1, e2, connection, new_c, prepath, path, knowns, inp_0);
      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert (Simpl(EvaluateONPUnary(new_c, path, knowns)) == Simpl(EvaluateONPUnary(new_c, prepath+path, knowns)));
    }
  }

  lemma EvaluateONPUnaryComposed2(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPUnaryRequirements(new_c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      (Seq.Last(path) !in knowns_2) &&
      EvaluateONPUnary(new_c, path, knowns) == EvaluateONPUnary(new_c, path, knowns_2)
    decreases |NodesNotInPath(new_c, path)|, 4
  {
    var head := Seq.Last(path);
    assert head !in knowns;
    ONPNotInKnownsNotInKnowns2(c, head, e1, e2, connection, new_c, knowns);
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(new_c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      assert PathInSubcircuit(path + [inp_0], e2.sc) by {
        reveal PathInSubcircuit();
      }
      EvaluateINPInnerComposed2(c, e1, e2, connection, new_c, path + [inp_0], knowns);
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

  lemma EvaluateINPInnerComposed1(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e1.sc)
    requires PathInSubcircuit(prepath, e2.sc)
    requires EvaluateINPInnerRequirements(new_c, path, knowns)
    requires EvaluateINPInnerRequirements(new_c, prepath + path, knowns)
    ensures
      var knowns_1 := ExtractMap(knowns, e1.finputs);
      (EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_1)) &&
      (Simpl(EvaluateINPInner(new_c, path, knowns)) == Simpl(EvaluateINPInner(new_c, prepath+path, knowns)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 2
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert new_c == ConnectCircuit(c, connection) by {
      reveal ConnectEntitiesImpl();
    }
    
    var knowns_1 := ExtractMap(knowns, e1.finputs); var np := Seq.Last(path);
    assert np.n in e1.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e1.finputs {
      assert np in knowns;
      assert np in knowns_1;
      assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_1);
      assert Simpl(EvaluateINPInner(new_c, path, knowns)) == Simpl(EvaluateINPInner(new_c, prepath+path, knowns));
    } else {
      assert np !in knowns by {
        assert knowns.Keys == e1.finputs + (e2.finputs - connection.Keys);
        InThisNotInThat(np.n, e1.sc, e2.sc);
        assert np.n !in e2.sc;
        FInputsInSc(new_c, e2);
        reveal NPsInSc();
        assert np !in e2.finputs;
      }
      assert np !in knowns_1;
      if np in new_c.PortSource {
        var onp := new_c.PortSource[np];
        assert ONPValid(new_c, onp) by {
          reveal CircuitValid();
        }
        assert onp.n in e1.sc by {
          assert np !in e1.finputs;
          reveal EntitySomewhatValid();
          assert np !in AllInputs(new_c, e1.sc);
          assert np !in ConnInputs(new_c, e1.sc);
          reveal ConnInputs();
        }
        assert EvaluateINPInnerRequirements(new_c, path, knowns);
        assert EvaluateINPInnerRequirements(new_c, path, knowns_1);
        assert EvaluateINPInnerRequirements(new_c, prepath + path, knowns);
        if onp in path {
          assert EvaluateINPInner(new_c, path, knowns) == EvalError({}, {path + [onp]});
          assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_1);
          assert Simpl(EvaluateINPInner(new_c, path, knowns)) == Simpl(EvaluateINPInner(new_c, prepath+path, knowns));
        } else {
          assert NPValid(new_c, onp) by {
            reveal CircuitValid();
          }
          //SetsNoIntersectionFromComposedValid(c, e1, e2);
          NPNotInPathHelper(onp, e1.sc, e2.sc, prepath, path);
          NodesNotInPathDecreases(new_c, prepath+path, onp);
          StillHasNoDuplicates(path, onp);
          StillHasNoDuplicates(prepath + path, onp);
          AppendPathValid(new_c, path, onp);
          AppendPathValid(new_c, prepath + path, onp);
          assert (prepath + path) + [onp] == prepath + (path + [onp]);
          assert Seq.HasNoDuplicates(prepath + (path + [onp]));
          assert PathInSubcircuit(path + [onp], e1.sc) by {
            reveal PathInSubcircuit();
          }
          EvaluateONPInnerComposed1(c, e1, e2, connection, new_c, prepath, path + [onp], knowns);
          assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_1);
          assert Simpl(EvaluateINPInner(new_c, path, knowns)) == Simpl(EvaluateINPInner(new_c, prepath+path, knowns));
        }
      } else {
        assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_1);
        assert Simpl(EvaluateINPInner(new_c, path, knowns)) == Simpl(EvaluateINPInner(new_c, prepath+path, knowns));
      }
    }
  }

  lemma EvaluateINPInnerComposed2(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateINPInnerRequirements(new_c, path, knowns)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      (EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_2))
    decreases |NodesNotInPath(new_c, path)|, 2
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert forall np :: np in e1.finputs ==> np in knowns;
    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
    var np := Seq.Last(path);
    assert np.n in e2.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e2.finputs {
      if np in knowns {
        assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_2);
      } else {
        assert np in connection.Keys;
        assert (np in new_c.PortSource) by {
          assert np in connection;
          reveal ConnectEntitiesImpl();
        }
        var onp := new_c.PortSource[np];
        assert onp.n in e1.sc && onp in e1.foutputs by {
          reveal ConnectEntitiesImpl();
          reveal ConnectionValid();
          assert onp in connection.Values;
          FOutputsInSc(new_c, e1);
          reveal NPsInSc();
        }
        assert ONPValid(new_c, onp) by {
          reveal CircuitValid();
        }
        assert onp !in path by {
          reveal PathInSubcircuit();
          InThisNotInThat(onp.n, e1.sc, e2.sc);
        } 
        NodesNotInPathDecreases(new_c, path, onp);
        StillHasNoDuplicates(path, onp);
        LengthOneNoDuplicates([onp]);
        assert PathValid(new_c, [onp]) by {reveal PathValid();}
        assert PathInSubcircuit([onp], e1.sc) by {reveal PathInSubcircuit();}
        EvaluateONPInnerComposed1(c, e1, e2, connection, new_c, path, [onp], knowns);
        assert (EvaluateONPInner(new_c, [onp], knowns) == EvaluateONPInner(new_c, [onp], knowns_1)); //  (1)
        assert (Simpl(EvaluateONPInner(new_c, path + [onp], knowns)) == Simpl(EvaluateONPInner(new_c, [onp], knowns))); // (2)
        assert EvaluateINPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path + [onp], knowns); // (3)
        assert (e1.f.requires(knowns_1)) && (e1.f(knowns_1).Keys == e1.foutputs) && (knowns_2[np] == e1.f(knowns_1)[onp]) by { // (4)
          Knowns2FromKnowns1(c, e1, e2, connection, knowns, np);
          reveal EntityFValid();
        }
        assert EvaluateONPInner(new_c, [onp], knowns_1) == EvalOk(e1.f(knowns_1)[onp]) by {
          assert EntityValid(new_c, e1);
          reveal EntityEvaluatesCorrectly();
        }
        Knowns2FromKnowns1(c, e1, e2, connection, knowns, np);
        assert EvaluateINPInner(new_c, path, knowns_2) == EvalOk(knowns_2[np]); // by it's own def
        assert EvaluateINPInner(new_c, path, knowns_2) == EvaluateONPInner(new_c, [onp], knowns_1); // by (4) and (5)
        assert EvaluateINPInner(new_c, path, knowns_2) == EvaluateONPInner(new_c, [onp], knowns); // by (1)
        assert EvaluateINPInner(new_c, path, knowns_2) == EvaluateONPInner(new_c, path + [onp], knowns); // by (2)
        assert EvaluateINPInner(new_c, path, knowns_2) == EvaluateINPInner(new_c, path, knowns); // by (3)
      }
    } else {
      assert np !in e2.finputs;
      assert knowns_2.Keys == e2.finputs;
      assert np !in knowns_2;
      assert np !in knowns by {
        assert np.n in e2.sc;
        SetsNoIntersectionSymm(e1.sc, e2.sc);
        InThisNotInThat(np.n, e2.sc, e1.sc);
        assert np.n !in e1.sc;
        FInputsInSc(new_c, e1);
        reveal NPsInSc();
      }
      if np in new_c.PortSource {
        var onp := new_c.PortSource[np];
        assert ONPValid(new_c, onp) by {
          reveal CircuitValid();
        }
        assert onp.n in e2.sc by {
          assert np !in e2.finputs;
          reveal EntitySomewhatValid();
          assert np !in AllInputs(new_c, e2.sc);
          assert np !in ConnInputs(new_c, e2.sc);
          reveal ConnInputs();
        }
        if onp in path {
          assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_2);
        } else {
          NodesNotInPathDecreases(new_c, path, onp);
          StillHasNoDuplicates(path, onp);
          assert PathInSubcircuit(path + [onp], e2.sc) by {
            reveal PathInSubcircuit();
          }
          EvaluateONPInnerComposed2(c, e1, e2, connection, new_c, path + [onp], knowns);
          assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_2);
        }
      } else {
        assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_2);
      }
    }
  }

  lemma EvaluateONPInnerComposed1(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, prepath: seq<NP>, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires EvaluateONPInnerRequirements(new_c, prepath + path, knowns)
    requires EvaluateONPInnerRequirements(new_c, path, knowns)
    requires PathInSubcircuit(path, e1.sc)
    requires PathInSubcircuit(prepath, e2.sc)
    ensures
      (forall np :: np in e1.finputs ==> np in knowns) &&
      var knowns_1 := ExtractMap(knowns, e1.finputs);
      (EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_1)) &&
      (Simpl(EvaluateONPInner(new_c, prepath + path, knowns)) == Simpl(EvaluateONPInner(new_c, path, knowns)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 6
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert forall np :: np in e1.finputs ==> np in knowns;
    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var np := Seq.Last(path);
    assert (np.n in e1.sc) && (np.n !in e2.sc) by {
      reveal PathInSubcircuit();
      InThisNotInThat(np.n, e1.sc, e2.sc);
    }
    Seq.LemmaAppendLast(prepath, path);
    assert np == Seq.Last(prepath + path);
    if np in knowns {
      assert np in knowns_1 by {
        FInputsInSc(new_c, e2);
        reveal NPsInSc();
        assert np !in e2.finputs;
      }
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_1);
      assert Simpl(EvaluateONPInner(new_c, prepath + path, knowns)) == Simpl(EvaluateONPInner(new_c, path, knowns));
    } else {
      assert np.n in new_c.NodeKind by {
        reveal CircuitValid();
      }
      var nk := new_c.NodeKind[np.n];
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed1(c, e1, e2, connection, new_c, prepath, path, knowns);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed1(c, e1, e2, connection, new_c, prepath, path, knowns);
        }
        case CInv() => {
          EvaluateONPUnaryComposed1(c, e1, e2, connection, new_c, prepath, path, knowns);
        }
        case CConst(b) => {}
        case CInput() => {}
        case CSeq() => {}
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_1);
      assert Simpl(EvaluateONPInner(new_c, prepath + path, knowns)) == Simpl(EvaluateONPInner(new_c, path, knowns));
    }
    assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_1);
    assert Simpl(EvaluateONPInner(new_c, prepath + path, knowns)) == Simpl(EvaluateONPInner(new_c, path, knowns));
  }

  lemma EvaluateONPInnerComposed2(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires EvaluateONPInnerRequirements(new_c, path, knowns)
    requires PathInSubcircuit(path, e2.sc)
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      var np := Seq.Last(path);
      (EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2))
    decreases |NodesNotInPath(new_c, path)|, 6
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
    var np := Seq.Last(path);
    assert (np.n in e2.sc) && (np.n !in e1.sc) by {
      reveal PathInSubcircuit();
      SetsNoIntersectionSymm(e2.sc, e1.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    if np in knowns {
      assert np in knowns_2 by {
        assert np.n in e2.sc;
        FInputsInSc(new_c, e1);
        reveal NPsInSc();
        SetsNoIntersectionSymm(e2.sc, e1.sc);
        InThisNotInThat(np.n, e2.sc, e1.sc);
        assert np !in e1.finputs;
      }
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2);
    } else {
      assert np !in e2.finputs by {
        ConnectionKeysINPs(c, e1, e2, connection);
        assert ONPValid(new_c, np);
        NotBothINPValidONPValid(new_c, np);
        reveal INPsValid();
      }
      var nk := new_c.NodeKind[np.n];
      assert !nk.CInput? && !nk.CSeq? by {
        if (nk.CInput? || nk.CSeq?) {
          reveal FinalInputs();
          reveal SeqInputs();
          assert np.n in e2.sc;
          assert ONPValid(new_c, np);
          assert nk.CSeq? ==> np in SeqInputs(new_c, e2.sc);
          assert nk.CInput? ==> np in FinalInputs(new_c, e2.sc);
          assert np in FinalInputs(new_c, e2.sc) + SeqInputs(new_c, e2.sc);
          reveal EntitySomewhatValid();
          assert e2.finputs == AllInputs(new_c, e2.sc);
          assert np in e2.finputs;
        }
      }
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed2(c, e1, e2, connection, new_c, path, knowns);
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed2(c, e1, e2, connection, new_c, path, knowns);
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2);
        }
        case CInv() => {
          EvaluateONPUnaryComposed2(c, e1, e2, connection, new_c, path, knowns);
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2);
        }
        case CConst(b) => {
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2);

        }
        case CInput() => {}
        case CSeq() => {}
      assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2);
    }
  }

  lemma EvaluateConnectEntitiesInner(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, np: NP, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires NPValid(new_c, np)
    requires np in e1.foutputs || np in e2.foutputs
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      var knowns_1 := ExtractMap(knowns, e1.finputs);
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      && NPValid(new_c, np)
      && (np.n in e1.sc ==> Evaluate(new_c, np, knowns_1) == Evaluate(new_c, np, knowns))
      && (np.n in e2.sc ==> Evaluate(new_c, np, knowns_2) == Evaluate(new_c, np, knowns))
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    var prepath: seq<NP> := [];
    var path := [np];
    assert np == Seq.Last(path);
    assert PathValid(new_c, path) && PathValid(new_c, prepath + path) by {
      reveal PathValid();
    }

    assert forall np :: np in e1.finputs ==> np in knowns;
    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);

    LengthOneNoDuplicates(path);
    LengthOneNoDuplicates(prepath + path);
    if np.n in e1.sc {
      assert PathInSubcircuit(prepath, e2.sc) by { reveal PathInSubcircuit(); }
      assert PathInSubcircuit(path, e1.sc) by { reveal PathInSubcircuit(); }
    } else {
      FOutputsInSc(new_c, e1);
      reveal NPsInSc();
      assert np !in e1.foutputs;
      assert np in e2.foutputs;
      FOutputsInSc(new_c, e2);
      assert PathInSubcircuit(path, e2.sc) by { reveal PathInSubcircuit(); }
    }

    if ONPValid(new_c, np) {
      if np.n in e1.sc {
        EvaluateONPInnerComposed1(c, e1, e2, connection, new_c, prepath, path, knowns);
        assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_1);
      } else {
        EvaluateONPInnerComposed2(c, e1, e2, connection, new_c, path, knowns);
        assert EvaluateONPInner(new_c, path, knowns) == EvaluateONPInner(new_c, path, knowns_2);
      }
    } else {
      if np.n in e1.sc {
        EvaluateINPInnerComposed1(c, e1, e2, connection, new_c, prepath, path, knowns);
        assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_1);
      } else {
        EvaluateINPInnerComposed2(c, e1, e2, connection, new_c, path, knowns);
        assert EvaluateINPInner(new_c, path, knowns) == EvaluateINPInner(new_c, path, knowns_2);
      }
    }
    if np.n in e1.sc {
      InThisNotInThat(np.n, e1.sc, e2.sc);
      assert np.n !in e2.sc;
      assert Evaluate(new_c, np, knowns) == Evaluate(new_c, np, knowns_1);
    } else {
      assert np.n in e2.sc;
      assert Evaluate(new_c, np, knowns) == Evaluate(new_c, np, knowns_2);
    }
  }

  lemma EvaluateConnectEntities(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, np: NP, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires NPValid(new_c, np)
    requires np in e1.foutputs || np in e2.foutputs
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      && e.f.requires(knowns)
      && np in e.f(knowns)
      && NPValid(new_c, np)
      && Evaluate(new_c, np, knowns) == EvalOk(e.f(knowns)[np])
  {
    EvaluateConnectEntitiesInner(c, e1, e2, connection, new_c, np, knowns);
    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
    ConnectEntitiesSomewhatValid(c, e1, e2, connection);
    assert ScValid(new_c, e1.sc) && ScValid(new_c, e2.sc) by {
      reveal EntitySomewhatValid();
      reveal ConnectEntitiesImpl();
      reveal ScValid();
    }
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert EntityValid(new_c, e1);
    assert EntityValid(new_c, e2);

    var knowns_1 := ExtractMap(knowns, e1.finputs);
    var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);

    assert e.foutputs == e1.foutputs + e2.foutputs by {
      reveal ConnectEntitiesImpl();
    }
    EntityFOutputsAreValid(new_c, e);
    FOutputsInSc(c, e1);
    if np in e1.foutputs {
      reveal NPsInSc();
      assert np.n in e1.sc;
      assert Evaluate(new_c, np, knowns_1) == Evaluate(new_c, np, knowns);
      reveal EntityFValid();
      assert knowns_1.Keys == e1.finputs;
      assert e1.f(knowns_1).Keys == e1.foutputs;
      assert Evaluate(new_c, np, knowns_1) == EvalOk(e1.f(knowns_1)[np]) by {
        assert EntityEvaluatesCorrectly(c, e1);
        reveal EntityEvaluatesCorrectly();
      }
      assert Evaluate(new_c, np, knowns) == Evaluate(new_c, np, knowns_1);
      assert np in e.foutputs by {
        reveal ConnectEntitiesImpl();
      }
      assert knowns.Keys == e.finputs by {
        reveal ConnectEntitiesImpl();
      }
      ConnectEntitiesFValid(c, e1, e2, connection);
      assert EntityFValid(new_c, e);
      assert e.f.requires(knowns);
      assert EvalOk(e1.f(knowns_1)[np]) == EvalOk(e.f(knowns)[np]) by {
        reveal ConnectEntitiesImpl();
        assert np in e.foutputs;
        assert np in e.f(knowns);
      }
      assert Evaluate(new_c, np, knowns) == EvalOk(e.f(knowns)[np]);
    } else {
      assert np in e2.foutputs;
      assert np in e.foutputs by {
        reveal ConnectEntitiesImpl();
      }
      ConnectEntitiesFValid(c, e1, e2, connection);
      reveal EntityFValid();
      reveal ConnectEntitiesImpl();
      assert knowns.Keys == e.finputs;
      assert e.f.requires(knowns);
      assert e.f(knowns).Keys == e.foutputs;
      FOutputsInSc(new_c, e2);
      reveal NPsInSc();
      assert np.n in e2.sc;
      reveal EntityEvaluatesCorrectly();
      assert Evaluate(new_c, np, knowns_2) == EvalOk(e2.f(knowns_2)[np]);
      ConnectEntitiesFHelper(c, e1, e2, connection, knowns, np);
      assert EvalOk(e2.f(knowns_2)[np]) == EvalOk(e.f(knowns)[np]) by {
        reveal ConnectEntitiesImpl();
      }
      assert Evaluate(new_c, np, knowns) == Evaluate(new_c, np, knowns_2);
      assert EvalOk(e2.f(knowns_2)[np]) == EvalOk(e.f(knowns)[np]);
      assert Evaluate(new_c, np, knowns) == EvalOk(e.f(knowns)[np]);

    }
  }

  lemma ConnectEntitiesValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      && EntityValid(new_c, e)
  {
    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
    ConnectEntitiesFValid(c, e1, e2, connection);
    ConnectEntitiesSomewhatValid(c, e1, e2, connection);
    assert e.foutputs == e1.foutputs + e2.foutputs by {
      reveal ConnectEntitiesImpl();
    }
    assert e.finputs == e1.finputs + (e2.finputs-connection.Keys) by {
      reveal ConnectEntitiesImpl();
    }
    forall knowns: map<NP, bool> | (knowns.Keys == e.finputs)
      ensures e.f.requires(knowns)
      ensures forall np :: np in e.foutputs ==>
          np in e.f(knowns) &&
          NPValid(new_c, np) &&
          (Evaluate(new_c, np, knowns) == EvalOk(e.f(knowns)[np]))
    {
      EntityFOutputsAreValid(c, e1);
      EntityFOutputsAreValid(c, e2);
      FOutputsInSc(c, e1);
      FOutputsInSc(c, e2);
      reveal EntityFValid();
      forall np | np in e.foutputs
        ensures
          //e.f.requires(knowns) &&
          && np in e.f(knowns)
          && NPValid(new_c, np)
          && (Evaluate(new_c, np, knowns) == EvalOk(e.f(knowns)[np]))
      {
        EntityFOutputsAreValid(new_c, e);
        reveal NPsInSc();
        assert NPValid(new_c, np);
        EvaluateConnectEntities(c, e1, e2, connection, new_c, np, knowns);
        assert (Evaluate(new_c, np, knowns) == EvalOk(e.f(knowns)[np]));
      }
    }
    reveal EntityEvaluatesCorrectly();
    assert ScValid(new_c, e.sc) by {
      reveal ConnectEntitiesImpl();
      reveal ScValid();
    }
    assert forall knowns: map<NP, bool> :: knowns.Keys == e.finputs ==>
      forall np :: np in e.foutputs ==>
        && Evaluate(new_c, np, knowns) == EvalOk(e.f(knowns)[np]);
    assert EntityEvaluatesCorrectly(new_c, e);
    assert EntityValid(new_c, e);
  }

  function ConnectEntities(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>): (r: (Circuit, Entity))
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures CircuitValid(r.0)
    ensures EntityValid(r.0, r.1)
  {
    ConnectEntitiesValid(c, e1, e2, connection);
    ConnectEntitiesImpl(c, e1, e2, connection)
  }

}

module ConnectionEval {

  import Std.Collections.Seq

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Connection
  import opened Subcircuit
  import opened MapFunction

  lemma Knowns2FromKnowns1(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, fi: FI, np: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires np in connection
    ensures
      && var new_c := ConnectEntitiesImpl(c, e1, e2, connection).0;
      && np in new_c.PortSource
      && var onp := new_c.PortSource[np];
      && var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
      && var knowns_2 := GetInputs2(e1.mf, e2.mf, connection, fi);
      && (np in knowns_2)
      && (e1.mf.f.requires(fi))
      && (onp in e1.mf.f(fi).outputs)
      && (knowns_2[np] == e1.mf.f(fi_1).outputs[onp])
  {
    var new_c := ConnectEntitiesImpl(c, e1, e2, connection).0;
    ConnectCircuitReqFromConnectEntitiesReq(c, e1, e2, connection);
    assert new_c == ConnectCircuit(c, connection) by {
      reveal ConnectEntitiesImpl();
    }
    var knowns_1 := ExtractMap(fi.inputs, e1.mf.inputs);
    var knowns_2 := GetInputs2(e1.mf, e2.mf, connection, fi);
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var onp := connection[np];
    assert onp == new_c.PortSource[np] by {
      reveal ConnectEntitiesImpl();
      reveal ConnectionValid();
    }
    assert np !in e1.mf.inputs by {
      ConnectionKeysInE2(c, e1, e2, connection);
      FInputsInSc(c, e1);
      reveal NPsInSc();
      SetsNoIntersectionSymm(e1.sc, e2.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    assert np !in fi.inputs;

    //var inputs_1 := ExtractMap(fi.inputs, e1.mf.inputs);
    //reveal MapFunctionValid();
    //var outputs_1 := e1.mf.f(FI(inputs_1, state1)).outputs;
    //assert outputs_1.Keys == e1.mf.outputs;
    //reveal ConnectionValid();
    //assert connection.Values <= e1.mf.outputs;
    //var connected := (map np | np in connection :: np := outputs_1[connection[np]]);
    //assert connected.Keys == connection.Keys;
    //assert knowns.Keys == e1.mf.inputs + (e2.mf.inputs - connection.Keys);
    //RearrangeKnownKeys(c, e1, e2, connection, knowns);
    //assert knowns.Keys == (e1.mf.inputs + e2.mf.inputs) - connection.Keys;
    //var combined_map := AddMaps(knowns, connected);
    //var inputs_2 := ExtractMap(combined_map, e2.mf.inputs);
    //assert inputs_2 == knowns_2;

    //assert np in connected;
    assert np in knowns_2;
  }

  lemma ONPNotInKnownsNotInKnowns2(c: Circuit, onp: NP, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires onp !in fi.inputs
    requires ONPValid(new_c, onp)
    ensures onp !in GetInputs2(e1.mf, e2.mf, connection, fi)
  {
    assert onp !in e1.mf.inputs + (e2.mf.inputs - connection.Keys);
    var knowns_2 := GetInputs2(e1.mf, e2.mf, connection, fi);
    assert knowns_2.Keys == e2.mf.inputs;
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
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit,
      prepath: seq<NP>, path: seq<NP>, fi: FI, inp: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires inp !in path
    requires inp.n in e1.sc
    requires INPValid(new_c, inp)
    requires EvaluateONPUnaryBinaryRequirements(new_c, path, fi)
    requires EvaluateONPUnaryBinaryRequirements(new_c, prepath + path, fi)
    ensures forall np :: np in e1.mf.inputs ==> np in fi.inputs
    ensures
      && var new_path := path + [inp];
      && Seq.HasNoDuplicates(new_path)
      && Seq.HasNoDuplicates(prepath + new_path)
      && PathValid(new_c, new_path)
      && PathValid(new_c, prepath + new_path)
      && var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
      && EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_1)
      && Simpl(EvaluateINPInner(new_c, new_path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+new_path, fi))
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
    assert forall np :: np in e1.mf.inputs ==> np in fi.inputs;
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var new_path := path + [inp];
    NodesNotInPathDecreases(new_c, prepath + path, inp);
    assert PathInSubcircuit(new_path, e1.sc) by {reveal PathInSubcircuit();}
    assert (prepath + path) + [inp] == prepath + (path + [inp]);
    assert Seq.Last(prepath + new_path) == inp;
    EvaluateINPInnerComposed1(c, e1, e2, connection, new_c, prepath, new_path, fi);
    assert EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_1);
    assert Simpl(EvaluateINPInner(new_c, new_path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+new_path, fi));
  }

  lemma EvaluateONPBinaryComposed1(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit,
      prepath: seq<NP>, path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires EvaluateONPBinaryRequirements(new_c, path, fi)
    requires EvaluateONPBinaryRequirements(new_c, prepath + path, fi)
    ensures
      (forall np :: np in e1.mf.inputs ==> np in fi.inputs) &&
      var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
      var np := Seq.Last(path);
      && (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_1))
      && (Simpl(EvaluateONPBinary(new_c, path, fi)) == Simpl(EvaluateONPBinary(new_c, prepath+path, fi)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 4
  {
    assert forall np :: np in e1.mf.inputs ==> np in fi.inputs;
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
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
      assert (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_1));
      assert (Simpl(EvaluateONPBinary(new_c, path, fi)) == Simpl(EvaluateONPBinary(new_c, prepath+path, fi)));
    } else if inp_1 in path {
      assert (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_1));
      assert (Simpl(EvaluateONPBinary(new_c, path, fi)) == Simpl(EvaluateONPBinary(new_c, prepath+path, fi)));
    } else {
      EvaluateONPComposed1Helper(c, e1, e2, connection, new_c, prepath, path, fi, inp_0);
      EvaluateONPComposed1Helper(c, e1, e2, connection, new_c, prepath, path, fi, inp_1);

      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert prepath + (path + [inp_1]) == (prepath + path) + [inp_1];

      assert (Simpl(EvaluateONPBinary(new_c, path, fi)) == Simpl(EvaluateONPBinary(new_c, prepath+path, fi)));
    }
  }

  lemma EvaluateONPComposed2Helper(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, fi: FI, inp: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPUnaryBinaryRequirements(new_c, path, fi)
    requires INPValid(new_c, inp)
    requires inp !in path
    requires inp.n in e2.sc
    ensures
      var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
      var new_path := path + [inp];
      Seq.HasNoDuplicates(new_path) &&
      PathValid(new_c, new_path) &&
      (EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_2))
    decreases |NodesNotInPath(new_c, path)|, 4
  {
    StillHasNoDuplicates(path, inp);
    AppendPathValid(new_c, path, inp);
    var new_path := path + [inp];
    NodesNotInPathDecreases(new_c, path, inp);
    reveal PathInSubcircuit();
    EvaluateINPInnerComposed2(c, e1, e2, connection, new_c, new_path, fi);
    var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
    assert (EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_2));
  }

  lemma EvaluateONPBinaryComposed2(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPBinaryRequirements(new_c, path, fi)
    ensures
      var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
      (Seq.Last(path) !in fi_2.inputs) &&
      (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_2))
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
    var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
    assert head !in fi_2.inputs;
    ONPNotInKnownsNotInKnowns2(c, head, e1, e2, connection, new_c, fi);
    if inp_0 in path {
      assert (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_2));
    } else if inp_1 in path {
      assert (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_2));
    } else {
      assert 
        var new_path := path + [inp_0];
        && Seq.HasNoDuplicates(new_path)
        && PathValid(new_c, new_path)
        && (EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_2)) by {
          //AppendPathValid(new_path, inp_0);
          EvaluateONPComposed2Helper(c, e1, e2, connection, new_c, path, fi, inp_0);
        }
      assert 
        var new_path := path + [inp_1];
        && Seq.HasNoDuplicates(new_path)
        && PathValid(new_c, new_path)
        && (EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_2)) by {
          //AppendPathValid(new_path, inp_0);
          EvaluateONPComposed2Helper(c, e1, e2, connection, new_c, path, fi, inp_1);
        }
      assert EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_2);
    }
    assert
      var knowns_2 := GetInputs2(e1.mf, e2.mf, connection, fi);
      (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_2));
  }

  lemma EvaluateONPUnaryComposed1(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit,
      prepath: seq<NP>, path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(prepath, e2.sc)
    requires PathInSubcircuit(path, e1.sc)
    requires EvaluateONPUnaryRequirements(new_c, path, fi)
    requires EvaluateONPUnaryRequirements(new_c, prepath+path, fi)
    ensures
      (forall np :: np in e1.mf.inputs ==> np in fi.inputs) &&
      var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
      var np := Seq.Last(path);
      (EvaluateONPUnary(new_c, path, fi) == EvaluateONPUnary(new_c, path, fi_1)) &&
      (Simpl(EvaluateONPUnary(new_c, path, fi)) == Simpl(EvaluateONPUnary(new_c, prepath+path, fi)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 5
  {
    assert forall np :: np in e1.mf.inputs ==> np in fi.inputs;
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var head := Seq.Last(path);
    assert head == Seq.Last(prepath + path);
    assert head.n in e1.sc by {reveal PathInSubcircuit();}
    assert NodeValid(new_c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    assert INPValid(new_c, inp_0) by {reveal CircuitValid();}
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
      assert (EvaluateONPUnary(new_c, path, fi) == EvaluateONPUnary(new_c, path, fi_1));
      assert (Simpl(EvaluateONPUnary(new_c, path, fi)) == Simpl(EvaluateONPUnary(new_c, prepath+path, fi)));
    } else {
      EvaluateONPComposed1Helper(c, e1, e2, connection, new_c, prepath, path, fi, inp_0);
      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert (Simpl(EvaluateONPUnary(new_c, path, fi)) == Simpl(EvaluateONPUnary(new_c, prepath+path, fi)));
    }
  }

  lemma EvaluateONPUnaryComposed2(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateONPUnaryRequirements(new_c, path, fi)
    ensures
      var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
      (Seq.Last(path) !in fi_2.inputs) &&
      EvaluateONPUnary(new_c, path, fi) == EvaluateONPUnary(new_c, path, fi_2)
    decreases |NodesNotInPath(new_c, path)|, 4
  {
    var head := Seq.Last(path);
    assert head !in fi.inputs;
    ONPNotInKnownsNotInKnowns2(c, head, e1, e2, connection, new_c, fi);
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(new_c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      assert PathInSubcircuit(path + [inp_0], e2.sc) by {
        reveal PathInSubcircuit();
      }
      EvaluateINPInnerComposed2(c, e1, e2, connection, new_c, path + [inp_0], fi);
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

  lemma EvaluateINPInnerComposed1(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit,
      prepath: seq<NP>, path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e1.sc)
    requires PathInSubcircuit(prepath, e2.sc)
    requires EvaluateINPInnerRequirements(new_c, path)
    requires EvaluateINPInnerRequirements(new_c, prepath + path)
    ensures
      var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
      (EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1)) &&
      (Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 2
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert new_c == ConnectCircuit(c, connection) by {
      reveal ConnectEntitiesImpl();
    }
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var np := Seq.Last(path);
    assert np.n in e1.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e1.mf.inputs {
      assert np in fi.inputs;
      assert np in fi_1.inputs;
      assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
      assert Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi));
    } else {
      assert np !in fi.inputs by {
        assert fi.inputs.Keys == e1.mf.inputs + (e2.mf.inputs - connection.Keys);
        InThisNotInThat(np.n, e1.sc, e2.sc);
        assert np.n !in e2.sc;
        FInputsInSc(new_c, e2);
        reveal NPsInSc();
        assert np !in e2.mf.inputs;
      }
      assert np !in fi_1.inputs;
      if np in new_c.PortSource {
        var onp := new_c.PortSource[np];
        assert ONPValid(new_c, onp) by {
          reveal CircuitValid();
        }
        assert onp.n in e1.sc by {
          assert np !in e1.mf.inputs;
          reveal EntitySomewhatValid();
          assert np !in AllInputs(new_c, e1.sc);
          assert np !in ConnInputs(new_c, e1.sc);
          reveal ConnInputs();
        }
        assert EvaluateINPInnerRequirements(new_c, path);
        assert EvaluateINPInnerRequirements(new_c, prepath + path);
        if onp in path {
          assert EvaluateINPInner(new_c, path, fi) == EvalError({}, {path + [onp]});
          assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
          assert Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi));
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
          EvaluateONPInnerComposed1(c, e1, e2, connection, new_c, prepath, path + [onp], fi);
          assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
          assert Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi));
        }
      } else {
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
        assert Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi));
      }
    }
  }

  lemma EvaluateINPInnerComposed2(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit,
      path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires PathInSubcircuit(path, e2.sc)
    requires EvaluateINPInnerRequirements(new_c, path)
    ensures
      var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
      (EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2))
    decreases |NodesNotInPath(new_c, path)|, 2
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert forall np :: np in e1.mf.inputs ==> np in fi.inputs;
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
    var np := Seq.Last(path);
    assert np.n in e2.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    if np in e2.mf.inputs {
      if np in fi.inputs {
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
      } else {
        assert np in connection.Keys;
        assert (np in new_c.PortSource) by {
          assert np in connection;
          reveal ConnectEntitiesImpl();
        }
        var onp := new_c.PortSource[np];
        assert onp.n in e1.sc && onp in e1.mf.outputs by {
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
        EvaluateONPInnerComposed1(c, e1, e2, connection, new_c, path, [onp], fi);
        assert (EvaluateONPInner(new_c, [onp], fi) == EvaluateONPInner(new_c, [onp], fi_1)); //  (1)
        assert (Simpl(EvaluateONPInner(new_c, path + [onp], fi)) == Simpl(EvaluateONPInner(new_c, [onp], fi))); // (2)
        assert EvaluateINPInner(new_c, path, fi) == EvaluateONPInner(new_c, path + [onp], fi); // (3)
        assert (e1.mf.f.requires(fi_1)) && (e1.mf.f(fi_1).outputs.Keys == e1.mf.outputs) && (fi_2.inputs[np] == e1.mf.f(fi_1).outputs[onp]) by { // (4)
          Knowns2FromKnowns1(c, e1, e2, connection, fi, np);
          reveal MapFunctionValid();
        }
        assert EvaluateONPInner(new_c, [onp], fi_1) == EvalOk(e1.mf.f(fi_1).outputs[onp]) by {
          assert EntityValid(new_c, e1);
          reveal EntityEvaluatesCorrectly();
        }
        Knowns2FromKnowns1(c, e1, e2, connection, fi, np);
        assert EvaluateINPInner(new_c, path, fi_2) == EvalOk(fi_2.inputs[np]); // by it's own def
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateONPInner(new_c, [onp], fi_1); // by (4) and (5)
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateONPInner(new_c, [onp], fi); // by (1)
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateONPInner(new_c, path + [onp], fi); // by (2)
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateINPInner(new_c, path, fi); // by (3)
      }
    } else {
      assert np !in e2.mf.inputs;
      assert fi_2.inputs.Keys == e2.mf.inputs;
      assert np !in fi_2.inputs;
      assert np !in fi.inputs by {
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
          assert np !in e2.mf.inputs;
          reveal EntitySomewhatValid();
          assert np !in AllInputs(new_c, e2.sc);
          assert np !in ConnInputs(new_c, e2.sc);
          reveal ConnInputs();
        }
        if onp in path {
          assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
        } else {
          NodesNotInPathDecreases(new_c, path, onp);
          StillHasNoDuplicates(path, onp);
          assert PathInSubcircuit(path + [onp], e2.sc) by {
            reveal PathInSubcircuit();
          }
          EvaluateONPInnerComposed2(c, e1, e2, connection, new_c, path + [onp], fi);
          assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
        }
      } else {
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
      }
    }
  }

  lemma EvaluateONPInnerComposed1(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit,
      prepath: seq<NP>, path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires EvaluateONPInnerRequirements(new_c, prepath + path)
    requires EvaluateONPInnerRequirements(new_c, path)
    requires PathInSubcircuit(path, e1.sc)
    requires PathInSubcircuit(prepath, e2.sc)
    ensures
      (forall np :: np in e1.mf.inputs ==> np in fi.inputs) &&
      var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
      (EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1)) &&
      (Simpl(EvaluateONPInner(new_c, prepath + path, fi)) == Simpl(EvaluateONPInner(new_c, path, fi)))
    decreases |NodesNotInPath(new_c, prepath + path)|, 6
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert forall np :: np in e1.mf.inputs ==> np in fi.inputs;
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var np := Seq.Last(path);
    assert (np.n in e1.sc) && (np.n !in e2.sc) by {
      reveal PathInSubcircuit();
      InThisNotInThat(np.n, e1.sc, e2.sc);
    }
    Seq.LemmaAppendLast(prepath, path);
    assert np == Seq.Last(prepath + path);
    if np in fi.inputs {
      assert np in fi_1.inputs by {
        FInputsInSc(new_c, e2);
        reveal NPsInSc();
        assert np !in e2.mf.inputs;
      }
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
      assert Simpl(EvaluateONPInner(new_c, prepath + path, fi)) == Simpl(EvaluateONPInner(new_c, path, fi));
    } else {
      assert np.n in new_c.NodeKind by {
        reveal CircuitValid();
      }
      var nk := new_c.NodeKind[np.n];
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed1(c, e1, e2, connection, new_c, prepath, path, fi);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed1(c, e1, e2, connection, new_c, prepath, path, fi);
        }
        case CInv() => {
          EvaluateONPUnaryComposed1(c, e1, e2, connection, new_c, prepath, path, fi);
        }
        case CConst(b) => {}
        case CSeq() => {}
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
      assert Simpl(EvaluateONPInner(new_c, prepath + path, fi)) == Simpl(EvaluateONPInner(new_c, path, fi));
    }
    assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
    assert Simpl(EvaluateONPInner(new_c, prepath + path, fi)) == Simpl(EvaluateONPInner(new_c, path, fi));
  }

  lemma EvaluateONPInnerComposed2(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit,
      path: seq<NP>, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires EvaluateONPInnerRequirements(new_c, path)
    requires PathInSubcircuit(path, e2.sc)
    ensures
      var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
      var np := Seq.Last(path);
      (EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2))
    decreases |NodesNotInPath(new_c, path)|, 6
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
    var np := Seq.Last(path);
    assert (np.n in e2.sc) && (np.n !in e1.sc) by {
      reveal PathInSubcircuit();
      SetsNoIntersectionSymm(e2.sc, e1.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    if np in fi.inputs {
      assert np in fi_2.inputs by {
        assert np.n in e2.sc;
        FInputsInSc(new_c, e1);
        reveal NPsInSc();
        SetsNoIntersectionSymm(e2.sc, e1.sc);
        InThisNotInThat(np.n, e2.sc, e1.sc);
        assert np !in e1.mf.inputs;
      }
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
    } else {
      assert np !in e2.mf.inputs by {
        ConnectionKeysINPs(c, e1, e2, connection);
        assert ONPValid(new_c, np);
        NotBothINPValidONPValid(new_c, np);
        reveal INPsValid();
      }
      var nk := new_c.NodeKind[np.n];
      assert !nk.CSeq? by {
        if nk.CSeq? {
          reveal SeqInputs();
          assert np.n in e2.sc;
          assert ONPValid(new_c, np);
          assert nk.CSeq? ==> np in SeqInputs(new_c, e2.sc);
          assert np in SeqInputs(new_c, e2.sc);
          reveal EntitySomewhatValid();
          assert e2.mf.inputs == AllInputs(new_c, e2.sc);
          assert np in e2.mf.inputs;
        }
      }
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed2(c, e1, e2, connection, new_c, path, fi);
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed2(c, e1, e2, connection, new_c, path, fi);
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
        case CInv() => {
          EvaluateONPUnaryComposed2(c, e1, e2, connection, new_c, path, fi);
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
        case CConst(b) => {
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);

        }
        case CSeq() => {}
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
    }
  }

  lemma EvaluateConnectEntitiesInner(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>,
      new_c: Circuit, np: NP, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires NPValid(new_c, np)
    requires np in e1.mf.outputs || np in e2.mf.outputs || np in StateINPs(e1.mf.state + e2.mf.state)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
      var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);
      && NPValid(new_c, np)
      && (np.n in e1.sc ==> Evaluate(new_c, np, fi_1) == Evaluate(new_c, np, fi))
      && (np.n in e2.sc ==> Evaluate(new_c, np, fi_2) == Evaluate(new_c, np, fi))
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    var prepath: seq<NP> := [];
    var path := [np];
    assert np == Seq.Last(path);
    assert PathValid(new_c, path) && PathValid(new_c, prepath + path) by {
      reveal PathValid();
    }

    assert forall np :: np in e1.mf.inputs ==> np in fi.inputs;
    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);

    LengthOneNoDuplicates(path);
    LengthOneNoDuplicates(prepath + path);
    if np.n in e1.sc {
      assert PathInSubcircuit(prepath, e2.sc) by { reveal PathInSubcircuit(); }
      assert PathInSubcircuit(path, e1.sc) by { reveal PathInSubcircuit(); }
    } else {
      FOutputsInSc(new_c, e1);
      reveal NPsInSc();
      assert np !in e1.mf.outputs;
      assert np in e2.mf.outputs;
      FOutputsInSc(new_c, e2);
      assert PathInSubcircuit(path, e2.sc) by { reveal PathInSubcircuit(); }
    }

    if ONPValid(new_c, np) {
      if np.n in e1.sc {
        EvaluateONPInnerComposed1(c, e1, e2, connection, new_c, prepath, path, fi);
        assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
      } else {
        EvaluateONPInnerComposed2(c, e1, e2, connection, new_c, path, fi);
        assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
      }
    } else {
      if np.n in e1.sc {
        EvaluateINPInnerComposed1(c, e1, e2, connection, new_c, prepath, path, fi);
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
      } else {
        EvaluateINPInnerComposed2(c, e1, e2, connection, new_c, path, fi);
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
      }
    }
    if np.n in e1.sc {
      InThisNotInThat(np.n, e1.sc, e2.sc);
      assert np.n !in e2.sc;
      assert Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_1);
    } else {
      assert np.n in e2.sc;
      assert Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_2);
    }
  }

  lemma {:vcs_split_on_every_assert} EvaluateConnectEntities(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, new_c: Circuit, np: NP, fi: FI)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires new_c == ConnectEntitiesImpl(c, e1, e2, connection).0
    requires NPValid(new_c, np)
    requires np in e1.mf.outputs || np in e2.mf.outputs || np in StateINPs(e1.mf.state + e2.mf.state)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      && e.mf.f.requires(fi)
      && NPValid(new_c, np)
      && (np in (e1.mf.outputs + e2.mf.outputs) ==>
          && np in e.mf.f(fi).outputs
          && Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]))
      && (np in StateINPs(e1.mf.state + e2.mf.state) ==>
          && np in e.mf.f(fi).state
          && Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).state[np]))
  {
    EvaluateConnectEntitiesInner(c, e1, e2, connection, new_c, np, fi);
    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
    assert e.mf.f.requires(fi) by {
      assert e.mf.inputs == e1.mf.inputs + (e2.mf.inputs - connection.Keys);
      reveal MapFunctionValid();
      reveal ConnectEntitiesImpl();
    }
    ConnectEntitiesSomewhatValid(c, e1, e2, connection);
    assert ScValid(new_c, e1.sc) && ScValid(new_c, e2.sc) by {
      reveal EntitySomewhatValid();
      reveal ConnectEntitiesImpl();
      reveal ScValid();
    }
    ConnectEntitiesEntitiesStillValid(c, e1, e2, connection);
    assert EntityValid(new_c, e1);
    assert EntityValid(new_c, e2);

    var fi_1 := ConnectFI1FromFI(e1.mf, e2.mf, connection, fi);
    var fi_2 := ConnectFI2FromFI(e1.mf, e2.mf, connection, fi);

    assert e.mf.outputs == e1.mf.outputs + e2.mf.outputs by {
      reveal ConnectEntitiesImpl();
    }
    EntityFOutputsAreValid(new_c, e);
    FOutputsInSc(c, e1);
    if np in e1.mf.outputs || np in StateINPs(e1.mf.state) {
      reveal NPsInSc();
      assert np.n in e1.sc;
      assert Evaluate(new_c, np, fi_1) == Evaluate(new_c, np, fi);
      reveal MapFunctionValid();
      assert fi_1.inputs.Keys == e1.mf.inputs;
      assert e1.mf.f(fi_1).outputs.Keys == e1.mf.outputs;
      if np in e1.mf.outputs {
        assert Evaluate(new_c, np, fi_1) == EvalOk(e1.mf.f(fi_1).outputs[np]) by {
          assert EntityEvaluatesCorrectly(c, e1);
          reveal EntityEvaluatesCorrectly();
        }
      } else {
        assert Evaluate(new_c, np, fi_1) == EvalOk(e1.mf.f(fi_1).state[np]) by {
          assert EntityEvaluatesCorrectly(c, e1);
          reveal EntityEvaluatesCorrectly();
        }
      }
      assert Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_1);
      assert np in e.mf.outputs || np in StateINPs(e.mf.state) by {
        reveal ConnectEntitiesImpl();
      }
      assert fi.inputs.Keys == e.mf.inputs by {
        reveal ConnectEntitiesImpl();
      }
      ConnectEntitiesFValid(c, e1, e2, connection);
      assert MapFunctionValid(e.mf);
      assert e.mf.f.requires(fi);
      if np in e1.mf.outputs {
        assert EvalOk(e1.mf.f(fi_1).outputs[np]) == EvalOk(e.mf.f(fi).outputs[np]) by {
          reveal ConnectEntitiesImpl();
          assert np in e.mf.outputs;
          assert np in e.mf.f(fi).outputs;
        }
      } else {
        assert EvalOk(e1.mf.f(fi_1).state[np]) == EvalOk(e.mf.f(fi).state[np]) by {
          reveal ConnectEntitiesImpl();
          assert np in e.mf.outputs;
          assert np in e.mf.f(fi).state;
        }
      }
      assert Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]);
    } else {
      assert np in e2.mf.outputs || np in StateINPs(e2.mf.state);
      assert np in e.mf.outputs || np in StateINPs(e.mf.state) by {
        reveal ConnectEntitiesImpl();
      }
      ConnectEntitiesFValid(c, e1, e2, connection);
      reveal MapFunctionValid();
      reveal ConnectEntitiesImpl();
      assert fi.inputs.Keys == e.mf.inputs;
      assert e.mf.f.requires(fi);
      assert e.mf.f(fi).outputs.Keys == e.mf.outputs;
      FOutputsInSc(new_c, e2);
      reveal NPsInSc();
      assert np.n in e2.sc;
      reveal EntityEvaluatesCorrectly();
      if np in e2.mf.outputs {
        assert Evaluate(new_c, np, fi_2) == EvalOk(e2.mf.f(fi_2).outputs[np]);
        ConnectEntitiesFHelper(c, e1, e2, connection, fi, np);
        assert EvalOk(e2.mf.f(fi_2).outputs[np]) == EvalOk(e.mf.f(fi).outputs[np]) by {
          reveal ConnectEntitiesImpl();
        }
        assert Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_2);
        assert EvalOk(e2.mf.f(fi_2).outputs[np]) == EvalOk(e.mf.f(fi).outputs[np]);
        assert Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]);
      } else {
        assert Evaluate(new_c, np, fi_2) == EvalOk(e2.mf.f(fi_2).state[np]);
        ConnectEntitiesFHelper(c, e1, e2, connection, fi, np);
        assert EvalOk(e2.mf.f(fi_2).outputs[np]) == EvalOk(e.mf.f(fi).state[np]) by {
          reveal ConnectEntitiesImpl();
        }
        assert Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_2);
        assert EvalOk(e2.mf.f(fi_2).outputs[np]) == EvalOk(e.mf.f(fi).state[np]);
        assert Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).state[np]);
      }
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
    assert e.mf.outputs == e1.mf.outputs + e2.mf.outputs by {
      reveal ConnectEntitiesImpl();
    }
    assert e.mf.inputs == e1.mf.inputs + (e2.mf.inputs-connection.Keys) by {
      reveal ConnectEntitiesImpl();
    }
    assert e.mf.state == e1.mf.state + e2.mf.state by {
      reveal ConnectEntitiesImpl();
    }
    forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
      ensures e.mf.f.requires(fi)
      ensures forall np :: np in e.mf.outputs ==>
          np in e.mf.f(fi).outputs &&
          NPValid(new_c, np) &&
          (Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]))
      ensures forall np :: np in StateINPs(e.mf.state) ==>
          np in e.mf.f(fi).state &&
          NPValid(new_c, np) &&
          (Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).state[np]))
    {
      EntityFOutputsAreValid(c, e1);
      EntityFOutputsAreValid(c, e2);
      FOutputsInSc(c, e1);
      FOutputsInSc(c, e2);
      reveal MapFunctionValid();
      forall np | np in e.mf.outputs
        ensures
          && np in e.mf.f(fi).outputs
          && NPValid(new_c, np)
          && (Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]))
      {
        EntityFOutputsAreValid(new_c, e);
        reveal NPsInSc();
        assert NPValid(new_c, np);
        EvaluateConnectEntities(c, e1, e2, connection, new_c, np, fi);
        assert (Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]));
      }
      forall np | np in StateINPs(e.mf.state)
        ensures
          && np in e.mf.f(fi).state
          && NPValid(new_c, np)
          && (Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).state[np]))
      {
        EntityFOutputsAreValid(new_c, e);
        reveal NPsInSc();
        assert NPValid(new_c, np);
        EvaluateConnectEntities(c, e1, e2, connection, new_c, np, fi);
        assert (Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).state[np]));
      }
    }
    reveal EntityEvaluatesCorrectly();
    assert ScValid(new_c, e.sc) by {
      reveal ConnectEntitiesImpl();
      reveal ScValid();
    }
    assert forall fi: FI :: FIValid(fi, e.mf.inputs, e.mf.state) ==>
      forall np :: np in e.mf.outputs ==>
        && Evaluate(new_c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]);
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

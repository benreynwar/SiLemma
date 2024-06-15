module ConnectionEval {

  import Std.Collections.Seq

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Scuf
  import opened Connection
  import opened Subcircuit
  import opened MapFunction
  import opened MapConnection

  datatype CESummary = CESummary(
    c: Circuit,              // The original circuit
    conn: ScufConnection,      // Connection from entity 1 to entity 2
    fi: FI,                  // The inputs into the combined entity

    // The below items can be derived from the above but it's tidier to
    // pass them directly it rather than repeating the definitions everywhere.

    new_c: Circuit,          // The circuit after the entities are connected
    fi_1: FI,                // The inputs into the first entity.
    fi_2: FI                 // The inputs into the second entity.
  )

  ghost predicate CESummaryValid(s: CESummary)
  {
    && ConnectEntitiesRequirements(s.c, s.conn)
    && FIValid(s.fi, s.conn.scuf_ab.mp.inputs, s.conn.scuf_ab.mp.state)
    && ConnectEntitiesRequirementsBonus(s.c, s.conn, s.fi)
    && (s.new_c == ConnectEntitiesImpl(s.c, s.conn))
    && (s.fi_1 == s.conn.fi2fia(s.fi))
    && (s.fi_2 == s.conn.fi2fib(s.fi))
  }

  function MakeCESSummary(c: Circuit, conn: ScufConnection, fi: FI): (s: CESummary)
    requires ConnectEntitiesRequirements(c, conn)
    requires FIValid(fi, conn.scuf_ab.mp.inputs, conn.scuf_ab.mp.state)
    ensures CESummaryValid(s)
  {
    ConnectEntitiesRequirementsUpgrade(c, conn, fi);
    var new_c := ConnectEntitiesImpl(c,conn);
    var fi_1 := conn.fi2fia(fi);
    var fi_2 := conn.fi2fib(fi);
    CESummary(c, conn, fi, new_c, fi_1, fi_2)
  }

  // Things that are easy to prove but we can give them in the requirements so the ensure
  // statements can depend on them.
  ghost predicate ConnectEntitiesRequirementsPlus(c: Circuit, conn: ScufConnection, fi: FI)
  {
    // These actually are requirementss.
    && ConnectEntitiesRequirements(c, conn)
    && FIValid(fi, conn.scuf_ab.mp.inputs, conn.scuf_ab.mp.state)
    // These are all easily proven consequences of the requirements that are easier to just
    // pass in as requirements.
    && ConnectEntitiesRequirementsBonus(c, conn, fi)
  }
  
  ghost predicate ConnectEntitiesRequirementsBonus(c: Circuit, conn: ScufConnection, fi: FI)
    requires ConnectEntitiesRequirements(c, conn)
    requires FIValid(fi, conn.scuf_ab.mp.inputs, conn.scuf_ab.mp.state)
  {
    //&& ConnectMapFunctionRequirement(e1.mp, e2.mp, e12.mp, conn)
    && var fi_1 := conn.fi2fia(fi);
    && var fi_2 := conn.fi2fib(fi);
    && var new_c := ConnectEntitiesImpl(c, conn);
    && FICircuitValid(new_c, fi)
    && FICircuitValid(new_c, fi_1)
    && FICircuitValid(new_c, fi_2)
    && ConnectCircuitRequirements(c, conn.GetConnection())
    && conn.scuf_a.Valid(new_c)
    && conn.scuf_b.Valid(new_c)
    //&& ConnectMapFunctionRequirement(e1.mp, e2.mp, connection)
  }

  lemma ConnectEntitiesRequirementsUpgrade(c: Circuit, conn: ScufConnection, fi: FI)
    requires ConnectEntitiesRequirements(c, conn)
    requires FIValid(fi, conn.scuf_ab.mp.inputs, conn.scuf_ab.mp.state)
    ensures ConnectEntitiesRequirementsBonus(c, conn, fi)
  {
    ConnectEntitiesReqToFICircuitValid(c, conn, fi);
    ConnectEntitiesEntitiesStillValid(c, conn);
    //ConnectEntitiesReqToConnectMapFunctionReq(c, e1, e2, e12, conn);
  }

  lemma ConnectEntitiesReqToFICircuitValid(c: Circuit, conn: ScufConnection, fi: FI)
    requires ConnectEntitiesRequirements(c, conn)
    requires FIValid(fi, conn.scuf_ab.mp.inputs, conn.scuf_ab.mp.state)
    ensures
      && var new_c := ConnectEntitiesImpl(c, conn);
      //&& ConnectMapFunctionRequirement(e1.mp, e2.mp, connection)
      && var fi_1 := conn.fi2fia(fi);
      && var fi_2 := conn.fi2fib(fi);
      && FICircuitValid(new_c, fi)
      && FICircuitValid(new_c, fi_1)
      && FICircuitValid(new_c, fi_2)
  {
    var e1 := conn.scuf_a;
    var e2 := conn.scuf_b;
    var e12 := conn.scuf_ab;
    //ConnectEntitiesReqToConnectMapFunctionReq(c, e1, e2, connection);
    assert e1.Valid(c);
    assert e2.Valid(c);
    var new_c := ConnectEntitiesImpl(c, conn);
    ConnectEntitiesSomewhatValid(c, conn);
    assert e12.SomewhatValid(new_c);
    ScufValidFiValidToFICircuitValid(new_c, e12, fi);
    assert FICircuitValid(new_c, fi);
    var fi_1 := conn.fi2fia(fi);
    var fi_2 := conn.fi2fib(fi);
    var connection := conn.GetConnection();
    assert ConnectionValid(c, e1, e2, connection) by {
      GetConnectionValid(c, conn);
    }
    assert fi_1.inputs.Keys <= fi.inputs.Keys;
    assert fi_2.inputs.Keys <= fi.inputs.Keys + connection.Keys;
    assert fi_1.state.Keys <= fi.state.Keys;
    assert fi_2.state.Keys <= fi.state.Keys;
    reveal FICircuitValid();
    reveal ConnectionValid();
    ConnectionKeysINPs(c, e1, e2, connection);
    assert forall np :: np in connection.Keys ==> INPValid(c, np) by {
      reveal INPsValid();
    }
    assert c.NodeKind == new_c.NodeKind by {
      reveal ConnectEntitiesImpl();
    }
    assert forall np :: np in connection.Keys ==> INPValid(new_c, np);
  }

  lemma Knowns2FromKnowns1(s: CESummary, np: NP)
    requires CESummaryValid(s)
    requires np in s.conn.scuf_b.mp.inputs 
    requires np !in s.conn.scuf_ab.mp.inputs 
    ensures
      && np in s.new_c.PortSource
      && var onp := s.new_c.PortSource[np];
      && (np in s.fi_2.inputs)
      && (s.conn.scuf_a.f.requires(s.fi_1))
      && (onp in s.conn.scuf_a.f(s.fi_1).outputs)
      && (s.fi_2.inputs[np] == s.conn.scuf_a.f(s.fi_1).outputs[onp])
  {
    var e1 := s.conn.scuf_a;
    var e2 := s.conn.scuf_b;
    var e12 := s.conn.scuf_ab;
    ConnectCircuitReqFromConnectEntitiesReq(s.c, s.conn);
    var connection := s.conn.GetConnection();
    assert s.new_c == ConnectCircuit(s.c, connection) by {
      reveal ConnectEntitiesImpl();
    }
    assert np in connection by {
      reveal Seq.ToSet();
      assert connection.Keys <= Seq.ToSet(e2.mp.inputs);
      assert connection.Keys == Seq.ToSet(e2.mp.inputs) - Seq.ToSet(e12.mp.inputs);
    }
    var onp := connection[np];
    assert onp == s.new_c.PortSource[np] by {
      reveal ConnectEntitiesImpl();
      reveal ConnectionValid();
    }
    assert np !in e1.mp.inputs by {
      reveal ConnectionValid();
      reveal Seq.ToSet();
      ConnectionKeysInE2(s.c, e1, e2, connection);
      FInputsInSc(s.c, e1);
      reveal NPsInSc();
      SetsNoIntersectionSymm(e1.sc, e2.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    assert np !in s.fi.inputs;
    assert np in s.fi_2.inputs;

    assert 
      && (e1.f.requires(s.fi_1))
      && (onp in e1.f(s.fi_1).outputs) by {
        //reveal MapFunction.Valid();
    }

    assert (s.fi_2.inputs[np] == e1.f(s.fi_1).outputs[onp]) by {
      assert s.fi_2 == s.conn.fi2fib(s.fi);
      assert s.fi_1 == s.conn.fi2fia(s.fi);
      var si := e12.mp.fi2si(s.fi);
      e12.mp.fi2si2fi(s.fi);
      assert s.fi == e12.mp.si2fi(si);
      var si_1 := s.conn.si2sia(si);
      assert SIValid(si_1, e1.mp.inputs, e1.mp.state);
      reveal UpdateFunction.Valid();
      var so_1 := e1.uf.sf(si_1);
      var fo_1 := e1.mp.so2fo(so_1);
      var si_2 := s.conn.si2sib(si);
      assert e2.mp.si2fi(si_2) == s.fi_2;
      //reveal e1.mp.Valid();
      reveal Seq.ToSet();
      reveal MapMatchesSeqs();
      var si_2_inputs := s.conn.abiao2bi.MapSeq(si.inputs, so_1.outputs);
      assert np in e2.mp.inputs;
      assert onp in e1.mp.outputs;
      var index_src := Seq.IndexOf(e2.mp.inputs, np);
      var index_snk := Seq.IndexOf(e1.mp.outputs, onp);
      reveal s.conn.ConnectionCorrect();
      assert s.conn.abiao2bi.conn[index_src] == (true, index_snk);
      assert si_2.inputs[index_src] == so_1.outputs[index_snk];
      assert si_2.inputs[index_src] == s.fi_2.inputs[np];
      assert so_1.outputs[index_snk] == fo_1.outputs[onp];
      calc {
        e1.f(s.fi_1);
        e1.f(s.fi_1);
        e1.mp.so2fo(e1.uf.sf(e1.mp.fi2si(s.fi_1)));
        {
          assert s.fi_1 == e1.mp.si2fi(si_1);
          assert si_1 == e1.mp.fi2si(s.fi_1);
        }
        e1.mp.so2fo(e1.uf.sf(si_1));
        e1.mp.so2fo(so_1);
        fo_1;
      }
      assert fo_1 == e1.f(s.fi_1);
    }
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

  lemma EvaluateONPComposed1Helper(s: CESummary, prepath: seq<NP>, path: seq<NP>, inp: NP)
    requires CESummaryValid(s)
    requires PathInSubcircuit(prepath, s.conn.scuf_b.sc)
    requires PathInSubcircuit(path, s.conn.scuf_a.sc)
    requires inp !in path
    requires inp.n in s.conn.scuf_a.sc
    requires INPValid(s.new_c, inp)
    requires EvaluateONPUnaryBinaryRequirements(s.new_c, path, s.fi)
    requires EvaluateONPUnaryBinaryRequirements(s.new_c, prepath + path, s.fi)

    ensures forall np :: np in s.conn.scuf_a.mp.inputs ==> np in s.fi.inputs
    ensures
      && var new_path := path + [inp];
      && Seq.HasNoDuplicates(new_path)
      && Seq.HasNoDuplicates(prepath + new_path)
      && PathValid(s.new_c, new_path)
      && PathValid(s.new_c, prepath + new_path)
      && EvaluateINPInner(s.new_c, new_path, s.fi) == EvaluateINPInner(s.new_c, new_path, s.fi_1)
      && Simpl(EvaluateINPInner(s.new_c, new_path, s.fi)) == Simpl(EvaluateINPInner(s.new_c, prepath+new_path, s.fi))
    decreases
      |NodesNotInPath(s.new_c, prepath + path)|, 3
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    StillHasNoDuplicates(path, inp);
    assert inp !in prepath by {
      reveal PathInSubcircuit();
      InThisNotInThat(inp.n, e1.sc, e2.sc);
    }
    StillHasNoDuplicates(prepath + path, inp);
    AppendPathValid(new_c, path, inp);
    AppendPathValid(new_c, prepath + path, inp);
    assert forall np :: np in e1.mp.inputs ==> np in fi.inputs by {
      reveal Seq.ToSet();
    }
    var new_path := path + [inp];
    NodesNotInPathDecreases(new_c, prepath + path, inp);
    assert PathInSubcircuit(new_path, e1.sc) by {reveal PathInSubcircuit();}
    assert (prepath + path) + [inp] == prepath + (path + [inp]);
    assert Seq.Last(prepath + new_path) == inp;
    EvaluateINPInnerComposed1(s, prepath, new_path);
    assert EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_1);
    assert Simpl(EvaluateINPInner(new_c, new_path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+new_path, fi));
  }

  lemma EvaluateONPBinaryComposed1(s: CESummary, prepath: seq<NP>, path: seq<NP>)
    requires CESummaryValid(s)
    requires PathInSubcircuit(prepath, s.conn.scuf_b.sc)
    requires PathInSubcircuit(path, s.conn.scuf_a.sc)
    requires EvaluateONPBinaryRequirements(s.new_c, path, s.fi)
    requires EvaluateONPBinaryRequirements(s.new_c, prepath + path, s.fi)
    ensures forall np :: np in s.conn.scuf_a.mp.inputs ==> np in s.fi.inputs
    ensures EvaluateONPBinary(s.new_c, path, s.fi) == EvaluateONPBinary(s.new_c, path, s.fi_1)
    ensures Simpl(EvaluateONPBinary(s.new_c, path, s.fi)) == Simpl(EvaluateONPBinary(s.new_c, prepath+path, s.fi))
    decreases |NodesNotInPath(s.new_c, prepath + path)|, 4
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    assert forall np :: np in e1.mp.inputs ==> np in fi.inputs by {
      reveal Seq.ToSet();
    }
    var head := Seq.Last(path);
    assert head == Seq.Last(prepath + path);
    assert head.n in e1.sc by {reveal PathInSubcircuit();}
    assert NodeValid(new_c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    assert INPValid(new_c, inp_0) && INPValid(new_c, inp_1) by {reveal Circuit.Valid();}
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    NPNotInPathHelper(inp_1, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
      assert (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_1));
      assert (Simpl(EvaluateONPBinary(new_c, path, fi)) == Simpl(EvaluateONPBinary(new_c, prepath+path, fi)));
    } else if inp_1 in path {
      assert (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_1));
      assert (Simpl(EvaluateONPBinary(new_c, path, fi)) == Simpl(EvaluateONPBinary(new_c, prepath+path, fi)));
    } else {
      EvaluateONPComposed1Helper(s, prepath, path, inp_0);
      EvaluateONPComposed1Helper(s, prepath, path, inp_1);

      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert prepath + (path + [inp_1]) == (prepath + path) + [inp_1];

      assert (Simpl(EvaluateONPBinary(new_c, path, fi)) == Simpl(EvaluateONPBinary(new_c, prepath+path, fi)));
    }
  }

  lemma EvaluateONPComposed2Helper(s: CESummary, path: seq<NP>, inp: NP)
    requires CESummaryValid(s)
    requires PathInSubcircuit(path, s.conn.scuf_b.sc)
    requires EvaluateONPUnaryBinaryRequirements(s.new_c, path, s.fi)
    requires INPValid(s.new_c, inp)
    requires inp !in path
    requires inp.n in s.conn.scuf_b.sc
    ensures
      var new_path := path + [inp];
      Seq.HasNoDuplicates(new_path) &&
      PathValid(s.new_c, new_path) &&
      (EvaluateINPInner(s.new_c, new_path, s.fi) == EvaluateINPInner(s.new_c, new_path, s.fi_2))
    decreases |NodesNotInPath(s.new_c, path)|, 4
  {
    StillHasNoDuplicates(path, inp);
    AppendPathValid(s.new_c, path, inp);
    var new_path := path + [inp];
    NodesNotInPathDecreases(s.new_c, path, inp);
    reveal PathInSubcircuit();
    EvaluateINPInnerComposed2(s, new_path);
    assert (EvaluateINPInner(s.new_c, new_path, s.fi) == EvaluateINPInner(s.new_c, new_path, s.fi_2));
  }

  lemma EvaluateONPBinaryComposed2(s: CESummary, path: seq<NP>)
    requires CESummaryValid(s)
    requires PathInSubcircuit(path, s.conn.scuf_b.sc)
    requires EvaluateONPBinaryRequirements(s.new_c, path, s.fi)
    ensures
      (Seq.Last(path).n !in s.fi_2.state) &&
      (EvaluateONPBinary(s.new_c, path, s.fi) == EvaluateONPBinary(s.new_c, path, s.fi_2))
    decreases |NodesNotInPath(s.new_c, path)|, 5
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    var head := Seq.Last(path);
    assert head.n in e2.sc by {
      reveal PathInSubcircuit();
    }
    var nk := new_c.NodeKind[head.n];
    assert NodeValid(new_c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    assert INPValid(new_c, inp_0) && INPValid(new_c, inp_1) by {reveal Circuit.Valid();}
    assert head.n !in fi_2.state;
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
          EvaluateONPComposed2Helper(s, path, inp_0);
        }
      assert 
        var new_path := path + [inp_1];
        && Seq.HasNoDuplicates(new_path)
        && PathValid(new_c, new_path)
        && (EvaluateINPInner(new_c, new_path, fi) == EvaluateINPInner(new_c, new_path, fi_2)) by {
          EvaluateONPComposed2Helper(s, path, inp_1);
        }
      assert EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_2);
    }
    assert
      (EvaluateONPBinary(new_c, path, fi) == EvaluateONPBinary(new_c, path, fi_2));
  }

  lemma EvaluateONPUnaryComposed1(s: CESummary, prepath: seq<NP>, path: seq<NP>)
    requires CESummaryValid(s)
    requires PathInSubcircuit(prepath, s.conn.scuf_b.sc)
    requires PathInSubcircuit(path, s.conn.scuf_a.sc)
    requires EvaluateONPUnaryRequirements(s.new_c, path, s.fi)
    requires EvaluateONPUnaryRequirements(s.new_c, prepath+path, s.fi)
    ensures
      && (forall np :: np in s.conn.scuf_a.mp.inputs ==> np in s.fi.inputs)
      && (EvaluateONPUnary(s.new_c, path, s.fi) == EvaluateONPUnary(s.new_c, path, s.fi_1))
      && (Simpl(EvaluateONPUnary(s.new_c, path, s.fi)) == Simpl(EvaluateONPUnary(s.new_c, prepath+path, s.fi)))
    decreases |NodesNotInPath(s.new_c, prepath + path)|, 5
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    assert forall np :: np in e1.mp.inputs ==> np in fi.inputs by {
      reveal Seq.ToSet();
    }
    var head := Seq.Last(path);
    assert head == Seq.Last(prepath + path);
    assert head.n in e1.sc by {reveal PathInSubcircuit();}
    assert NodeValid(new_c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    assert INPValid(new_c, inp_0) by {reveal Circuit.Valid();}
    NPNotInPathHelper(inp_0, e1.sc, e2.sc, prepath, path);
    if inp_0 in path {
      assert (EvaluateONPUnary(new_c, path, fi) == EvaluateONPUnary(new_c, path, fi_1));
      assert (Simpl(EvaluateONPUnary(new_c, path, fi)) == Simpl(EvaluateONPUnary(new_c, prepath+path, fi)));
    } else {
      EvaluateONPComposed1Helper(s, prepath, path, inp_0);
      assert prepath + (path + [inp_0]) == (prepath + path) + [inp_0];
      assert (Simpl(EvaluateONPUnary(new_c, path, fi)) == Simpl(EvaluateONPUnary(new_c, prepath+path, fi)));
    }
  }

  lemma EvaluateONPUnaryComposed2(s: CESummary, path: seq<NP>)
    requires CESummaryValid(s)
    requires PathInSubcircuit(path, s.conn.scuf_b.sc)
    requires EvaluateONPUnaryRequirements(s.new_c, path, s.fi)
    ensures
      && (Seq.Last(path) !in s.fi_2.inputs)
      && (EvaluateONPUnary(s.new_c, path, s.fi) == EvaluateONPUnary(s.new_c, path, s.fi_2))
    decreases |NodesNotInPath(s.new_c, path)|, 4
  {
    var head := Seq.Last(path);
    assert head !in s.fi_2.inputs by {
      reveal FICircuitValid();
    }
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(s.new_c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      assert PathInSubcircuit(path + [inp_0], s.conn.scuf_b.sc) by {
        reveal PathInSubcircuit();
      }
      EvaluateINPInnerComposed2(s, path + [inp_0]);
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

  lemma EvaluateINPInnerComposed1(s: CESummary, prepath: seq<NP>, path: seq<NP>)
    requires CESummaryValid(s)
    requires PathInSubcircuit(path, s.conn.scuf_a.sc)
    requires PathInSubcircuit(prepath, s.conn.scuf_b.sc)
    requires EvaluateINPInnerRequirements(s.new_c, path, s.fi)
    requires EvaluateINPInnerRequirements(s.new_c, prepath + path, s.fi)
    ensures EvaluateINPInner(s.new_c, path, s.fi) == EvaluateINPInner(s.new_c, path, s.fi_1)
    ensures Simpl(EvaluateINPInner(s.new_c, path, s.fi)) == Simpl(EvaluateINPInner(s.new_c, prepath+path, s.fi))
    decreases |NodesNotInPath(s.new_c, prepath + path)|, 2
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b; var e12 := s.conn.scuf_ab;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    var np := Seq.Last(path);
    assert np.n in e1.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;

    assert (np in fi.inputs) == (np in fi_1.inputs) by {
      assert fi.inputs.Keys == Seq.ToSet(e12.mp.inputs);
      InThisNotInThat(np.n, e1.sc, e2.sc);
      FInputsInSc(new_c, e2);
      reveal NPsInSc();
      reveal Seq.ToSet();
      assert np !in e2.mp.inputs;
    }

    if np in fi.inputs {
      assert np in fi_1.inputs;
      s.conn.fi2fiaInfo(fi);
      assert fi.inputs[np] == fi_1.inputs[np];
      assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
      assert Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi));
    } else {
      if np in new_c.PortSource {
        var onp := new_c.PortSource[np];
        assert ONPValid(new_c, onp) by {
          reveal Circuit.Valid();
        }
        assert onp.n in e1.sc by {
          reveal Scuf.SomewhatValid();
          reveal ConnInputs();
        }
        if onp in path {
          assert EvaluateINPInner(new_c, path, fi) == EvalError({}, {path + [onp]});
          assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
          assert Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi));
        } else {
          assert && EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1)
                 && Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi)) by {
            assert NPValid(new_c, onp) by {
              reveal Circuit.Valid();
            }
            NPNotInPathHelper(onp, e1.sc, e2.sc, prepath, path);
            StillHasNoDuplicates(path, onp);
            StillHasNoDuplicates(prepath + path, onp);
            AppendPathValid(new_c, path, onp);
            AppendPathValid(new_c, prepath + path, onp);
            assert PathInSubcircuit(path + [onp], e1.sc) by {
              reveal PathInSubcircuit();
            }
            assert (prepath + path) + [onp] == prepath + (path + [onp]);
            NodesNotInPathDecreases(new_c, prepath+path, onp);
            assert EvaluateONPInnerRequirements(new_c, prepath + (path +[onp]), fi) by {
              assert Seq.HasNoDuplicates(prepath + (path + [onp]));
            }
            assert EvaluateONPInnerRequirements(new_c, path + [onp], fi);
            EvaluateONPInnerComposed1(s, prepath, path + [onp]);
          }
        }
      } else {
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
        assert Simpl(EvaluateINPInner(new_c, path, fi)) == Simpl(EvaluateINPInner(new_c, prepath+path, fi));
      }
    }
  }

  lemma EvaluateINPInnerComposed2(s: CESummary, path: seq<NP>)
    requires CESummaryValid(s)
    requires PathInSubcircuit(path, s.conn.scuf_b.sc)
    requires EvaluateINPInnerRequirements(s.new_c, path, s.fi)
    ensures
      && (EvaluateINPInner(s.new_c, path, s.fi) == EvaluateINPInner(s.new_c, path, s.fi_2))
    decreases |NodesNotInPath(s.new_c, path)|, 2
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    assert forall np :: np in e1.mp.inputs ==> np in fi.inputs by {
      reveal Seq.ToSet();
    }
    var np := Seq.Last(path);
    assert np.n in e2.sc by {
      reveal PathInSubcircuit();
    }
    var tail := Seq.DropLast(path);
    assert Seq.HasNoDuplicates(path);
    HasNoDuplicatesMeansHeadNotInTail(path);
    assert np !in tail;
    assert fi.inputs.Keys == Seq.ToSet(e1.mp.inputs) + (Seq.ToSet(e2.mp.inputs) - connection.Keys);
    assert np !in Seq.ToSet(e1.mp.inputs) by {
      reveal Seq.ToSet();
      FInputsInSc(c, e1);
      reveal NPsInSc();
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    if np in Seq.ToSet(e2.mp.inputs) {
      assert np in fi_2.inputs;
      if np in fi.inputs {
        s.conn.fi2fibInfo(fi);
        assert fi.inputs[np] == fi_2.inputs[np];
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
      } else {
        assert np in connection.Keys;
        assert (np in new_c.PortSource) by {
          assert np in connection;
          reveal ConnectEntitiesImpl();
        }
        var onp := new_c.PortSource[np];
        assert onp.n in e1.sc && onp in e1.mp.outputs by {
          reveal ConnectEntitiesImpl();
          reveal ConnectionValid();
          assert onp in connection.Values;
          FOutputsInSc(new_c, e1);
          reveal NPsInSc();
          reveal Seq.ToSet();
        }
        assert ONPValid(new_c, onp) by {
          reveal Circuit.Valid();
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
        EvaluateONPInnerComposed1(s, path, [onp]);
        assert (EvaluateONPInner(new_c, [onp], fi) == EvaluateONPInner(new_c, [onp], fi_1));
        assert (Simpl(EvaluateONPInner(new_c, path + [onp], fi)) ==
                Simpl(EvaluateONPInner(new_c, [onp], fi)));
        assert EvaluateINPInner(new_c, path, fi) == EvaluateONPInner(new_c, path + [onp], fi);
        assert (e1.f.requires(fi_1)) && (e1.f(fi_1).outputs.Keys == Seq.ToSet(e1.mp.outputs)) &&
               (onp in e1.f(fi_1).outputs) &&
               (fi_2.inputs[np] == e1.f(fi_1).outputs[onp]) by {
          //reveal MapFunction.Valid();
          reveal Seq.ToSet();
          reveal MapMatchesSeqs();
          Knowns2FromKnowns1(s, np);
          assert s.fi_2 == fi_2;
          assert s.fi_1 == fi_1;
          assert fi_2.inputs[np] == e1.f(fi_1).outputs[onp];
        }
        assert EvaluateONPInner(new_c, [onp], fi_1) == EvalOk(MFLookupOutput(e1, fi_1, onp)) by {
          assert e1.Valid(new_c);
          reveal Seq.ToSet();
          reveal Scuf.EvaluatesCorrectly();
        }
        assert EvaluateINPInner(new_c, path, fi_2) == EvalOk(fi_2.inputs[np]);
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateONPInner(new_c, [onp], fi_1);
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateONPInner(new_c, [onp], fi);
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateONPInner(new_c, path + [onp], fi);
        assert EvaluateINPInner(new_c, path, fi_2) == EvaluateINPInner(new_c, path, fi);
      }
    } else {
      assert np !in Seq.ToSet(e2.mp.inputs);
      assert fi_2.inputs.Keys == Seq.ToSet(e2.mp.inputs);
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
          reveal Circuit.Valid();
        }
        assert onp.n in e2.sc by {
          reveal Seq.ToSet();
          assert np !in e2.mp.inputs;
          reveal Scuf.SomewhatValid();
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
          EvaluateONPInnerComposed2(s, path + [onp]);
          assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
        }
      } else {
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
      }
    }
  }

  lemma EvaluateONPInnerComposed1(s: CESummary, prepath: seq<NP>, path: seq<NP>)
    requires CESummaryValid(s)
    requires EvaluateONPInnerRequirements(s.new_c, prepath + path, s.fi)
    requires EvaluateONPInnerRequirements(s.new_c, path, s.fi)
    requires PathInSubcircuit(path, s.conn.scuf_a.sc)
    requires PathInSubcircuit(prepath, s.conn.scuf_b.sc)
    ensures
      && (forall np :: np in s.conn.scuf_a.mp.inputs ==> np in s.fi.inputs)
      && (EvaluateONPInner(s.new_c, path, s.fi) == EvaluateONPInner(s.new_c, path, s.fi_1))
      && (Simpl(EvaluateONPInner(s.new_c, prepath + path, s.fi)) == Simpl(EvaluateONPInner(s.new_c, path, s.fi)))
    decreases |NodesNotInPath(s.new_c, prepath + path)|, 6
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();
    var np := Seq.Last(path);

    assert (np.n in e1.sc) && (np.n !in e2.sc) by {
      reveal PathInSubcircuit();
      InThisNotInThat(np.n, e1.sc, e2.sc);
    }
    Seq.LemmaAppendLast(prepath, path);
    assert np == Seq.Last(prepath + path);

    assert (np.n in fi.state) == (np.n in fi_1.state) by {
      reveal Seq.ToSet();
      assert np.n !in e2.mp.state by {
        FInputsInSc(new_c, e2);
        reveal NPsInSc();
      }
    }

    if np.n in fi.state {
      s.conn.fi2fiaInfo(fi);
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
      assert Simpl(EvaluateONPInner(new_c, prepath + path, fi)) == Simpl(EvaluateONPInner(new_c, path, fi));
    } else {
      assert np.n in new_c.NodeKind by {
        reveal Circuit.Valid();
      }
      var nk := new_c.NodeKind[np.n];
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed1(s, prepath, path);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed1(s, prepath, path);
        }
        case CInv() => {
          EvaluateONPUnaryComposed1(s, prepath, path);
        }
        case CIden() => {
          EvaluateONPUnaryComposed1(s, prepath, path);
        }
        case CConst(b) => {}
        case CSeq() => {}
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
      assert Simpl(EvaluateONPInner(new_c, prepath + path, fi)) == Simpl(EvaluateONPInner(new_c, path, fi));
    }
    assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
    assert Simpl(EvaluateONPInner(new_c, prepath + path, fi)) == Simpl(EvaluateONPInner(new_c, path, fi));
    reveal Seq.ToSet();
  }

  lemma EvaluateONPInnerComposed2(s: CESummary, path: seq<NP>)
    requires
      && CESummaryValid(s)
      && EvaluateONPInnerRequirements(s.new_c, path, s.fi)
      && PathInSubcircuit(path, s.conn.scuf_b.sc)
    ensures
      && var np := Seq.Last(path);
      && (EvaluateONPInner(s.new_c, path, s.fi) == EvaluateONPInner(s.new_c, path, s.fi_2))
    decreases
      |NodesNotInPath(s.new_c, path)|, 6
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();
    var np := Seq.Last(path);

    assert (np.n in e2.sc) && (np.n !in e1.sc) by {
      reveal PathInSubcircuit();
      SetsNoIntersectionSymm(e2.sc, e1.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
    }
    assert ONPValid(new_c, np);
    assert (np.n in fi.state) == (np.n in fi_2.state) by {
      assert np.n !in e1.mp.state by {
        FInputsInSc(new_c, e1);
        reveal NPsInSc();
      }
      reveal Seq.ToSet();
    }
    if np.n in fi.state {
      assert np.n in fi_2.state;
      s.conn.fi2fibInfo(fi);
      assert fi.state[np.n] == fi_2.state[np.n];
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
    } else {
      assert np !in StateONPs(e1.mp.state + e2.mp.state) by {
        reveal Seq.ToSet();
      }
      var nk := new_c.NodeKind[np.n];
      assert !nk.CSeq? by {
        if nk.CSeq? {
          assert np.n in AllSeq(new_c, e2.sc) by {
            reveal AllSeq();
          }
          assert np.n in AllSeq(new_c, e2.sc);
          assert np in StateONPs(e2.mp.state) by {
            reveal AllSeq();
            reveal Scuf.SomewhatValid();
          }
          assert false;
        }
      }
      match nk
        case CXor() => {
          EvaluateONPBinaryComposed2(s, path);
          assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
        case CAnd() => {
          EvaluateONPBinaryComposed2(s, path);
          assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
        case CInv() => {
          EvaluateONPUnaryComposed2(s, path);
          assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
        case CIden() => {
          EvaluateONPUnaryComposed2(s, path);
          assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
        case CConst(b) => {
          assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
        }
      assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
    }
  }

  lemma EvaluateConnectEntitiesInner(s: CESummary, np: NP)
    requires
      && CESummaryValid(s)
      && NPValid(s.new_c, np)
      && (np in s.conn.scuf_a.mp.outputs || np in s.conn.scuf_b.mp.outputs || np in StateINPs(s.conn.scuf_a.mp.state + s.conn.scuf_b.mp.state))
    ensures
      && (np.n in s.conn.scuf_a.sc ==> Evaluate(s.new_c, np, s.fi_1) == Evaluate(s.new_c, np, s.fi))
      && (np.n in s.conn.scuf_b.sc ==> Evaluate(s.new_c, np, s.fi_2) == Evaluate(s.new_c, np, s.fi))
  {
    var c := s.c; var new_c := s.new_c;
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    var prepath: seq<NP> := [];
    var path := [np];
    assert np == Seq.Last(path);
    assert PathValid(new_c, path) && PathValid(new_c, prepath + path) by {
      reveal PathValid();
    }

    LengthOneNoDuplicates(path);
    LengthOneNoDuplicates(prepath + path);
    if np in e1.mp.outputs || np in StateINPs(e1.mp.state) {
      assert np.n in e1.sc by {
        FOutputsInSc(s.c, e1);
        reveal Seq.ToSet();
        reveal NPsInSc();
      }
      InThisNotInThat(np.n, e1.sc, e2.sc);
      assert PathInSubcircuit(prepath, e2.sc) by { reveal PathInSubcircuit(); }
      assert PathInSubcircuit(path, e1.sc) by { reveal PathInSubcircuit(); }
    } else {
      assert np in e2.mp.outputs || np in StateINPs(e2.mp.state);
      assert np.n in e2.sc by {
        FOutputsInSc(s.c, e2);
        reveal Seq.ToSet();
        reveal NPsInSc();
      }
      SetsNoIntersectionSymm(e2.sc, e1.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
      assert PathInSubcircuit(path, e2.sc) by { reveal PathInSubcircuit(); }
    }

    if ONPValid(new_c, np) {
      if np in e1.mp.outputs || np in StateINPs(e1.mp.state) {
        EvaluateONPInnerComposed1(s, prepath, path);
        assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_1);
      } else {
        EvaluateONPInnerComposed2(s, path);
        assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_2);
      }
    } else {
      if np in e1.mp.outputs || np in StateINPs(e1.mp.state) {
        EvaluateINPInnerComposed1(s, prepath, path);
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_1);
      } else {
        EvaluateINPInnerComposed2(s, path);
        assert EvaluateINPInner(new_c, path, fi) == EvaluateINPInner(new_c, path, fi_2);
      }
    }
    if np in e1.mp.outputs || np in StateINPs(e1.mp.state) {
      assert Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_1);
    } else {
      assert Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_2);
    }
  }

  lemma EvaluateConnectEntities(s: CESummary, np: NP)
    requires
      && CESummaryValid(s)
      && NPValid(s.new_c, np)
      && (np in s.conn.scuf_ab.mp.outputs || np in StateINPs(s.conn.scuf_ab.mp.state))
    ensures
      (Evaluate(s.new_c, np, s.fi) == EvalOk(MFLookup(s.conn.scuf_ab, s.fi, np)))
  {
    var e1 := s.conn.scuf_a; var e2 := s.conn.scuf_b;
    var new_c := s.new_c; var e12 := s.conn.scuf_ab;
    var fi := s.fi; var fi_1 := s.fi_1; var fi_2 := s.fi_2;
    var connection := s.conn.GetConnection();

    assert np in e12.mp.outputs ==> (np in s.conn.scuf_a.mp.outputs || np in e2.mp.outputs) by {
      assert Seq.ToSet(e12.mp.outputs) <= Seq.ToSet(e1.mp.outputs) + Seq.ToSet(e2.mp.outputs);
      if np in e12.mp.outputs {
        reveal Seq.ToSet();
        assert np in Seq.ToSet(e12.mp.outputs);
        assert np in Seq.ToSet(e1.mp.outputs) + Seq.ToSet(e2.mp.outputs);
        assert np in e1.mp.outputs || np in e2.mp.outputs;
      }
    }

    //e1.mp.NotInBothOutputsAndStateINPs(np);
    //e2.mp.NotInBothOutputsAndStateINPs(np);
    //e12.mp.NotInBothOutputsAndStateINPs(np);

    assert np in StateINPs(e12.mp.state) ==> np in StateINPs(e1.mp.state + e2.mp.state) by {
      assert Seq.ToSet(e12.mp.state) == Seq.ToSet(e1.mp.state) + Seq.ToSet(e2.mp.state);
      reveal Seq.ToSet();
      if np in StateINPs(e12.mp.state) {
        assert np.n in e12.mp.state;
        assert np.n in Seq.ToSet(e12.mp.state);
        assert np.n in Seq.ToSet(e1.mp.state) || np.n in Seq.ToSet(e2.mp.state);
        assert np.n in e1.mp.state || np.n in e2.mp.state;
        assert np.n in e1.mp.state + e2.mp.state;
      }
    }
    EvaluateConnectEntitiesInner(s, np);

    assert (Seq.ToSet(e1.mp.outputs) !! StateINPs(e2.mp.state)) && (Seq.ToSet(e2.mp.outputs) !! StateINPs(e1.mp.state)) by {
      FOutputsInSc(s.c, e1);
      FOutputsInSc(s.c, e2);
      assert e1.sc !! e2.sc;
      reveal NPsInSc();
    }
    if np in e1.mp.outputs || np in e2.mp.outputs {
      assert np in e12.mp.outputs by {
        reveal Seq.ToSet();
        assert SeqsNoIntersection(e2.mp.outputs, StateINPsSeq(e2.mp.state));
        assert SeqsNoIntersection(e1.mp.outputs, StateINPsSeq(e1.mp.state));
        StateINPsSeqSame(e2.mp.state);
        StateINPsSeqSame(e1.mp.state);
        assert np !in StateINPs(e2.mp.state);
        assert np !in StateINPs(e1.mp.state);
      }
    }
    if np in StateINPs(e1.mp.state) || np in StateINPs(e2.mp.state) {
      assert np in StateINPs(e12.mp.state) by {
        reveal Seq.ToSet();
        StateINPsSeqSame(e2.mp.state);
        StateINPsSeqSame(e1.mp.state);
        assert np !in e1.mp.outputs;
        assert np !in e2.mp.outputs;
      }
    }

    if np in e1.mp.outputs || np in StateINPs(e1.mp.state) {
      assert np in Seq.ToSet(e1.mp.outputs) || np in StateINPs(e1.mp.state) by {
        reveal Seq.ToSet();
      }
      assert np.n in e1.sc by {
        FOutputsInSc(s.new_c, e1);
        reveal NPsInSc();
        reveal Seq.ToSet();
      }
      calc {
        Evaluate(new_c, np, fi);
        Evaluate(new_c, np, fi_1);
        {
          assert e1.Valid(new_c);
          reveal Scuf.EvaluatesCorrectly();
        }
        EvalOk(MFLookup(e1, fi_1, np));
        {
          reveal Seq.ToSet();
          if np in e1.mp.outputs {
            s.conn.MFABMFAConsistentOutputs(fi, np);
          } else {
            s.conn.MFABMFAConsistentState(fi, np);
          }
        }
        EvalOk(MFLookup(e12, fi, np));
      }
    } else {
      assert np in e2.mp.outputs || np in StateINPs(e2.mp.state);
      assert np.n in e2.sc by {
        FOutputsInSc(s.new_c, e2);
        reveal NPsInSc();
        reveal Seq.ToSet();
      }
      calc {
        Evaluate(new_c, np, fi);
        Evaluate(new_c, np, fi_2);
        {
          assert e2.Valid(new_c);
          reveal Seq.ToSet();
          reveal Scuf.EvaluatesCorrectly();
        }
        EvalOk(MFLookup(e2, fi_2, np));
        {
          reveal Seq.ToSet();
          if np in e2.mp.outputs {
            s.conn.MFABMFBConsistentOutputs(fi, np);
          } else {
            s.conn.MFABMFBConsistentState(fi, np);
          }
        }
        EvalOk(MFLookup(e12, fi, np));
      }
    }
  }

  lemma ConnectEntitiesValid(c: Circuit, conn: ScufConnection)
    requires ConnectEntitiesRequirements(c, conn)
    ensures
      var new_c := ConnectEntitiesImpl(c, conn);
      && conn.scuf_ab.Valid(new_c)
  {
    var new_c := ConnectEntitiesImpl(c, conn);
    ConnectEntitiesSomewhatValid(c, conn);
    var e1 := conn.scuf_a;
    var e2 := conn.scuf_b;
    var e12 := conn.scuf_ab;
    forall fi: FI | FIValid(fi, e12.mp.inputs, e12.mp.state)
      ensures forall np :: np in Seq.ToSet(e12.mp.outputs) ==>
          && np in e12.f(fi).outputs
          && NPValid(new_c, np)
          && FICircuitValid(new_c, fi)
          && (Evaluate(new_c, np, fi) == EvalOk(e12.f(fi).outputs[np]))
      ensures forall np :: np in Seq.ToSet(e12.mp.outputs) ==>
          && np in e12.mp.outputs
          && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(e12, fi, np)))
      ensures forall np :: np in StateINPs(e12.mp.state) ==>
          && np.n in e12.f(fi).state
          && NPValid(new_c, np)
          && FICircuitValid(new_c, fi)
          && (Evaluate(new_c, np, fi) == EvalOk(e12.f(fi).state[np.n]))
      ensures forall np :: np in StateINPs(e12.mp.state) ==>
          && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(e12, fi, np)))
    {
      ScufFOutputsAreValid(c, e1);
      ScufFOutputsAreValid(c, e2);
      FOutputsInSc(c, e1);
      FOutputsInSc(c, e2);
      var s := MakeCESSummary(c, conn, fi);
      //reveal MapFunction.Valid();
      forall np | np in Seq.ToSet(e12.mp.outputs)
        ensures
          && np in e12.f(fi).outputs
          && NPValid(new_c, np)
          && (Evaluate(new_c, np, fi) == EvalOk(e12.f(fi).outputs[np]))
          && np in e12.mp.outputs
          && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(e12, fi, np)))
      {
        assert np in e12.mp.outputs by {
          reveal Seq.ToSet();
        }
        ScufFOutputsAreValid(new_c, e12);
        reveal NPsInSc();
        assert NPValid(new_c, np);
        EvaluateConnectEntities(s, np);
        //reveal e12.mp.Valid();
        var fo := e12.f(fi);
        assert FOValid(fo, e12.mp.outputs, e12.mp.state);
        assert np in fo.outputs by {
          reveal Seq.ToSet();
          //reveal e12.mp.Valid();
        }
        assert (Evaluate(new_c, np, fi) == EvalOk(e12.f(fi).outputs[np]));
        assert (Evaluate(new_c, np, fi) == EvalOk(MFLookup(e12, fi, np)));
      }
      forall np | np in StateINPs(e12.mp.state)
        ensures
          && np.n in e12.f(fi).state
          && NPValid(new_c, np)
          && (Evaluate(new_c, np, fi) == EvalOk(e12.f(fi).state[np.n]))
          && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(e12, fi, np)))
      {
        ScufFOutputsAreValid(new_c, e12);
        reveal NPsInSc();
        assert NPValid(new_c, np);
        EvaluateConnectEntities(s, np);
        assert np.n in e12.f(fi).state by {
          reveal Seq.ToSet();
          //reveal e12.mp.Valid();
        }
        assert (Evaluate(new_c, np, fi) == EvalOk(e12.f(fi).state[np.n]));
        assert (Evaluate(new_c, np, fi) == EvalOk(MFLookup(e12, fi, np)));
      }
    }
    reveal Scuf.EvaluatesCorrectly();
    assert ScValid(new_c, e12.sc) by {
      reveal ConnectEntitiesImpl();
      reveal ScValid();
    }
    assert forall fi: FI :: FIValid(fi, e12.mp.inputs, e12.mp.state) ==>
      forall np :: np in Seq.ToSet(e12.mp.outputs) ==>
        && Evaluate(new_c, np, fi) == EvalOk(e12.f(fi).outputs[np]);
    assert forall fi: FI :: FIValid(fi, e12.mp.inputs, e12.mp.state) ==>
      (forall np :: np in (Seq.ToSet(e12.mp.outputs) + StateINPs(e12.mp.state)) ==>
      Evaluate(new_c, np, fi) == EvalOk(MFLookup(e12, fi, np))
      );
    assert e12.EvaluatesCorrectly(new_c);
    assert e12.Valid(new_c);
  }

  function ConnectEntities(
      c: Circuit, conn: ScufConnection): (new_c: Circuit)
    requires ConnectEntitiesRequirements(c, conn)
    ensures new_c.Valid()
    ensures conn.scuf_ab.Valid(new_c)
    ensures IsIsland(new_c, conn.scuf_ab.sc)
    ensures new_c.NodeKind == c.NodeKind
  {
    ConnectEntitiesValid(c, conn);
    ConnectEntitiesIsIsland(c, conn);
    ConnectEntitiesImpl(c, conn)
  }

}

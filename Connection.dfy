module Connection {

  import opened Circ
  import opened Utils
  import opened Scuf
  import opened Subcircuit
  import opened Eval
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened MapConnection

  opaque ghost predicate ConnectionValid(c: Circuit, e1: Scuf, e2: Scuf, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
  {
    && (connection.Keys <= Seq.ToSet(e2.mp.inputs))
    && (connection.Values <= Seq.ToSet(e1.mp.outputs))
    && SetsNoIntersection(connection.Keys, c.PortSource.Keys)
  }

  lemma GetConnectionValid(c: Circuit, conn: ScufConnection)
    requires c.Valid()
    requires conn.SomewhatValid()
    requires conn.ValidInCircuit(c)
    ensures
      var connection := conn.GetConnection();
      ConnectionValid(c, conn.scuf_a, conn.scuf_b, connection)
  {
    reveal ConnectionValid();
  }

  lemma ConnectionValuesInE1(c: Circuit, e1: Scuf, e2: Scuf, connection: map<NP, NP>)
    requires c.Valid()
    requires e1.Valid(c)
    requires e2.Valid(c)
    requires ConnectionValid(c, e1, e2, connection)
    ensures NPsInSc(e1.sc, connection.Values)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    FOutputsInSc(c, e1);
  }

  lemma ConnectionKeysInE2(c: Circuit, e1: Scuf, e2: Scuf, connection: map<NP, NP>)
    requires c.Valid()
    requires e1.Valid(c)
    requires e2.Valid(c)
    requires ConnectionValid(c, e1, e2, connection)
    ensures NPsInSc(e2.sc, connection.Keys)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    FInputsInSc(c, e2);
  }

  lemma ConnectionKeysINPs(c: Circuit, e1: Scuf, e2: Scuf, connection: map<NP, NP>)
    requires c.Valid()
    requires e1.Valid(c)
    requires e2.Valid(c)
    requires ConnectionValid(c, e1, e2, connection)
    ensures INPsValid(c, connection.Keys)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    reveal INPsValid();
    reveal Scuf.SomewhatValid();
    ScufFInputsAreValid(c, e2);
  }

  lemma ConnectionValuesONPs(c: Circuit, e1: Scuf, e2: Scuf, connection: map<NP, NP>)
    requires c.Valid()
    requires e1.Valid(c)
    requires e2.Valid(c)
    requires ConnectionValid(c, e1, e2, connection)
    ensures ONPsValid(c, connection.Values)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    reveal ONPsValid();
    reveal Scuf.SomewhatValid();
    ScufFOutputsAreValid(c, e1);
  }

  lemma IsIslandInputsNotInPortSource(c: Circuit, e: Scuf)
    requires c.Valid()
    requires e.SomewhatValid(c)
    requires IsIsland(c, e.sc)
    ensures Seq.ToSet(e.mp.inputs) !! c.PortSource.Keys
  {
    reveal IsIsland();
    reveal Scuf.SomewhatValid();
    reveal ConnInputs();
    reveal UnconnInputs();
  }

  ghost predicate ConnectEntitiesRequirements(c: Circuit, conn: ScufConnection) {
    && c.Valid()
    && conn.Valid()
    && conn.ValidInCircuit(c)
  }

  lemma ConnectionInSc(c: Circuit, conn: ScufConnection)
    requires ConnectEntitiesRequirements(c, conn)
    ensures
      var connection := conn.GetConnection();
      && NPsInSc(conn.scuf_b.sc, connection.Keys)
      && NPsInSc(conn.scuf_a.sc, connection.Values)
      && NPsNotInSc(conn.scuf_b.sc, connection.Values)
      && NPsNotInSc(conn.scuf_a.sc, connection.Keys)
  {
    var connection := conn.GetConnection();
    assert connection.Values <= Seq.ToSet(conn.scuf_a.mp.outputs);
    assert connection.Keys == Seq.ToSet(conn.scuf_b.mp.inputs) - Seq.ToSet(conn.scuf_ab.mp.inputs);
    reveal NPsInSc();
    reveal NPsNotInSc();
    reveal Seq.ToSet();
    FOutputsInSc(c, conn.scuf_a);
    FOutputsInSc(c, conn.scuf_b);
    FInputsInSc(c, conn.scuf_a);
    FInputsInSc(c, conn.scuf_b);
  }

  opaque predicate ConnectCircuitRequirements(c: Circuit, connection: map<NP, NP>)
  {
    && (forall np :: np in connection.Keys ==> INPValid(c, np) && np !in c.PortSource)
    && (forall np :: np in connection.Values ==> ONPValid(c, np))
  }

  function ConnectCircuit(c: Circuit, connection: map<NP, NP>): (r: Circuit)
    requires c.Valid()
    requires ConnectCircuitRequirements(c, connection)
    ensures r.Valid()
  {
    reveal Circuit.Valid();
    reveal ConnectCircuitRequirements();
    var new_c := Circuit(
      c.NodeKind,
      AddMaps(c.PortSource, connection)
    );
    assert new_c.PortSource.Values == c.PortSource.Values + connection.Values;
    assert (forall np :: np in new_c.PortSource.Values ==> ONPValid(new_c, np));
    assert (forall np :: np in new_c.PortSource.Keys ==> INPValid(new_c, np));
    new_c
  }

  lemma ConnectCircuitOtherIsIsland(c: Circuit, connection: map<NP, NP>, e: Scuf)
    requires c.Valid()
    requires ConnectCircuitRequirements(c, connection)
    requires e.Valid(c)
    requires IsIsland(c, e.sc)
    requires NPsNotInSc(e.sc, connection.Keys)
    requires NPsNotInSc(e.sc, connection.Values)
    ensures
      var new_c := ConnectCircuit(c, connection);
      IsIsland(new_c, e.sc)
    {
      reveal IsIsland();
      var new_c := ConnectCircuit(c, connection);
      assert new_c.PortSource.Keys == c.PortSource.Keys + connection.Keys;
      assert forall np :: np in new_c.PortSource && np.n in e.sc ==> np in c.PortSource by {
        reveal NPsNotInSc();
      }
      assert new_c.PortSource.Values == c.PortSource.Values + connection.Values;
      assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
      forall np | np in new_c.PortSource
        ensures !((np.n !in e.sc) && (new_c.PortSource[np].n in e.sc))
      {
        if np.n !in e.sc && new_c.PortSource[np].n in e.sc {
          assert np !in c.PortSource;
          assert np in connection.Keys;
          assert new_c.PortSource[np] in connection.Values;
          reveal NPsNotInSc();
          assert false;
        }
      }
      assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    }

  lemma ConnectEntitiesOtherConnUnchanged(c: Circuit, connection: map<NP, NP>, e: Scuf)
    requires c.Valid()
    requires ConnectCircuitRequirements(c, connection)
    requires e.Valid(c)
    requires NPsNotInSc(e.sc, connection.Keys)
    requires NPsNotInSc(e.sc, connection.Values)
    ensures
      var new_c := ConnectCircuit(c, connection);
      && ScValid(new_c, e.sc)
      && (ConnInputs(c, e.sc) == ConnInputs(new_c, e.sc))
      && (UnconnInputs(c, e.sc) == UnconnInputs(new_c, e.sc))
      && (ConnOutputs(c, e.sc) == ConnOutputs(new_c, e.sc))
  {
    var new_c := ConnectCircuit(c, connection);
    assert new_c.PortSource.Keys == c.PortSource.Keys + connection.Keys;
    assert new_c.PortSource.Values == c.PortSource.Values + connection.Values;
    assert ScValid(new_c, e.sc) by {
      reveal ScValid();
    }
    forall np: NP | np.n in e.sc
      ensures (np in ConnInputs(c, e.sc)) == (np in ConnInputs(new_c, e.sc))
      ensures (np in UnconnInputs(c, e.sc)) == (np in UnconnInputs(new_c, e.sc))
    {
      assert np !in connection.Keys by {
        reveal NPsNotInSc();
      }
      // ConnInputs conserved
      if (np in c.PortSource) && (c.PortSource[np].n !in e.sc) {
        assert np in new_c.PortSource;
        assert new_c.PortSource[np].n !in e.sc;
      }
      if (np in new_c.PortSource) && (new_c.PortSource[np].n !in e.sc) {
        assert np in c.PortSource;
        assert c.PortSource[np].n !in e.sc;
      }
      // UnconnInputs conserved
      if (np !in c.PortSource && INPValid(c, np)) {
        assert (np !in new_c.PortSource);
        assert INPValid(new_c, np);
      }
      if (np !in new_c.PortSource && INPValid(new_c, np)) {
        assert np !in c.PortSource;
        assert INPValid(c, np);
      }
      reveal ConnInputs();
      reveal UnconnInputs();
    }
    forall np: NP | np.n !in e.sc
      ensures
        ((np in c.PortSource) && (c.PortSource[np].n in e.sc)) ==
        ((np in new_c.PortSource) && (new_c.PortSource[np].n in e.sc))
    {
      // ConnOutputs conserved
      if (np in c.PortSource) && (c.PortSource[np].n in e.sc) {
        assert np in new_c.PortSource;
        assert new_c.PortSource[np].n in e.sc;
      }
      if (np in new_c.PortSource) && (new_c.PortSource[np].n in e.sc) {
        assert new_c.PortSource[np] !in connection.Values by {
          reveal NPsNotInSc();
        }
        assert c.PortSource[np].n in e.sc;
        assert np in c.PortSource;
      }
    }
    reveal ConnInputs();
    reveal UnconnInputs();
    reveal ConnOutputs();
  }

  lemma ConnectCircuitOtherScufValid(c: Circuit, connection: map<NP, NP>, e: Scuf)
    requires c.Valid()
    requires ConnectCircuitRequirements(c, connection)
    requires e.Valid(c)
    requires NPsNotInSc(e.sc, connection.Keys)
    requires NPsNotInSc(e.sc, connection.Values)
    ensures
      var new_c := ConnectCircuit(c, connection);
      && e.Valid(new_c)
  {
    ConnectEntitiesOtherConnUnchanged(c, connection, e);

    var new_c := ConnectCircuit(c, connection);
    assert ScValid(new_c, e.sc) by {
      reveal ScValid();
    }

    assert e.SomewhatValid(new_c) by {
      reveal Scuf.SomewhatValid();
      assert ScValid(new_c, e.sc);
      assert (AllONPs(new_c, e.sc) >= Seq.ToSet(e.mp.outputs) >= ConnOutputs(new_c, e.sc)) by {
        reveal AllONPs();
        assert new_c.NodeKind == c.NodeKind;
      }
      assert (Seq.ToSet(e.mp.inputs) == AllInputs(new_c, e.sc));
      assert (Seq.ToSet(e.mp.state) == AllSeq(new_c, e.sc)) by {
        reveal AllSeq();
      }
    }
    assert NoInternalConnections(connection, e.sc) by {
      reveal NPsNotInSc();
      reveal NoInternalConnections();
    }
    ConnectCircuitConservesSubcircuit(c, connection, e.sc);
    assert OutputsInFOutputs(new_c, e) by {
      reveal Scuf.SomewhatValid();
      assert OutputsInFOutputs(c, e);
      reveal ConnOutputs();
      assert ConnOutputs(new_c, e.sc) == ConnOutputs(c, e.sc);
    }
    ScufConserved(c, new_c, e);
  }

  lemma ConnectCircuitConservesSubcircuit(c: Circuit, connection: map<NP, NP>, sc: set<CNode>)
    requires c.Valid()
    requires ConnectCircuitRequirements(c, connection)
    requires ScValid(c, sc)
    requires NoInternalConnections(connection, sc)
    ensures SubcircuitConserved(c, ConnectCircuit(c, connection), sc)
  {
    reveal NoInternalConnections();
    var ca := c;
    var cb := ConnectCircuit(c, connection);
    reveal ScValid();
    assert (forall n :: n in sc ==> n in cb.NodeKind);
    assert (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n]);
    assert (forall np: NP :: np.n in sc && np in ca.PortSource ==>
            np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np]);
    assert (forall np: NP :: np.n in sc && np !in ca.PortSource && np in cb.PortSource ==>
        cb.PortSource[np].n !in sc);
    reveal SubcircuitConserved();
  }

  opaque predicate NoInternalConnections(connection: map<NP, NP>, sc: set<CNode>)
  {
    && (forall np :: np in connection.Keys && np.n in sc ==> connection[np].n !in sc)
  }

  // opaque predicate ConnectionValuesInFOutputs(connection: map<NP, NP>, e: Scuf)
  // {
  //   && (forall np :: np in connection.Values && np.n in e.sc ==> np in e.mf.outputs)
  // }

  predicate ConnectionsScufCompatible(connection: map<NP, NP>, e: Scuf)
  {
    // for e1
    && NoInternalConnections(connection, e.sc)
    && connection.Values <= Seq.ToSet(e.mp.outputs)
  }

  predicate ConnectionsScuf2Compatible(connection: map<NP, NP>, e: Scuf)
  {
    // for e2
    && NoInternalConnections(connection, e.sc)
    && NPsNotInSc(e.sc, connection.Values)
  }


  lemma ConnectCircuitEntitiesStillValid(c: Circuit, connection: map<NP, NP>, e: Scuf)
    requires c.Valid()
    requires ConnectCircuitRequirements(c, connection)
    requires e.Valid(c)
    requires ConnectionsScufCompatible(connection, e)
    ensures e.Valid(ConnectCircuit(c, connection))
  {
    reveal NoInternalConnections();
    var new_c := ConnectCircuit(c, connection);
    ConnectCircuitConservesSubcircuit(c, connection, e.sc);
    assert ScValid(new_c, e.sc) by {
      reveal ScValid();
    }
    assert OutputsInFOutputs(new_c, e) by {
      reveal ConnOutputs();
      reveal Scuf.SomewhatValid();
      assert OutputsInFOutputs(c, e);
      //reveal ConnectionValuesInFOutputs();
      //assert ConnectionValuesInFOutputs(connection, e);
    }
    ScufConserved(c, new_c, e);
  }

  lemma ConnectEntitiesIsIsland(c: Circuit, conn: ScufConnection)
    requires ConnectEntitiesRequirements(c, conn)
    ensures
      var new_c := ConnectEntitiesImpl(c, conn);
      IsIsland(new_c, conn.scuf_ab.sc)
  {
    reveal NPsInSc();
    var new_c := ConnectEntitiesImpl(c, conn);
    var e1 := conn.scuf_a;
    var e2 := conn.scuf_b;
    var e12 := conn.scuf_ab;
    var sc1 := conn.scuf_a.sc;
    var sc2 := conn.scuf_b.sc;
    assert ScValid(c, sc1 + sc2) by {
      reveal ScValid();
    }
    var sco := SubcircuitComplement(c, sc1 + sc2);
    assert |sco * sc1| == 0;
    assert |sco * sc2| == 0;

    assert IsIsland(c, sc1);
    assert IsIsland(c, sc2);
    assert IsIsland(c, sc1 + sc2) by {
      reveal IsIsland();
    }
    assert IsIsland(c, sco) by {
      reveal ScValid();
      IsIslandComplementIsIsland(c, sc1+sc2);
    }

    assert NoConnFromTo(c, sc1, sc2) by {reveal ScValid(); IsIslandNoConns(c, sc1, sc2);}
    assert NoConnFromTo(c, sc1, sco) by {reveal ScValid(); IsIslandNoConns(c, sc1, sco);}
    assert NoConnFromTo(c, sc2, sc1) by {reveal ScValid(); IsIslandNoConns(c, sc2, sc1);}
    assert NoConnFromTo(c, sc2, sco) by {reveal ScValid(); IsIslandNoConns(c, sc2, sco);}
    assert NoConnFromTo(c, sco, sc1) by {reveal ScValid(); IsIslandNoConns(c, sco, sc1);}
    assert NoConnFromTo(c, sco, sc2) by {reveal ScValid(); IsIslandNoConns(c, sco, sc2);}

    forall np: NP | np in new_c.PortSource
      ensures np.n in sc1+sc2 ==> new_c.PortSource[np].n in sc1+sc2
      ensures np.n !in sc1+sc2 ==> new_c.PortSource[np].n !in sc1+sc2
    {
      reveal Circuit.Valid();
      reveal ConnectionValid();
      reveal IsIsland();
      reveal ConnectEntitiesImpl();
      assert NodeValid(c, np.n);
      InScOrComplement(c, sc1+sc2, np.n);
      var connection := conn.GetConnection();
      assert ConnectionValid(c, e1, e2, connection);
      if np !in connection {
        assert new_c.PortSource[np] == c.PortSource[np];
      }
      if np.n in sc1 {
        assert np !in connection.Keys by {
          ConnectionKeysInE2(c, e1, e2, connection);
          reveal NPsInSc();
          InThisNotInThat(np.n, e1.sc, e2.sc);
        }
        assert new_c.PortSource[np] == c.PortSource[np];
        assert new_c.PortSource[np].n in sc1;
      } else if np.n in sc2 {
        if np in connection.Keys {
          assert new_c.PortSource[np] == connection[np];
          ConnectionValuesInE1(c, e1, e2, connection);
          assert connection[np].n in sc1;
          assert new_c.PortSource[np].n in sc1;
        } else {
          assert new_c.PortSource[np] == c.PortSource[np];
        }
        assert new_c.PortSource[np].n in sc1 + sc2;
      } else {
        assert np.n in sco;
        assert np !in connection.Keys && np !in connection.Values by {
          ConnectionKeysInE2(c, e1, e2, connection);
          ConnectionValuesInE1(c, e1, e2, connection);
          reveal NPsInSc();
        }
        assert new_c.PortSource[np] == c.PortSource[np];
        assert new_c.PortSource[np].n !in sc1;
        assert new_c.PortSource[np].n !in sc2;
      }
    }
    reveal IsIsland();
    assert e12.sc == sc1 + sc2 by {
      reveal ConnectEntitiesImpl();
    }
    assert (forall np :: np in new_c.PortSource && np.n in e12.sc ==> new_c.PortSource[np].n in e12.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e12.sc ==> new_c.PortSource[np].n !in e12.sc);
    assert IsIsland(new_c, e12.sc);
  }

  lemma ConnectCircuitReqFromConnectEntitiesReq(c: Circuit, conn: ScufConnection)
    requires ConnectEntitiesRequirements(c, conn)
    ensures ConnectCircuitRequirements(c, conn.GetConnection())
  {
    reveal ConnectionValid();
    reveal Scuf.SomewhatValid();
    reveal ConnectCircuitRequirements();
    var connection := conn.GetConnection();
    ConnectionKeysINPs(c, conn.scuf_a, conn.scuf_b, connection);
    ConnectionValuesONPs(c, conn.scuf_a, conn.scuf_b, connection);
    reveal INPsValid();
    reveal ONPsValid();
    SetsNoIntersectionDuh(connection.Keys, c.PortSource.Keys);
    assert (forall np :: np in connection.Keys ==> INPValid(c, np) && np !in c.PortSource);
    assert (forall np :: np in connection.Values ==> ONPValid(c, np));
  }

  opaque function ConnectEntitiesImpl(
      c: Circuit, conn: ScufConnection): (r: Circuit)
    requires ConnectEntitiesRequirements(c, conn)
    ensures r.Valid()
    ensures r.NodeKind == c.NodeKind
  {
    var connection := conn.GetConnection();

    assert ConnectCircuitRequirements(c, connection) by {
      ConnectCircuitReqFromConnectEntitiesReq(c, conn);
    }
    var new_c := ConnectCircuit(c, connection);
    new_c
  }

  lemma NPSetsNoIntersection(c: Circuit, conn: ScufConnection, nps1: set<NP>, nps2: set<NP>)
    requires ConnectEntitiesRequirements(c, conn)
    requires NPsInSc(conn.scuf_a.sc, nps1)
    requires NPsInSc(conn.scuf_b.sc, nps2)
    ensures SetsNoIntersection(nps1, nps2)
  {
    reveal NPsInSc();
    var e1 := conn.scuf_a;
    var e2 := conn.scuf_b;
    if exists np :: np in nps1 && np in nps2 {
      var np :| np in nps1 && np in nps2;
      assert np.n in e1.sc && np.n in e2.sc;
      assert SetsNoIntersection(e1.sc, e2.sc);
      NotInBoth(np.n, e1.sc, e2.sc);
      assert false;
    }
  }

  lemma ReorderSets<T>(a: set<T>, b: set<T>, c: set<T>)
    requires SetsNoIntersection(b, c)
    ensures (a - b) + c == (a + c) - b
  {
    SetsNoIntersectionDuh(b, c);
    assert !exists x :: x in b && x in c;
  }

  lemma ReorderSets2<T>(a: set<T>, b: set<T>, c: set<T>)
    requires SetsNoIntersection(a, c)
    ensures (a + b) - c == a + (b - c)
  {
    SetsNoIntersectionDuh(a, c);
    assert !exists x :: x in a && x in c;
  }

  lemma ConnectEntitiesSomewhatValid(c: Circuit, conn: ScufConnection)
    requires ConnectEntitiesRequirements(c, conn)
    ensures
      var new_c := ConnectEntitiesImpl(c, conn);
      conn.scuf_ab.SomewhatValid(new_c)
  {
    var e1 := conn.scuf_a;
    var e2 := conn.scuf_b;
    var e12 := conn.scuf_ab;
    ConnectEntitiesEntitiesStillValid(c, conn);
    var new_c := ConnectEntitiesImpl(c, conn);
    var connection := conn.GetConnection();
    assert ScValid(new_c, e12.sc) && ScValid(new_c, e1.sc) && ScValid(new_c, e2.sc) by {
      reveal ScValid();
      reveal ConnectEntitiesImpl();
    }
    assert (AllONPs(new_c, e12.sc) >= Seq.ToSet(e12.mp.outputs)) by {
      reveal AllONPs();
      reveal Seq.ToSet();
      assert AllONPs(new_c, e12.sc) == AllONPs(new_c, e1.sc) + AllONPs(new_c, e2.sc);
      assert Seq.ToSet(e12.mp.outputs) <= Seq.ToSet(e1.mp.outputs) + Seq.ToSet(e2.mp.outputs);
      calc {
        AllONPs(new_c, e12.sc);
        ==
        AllONPs(new_c, e1.sc) + AllONPs(new_c, e2.sc);
        >=
        {
          reveal Scuf.SomewhatValid();
          assert AllONPs(new_c, e1.sc) >= Seq.ToSet(e1.mp.outputs);
          assert AllONPs(new_c, e2.sc) >= Seq.ToSet(e2.mp.outputs);
        }
        Seq.ToSet(e1.mp.outputs) + Seq.ToSet(e2.mp.outputs);
        >=
        Seq.ToSet(e12.mp.outputs);
      }
    }
    assert (Seq.ToSet(e12.mp.outputs) >= ConnOutputs(new_c, e12.sc)) by {
      ConnectEntitiesIsIsland(c, conn);
      IsIslandNoOutputs(new_c, e12.sc);
      assert |ConnOutputs(new_c, e12.sc)| == 0;
    }
    assert (Seq.ToSet(e12.mp.state) == AllSeq(new_c, e12.sc)) by {
      reveal Seq.ToSet();
      reveal AllSeq();
      reveal ConnectEntitiesImpl();
      reveal Scuf.SomewhatValid();
    }
    //ConnectEntitiesFOutputsCorrect(c, e1, e2, connection);

    assert (Seq.ToSet(e12.mp.inputs) == AllInputs(new_c, e12.sc)) by {
      calc {
        AllInputs(new_c, e12.sc);
        UnconnInputs(new_c, e12.sc) + ConnInputs(new_c, e12.sc);
        {
          reveal ScValid();
          reveal UnconnInputs();
          reveal ConnectEntitiesImpl();
          assert UnconnInputs(new_c, e12.sc) == UnconnInputs(c, e12.sc)-connection.Keys;
        }
        (UnconnInputs(c, e12.sc)-connection.Keys) + ConnInputs(new_c, e12.sc);
        {
          ConnectEntitiesIsIsland(c, conn);
          IsIslandNoInputs(new_c, e12.sc);
          reveal IsIsland();
          reveal ConnInputs();
          assert |ConnInputs(new_c, e12.sc)| == 0;
        }
        (UnconnInputs(c, e12.sc)-connection.Keys);
        {
          reveal SeqInputs();
          reveal ConnectEntitiesImpl();
          assert SeqInputs(new_c, e12.sc) == SeqInputs(c, e12.sc);
        }
        (UnconnInputs(c, e12.sc)-connection.Keys);
        {
          UnconnInputsAdd(c, e1.sc, e2.sc);
          reveal ConnectEntitiesImpl();
          assert UnconnInputs(c, e12.sc) == UnconnInputs(c, e1.sc) + UnconnInputs(c, e2.sc);
        }
        ((UnconnInputs(c, e1.sc)+UnconnInputs(c, e2.sc))-connection.Keys);
        {
          assert ConnectionValid(c, e1, e2, connection) by {
            reveal ConnectionValid();
          }
          ConnectionKeysInE2(c, e1, e2, connection);
          NPSetsNoIntersection(c, conn, UnconnInputs(c, e1.sc), connection.Keys);
          assert |UnconnInputs(c, e1.sc) * connection.Keys| == 0;
          ReorderSets2(UnconnInputs(c, e1.sc), UnconnInputs(c, e2.sc), connection.Keys);
        }
        UnconnInputs(c, e1.sc)+(UnconnInputs(c, e2.sc)-connection.Keys);
        (UnconnInputs(c, e1.sc) + ((UnconnInputs(c, e2.sc)-connection.Keys)));
        {
          assert ConnectionValid(c, e1, e2, connection) by {
            reveal ConnectionValid();
          }
          ConnectionKeysINPs(c, e1, e2, connection);
        }
        UnconnInputs(c, e1.sc) + (UnconnInputs(c, e2.sc) - connection.Keys);
        {
          reveal IsIsland();
          reveal ConnInputs();
          assert |ConnInputs(c, e1.sc)| == 0;
          assert |ConnInputs(c, e2.sc)| == 0;
        }
        AllInputs(c, e1.sc) + (AllInputs(c, e2.sc) - connection.Keys);
        {
          reveal Scuf.SomewhatValid();
        }
        Seq.ToSet(e1.mp.inputs) + (Seq.ToSet(e2.mp.inputs) - connection.Keys);
        {
          reveal ConnectEntitiesImpl();
        }
        Seq.ToSet(e12.mp.inputs);
      }
    }
    reveal Scuf.SomewhatValid();
  }

  lemma ConnectEntitiesEntitiesStillValid(c: Circuit, conn: ScufConnection)
    requires ConnectEntitiesRequirements(c, conn)
    ensures
      && ConnectCircuitRequirements(c, conn.GetConnection())
      && var new_c := ConnectEntitiesImpl(c, conn);
      && conn.scuf_a.Valid(new_c)
      && conn.scuf_b.Valid(new_c)
  {
    var e1 := conn.scuf_a;
    var e2 := conn.scuf_b;
    var new_c := ConnectEntitiesImpl(c, conn);
    ConnectCircuitReqFromConnectEntitiesReq(c, conn);
    var connection := conn.GetConnection();
    assert connection.Values <= Seq.ToSet(e1.mp.outputs);
    assert new_c == ConnectCircuit(c, connection) by {
      reveal ConnectEntitiesImpl();
    }
    assert NoInternalConnections(connection, e1.sc) by {
      reveal NoInternalConnections();
      reveal ConnectionValid();
      ConnectionKeysInE2(c, e1, e2, connection);
      forall np | np in connection.Keys
        ensures np.n !in e1.sc
      {
        assert SetsNoIntersection(e1.sc, e2.sc);
        SetsNoIntersectionSymm(e1.sc, e2.sc);
        reveal NPsInSc();
        assert np.n in e2.sc;
        InThisNotInThat(np.n, e2.sc, e1.sc);
      }
    }
    assert connection.Values <= Seq.ToSet(e1.mp.outputs) by {
      reveal ConnectionValid();
    }
    ConnectCircuitEntitiesStillValid(c, connection, e1);
    assert ConnectionsScufCompatible(connection, e1);
    assert NoInternalConnections(connection, e2.sc) by {
      reveal NoInternalConnections();
      reveal ConnectionValid();
      ConnectionValuesInE1(c, e1, e2, connection);
      forall np | np in connection.Values
        ensures np.n !in e2.sc
      {
        assert SetsNoIntersection(e1.sc, e2.sc);
        reveal NPsInSc();
        assert np.n in e1.sc;
        InThisNotInThat(np.n, e1.sc, e2.sc);
      }
    }
    ConnectCircuitConservesSubcircuit(c, connection, e2.sc);
    assert ScValid(new_c, e2.sc) by {
      reveal ScValid();
    }
    assert OutputsInFOutputs(new_c, e2) by {
      assert OutputsInFOutputs(c, e2) by {
        reveal Scuf.SomewhatValid();
      }
      assert connection.Values <= Seq.ToSet(conn.scuf_a.mp.outputs);
      assert AllONPs(c, e1.sc) >= Seq.ToSet(e1.mp.outputs) by {
        reveal Scuf.SomewhatValid();
      }
      assert NPsInSc(e1.sc, connection.Values) by {
        reveal AllONPs();
        reveal NPsInSc();
      }
      assert NPsNotInSc(e2.sc, connection.Values) by {
        reveal NPsInSc();
        reveal NPsNotInSc();
      }
      assert ConnOutputs(c, e2.sc) == ConnOutputs(new_c, e2.sc) by {
        reveal NPsNotInSc();
        reveal ConnOutputs();
      }
    }
    ScufConserved(c, new_c, e2);
  }

}
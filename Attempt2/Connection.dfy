module Connection {

  import opened Circ
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened Eval
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened MapConnection

  opaque ghost predicate ConnectionValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
  {
    && (connection.Keys <= Seq.ToSet(e2.mf.inputs))
    && (connection.Values <= Seq.ToSet(e1.mf.outputs))
    && SetsNoIntersection(connection.Keys, c.PortSource.Keys)
  }

  lemma ConnectionValuesInE1(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires CircuitValid(c)
    requires EntityValid(c, e1)
    requires EntityValid(c, e2)
    requires ConnectionValid(c, e1, e2, connection)
    ensures NPsInSc(e1.sc, connection.Values)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    FOutputsInSc(c, e1);
  }

  lemma ConnectionKeysInE2(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires CircuitValid(c)
    requires EntityValid(c, e1)
    requires EntityValid(c, e2)
    requires ConnectionValid(c, e1, e2, connection)
    ensures NPsInSc(e2.sc, connection.Keys)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    FInputsInSc(c, e2);
  }

  lemma ConnectionKeysINPs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires CircuitValid(c)
    requires EntityValid(c, e1)
    requires EntityValid(c, e2)
    requires ConnectionValid(c, e1, e2, connection)
    ensures INPsValid(c, connection.Keys)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    reveal INPsValid();
    reveal EntitySomewhatValid();
    EntityFInputsAreValid(c, e2);
  }

  lemma ConnectionValuesONPs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires CircuitValid(c)
    requires EntityValid(c, e1)
    requires EntityValid(c, e2)
    requires ConnectionValid(c, e1, e2, connection)
    ensures ONPsValid(c, connection.Values)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    reveal ONPsValid();
    reveal EntitySomewhatValid();
    EntityFOutputsAreValid(c, e1);
  }

  lemma IsIslandInputsNotInPortSource(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    requires IsIsland(c, e.sc)
    ensures Seq.ToSet(e.mf.inputs) !! c.PortSource.Keys
  {
    reveal IsIsland();
    reveal EntitySomewhatValid();
    reveal ConnInputs();
    reveal UnconnInputs();
  }

  ghost predicate ConnectEntitiesRequirements(c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection) {
    && CircuitValid(c)
    && EntityValid(c, e1)
    && EntityValid(c, e2)
    && e1.sc !! e2.sc
    && e12.sc == e1.sc + e2.sc
    && conn.Valid()
    && conn.mf_a == e1.mf
    && conn.mf_b == e2.mf
    && conn.mf_ab == e12.mf
    && conn.GetConnection().Keys !! c.PortSource.Keys
    && IsIsland(c, e1.sc)
    && IsIsland(c, e2.sc)
  }

  lemma ConnectionInSc(c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection)
    requires ConnectEntitiesRequirements(c, e1, e2, e12, conn)
    ensures
      var connection := conn.GetConnection();
      && NPsInSc(e2.sc, connection.Keys)
      && NPsInSc(e1.sc, connection.Values)
      && NPsNotInSc(e2.sc, connection.Values)
      && NPsNotInSc(e1.sc, connection.Keys)
  {
    var connection := conn.GetConnection();
    assert connection.Values <= Seq.ToSet(e1.mf.outputs);
    assert connection.Keys == Seq.ToSet(e2.mf.inputs) - Seq.ToSet(e12.mf.inputs);
    reveal NPsInSc();
    reveal NPsNotInSc();
    reveal Seq.ToSet();
    FOutputsInSc(c, e1);
    FOutputsInSc(c, e2);
    FInputsInSc(c, e1);
    FInputsInSc(c, e2);
  }

  opaque predicate ConnectCircuitRequirements(c: Circuit, connection: map<NP, NP>)
  {
    && (forall np :: np in connection.Keys ==> INPValid(c, np) && np !in c.PortSource)
    && (forall np :: np in connection.Values ==> ONPValid(c, np))
  }

  function ConnectCircuit(c: Circuit, connection: map<NP, NP>): (r: Circuit)
    requires CircuitValid(c)
    requires ConnectCircuitRequirements(c, connection)
    ensures CircuitValid(r)
  {
    reveal CircuitValid();
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

  lemma ConnectCircuitOtherIsIsland(c: Circuit, connection: map<NP, NP>, e: Entity)
    requires CircuitValid(c)
    requires ConnectCircuitRequirements(c, connection)
    requires EntityValid(c, e)
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

  lemma ConnectEntitiesOtherConnUnchanged(c: Circuit, connection: map<NP, NP>, e: Entity)
    requires CircuitValid(c)
    requires ConnectCircuitRequirements(c, connection)
    requires EntityValid(c, e)
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

  lemma ConnectCircuitOtherEntityValid(c: Circuit, connection: map<NP, NP>, e: Entity)
    requires CircuitValid(c)
    requires ConnectCircuitRequirements(c, connection)
    requires EntityValid(c, e)
    requires NPsNotInSc(e.sc, connection.Keys)
    requires NPsNotInSc(e.sc, connection.Values)
    ensures
      var new_c := ConnectCircuit(c, connection);
      && EntityValid(new_c, e)
  {
    ConnectEntitiesOtherConnUnchanged(c, connection, e);

    var new_c := ConnectCircuit(c, connection);
    assert ScValid(new_c, e.sc) by {
      reveal ScValid();
    }

    assert EntitySomewhatValid(new_c, e) by {
      reveal EntitySomewhatValid();
      assert ScValid(new_c, e.sc);
      assert (AllONPs(new_c, e.sc) >= Seq.ToSet(e.mf.outputs) >= ConnOutputs(new_c, e.sc)) by {
        reveal AllONPs();
        assert new_c.NodeKind == c.NodeKind;
      }
      assert (Seq.ToSet(e.mf.inputs) == AllInputs(new_c, e.sc));
      assert (Seq.ToSet(e.mf.state) == AllSeq(new_c, e.sc)) by {
        reveal AllSeq();
      }
    }
    assert NoInternalConnections(connection, e.sc) by {
      reveal NPsNotInSc();
      reveal NoInternalConnections();
    }
    ConnectCircuitConservesSubcircuit(c, connection, e.sc);
    assert OutputsInFOutputs(new_c, e) by {
      reveal EntitySomewhatValid();
      assert OutputsInFOutputs(c, e);
      reveal ConnOutputs();
      assert ConnOutputs(new_c, e.sc) == ConnOutputs(c, e.sc);
    }
    EntityConserved(c, new_c, e);
  }

  lemma ConnectCircuitConservesSubcircuit(c: Circuit, connection: map<NP, NP>, sc: set<CNode>)
    requires CircuitValid(c)
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

  // opaque predicate ConnectionValuesInFOutputs(connection: map<NP, NP>, e: Entity)
  // {
  //   && (forall np :: np in connection.Values && np.n in e.sc ==> np in e.mf.outputs)
  // }

  predicate ConnectionsEntityCompatible(connection: map<NP, NP>, e: Entity)
  {
    // for e1
    && NoInternalConnections(connection, e.sc)
    && connection.Values <= Seq.ToSet(e.mf.outputs)
  }

  predicate ConnectionsEntity2Compatible(connection: map<NP, NP>, e: Entity)
  {
    // for e2
    && NoInternalConnections(connection, e.sc)
    && NPsNotInSc(e.sc, connection.Values)
  }


  lemma ConnectCircuitEntitiesStillValid(c: Circuit, connection: map<NP, NP>, e: Entity)
    requires CircuitValid(c)
    requires ConnectCircuitRequirements(c, connection)
    requires EntityValid(c, e)
    requires ConnectionsEntityCompatible(connection, e)
    ensures EntityValid(ConnectCircuit(c, connection), e)
  {
    reveal NoInternalConnections();
    var new_c := ConnectCircuit(c, connection);
    ConnectCircuitConservesSubcircuit(c, connection, e.sc);
    assert ScValid(new_c, e.sc) by {
      reveal ScValid();
    }
    assert OutputsInFOutputs(new_c, e) by {
      reveal ConnOutputs();
      reveal EntitySomewhatValid();
      assert OutputsInFOutputs(c, e);
      //reveal ConnectionValuesInFOutputs();
      //assert ConnectionValuesInFOutputs(connection, e);
    }
    EntityConserved(c, new_c, e);
  }

  lemma ConnectEntitiesIsIsland(c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection)
    requires ConnectEntitiesRequirements(c, e1, e2, e12, conn)
    ensures
      var new_c := ConnectEntitiesImpl(c, e1, e2, e12, conn);
      IsIsland(new_c, e12.sc)
  {
    reveal NPsInSc();
    var new_c := ConnectEntitiesImpl(c, e1, e2, e12, conn);
    var sc1 := e1.sc;
    var sc2 := e2.sc;
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
      reveal CircuitValid();
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

  lemma ConnectCircuitReqFromConnectEntitiesReq(c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection)
    requires ConnectEntitiesRequirements(c, e1, e2, e12, conn)
    ensures ConnectCircuitRequirements(c, conn.GetConnection())
  {
    reveal ConnectionValid();
    reveal EntitySomewhatValid();
    reveal ConnectCircuitRequirements();
    var connection := conn.GetConnection();
    ConnectionKeysINPs(c, e1, e2, connection);
    ConnectionValuesONPs(c, e1, e2, connection);
    reveal INPsValid();
    reveal ONPsValid();
    SetsNoIntersectionDuh(connection.Keys, c.PortSource.Keys);
    assert (forall np :: np in connection.Keys ==> INPValid(c, np) && np !in c.PortSource);
    assert (forall np :: np in connection.Values ==> ONPValid(c, np));
  }

  opaque function ConnectEntitiesImpl(
      c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection): (r: Circuit)
    requires ConnectEntitiesRequirements(c, e1, e2, e12, conn)
    ensures CircuitValid(r)
  {
    var connection := conn.GetConnection();

    assert ConnectCircuitRequirements(c, connection) by {
      ConnectCircuitReqFromConnectEntitiesReq(c, e1, e2, e12, conn);
    }
    var new_c := ConnectCircuit(c, connection);
    new_c
  }

  lemma NPSetsNoIntersection(c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection, nps1: set<NP>, nps2: set<NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, e12, conn)
    requires NPsInSc(e1.sc, nps1)
    requires NPsInSc(e2.sc, nps2)
    ensures SetsNoIntersection(nps1, nps2)
  {
    reveal NPsInSc();
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

  lemma ConnectEntitiesSomewhatValid(c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection)
    requires ConnectEntitiesRequirements(c, e1, e2, e12, conn)
    ensures
      var new_c := ConnectEntitiesImpl(c, e1, e2, e12, conn);
      EntitySomewhatValid(new_c, e12)
  {
    ConnectEntitiesEntitiesStillValid(c, e1, e2, e12, conn);
    var new_c := ConnectEntitiesImpl(c, e1, e2, e12, conn);
    var connection := conn.GetConnection();
    assert ScValid(new_c, e12.sc) && ScValid(new_c, e1.sc) && ScValid(new_c, e2.sc) by {
      reveal ScValid();
      reveal ConnectEntitiesImpl();
    }
    assert (AllONPs(new_c, e12.sc) >= Seq.ToSet(e12.mf.outputs)) by {
      reveal AllONPs();
      reveal Seq.ToSet();
      assert AllONPs(new_c, e12.sc) == AllONPs(new_c, e1.sc) + AllONPs(new_c, e2.sc);
      assert Seq.ToSet(e12.mf.outputs) <= Seq.ToSet(e1.mf.outputs) + Seq.ToSet(e2.mf.outputs);
      calc {
        AllONPs(new_c, e12.sc);
        ==
        AllONPs(new_c, e1.sc) + AllONPs(new_c, e2.sc);
        >=
        {
          reveal EntitySomewhatValid();
          assert AllONPs(new_c, e1.sc) >= Seq.ToSet(e1.mf.outputs);
          assert AllONPs(new_c, e2.sc) >= Seq.ToSet(e2.mf.outputs);
        }
        Seq.ToSet(e1.mf.outputs) + Seq.ToSet(e2.mf.outputs);
        >=
        Seq.ToSet(e12.mf.outputs);
      }
    }
    assert (Seq.ToSet(e12.mf.outputs) >= ConnOutputs(new_c, e12.sc)) by {
      ConnectEntitiesIsIsland(c, e1, e2, e12, conn);
      IsIslandNoOutputs(new_c, e12.sc);
      assert |ConnOutputs(new_c, e12.sc)| == 0;
    }
    assert (Seq.ToSet(e12.mf.state) == AllSeq(new_c, e12.sc)) by {
      reveal Seq.ToSet();
      reveal AllSeq();
      reveal ConnectEntitiesImpl();
      reveal EntitySomewhatValid();
    }
    //ConnectEntitiesFOutputsCorrect(c, e1, e2, connection);

    assert (Seq.ToSet(e12.mf.inputs) == AllInputs(new_c, e12.sc)) by {
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
          ConnectEntitiesIsIsland(c, e1, e2, e12, conn);
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
          NPSetsNoIntersection(c, e1, e2, e12, conn, UnconnInputs(c, e1.sc), connection.Keys);
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
          reveal EntitySomewhatValid();
        }
        Seq.ToSet(e1.mf.inputs) + (Seq.ToSet(e2.mf.inputs) - connection.Keys);
        {
          reveal ConnectEntitiesImpl();
        }
        Seq.ToSet(e12.mf.inputs);
      }
    }
    reveal EntitySomewhatValid();
  }

  lemma ConnectEntitiesEntitiesStillValid(c: Circuit, e1: Entity, e2: Entity, e12: Entity, conn: MFConnection)
    requires ConnectEntitiesRequirements(c, e1, e2, e12, conn)
    ensures
      && ConnectCircuitRequirements(c, conn.GetConnection())
      && var new_c := ConnectEntitiesImpl(c, e1, e2, e12, conn);
      && EntityValid(new_c, e1)
      && EntityValid(new_c, e2)
  {
    var new_c := ConnectEntitiesImpl(c, e1, e2, e12, conn);
    ConnectCircuitReqFromConnectEntitiesReq(c, e1, e2, e12, conn);
    var connection := conn.GetConnection();
    assert connection.Values <= Seq.ToSet(e1.mf.outputs);
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
    assert connection.Values <= Seq.ToSet(e1.mf.outputs) by {
      reveal ConnectionValid();
    }
    ConnectCircuitEntitiesStillValid(c, connection, e1);
    assert ConnectionsEntityCompatible(connection, e1);
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
        reveal EntitySomewhatValid();
      }
      assert connection.Values <= Seq.ToSet(conn.mf_a.outputs);
      assert AllONPs(c, e1.sc) >= Seq.ToSet(e1.mf.outputs) by {
        reveal EntitySomewhatValid();
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
    EntityConserved(c, new_c, e2);
  }

}
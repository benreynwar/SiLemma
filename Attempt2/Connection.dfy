module Connection {

  import opened Circ
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened Eval
  import opened ConservedSubcircuit

  opaque ghost predicate ConnectionValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
  {
    && (connection.Keys <= e2.finputs * AllINPs(c, e2.sc))
    && (connection.Values <= e1.foutputs * AllONPs(c, e1.sc))
    && SetsNoIntersection(connection.Keys, c.PortSource.Keys)
  }

  lemma ConnectionValuesInE1(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
    requires ConnectionValid(c, e1, e2, connection)
    ensures NPsInSc(e1.sc, connection.Values)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
  }

  lemma ConnectionKeysInE2(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
    requires ConnectionValid(c, e1, e2, connection)
    ensures NPsInSc(e2.sc, connection.Keys)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
  }

  lemma ConnectionKeysINPs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
    requires ConnectionValid(c, e1, e2, connection)
    ensures INPsValid(c, connection.Keys)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    reveal INPsValid();
  }

  lemma ConnectionValuesONPs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
    requires ConnectionValid(c, e1, e2, connection)
    ensures ONPsValid(c, connection.Values)
  {
    reveal ScValid();
    reveal ConnectionValid();
    reveal NPsInSc();
    reveal ONPsValid();
  }

  ghost predicate ConnectEntitiesRequirements(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>) {
    && CircuitValid(c)
    && EntityValid(c, e1)
    && EntityValid(c, e2)
    && IsIsland(c, e1.sc)
    && IsIsland(c, e2.sc)
    && SetsNoIntersection(e1.sc, e2.sc)
    && ConnectionValid(c, e1, e2, connection)
  }

  lemma OtherNoIntersection(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures SetsNoIntersection(AllInputs(c, e1.sc), AllInputs(c, e2.sc))
    ensures SetsNoIntersection(AllPossibleOutputs(c, e1.sc), AllPossibleOutputs(c, e2.sc))
  {
    reveal NPsInSc();
    reveal AllONPs();
    reveal AllINPs();
    reveal ConnInputs();
    reveal ConnOutputs();
    reveal UnconnInputs();
    assert NPsInSc(e1.sc, AllInputs(c, e1.sc));
    assert NPsInSc(e1.sc, AllPossibleOutputs(c, e1.sc));
    assert NPsInSc(e2.sc, AllInputs(c, e2.sc));
    assert NPsInSc(e2.sc, AllPossibleOutputs(c, e2.sc));
    NPSetsNoIntersection(c, e1, e2, connection, AllInputs(c, e1.sc), AllInputs(c, e2.sc));
    NPSetsNoIntersection(c, e1, e2, connection, AllPossibleOutputs(c, e1.sc), AllPossibleOutputs(c, e2.sc));
  }

  function ConnectEntitiesFInputs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>): (r: set<NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    // The inputs into e1 and e2, minus any inputs into e1 that came from e1
    ensures e1.finputs <= r
  {
    e1.finputs + (e2.finputs - connection.Keys)
  }

  function ConnectEntitiesF(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>,
                            knowns: map<NP, bool>): (r: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == ConnectEntitiesFInputs(c, e1, e2, connection)
    ensures r.Keys == e1.foutputs + e2.foutputs
  {
    var inputs_1 := ExtractMap(knowns, e1.finputs);
    reveal EntityFValid();
    assert inputs_1.Keys == e1.finputs;
    assert e1.f.requires(inputs_1);
    var outputs_1 := e1.f(inputs_1);
    assert connection.Values <= outputs_1.Keys by { reveal ConnectionValid(); }
    var outputs_1_to_2 := ExtractMap(outputs_1, connection.Values);
    var inputs_2_from_1 := (map np | np in connection :: np := outputs_1_to_2[connection[np]]);
    var combined_inputs := knowns + inputs_2_from_1;
    var inputs_2 := ExtractMap(combined_inputs, e2.finputs);
    var outputs_2 := e2.f(inputs_2);
    assert outputs_2.Keys == e2.foutputs;
    OtherNoIntersection(c, e1, e2, connection);
    reveal EntitySomewhatValid();
    FOutputsInSc(c, e1);
    FOutputsInSc(c, e2);
    NPSetsNoIntersection(c, e1, e2, connection, outputs_1.Keys, outputs_2.Keys);
    var combined_outputs := AddMaps(outputs_1, outputs_2);
    combined_outputs
  }

  lemma RearrangeKnownKeys(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
    ensures knowns.Keys == (e1.finputs + e2.finputs) - connection.Keys
  {
    ConnectionKeysInE2(c, e1, e2, connection);
    forall np | np in connection.Keys
      ensures np !in e1.finputs
    {
      reveal NPsInSc();
      assert np.n in e2.sc;
      SetsNoIntersectionSymm(e1.sc, e2.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
      assert np.n !in e1.sc;
      FInputsInSc(c, e1);
      assert np !in e1.finputs;
    }
  }

  function CalculateE2Inputs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, knowns: map<NP, bool>): (r: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.finputs + (e2.finputs - connection.Keys)
  {
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
    inputs_2
  }

  lemma ConnectEntitiesFHelper(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, knowns: map<NP, bool>, np: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == ConnectEntitiesFInputs(c, e1, e2, connection)
    requires np in e2.foutputs
    ensures
      var knowns_2 := CalculateE2Inputs(c, e1, e2, connection, knowns);
      && e2.f.requires(knowns_2)
      && np in e2.f(knowns_2)
      && e2.f(knowns_2)[np] == ConnectEntitiesF(c, e1, e2, connection, knowns)[np]
  {
    var inputs_1 := ExtractMap(knowns, e1.finputs);
    reveal EntityFValid();
    assert inputs_1.Keys == e1.finputs;
    assert e1.f.requires(inputs_1);
    var outputs_1 := e1.f(inputs_1);
    assert connection.Values <= outputs_1.Keys by { reveal ConnectionValid(); }
    var outputs_1_to_2 := ExtractMap(outputs_1, connection.Values);
    var inputs_2_from_1 := (map np | np in connection :: np := outputs_1_to_2[connection[np]]);
    var combined_inputs := knowns + inputs_2_from_1;
    var inputs_2 := ExtractMap(combined_inputs, e2.finputs);

    assert inputs_2 == CalculateE2Inputs(c, e1, e2, connection, knowns);

    var outputs_2 := e2.f(inputs_2);
    assert outputs_2.Keys == e2.foutputs;
    OtherNoIntersection(c, e1, e2, connection);
    reveal EntitySomewhatValid();
    FOutputsInSc(c, e1);
    FOutputsInSc(c, e2);
    NPSetsNoIntersection(c, e1, e2, connection, outputs_1.Keys, outputs_2.Keys);
    var combined_outputs := AddMaps(outputs_1, outputs_2);
    assert combined_outputs == ConnectEntitiesF(c, e1, e2, connection, knowns);
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

  opaque predicate ConnectionValuesInFOutputs(connection: map<NP, NP>, e: Entity)
  {
    && (forall np :: np in connection.Values && np.n in e.sc ==> np in e.foutputs)
  }

  predicate ConnectionsEntityCompatible(connection: map<NP, NP>, e: Entity)
  {
    && NoInternalConnections(connection, e.sc)
    && ConnectionValuesInFOutputs(connection, e)
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
      reveal ConnectionValuesInFOutputs();
    }
    EntityConserved(c, new_c, e);
  }

  lemma ConnectEntitiesIsIsland(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      IsIsland(new_c, e.sc)
  {
    reveal NPsInSc();
    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
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
      if np !in connection {
        assert new_c.PortSource[np] == c.PortSource[np];
      }
      if np.n in sc1 {
        assert np !in connection.Keys;
        assert new_c.PortSource[np] == c.PortSource[np];
        assert new_c.PortSource[np].n in sc1;
      } else if np.n in sc2 {
        assert np !in connection.Values;
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
        assert np !in connection.Keys;
        assert np !in connection.Values;
        assert new_c.PortSource[np] == c.PortSource[np];
        assert new_c.PortSource[np].n !in sc1;
        assert new_c.PortSource[np].n !in sc2;
      }
    }
    reveal IsIsland();
    assert e.sc == sc1 + sc2 by {
      reveal ConnectEntitiesImpl();
    }
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    assert IsIsland(new_c, e.sc);
  }

  lemma ConnectCircuitReqFromConnectEntitiesReq(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures ConnectCircuitRequirements(c, connection)
  {
    reveal ConnectionValid();
    reveal EntitySomewhatValid();
    reveal ConnectCircuitRequirements();
    ConnectionKeysINPs(c, e1, e2, connection);
    ConnectionValuesONPs(c, e1, e2, connection);
    reveal INPsValid();
    reveal ONPsValid();
    SetsNoIntersectionDuh(connection.Keys, c.PortSource.Keys);
    assert (forall np :: np in connection.Keys ==> INPValid(c, np) && np !in c.PortSource);
    assert (forall np :: np in connection.Values ==> ONPValid(c, np));
  }

  opaque function ConnectEntitiesImpl(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>): (r: (Circuit, Entity))
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures CircuitValid(r.0)
  {
    var new_finputs := ConnectEntitiesFInputs(c, e1, e2, connection);
    var new_f := (knowns: map<NP, bool>) requires knowns.Keys == new_finputs =>
      ConnectEntitiesF(c, e1, e2, connection, knowns);
    var e := Entity(
      e1.sc + e2.sc,
      new_finputs,
      e1.foutputs + e2.foutputs,
      new_f
    );

    assert ConnectCircuitRequirements(c, connection) by {
      ConnectCircuitReqFromConnectEntitiesReq(c, e1, e2, connection);
    }
    var new_c := ConnectCircuit(c, connection);
    (new_c, e)
  }

  lemma ConnectEntitiesScValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      ScValid(new_c, e.sc)
  {
    reveal ConnectEntitiesImpl();
    reveal ScValid();
  }

  lemma ConnectEntitiesFOutputsCorrect(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      && ScValid(new_c, e.sc)
      && (AllPossibleOutputs(new_c, e.sc) >= e.foutputs >= AllOutputs(new_c, e.sc))
  {
    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
    reveal ScValid();
    reveal ConnectEntitiesImpl();
    reveal AllONPs();
    reveal SeqOutputs();
    reveal FinalOutputs();
    assert AllOutputs(c, e.sc) == AllOutputs(c, e1.sc) + AllOutputs(c, e2.sc) by {
      reveal IsIsland();
      reveal ConnOutputs();
    }
    assert AllPossibleOutputs(new_c, e.sc) == AllPossibleOutputs(c, e1.sc) + AllPossibleOutputs(c, e2.sc);
    assert ConnOutputs(c, e1.sc) == {} by {
      reveal IsIsland();
      reveal ConnOutputs();
    }
    ConnectEntitiesIsIsland(c, e1, e2,  connection);
    IsIslandNoOutputs(new_c, e.sc);
    IsIslandNoOutputs(c, e1.sc);
    IsIslandNoOutputs(c, e2.sc);

    assert e.foutputs >= AllOutputs(c, e1.sc) + AllOutputs(c, e2.sc) by {reveal EntitySomewhatValid();}
    assert e.foutputs <= AllPossibleOutputs(c, e1.sc) + AllPossibleOutputs(c, e2.sc) by {reveal EntitySomewhatValid();}

    assert AllPossibleOutputs(c, e.sc) >= e.foutputs >= AllOutputs(c, e.sc) by {reveal EntitySomewhatValid();}
  }

  lemma NPSetsNoIntersection(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, nps1: set<NP>, nps2: set<NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
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

  lemma ConnectEntitiesSomewhatValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      EntitySomewhatValid(new_c, e)
  {
    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
    ConnectEntitiesFOutputsCorrect(c, e1, e2, connection);

    calc {
      AllInputs(new_c, e.sc) == UnconnInputs(new_c, e.sc) + ConnInputs(new_c, e.sc) + SeqInputs(new_c, e.sc) + FinalInputs(new_c, e.sc);
      {
        reveal ScValid();
        reveal UnconnInputs();
        reveal ConnectEntitiesImpl();
        assert UnconnInputs(new_c, e.sc) == UnconnInputs(c, e.sc)-connection.Keys;
      }
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e.sc)-connection.Keys) + ConnInputs(new_c, e.sc) + SeqInputs(new_c, e.sc) + FinalInputs(new_c, e.sc);
      {
        ConnectEntitiesIsIsland(c, e1, e2,  connection);
        IsIslandNoInputs(new_c, e.sc);
        reveal IsIsland();
        reveal ConnInputs();
        assert |ConnInputs(new_c, e.sc)| == 0;
      }
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e.sc)-connection.Keys) + SeqInputs(new_c, e.sc) + FinalInputs(new_c, e.sc);
      {
        reveal SeqInputs();
        reveal FinalInputs();
        reveal ConnectEntitiesImpl();
        assert SeqInputs(new_c, e.sc) == SeqInputs(c, e.sc);
        assert FinalInputs(new_c, e.sc) == FinalInputs(c, e.sc);
      }
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e.sc)-connection.Keys) + SeqInputs(c, e.sc) + FinalInputs(c, e.sc);
      {
        UnconnInputsAdd(c, e1.sc, e2.sc);
        reveal ConnectEntitiesImpl();
        assert UnconnInputs(c, e.sc) == UnconnInputs(c, e1.sc) + UnconnInputs(c, e2.sc);
        reveal SeqInputs();
        reveal FinalInputs();
        assert SeqInputs(c, e.sc) == SeqInputs(c, e1.sc) + SeqInputs(c, e2.sc);
        assert FinalInputs(c, e.sc) == FinalInputs(c, e1.sc) + FinalInputs(c, e2.sc);
      }
      AllInputs(new_c, e.sc) == ((UnconnInputs(c, e1.sc)+UnconnInputs(c, e2.sc))-connection.Keys) +
                                 SeqInputs(c, e1.sc) + SeqInputs(c, e2.sc) + FinalInputs(c, e1.sc) + FinalInputs(c, e2.sc);
      {
        ConnectionKeysInE2(c, e1, e2, connection);
        NPSetsNoIntersection(c, e1, e2, connection, UnconnInputs(c, e1.sc), connection.Keys);
        assert |UnconnInputs(c, e1.sc) * connection.Keys| == 0;
        ReorderSets2(UnconnInputs(c, e1.sc), UnconnInputs(c, e2.sc), connection.Keys);
      }
      AllInputs(new_c, e.sc) == UnconnInputs(c, e1.sc)+(UnconnInputs(c, e2.sc)-connection.Keys) +
                                 SeqInputs(c, e1.sc) + SeqInputs(c, e2.sc) + FinalInputs(c, e1.sc) + FinalInputs(c, e2.sc);
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e1.sc) + SeqInputs(c, e1.sc) + FinalInputs(c, e1.sc)) +
                                ((UnconnInputs(c, e2.sc)-connection.Keys) + SeqInputs(c, e2.sc) + FinalInputs(c, e2.sc));
      {
        ConnectionKeysINPs(c, e1, e2, connection);
        INPsAndONPsNoIntersection(c, connection.Keys, SeqInputs(c, e2.sc));
        INPsAndONPsNoIntersection(c, connection.Keys, FinalInputs(c, e2.sc));
        SetsNoIntersectionAdds(connection.Keys, SeqInputs(c, e2.sc), FinalInputs(c, e2.sc));
        ReorderSets(UnconnInputs(c, e2.sc), connection.Keys, SeqInputs(c, e2.sc) + FinalInputs(c, e2.sc));
        assert ((UnconnInputs(c, e2.sc)-connection.Keys) + SeqInputs(c, e2.sc) + FinalInputs(c, e2.sc)) ==
               ((UnconnInputs(c, e2.sc) + SeqInputs(c, e2.sc) + FinalInputs(c, e2.sc)) - connection.Keys);
      }
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e1.sc) + SeqInputs(c, e1.sc) + FinalInputs(c, e1.sc)) +
                                ((UnconnInputs(c, e2.sc) + SeqInputs(c, e2.sc) + FinalInputs(c, e2.sc)) - connection.Keys);
      {
        reveal IsIsland();
        reveal ConnInputs();
        assert |ConnInputs(c, e1.sc)| == 0;
        assert |ConnInputs(c, e2.sc)| == 0;
        assert AllInputs(c, e1.sc) == (UnconnInputs(c, e1.sc) + SeqInputs(c, e1.sc) + FinalInputs(c, e1.sc));
        assert AllInputs(c, e2.sc) == (UnconnInputs(c, e2.sc) + SeqInputs(c, e2.sc) + FinalInputs(c, e2.sc));
      }
      AllInputs(new_c, e.sc) == AllInputs(c, e1.sc) + (AllInputs(c, e2.sc) - connection.Keys);
      {
        reveal EntitySomewhatValid();
      }
      AllInputs(new_c, e.sc) == e1.finputs + (e2.finputs - connection.Keys);
      {
        reveal ConnectEntitiesImpl();
      }
      AllInputs(new_c, e.sc) == e.finputs;
    }
    reveal EntitySomewhatValid();
    assert EntitySomewhatValid(new_c, e);
  }

  lemma ConnectEntitiesFValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      EntityFValid(new_c, e)
  {
    reveal ConnectEntitiesImpl();
    reveal EntityFValid();
  }

  lemma ConnectEntitiesEntitiesStillValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      && ConnectCircuitRequirements(c, connection)
      && var new_c := ConnectEntitiesImpl(c, e1, e2, connection).0;
      && EntityValid(new_c, e1)
      && EntityValid(new_c, e2)
  {
    var new_c := ConnectEntitiesImpl(c, e1, e2, connection).0;
    ConnectCircuitReqFromConnectEntitiesReq(c, e1, e2, connection);
    assert new_c == ConnectCircuit(c, connection) by {
      reveal ConnectEntitiesImpl();
    }
    ConnectCircuitReqFromConnectEntitiesReq(c, e1, e2, connection);
    assert NoInternalConnections(connection, e1.sc) by {
      reveal NoInternalConnections();
      reveal ConnectionValid();
      assert (connection.Keys <= e2.finputs * AllINPs(c, e2.sc));
      assert (connection.Values <= e1.foutputs * AllONPs(c, e1.sc));
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
    assert ConnectionValuesInFOutputs(connection, e1) by {
      reveal ConnectionValuesInFOutputs();
      reveal ConnectionValid();
    }
    ConnectCircuitEntitiesStillValid(c, connection, e1);
    assert ConnectionsEntityCompatible(connection, e1);
    assert NoInternalConnections(connection, e2.sc) by {
      reveal NoInternalConnections();
      reveal ConnectionValid();
      assert (connection.Keys <= e2.finputs * AllINPs(c, e2.sc));
      assert (connection.Values <= e1.foutputs * AllONPs(c, e1.sc));
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
    assert ConnectionValuesInFOutputs(connection, e2) by {
      ConnectionValuesInE1(c, e1, e2, connection);
      forall np | np in connection.Values
        ensures np.n !in e2.sc
      {
        reveal NPsInSc();
        assert np.n in e1.sc;
        InThisNotInThat(np.n, e1.sc, e2.sc);
      }
      reveal ConnectionValuesInFOutputs();
    }
    assert ConnectionsEntityCompatible(connection, e2);
    ConnectCircuitEntitiesStillValid(c, connection, e2);
  }

  //lemma ConnectEntitiesValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
  //  requires ConnectEntitiesRequirements(c, e1, e2, connection)
  //  ensures
  //    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
  //    EntityEvaluatesCorrectly(new_c, e)
  //{
  //  //reveal ConnectEntitiesImpl();
  //  var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
  //  forall knowns: map<NP, bool> | knowns.Keys == e.finputs {
  //    forall np | np in e.foutputs {
  //      assert Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np]);
  //    }
  //  }
  //}

  //lemma SetsNoIntersectionFromComposedValid(c: Circuit, e1: Entity, e2: Entity)
  //requires ComposedValid(c, e1, e2)
  //ensures SetsNoIntersection(e1.sc, e2.sc)
  //ensures SetsNoIntersection(e1.finputs, e2.finputs)
  //ensures SetsNoIntersection(e1.foutputs, e2.foutputs)
  //ensures SetsNoIntersection(e1.finputs, e2.foutputs)
  //ensures SetsNoIntersection(e1.foutputs, e2.finputs)
  //{
  //  reveal ScValid();
  //  
  //  //reveal EntityValid();
  //  //reveal NPsValidAndInSc();
  //}

  //function ComposeEntity(c: Circuit, e1: Entity, e2: Entity): (r: Entity)
  //  requires ComposedValid(c, e1, e2)
  //  ensures EntityValid(c, r)
  //{
  //  var combined_input_keys := ComposeEntityInputs(c, e1, e2);
  //  var e := Entity(
  //    CombineSets(e1.sc, e2.sc),
  //    combined_input_keys,
  //    e1.foutputs + e2.foutputs,
  //    (combined_inputs: map<NP, bool>) requires combined_inputs.Keys == combined_input_keys =>
  //      ComposeEntityF(c, e1, e2, combined_inputs)
  //  );
  //  assert ScValid(c, e.sc) by {reveal ScValid();}
  //  assert (ScInputBoundary(c, e.sc) == e.finputs) by {
  //    ComposeEntityInputsCorrect(c, e1, e2);
  //  }
  //  assert SetsNoIntersection(e.finputs, e.foutputs) by {
  //    SetsNoIntersectionFromComposedValid(c, e1, e2);
  //  }
  //  //assert NPsValidAndInSc(c, e.sc, e.outputs) by {reveal NPsValidAndInSc();}
  //  //assert NPsValidAndInSc(c, e.sc, e.inputs) by {reveal NPsValidAndInSc();}
  //  //assert MapFunctionValid(EtoMf(e)) by {reveal MapFunctionValid();}
  //  //assert EntityScOutputsInOutputs(c, e.sc, e.outputs) by {reveal EntityScOutputsInOutputs();}
  //  //assert EntityValid(c, e);
  //  e
  //}

  //function ComposeEntityInputs(c: Circuit, e1: Entity, e2: Entity): (r: set<NP>)
  //  requires ComposedValid(c, e1, e2)
  //  ensures forall np :: np in e1.finputs ==> np in r
  //{
  //  (e1.finputs + e2.finputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc)
  //}

  //lemma {:vcs_split_on_every_assert} ComposeEntityInputsCorrectHelper(c: Circuit, e1: Entity, e2: Entity)
  //  requires ComposedValid(c, e1, e2)
  //  ensures
  //    ScValid(c, e1.sc) &&
  //    ScValid(c, e2.sc) &&
  //    ScValid(c, e1.sc + e2.sc) &&
  //    NPBetweenSubcircuitsComplement(c, e1.sc + e2.sc, e1.sc + e2.sc) ==
  //      NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
  //      NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
  //      NPBetweenSubcircuits(c, e2.sc, e1.sc)
  //{
  //  assert ScValid(c, e1.sc);
  //  assert ScValid(c, e2.sc);
  //  assert ScValid(c, e1.sc + e2.sc) by {reveal ScValid();}
  //  assert NPBetweenSubcircuitsComplement(c, e1.sc + e2.sc, e1.sc + e2.sc) ==
  //      NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) + NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
  //      NPBetweenSubcircuits(c, e2.sc, e1.sc) - NPBetweenSubcircuits(c, e1.sc, e2.sc);
  //  assert NPBetweenSubcircuits(c, e1.sc, e2.sc) == {};
  //}

  //lemma ComposeEntityInputsCorrect(c: Circuit, e1: Entity, e2: Entity)
  //  requires ComposedValid(c, e1, e2)
  //  ensures ScValid(c, e1.sc + e2.sc)
  //  ensures
  //    ScInputBoundary(c, e1.sc + e2.sc) == ComposeEntityInputs(c, e1, e2)
  //{
  //  assert ScValid(c, e1.sc + e2.sc) && ScValid(c, e1.sc) && ScValid(c, e2.sc) by {
  //    reveal ScValid();
  //  }
  //  var ui := UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc);
  //  var nb :=  NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
  //             NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
  //             NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //  calc {
  //    ComposeEntityInputs(c, e1, e2);
  //    (e1.finputs + e2.finputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //    //{reveal EntityValid();}
  //    ScInputBoundary(c, e1.sc) + ScInputBoundary(c, e2.sc)
  //      - NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //    NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
  //      UnconnectedINPs(c, e1.sc) + InternalInputs(c, e1.sc) +
  //      NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) +
  //      UnconnectedINPs(c, e2.sc) + InternalInputs(c, e2.sc) -
  //      NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //    UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc) +
  //      NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
  //      NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
  //      NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //    {
  //      // Need to show that the terms in NPBetweenSubcircuits are not in Unconnected or Internal.
  //      assert forall np :: np in UnconnectedINPs(c, e1.sc + e2.sc) ==> np !in c.PortSource;
  //      reveal CircuitValid();
  //      assert forall np :: np in InternalInputs(c, e1.sc + e2.sc) ==> np !in c.PortSource;
  //      assert forall np :: np in NPBetweenSubcircuits(c, e2.sc, e1.sc) ==> np in c.PortSource;
  //    }
  //    UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc) +
  //      (NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
  //      NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
  //      NPBetweenSubcircuits(c, e2.sc, e1.sc));
  //    {ComposeEntityInputsCorrectHelper(c, e1, e2);}
  //    UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc) +
  //      NPBetweenSubcircuitsComplement(c, e1.sc + e2.sc, e1.sc + e2.sc);
  //    ScInputBoundary(c, e1.sc + e2.sc);
  //  }
  //}

  //lemma ONPNotInKnownsNotInKnowns2(c: Circuit, onp: NP, e1: Entity, e2: Entity, knowns: map<NP, bool>)
  //  requires ComposedValid(c, e1, e2)
  //  requires GoodKnownKeys(c, e1, e2, knowns)
  //  requires onp !in knowns
  //  requires ONPValid(c, onp)
  //  ensures onp !in CalculateE2Inputs(c, e1, e2, knowns)
  //{
  //  reveal GoodKnownKeys();
  //  assert (onp !in (e1.finputs + e2.finputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc));
  //  var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
  //  var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //  assert forall np :: np in knowns_2 ==> np in e2_inputs_from_e1_keys || np in knowns;
  //  assert onp !in e2_inputs_from_e1_keys by {
  //    reveal CircuitValid();
  //  }
  //}

  //opaque predicate GoodKnownKeys(c: Circuit, e1: Entity, e2: Entity, knowns: map<NP, bool>)
  //  requires ComposedValid(c, e1, e2)
  //{
  //  knowns.Keys == ComposeEntityInputs(c, e1, e2)
  //}

  //lemma InE1ButNotE1InputsNotInKnowns(c: Circuit, e1: Entity, e2: Entity, knowns: map<NP, bool>, np: NP)
  //  requires ComposedValid(c, e1, e2)
  //  requires GoodKnownKeys(c, e1, e2, knowns)
  //  requires np.n in e1.sc
  //  requires np !in e1.finputs
  //  ensures np !in knowns
  //{
  //  reveal GoodKnownKeys();
  //  reveal ScValid();
  //  InThisNotInThat(np.n, e1.sc, e2.sc);
  //  assert np.n !in e2.sc;
  //  assert knowns.Keys == (e1.finputs + e2.finputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //  //reveal EntityValid();
  //  //reveal NPsValidAndInSc();
  //  assert np !in e2.finputs;
  //}

  //lemma InE2ButNotE2InputsNotInKnowns(c: Circuit, e1: Entity, e2: Entity, knowns: map<NP, bool>, np: NP)
  //  requires ComposedValid(c, e1, e2)
  //  requires GoodKnownKeys(c, e1, e2, knowns)
  //  requires np.n in e2.sc
  //  requires np !in e2.finputs
  //  ensures np !in knowns
  //{
  //  reveal GoodKnownKeys();
  //  reveal ScValid();
  //  InThisNotInThat(np.n, e2.sc, e1.sc);
  //  assert np.n !in e1.sc;
  //  assert knowns.Keys == (e1.finputs + e2.finputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //  //reveal EntityValid();
  //  //reveal NPsValidAndInSc();
  //  assert np !in e2.finputs;
  //}

  //function CalculateE2Inputs(c: Circuit, e1: Entity, e2: Entity, knowns: map<NP, bool>): (r: map<NP, bool>)
  //  requires ComposedValid(c, e1, e2)
  //  requires GoodKnownKeys(c, e1, e2, knowns)
  //{
  //  reveal CircuitValid();
  //  reveal GoodKnownKeys();
  //  //var mf1 := EtoMf(e1);
  //  //var mf2 := EtoMf(e2);
  //  //assert MapFunctionValid(mf1);
  //  //assert MapFunctionValid(mf2);
  //  var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //  var e2_inputs_from_e1 := (map np | np in e2_inputs_from_e1_keys :: np := c.PortSource[np]);
  //  assert forall np :: np in e2_inputs_from_e1_keys ==> np in e2.finputs;
  //  //assert forall np :: np in e2_inputs_from_e1.Values ==> np in e1.foutputs by {
  //  //  reveal EntityScOutputsInOutputs();
  //  //}
  //  ////assert SetsNoIntersection(mf1.inputs+mf1.outputs, mf2.inputs+mf2.outputs) by {
  //  ////  reveal NPsValidAndInSc();
  //  ////}
  //  //GetInputs2(mf1, mf2, e2_inputs_from_e1, knowns)
  //  map[]
  //}

  //lemma CalculateE2InputsKeysCorrect(c: Circuit, e1: Entity, e2: Entity, knowns: map<NP, bool>)
  //  requires ComposedValid(c, e1, e2)
  //  requires GoodKnownKeys(c, e1, e2, knowns)
  //  ensures
  //    CalculateE2Inputs(c, e1, e2, knowns).Keys == e2.finputs
  //{
  //}

  //function ComposeEntityF(c: Circuit, e1: Entity, e2: Entity, combined_inputs: map<NP, bool>): (r: map<NP, bool>)
  //  requires ComposedValid(c, e1, e2)
  //  requires combined_inputs.Keys == ComposeEntityInputs(c, e1, e2)
  //{
  //  //reveal EntityValid();
  //  //var mf1 := MapFunction(e1.finputs, e1.foutputs, e1.f);
  //  //var mf2 := MapFunction(e2.finputs, e2.foutputs, e2.f);
  //  //assert MapFunctionValid(mf1);
  //  //assert MapFunctionValid(mf2);
  //  var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
  //  var e2_inputs_from_e1 := (map np | np in e2_inputs_from_e1_keys :: np := c.PortSource[np]);
  //  assert forall np :: np in e2_inputs_from_e1_keys ==> np in e2.finputs by {
  //    reveal CircuitValid();
  //  }
  //  assert forall np :: np in e2_inputs_from_e1.Values ==> np in e1.foutputs by {
  //    //reveal EntityScOutputsInOutputs();
  //    reveal CircuitValid();
  //  }
  //  //assert SetsNoIntersection(mf1.inputs+mf1.outputs, mf2.inputs+mf2.outputs) by {
  //  //  //reveal NPsValidAndInSc();
  //  //}
  //  //ComposeMapFunction(mf1, mf2, e2_inputs_from_e1, combined_inputs)
  //  map[]
  //}
}
module Connection {

  import opened Circ
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened Eval
  import opened ConservedSubcircuit
  import opened MapFunction

  opaque ghost predicate ConnectionValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
  {
    && (connection.Keys <= e2.mf.inputs * AllINPs(c, e2.sc))
    && (connection.Values <= e1.mf.outputs * AllONPs(c, e1.sc))
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
    ensures SetsNoIntersection(AllONPs(c, e1.sc), AllONPs(c, e2.sc))
  {
    reveal NPsInSc();
    reveal AllONPs();
    reveal AllINPs();
    reveal ConnInputs();
    reveal ConnOutputs();
    reveal UnconnInputs();
    assert NPsInSc(e1.sc, AllInputs(c, e1.sc));
    assert NPsInSc(e1.sc, AllONPs(c, e1.sc));
    assert NPsInSc(e2.sc, AllInputs(c, e2.sc));
    assert NPsInSc(e2.sc, AllONPs(c, e2.sc));
    NPSetsNoIntersection(c, e1, e2, connection, AllInputs(c, e1.sc), AllInputs(c, e2.sc));
    NPSetsNoIntersection(c, e1, e2, connection, AllONPs(c, e1.sc), AllONPs(c, e2.sc));
  }

  function ConnectEntitiesFInputs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>): (r: set<NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    // The inputs into e1 and e2, minus any inputs into e1 that came from e1
    ensures e1.mf.inputs <= r
  {
    e1.mf.inputs + (e2.mf.inputs - connection.Keys)
  }

  lemma MFNoIntersection(c: Circuit, e1: Entity, e2: Entity)
    requires CircuitValid(c)
    requires EntityValid(c, e1)
    requires EntityValid(c, e2)
    requires SetsNoIntersection(e1.sc, e2.sc)
    ensures SetsNoIntersection(e1.mf.state, e2.mf.state)
    ensures SetsNoIntersection(StateINPs(e1.mf.state), StateINPs(e2.mf.state))
    ensures SetsNoIntersection(StateONPs(e1.mf.state), StateONPs(e2.mf.state))
    ensures SetsNoIntersection(e1.mf.inputs, e2.mf.inputs)
    ensures SetsNoIntersection(e1.mf.outputs, e2.mf.outputs)
  {
    reveal MapFunctionValid();
    reveal EntitySomewhatValid();
    assert e1.mf.state <= e1.sc;
    assert e2.mf.state <= e2.sc;
    if exists n :: n in e1.mf.state && n in e2.mf.state {
      var n :| n in e1.mf.state && n in e2.mf.state;
      assert n in e1.sc && n in e2.sc;
      assert n in e1.sc * e2.sc;
      assert false;
    }
    reveal ConnInputs();
    reveal UnconnInputs();
    if exists np :: np in e1.mf.inputs && np in e2.mf.inputs {
      var np :| np in e1.mf.inputs && np in e2.mf.inputs;
      assert np.n in e1.sc && np.n in e2.sc;
      assert np.n in e1.sc * e2.sc;
      assert false;
    }
    reveal AllONPs();
    if exists np :: np in e1.mf.outputs && np in e2.mf.outputs {
      var np :| np in e1.mf.outputs && np in e2.mf.outputs;
      assert np.n in e1.sc && np.n in e2.sc;
      assert np.n in e1.sc * e2.sc;
      assert false;
    }
    assert SetsNoIntersection(e1.mf.state, e2.mf.state);
  }

  function {:vcs_split_on_every_assert} ConnectEntitiesF(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, fi: FI): (r: FO)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires fi.inputs.Keys == ConnectEntitiesFInputs(c, e1, e2, connection)
    requires fi.state.Keys == StateONPs(e1.mf.state + e2.mf.state)
    ensures r.outputs.Keys == e1.mf.outputs + e2.mf.outputs
    ensures r.state.Keys == StateINPs(e1.mf.state + e2.mf.state)
  {
    var inputs_1 := ExtractMap(fi.inputs, e1.mf.inputs);
    var state1 := ExtractMap(fi.state, StateONPs(e1.mf.state));
    var state2 := ExtractMap(fi.state, StateONPs(e2.mf.state));
    reveal MapFunctionValid();
    assert inputs_1.Keys == e1.mf.inputs;
    assert e1.mf.f.requires(FI(inputs_1, state1));
    var fo_1 := e1.mf.f(FI(inputs_1, state1));
    var outputs_1 := fo_1.outputs;
    assert connection.Values <= outputs_1.Keys by { reveal ConnectionValid(); }
    var outputs_1_to_2 := ExtractMap(outputs_1, connection.Values);
    var inputs_2_from_1 := (map np | np in connection :: np := outputs_1_to_2[connection[np]]);
    var combined_inputs := fi.inputs + inputs_2_from_1;
    var inputs_2 := ExtractMap(combined_inputs, e2.mf.inputs);
    var fo_2 := e2.mf.f(FI(inputs_2, state2));
    var outputs_2 := fo_2.outputs;
    assert outputs_2.Keys == e2.mf.outputs;
    OtherNoIntersection(c, e1, e2, connection);
    reveal EntitySomewhatValid();
    FOutputsInSc(c, e1);
    FOutputsInSc(c, e2);
    NPSetsNoIntersection(c, e1, e2, connection, outputs_1.Keys, outputs_2.Keys);
    MFNoIntersection(c, e1, e2);
    var combined_outputs := AddMaps(outputs_1, outputs_2);
    assert fo_1.state.Keys == StateINPs(e1.mf.state);
    assert fo_2.state.Keys == StateINPs(e2.mf.state);
    var new_state := AddMaps(fo_1.state, fo_2.state);
    FO(combined_outputs, new_state)
  }

  lemma RearrangeKnownKeys(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, knowns: map<NP, bool>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires knowns.Keys == e1.mf.inputs + (e2.mf.inputs - connection.Keys)
    ensures knowns.Keys == (e1.mf.inputs + e2.mf.inputs) - connection.Keys
  {
    ConnectionKeysInE2(c, e1, e2, connection);
    forall np | np in connection.Keys
      ensures np !in e1.mf.inputs
    {
      reveal NPsInSc();
      assert np.n in e2.sc;
      SetsNoIntersectionSymm(e1.sc, e2.sc);
      InThisNotInThat(np.n, e2.sc, e1.sc);
      assert np.n !in e1.sc;
      FInputsInSc(c, e1);
      assert np !in e1.mf.inputs;
    }
  }

  //function CalculateE2Inputs(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, fi: FI): (r: map<NP, bool>)
  //  requires ConnectEntitiesRequirements(c, e1, e2, connection)
  //  requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
  //{
  //  var fi_1 := FI(ExtractMap(fi.inputs, e1.mf.inputs), ExtractMap(fi.state, StateONPs(e1.mf.state)));
  //  reveal MapFunctionValid();
  //  var outputs_1 := e1.mf.f(fi_1).outputs;
  //  assert outputs_1.Keys == e1.mf.outputs;
  //  reveal ConnectionValid();
  //  assert connection.Values <= e1.mf.outputs;
  //  var connected := (map np | np in connection :: np := outputs_1[connection[np]]);
  //  assert connected.Keys == connection.Keys;
  //  assert fi.inputs.Keys == e1.mf.inputs + (e2.mf.inputs - connection.Keys);
  //  RearrangeKnownKeys(c, e1, e2, connection, fi.inputs);
  //  assert fi.inputs.Keys == (e1.mf.inputs + e2.mf.inputs) - connection.Keys;
  //  var combined_map := AddMaps(fi.inputs, connected);
  //  var inputs_2 := ExtractMap(combined_map, e2.mf.inputs);
  //  inputs_2
  //}

  lemma ConnectEntitiesFHelper(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>, fi: FI, np: NP)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    requires FIValid(fi, e1.mf.inputs + (e2.mf.inputs - connection.Keys), e1.mf.state + e2.mf.state)
    requires np in e2.mf.outputs
    ensures
      var state1 := ExtractMap(fi.state, StateONPs(e1.mf.state));
      var state2 := ExtractMap(fi.state, StateONPs(e2.mf.state));
      var knowns_2 := GetInputs2(e1.mf, e2.mf, connection, fi);
      && e2.mf.f.requires(FI(knowns_2, state2))
      && np in e2.mf.f(FI(knowns_2, state2)).outputs
      && e2.mf.f(FI(knowns_2, state2)).outputs[np] ==
          ConnectEntitiesF(c, e1, e2, connection, fi).outputs[np]
  {
    var state1 := ExtractMap(fi.state, StateONPs(e1.mf.state));
    var state2 := ExtractMap(fi.state, StateONPs(e2.mf.state));
    var inputs_1 := ExtractMap(fi.inputs, e1.mf.inputs);
    reveal MapFunctionValid();
    assert inputs_1.Keys == e1.mf.inputs;
    assert e1.mf.f.requires(FI(inputs_1, state1));
    var outputs_1 := e1.mf.f(FI(inputs_1, state1)).outputs;
    assert connection.Values <= outputs_1.Keys by { reveal ConnectionValid(); }
    var outputs_1_to_2 := ExtractMap(outputs_1, connection.Values);
    var inputs_2_from_1 := (map np | np in connection :: np := outputs_1_to_2[connection[np]]);
    var combined_inputs := fi.inputs + inputs_2_from_1;
    var inputs_2 := ExtractMap(combined_inputs, e2.mf.inputs);

    assert inputs_2 == GetInputs2(e1.mf, e2.mf, connection, fi);

    var outputs_2 := e2.mf.f(FI(inputs_2, state2)).outputs;
    assert outputs_2.Keys == e2.mf.outputs;
    OtherNoIntersection(c, e1, e2, connection);
    reveal EntitySomewhatValid();
    FOutputsInSc(c, e1);
    FOutputsInSc(c, e2);
    NPSetsNoIntersection(c, e1, e2, connection, outputs_1.Keys, outputs_2.Keys);
    var combined_outputs := AddMaps(outputs_1, outputs_2);
    assert combined_outputs == ConnectEntitiesF(c, e1, e2, connection, fi).outputs;
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
    && (forall np :: np in connection.Values && np.n in e.sc ==> np in e.mf.outputs)
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

  lemma MFNPsInSc(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntityValid(c, e)
    ensures NPsInSc(e.sc, MFNPs(e.mf))
  {
  }

  lemma ConnectEntitiesReqToConnectMapFunctionReq(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures ConnectMapFunctionRequirement(e1.mf, e2.mf, connection)
  {
    assert MapFunctionValid(e1.mf);
    assert MapFunctionValid(e2.mf);
    reveal ConnectionValid();
    assert (forall np :: np in connection.Keys ==> np in e2.mf.inputs);
    assert (forall np :: np in connection.Values ==> np in e1.mf.outputs);
    assert SetsNoIntersection(e1.sc, e2.sc);
    reveal EntitySomewhatValid();
    assert e1.mf.state <= e1.sc;
    assert e2.mf.state <= e2.sc;
    SubsetsNoIntersection(e1.sc, e2.sc, e1.mf.state, e2.mf.state);
    assert SetsNoIntersection(e1.mf.state, e2.mf.state);
    MFNPsInSc(c, e1);
    MFNPsInSc(c, e2);
    ScNoIntersectionNPsNoIntersection(e1.sc, e2.sc, MFNPs(e1.mf), MFNPs(e2.mf));
    assert SetsNoIntersection(MFNPs(e1.mf), MFNPs(e2.mf));
  }

  opaque function ConnectEntitiesImpl(
      c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>): (r: (Circuit, Entity))
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures CircuitValid(r.0)
  {
    assert connection.Keys <= e2.mf.inputs by {
      reveal ConnectionValid();
    }
    assert connection.Values <= e1.mf.outputs by {
      reveal ConnectionValid();
    }
    assert SetsNoIntersection(e1.mf.inputs + e1.mf.outputs, e2.mf.inputs + e2.mf.outputs) by {
      reveal ConnectionValid();
      assert SetsNoIntersection(e1.sc, e2.sc);
      reveal EntitySomewhatValid();
      FInputsInSc(c, e1);
      FInputsInSc(c, e2);
      FOutputsInSc(c, e1);
      FOutputsInSc(c, e2);
      reveal NPsInSc();
      assert forall np :: np in e1.mf.inputs + e1.mf.outputs ==> np.n in e1.sc;
      assert forall np :: np in e2.mf.inputs + e2.mf.outputs ==> np.n in e2.sc;
      if exists np :: np in e1.mf.inputs + e1.mf.outputs && np in e2.mf.inputs + e2.mf.outputs {
        var np :| np in e1.mf.inputs + e1.mf.outputs && np in e2.mf.inputs + e2.mf.outputs;
        assert np.n in e1.sc && np.n in e2.sc;
        assert np.n in e1.sc * e2.sc;
        assert false;
      }
    }
    assert SetsNoIntersection(e1.mf.state, e2.mf.state) by {
      reveal EntitySomewhatValid();
      SubsetsNoIntersection(e1.sc, e2.sc, e1.mf.state, e2.mf.state);
    }
    var mf := ConnectMapFunction(e1.mf, e2.mf, connection);
    var e := Entity(e1.sc + e2.sc, mf);

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
      && (AllONPs(new_c, e.sc) >= e.mf.outputs >= ConnOutputs(new_c, e.sc))
  {
    var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
    reveal ScValid();
    reveal ConnectEntitiesImpl();
    reveal AllONPs();
    reveal SeqOutputs();
    assert ConnOutputs(c, e.sc) == ConnOutputs(c, e1.sc) + ConnOutputs(c, e2.sc) by {
      reveal IsIsland();
      reveal ConnOutputs();
    }
    assert AllONPs(new_c, e.sc) == AllONPs(c, e1.sc) + AllONPs(c, e2.sc);
    assert ConnOutputs(c, e1.sc) == {} by {
      reveal IsIsland();
      reveal ConnOutputs();
    }
    ConnectEntitiesIsIsland(c, e1, e2,  connection);
    IsIslandNoOutputs(new_c, e.sc);
    IsIslandNoOutputs(c, e1.sc);
    IsIslandNoOutputs(c, e2.sc);

    assert e.mf.outputs >= ConnOutputs(c, e1.sc) + ConnOutputs(c, e2.sc) by {reveal EntitySomewhatValid();}
    assert e.mf.outputs <= AllONPs(c, e1.sc) + AllONPs(c, e2.sc) by {reveal EntitySomewhatValid();}

    assert AllONPs(c, e.sc) >= e.mf.outputs >= ConnOutputs(c, e.sc) by {reveal EntitySomewhatValid();}
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
      AllInputs(new_c, e.sc) == UnconnInputs(new_c, e.sc) + ConnInputs(new_c, e.sc);
      {
        reveal ScValid();
        reveal UnconnInputs();
        reveal ConnectEntitiesImpl();
        assert UnconnInputs(new_c, e.sc) == UnconnInputs(c, e.sc)-connection.Keys;
      }
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e.sc)-connection.Keys) + ConnInputs(new_c, e.sc);
      {
        ConnectEntitiesIsIsland(c, e1, e2,  connection);
        IsIslandNoInputs(new_c, e.sc);
        reveal IsIsland();
        reveal ConnInputs();
        assert |ConnInputs(new_c, e.sc)| == 0;
      }
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e.sc)-connection.Keys);
      {
        reveal SeqInputs();
        reveal ConnectEntitiesImpl();
        assert SeqInputs(new_c, e.sc) == SeqInputs(c, e.sc);
      }
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e.sc)-connection.Keys);
      {
        UnconnInputsAdd(c, e1.sc, e2.sc);
        reveal ConnectEntitiesImpl();
        assert UnconnInputs(c, e.sc) == UnconnInputs(c, e1.sc) + UnconnInputs(c, e2.sc);
      }
      AllInputs(new_c, e.sc) == ((UnconnInputs(c, e1.sc)+UnconnInputs(c, e2.sc))-connection.Keys);
      {
        ConnectionKeysInE2(c, e1, e2, connection);
        NPSetsNoIntersection(c, e1, e2, connection, UnconnInputs(c, e1.sc), connection.Keys);
        assert |UnconnInputs(c, e1.sc) * connection.Keys| == 0;
        ReorderSets2(UnconnInputs(c, e1.sc), UnconnInputs(c, e2.sc), connection.Keys);
      }
      AllInputs(new_c, e.sc) == UnconnInputs(c, e1.sc)+(UnconnInputs(c, e2.sc)-connection.Keys);
      AllInputs(new_c, e.sc) == (UnconnInputs(c, e1.sc) + ((UnconnInputs(c, e2.sc)-connection.Keys)));
      {
        ConnectionKeysINPs(c, e1, e2, connection);
      }
      AllInputs(new_c, e.sc) == UnconnInputs(c, e1.sc) + (UnconnInputs(c, e2.sc) - connection.Keys);
      {
        reveal IsIsland();
        reveal ConnInputs();
        assert |ConnInputs(c, e1.sc)| == 0;
        assert |ConnInputs(c, e2.sc)| == 0;
      }
      AllInputs(new_c, e.sc) == AllInputs(c, e1.sc) + (AllInputs(c, e2.sc) - connection.Keys);
      {
        reveal EntitySomewhatValid();
      }
      AllInputs(new_c, e.sc) == e1.mf.inputs + (e2.mf.inputs - connection.Keys);
      {
        reveal ConnectEntitiesImpl();
      }
      AllInputs(new_c, e.sc) == e.mf.inputs;
    }
    reveal EntitySomewhatValid();
    calc {
      e.mf.state;
      {reveal ConnectEntitiesImpl();}
      e1.mf.state + e2.mf.state;
      AllSeq(c, e1.sc) + AllSeq(c, e2.sc);
      {reveal AllSeq(); reveal ScValid();}
      AllSeq(c, e1.sc + e2.sc);
      {reveal ConnectEntitiesImpl();}
      AllSeq(c, e.sc);
      {
        reveal ConnectEntitiesImpl();
        assert c.NodeKind == new_c.NodeKind;
        reveal AllSeq();
      }
      AllSeq(new_c, e.sc);
    }
    assert ScValid(c, e.sc) by {
      reveal ScValid();
      reveal ConnectEntitiesImpl();
    }
    assert e.mf.state == AllSeq(new_c, e.sc);
    assert EntitySomewhatValid(new_c, e);
  }

  lemma ConnectEntitiesFValid(c: Circuit, e1: Entity, e2: Entity, connection: map<NP, NP>)
    requires ConnectEntitiesRequirements(c, e1, e2, connection)
    ensures
      var (new_c, e) := ConnectEntitiesImpl(c, e1, e2, connection);
      MapFunctionValid(e.mf)
  {
    reveal ConnectEntitiesImpl();
    reveal MapFunctionValid();
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
      assert (connection.Keys <= e2.mf.inputs * AllINPs(c, e2.sc));
      assert (connection.Values <= e1.mf.outputs * AllONPs(c, e1.sc));
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
      assert (connection.Keys <= e2.mf.inputs * AllINPs(c, e2.sc));
      assert (connection.Values <= e1.mf.outputs * AllONPs(c, e1.sc));
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

}
module IslandBundle {

  import opened Std.Wrappers

  import opened Circ
  import opened Entity
  import opened ConservedSubcircuit
  import opened Utils
  import opened Connection
  import opened ConnectionEval
  import opened Subcircuit
  import opened MapFunction
  import opened MapConnection
  import opened CombineParallel
  import opened CombineSeries

  // All nodes in the circuit are in exactly one Equiv.
  // This helps with reasoning about the circuit when adding stuff.

  datatype IslandBundle = IslandBundle(
    c: Circuit,
    bg: Circuit,
    es: seq<Option<Entity>>,
    NodeEquiv: map<CNode, nat>
  )

  ghost opaque predicate IslandBundleValid(eb: IslandBundle) {
    && CircuitValid(eb.c)
    && (forall e :: e in eb.es && e.Some? ==> EntityValid(eb.c, e.value))
    // All Equivs are islands (i.e. not connections in or out)
    && (forall e :: e in eb.es && e.Some? ==> IsIsland(eb.c, e.value.sc))
    // NodeEquiv points to an Entity in the eb.es seq.
    && (forall n :: n in eb.NodeEquiv ==> eb.NodeEquiv[n] < |eb.es|)
    // All nodes in an Entity must be pointed to from this NodeEquiv map
    && (forall index: nat :: index < |eb.es| && eb.es[index].Some? ==>
        (forall n :: n in eb.es[index].value.sc ==> n in eb.NodeEquiv && eb.NodeEquiv[n] == index))
    // The background nodes are not in any of the entities.
    && (eb.bg.NodeKind.Keys !! eb.NodeEquiv.Keys)
    && (eb.c.NodeKind.Keys == eb.bg.NodeKind.Keys + eb.NodeEquiv.Keys)
    && CircuitUnconnected(eb.bg, eb.c)
    && CircuitConserved(eb.bg, eb.c)
    && ScValid(eb.c, eb.bg.NodeKind.Keys)
  }

  function IslandBundleFromCircuit(c: Circuit): (eb: IslandBundle)
    requires CircuitValid(c)
    ensures IslandBundleValid(eb)
  {
    var eb := IslandBundle(c, c, [], map[]);
    reveal IslandBundleValid();
    reveal CircuitUnconnected();
    reveal CircuitConserved();
    reveal ScValid();
    eb
  }

  lemma IslandBundleToSetsNoIntersection(eb: IslandBundle, e1_index: nat, e2_index: nat)
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    ensures
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      SetsNoIntersection(e1.sc, e2.sc)
  {
    reveal IslandBundleValid();
  }

  lemma IsIslandToNoScOutputs(c: Circuit, sc: set<CNode>)
    requires CircuitValid(c)
    requires IsIsland(c, sc)
    ensures ScOutputBoundary(c, sc) == {}
  {
    reveal CircuitValid();
    reveal IsIsland();
  }

  lemma AddEntityCorrect(eb: IslandBundle, new_c: Circuit, new_e: Entity)
    requires IslandBundleValid(eb)
    requires CircuitConserved(eb.c, new_c)
    requires CircuitUnconnected(eb.c, new_c)
    requires CircuitValid(new_c)
    requires EntityValid(new_c, new_e)
    requires IsIsland(new_c, new_e.sc)
    requires forall n :: n in new_e.sc ==> n !in eb.NodeEquiv
    requires forall n :: n in new_e.sc ==> n !in eb.bg.NodeKind
    requires new_c.NodeKind.Keys == eb.c.NodeKind.Keys + new_e.sc
    ensures IslandBundleValid(AddEntityImpl(eb, new_c, new_e).0)
  {
    var (new_eb, ref) := AddEntityImpl(eb, new_c, new_e);
    assert CircuitValid(eb.c) && CircuitValid(new_eb.c) by {
      reveal IslandBundleValid();
    }
    forall index: nat | index < |eb.es| && eb.es[index].Some?
      ensures
        var e := eb.es[index].value;
        && EntityValid(new_c, e)
        && IsIsland(new_c, e.sc)
    {
      var e := eb.es[index].value;
      assert IsIsland(eb.c, e.sc) by {
        reveal IslandBundleValid();
      }
      assert EntityValid(eb.c, e) by {
        reveal IslandBundleValid();
      }
      assert ScValid(eb.c, e.sc) by {
      }
      assert ScValid(new_c, e.sc) by {
        reveal ScValid();
      }
      IsIslandConserved(eb.c, new_eb.c, e.sc);
      IsIslandToNoScOutputs(eb.c, e.sc);
      IsIslandToNoScOutputs(new_eb.c, e.sc);
      CircuitConservedToSubcircuitConserved(eb.c, new_eb.c, e.sc);
      assert SubcircuitConserved(eb.c, new_eb.c, e.sc);
      assert OutputsInFOutputs(new_eb.c, e) by {
        IsIslandNoOutputs(new_eb.c, e.sc);
        reveal IsIsland();
        reveal ConnOutputs();
        assert IsIsland(new_eb.c, e.sc);
        assert |ConnOutputs(new_eb.c, e.sc)| == 0;
      }
      EntityConserved(eb.c, new_eb.c, e);
      assert EntityValid(new_eb.c, e) by {
        reveal IslandBundleValid();
      }
    }
    assert IslandBundleValid(new_eb) by {
      reveal IslandBundleValid();
      reveal CircuitUnconnected();
      reveal CircuitConserved();
      reveal ScValid();
    }
  }

  function AddEntityImpl(eb: IslandBundle, new_c: Circuit, new_e: Entity): (r: (IslandBundle, nat))
    requires IslandBundleValid(eb)
    requires CircuitConserved(eb.c, new_c)
    requires CircuitUnconnected(eb.c, new_c)
    requires CircuitValid(new_c)
    requires EntityValid(new_c, new_e)
    requires IsIsland(new_c, new_e.sc)
    requires forall n :: n in new_e.sc ==> n !in eb.NodeEquiv
    requires new_c.NodeKind.Keys == eb.c.NodeKind.Keys + new_e.sc
    ensures r.1 < |r.0.es|
    ensures r.0.es[r.1].Some?
    ensures r.0.es[r.1].value == new_e
  {
    var new_node_equiv := (map n | n in new_e.sc :: n := |eb.es|);
    var new_eb := IslandBundle(
      new_c,
      eb.bg,
      eb.es + [Some(new_e)],
      AddMaps(eb.NodeEquiv, new_node_equiv)
    );
    (new_eb, |eb.es|)
  }

  function AddEntity(eb: IslandBundle, new_c: Circuit, new_e: Entity): (r: (IslandBundle, nat))
    requires IslandBundleValid(eb)
    requires SimpleInsertion(eb.c, new_c, new_e)
    ensures IslandBundleValid(r.0)
    ensures r.1 < |r.0.es|
    ensures r.0.es[r.1].Some?
    ensures r.0.es[r.1].value == new_e
  {
    reveal IslandBundleValid();
    AddEntityCorrect(eb, new_c, new_e);
    AddEntityImpl(eb, new_c, new_e)
  }

  lemma InThisENotInThatE(eb: IslandBundle, e1_index: nat, e2_index: nat, nps: set<NP>)
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires NPsInSc(eb.es[e1_index].value.sc, nps)
    ensures NPsNotInSc(eb.es[e2_index].value.sc, nps)
  {
    reveal NPsInSc();
    reveal NPsNotInSc();
    reveal IslandBundleValid();
    var sc1 := eb.es[e1_index].value.sc;
    var sc2 := eb.es[e2_index].value.sc;
  }

  lemma EntityBackgroundNoIntersection(eb: IslandBundle, e1_index: nat)
    requires IslandBundleValid(eb)
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    ensures eb.es[e1_index].value.sc !! eb.bg.NodeKind.Keys
  {
    reveal IslandBundleValid();
  }

  lemma IBConnectEntitiesRequirements(
      eb: IslandBundle, e1_index: nat, e2_index: nat, e12: Entity, conn: MFConnection)
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires conn.Valid()
    requires
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      ConnectEntitiesRequirements(eb.c, e1, e2, e12, conn)
    ensures
      ConnectCircuitRequirements(eb.c, conn.GetConnection())
  {
    var e1 := eb.es[e1_index].value;
    var e2 := eb.es[e2_index].value;
    reveal IslandBundleValid();
    InputsOfIslandNotInPortSource(eb.c, e2);
    assert ConnectEntitiesRequirements(eb.c, e1, e2, e12, conn);
    ConnectCircuitReqFromConnectEntitiesReq(eb.c, e1, e2, e12, conn);
  }


  function IBConnectEntitiesImpl(eb: IslandBundle, e1_index: nat, e2_index: nat, e12: Entity,
                                 conn: MFConnection): (r: (IslandBundle, nat))
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      ConnectEntitiesRequirements(eb.c, e1, e2, e12, conn)
    ensures |r.0.es| == |eb.es| + 1
    ensures r.1 < |r.0.es|
    ensures r.0.es[r.1].Some?
    ensures r.0.es[e1_index].None?
    ensures r.0.es[e2_index].None?
    ensures r.0.c.NodeKind == eb.c.NodeKind
  {
    var e1 := eb.es[e1_index].value;
    var e2 := eb.es[e2_index].value;
    //IBConnectEntitiesRequirements(eb, e1_index, e2_index, e12, conn);
    assert ConnectEntitiesRequirements(eb.c, e1, e2, e12, conn);
    var new_c := ConnectEntities(eb.c, e1, e2, e12, conn);
    assert EntityValid(new_c, e12);
    assert IsIsland(new_c, e12.sc);
    var new_es := seq(|eb.es|, (i: nat) requires i < |eb.es| =>
      if i == e1_index then None else if i == e2_index then None else eb.es[i]) + [Some(e12)];
    assert new_es[e1_index].None?;
    assert new_es[e2_index].None?;
    var new_node_equiv := (map n | n in eb.NodeEquiv :: if eb.NodeEquiv[n] == e1_index || eb.NodeEquiv[n] == e2_index
      then |new_es|-1 else eb.NodeEquiv[n]);
    var ib := IslandBundle(
      new_c,
      eb.bg,
      new_es,
      new_node_equiv
    );
    (ib, |new_es|-1)
  }

  lemma IBConnectEntitiesCorrect(eb: IslandBundle, e1_index: nat, e2_index: nat, e12: Entity, conn: MFConnection)
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      ConnectEntitiesRequirements(eb.c, e1, e2, e12, conn)
    ensures IslandBundleValid(IBConnectEntitiesImpl(eb, e1_index, e2_index, e12, conn).0)
  {
    var e1 := eb.es[e1_index].value;
    var e2 := eb.es[e2_index].value;
    IBConnectEntitiesRequirements(eb, e1_index, e2_index, e12, conn);
    var new_c := ConnectEntities(eb.c, e1, e2, e12, conn);
    assert new_c == ConnectCircuit(eb.c, conn.GetConnection()) by {
      reveal ConnectEntitiesImpl();
    }
    var (ib, e_index) := IBConnectEntitiesImpl(eb, e1_index, e2_index, e12, conn);
    reveal IslandBundleValid();
    assert CircuitValid(ib.c);
    assert ib.NodeEquiv == (map n | n in eb.NodeEquiv :: if eb.NodeEquiv[n] == e1_index || eb.NodeEquiv[n] == e2_index
      then |ib.es|-1 else eb.NodeEquiv[n]);
    forall index: nat | index < |ib.es|
      ensures ib.es[index].Some? ==> (
        var e := ib.es[index].value;
        && EntityValid(new_c, e)
        && IsIsland(new_c, e.sc)
        && (forall n :: n in ib.es[index].value.sc ==> n in ib.NodeEquiv && ib.NodeEquiv[n] == index)
      )
    {
      if index == e1_index {
        assert ib.es[index].None?;
      } else if index == e2_index {
        assert ib.es[index].None?;
      } else if index == |ib.es| -1 {
        assert ib.es[index] == Some(e12);
        assert EntityValid(new_c, e12);
        assert IsIsland(new_c, e12.sc);
        assert e12.sc == e1.sc + e2.sc by {
          reveal ConnectEntitiesImpl();
        }
        assert forall n :: n in e12.sc ==> (n in e1.sc) || (n in e2.sc);
        assert forall n :: n in e12.sc ==>
          (n in eb.NodeEquiv) && ((eb.NodeEquiv[n] == e1_index) || (eb.NodeEquiv[n] == e2_index)) by {
            reveal IslandBundleValid();
          }
        assert forall n :: n in e12.sc ==> n in ib.NodeEquiv && ib.NodeEquiv[n] == index;
      } else {
        assert ib.es[index] == eb.es[index];
        if eb.es[index].Some? {
          var e := eb.es[index].value;
          var connection := conn.GetConnection();
          assert NPsNotInSc(e.sc, connection.Keys) by {
            FInputsInSc(eb.c, e2);
            assert NPsInSc(e2.sc, connection.Keys) by { reveal NPsInSc(); }
            InThisENotInThatE(eb, e2_index, index, connection.Keys);
            assert NPsNotInSc(e.sc, connection.Keys);
          }
          assert NPsNotInSc(e.sc, connection.Values) by {
            FOutputsInSc(eb.c, e1);
            assert NPsInSc(e1.sc, connection.Values) by { reveal NPsInSc(); }
            InThisENotInThatE(eb, e1_index, index, connection.Values);
            assert NPsNotInSc(e.sc, connection.Values);
          }
          assert NoInternalConnections(connection, e.sc) by {
            reveal NoInternalConnections();
            reveal NPsNotInSc();
          }
          ConnectCircuitConservesSubcircuit(eb.c, connection, e.sc);
          assert EntityValid(new_c, e) by {
            reveal ScValid();
            reveal SubcircuitConserved();
            reveal ConnectEntitiesImpl();
            ConnectEntitiesOtherConnUnchanged(eb.c, connection, e);
            assert OutputsInFOutputs(new_c, e) by {
              reveal EntitySomewhatValid();
            }
            EntityConserved(eb.c, new_c, e);
          }
          ConnectCircuitOtherIsIsland(eb.c, connection, e);
          assert IsIsland(new_c, e.sc);
          assert forall n :: n in e.sc ==> n in ib.NodeEquiv && ib.NodeEquiv[n] == index by {
            reveal IslandBundleValid();
          }
        }
      }
    }
    assert (forall e :: e in ib.es && e.Some? ==> EntityValid(ib.c, e.value));
    assert (forall e :: e in ib.es && e.Some? ==> IsIsland(ib.c, e.value.sc));
    assert (forall n :: n in ib.NodeEquiv ==> ib.NodeEquiv[n] < |ib.es|);
    assert (forall index: nat :: index < |ib.es| && ib.es[index].Some? ==>
     (forall n :: n in ib.es[index].value.sc ==> n in ib.NodeEquiv && ib.NodeEquiv[n] == index));
    assert IslandBundleValid(ib) by {
      reveal CircuitUnconnected();
      reveal CircuitConserved();
      reveal ConnectEntitiesImpl();
      var connection := conn.GetConnection();
      ConnectionInSc(eb.c, e1, e2, e12, conn);
      assert NPsInSc(e2.sc, connection.Keys);
      assert NPsInSc(e1.sc, connection.Values);
      EntityBackgroundNoIntersection(eb, e1_index);
      EntityBackgroundNoIntersection(eb, e2_index);
      assert NoInternalConnections(connection, eb.bg.NodeKind.Keys) by {
       reveal NPsInSc();
       reveal NoInternalConnections();
      }
      ConnectCircuitConservesSubcircuit(eb.c, connection, eb.bg.NodeKind.Keys);
      reveal IslandBundleValid();
      var bg := eb.bg;
      assert bg == ib.bg;
      forall np | np in ib.c.PortSource && np !in bg.PortSource
        ensures np.n !in ib.bg.NodeKind && ib.c.PortSource[np].n !in ib.bg.NodeKind
      {
        if np in eb.c.PortSource {
          assert np.n !in bg.NodeKind && eb.c.PortSource[np].n !in bg.NodeKind;
          assert np.n !in bg.NodeKind && ib.c.PortSource[np].n !in bg.NodeKind;
        } else {
          assert ib.c.PortSource.Keys == eb.c.PortSource.Keys + connection.Keys;
          assert np in connection.Keys;
          reveal NPsInSc();
          assert np.n in e2.sc;
          assert np.n !in ib.bg.NodeKind;
          assert ib.c.PortSource[np] in connection.Values;
          assert ib.c.PortSource[np].n in e1.sc;
          assert ib.c.PortSource[np].n !in ib.bg.NodeKind;
        }
      }
      assert (forall np :: np in eb.c.PortSource && np !in eb.bg.PortSource ==> np.n !in eb.bg.NodeKind && eb.c.PortSource[np].n !in eb.bg.NodeKind);
      assert (forall np :: np in ib.c.PortSource && np !in ib.bg.PortSource ==> np.n !in ib.bg.NodeKind && ib.c.PortSource[np].n !in ib.bg.NodeKind);
      assert CircuitUnconnected(ib.bg, ib.c);
      assert CircuitConserved(ib.bg, ib.c);
      assert ScValid(ib.c, ib.bg.NodeKind.Keys) by {
        reveal ScValid();
      }
    }
  }

  function IBConnectEntities(eb: IslandBundle, e1_index: nat, e2_index: nat, e12: Entity,
                             conn: MFConnection): (r: (IslandBundle, nat))
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      ConnectEntitiesRequirements(eb.c, e1, e2, e12, conn)
    ensures IslandBundleValid(r.0)
  {
    IBConnectEntitiesCorrect(eb, e1_index, e2_index, e12, conn);
    IBConnectEntitiesImpl(eb, e1_index, e2_index, e12, conn)
  }

  opaque function IBCombineParallelEntities(eb: IslandBundle, e1_index: nat, e2_index: nat): (r: (IslandBundle, nat))
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      CombineParallelEntitiesRequirements(eb.c, e1, e2)
    ensures IslandBundleValid(r.0)
    ensures |r.0.es| == |eb.es| + 1
    ensures r.1 < |r.0.es|
    ensures r.0.es[r.1].Some?
    ensures r.0.es[e1_index].None?
    ensures r.0.es[e2_index].None?
    ensures r.0.c.NodeKind == eb.c.NodeKind
    ensures
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      var e := r.0.es[r.1].value;
      && (e.mf.inputs == e1.mf.inputs + e2.mf.inputs)
      && (e.mf.outputs == e1.mf.outputs + e2.mf.outputs)
      && (e.mf.state == e1.mf.state + e2.mf.state)
      && (e.sc == e1.sc + e2.sc)
      && (e1.mf.NPs() !! e2.mf.NPs())
      && (Seq.ToSet(e1.mf.state) !! Seq.ToSet(e2.mf.state))
      && (e.mf == ParallelCombiner(e1.mf, e2.mf).mf())
    ensures
      forall index: nat :: index < |eb.es| && index != e1_index && index != e2_index ==> eb.es[index] == r.0.es[index]
    ensures eb.bg == r.0.bg
  {
    var e1 := eb.es[e1_index].value;
    var e2 := eb.es[e2_index].value;
    var (e12, conn) := CombineParallelEntityConn(eb.c, e1, e2);
    IBConnectEntitiesCorrect(eb, e1_index, e2_index, e12, conn);
    IBConnectEntitiesImpl(eb, e1_index, e2_index, e12, conn)
  }

  opaque function IBCombineSeriesEntities(eb: IslandBundle, e1_index: nat, e2_index: nat): (r: (IslandBundle, nat))
    requires IslandBundleValid(eb)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      CombineSeriesEntitiesRequirements(eb.c, e1, e2)
    ensures IslandBundleValid(r.0)
    ensures |r.0.es| == |eb.es| + 1
    ensures r.1 < |r.0.es|
    ensures r.0.es[r.1].Some?
    ensures r.0.es[e1_index].None?
    ensures r.0.es[e2_index].None?
    ensures r.0.c.NodeKind == eb.c.NodeKind
    ensures eb.bg == r.0.bg
    ensures
      var e1 := eb.es[e1_index].value;
      var e2 := eb.es[e2_index].value;
      var e := r.0.es[r.1].value;
      && (e.mf.inputs == e1.mf.inputs)
      && (e.mf.outputs == e2.mf.outputs)
      && (e.mf.state == e1.mf.state + e2.mf.state)
      && (e.sc == e1.sc + e2.sc)
      && (e1.mf.NPs() !! e2.mf.NPs())
      && (Seq.ToSet(e1.mf.state) !! Seq.ToSet(e2.mf.state))
      && (e.mf == SeriesCombiner(e1.mf, e2.mf).mf())
  {
    var e1 := eb.es[e1_index].value;
    var e2 := eb.es[e2_index].value;
    var (e12, conn) := CombineSeriesEntityConn(eb.c, e1, e2);
    IBConnectEntitiesCorrect(eb, e1_index, e2_index, e12, conn);
    IBConnectEntitiesImpl(eb, e1_index, e2_index, e12, conn)
  }

  function IBSwapMF(eb: IslandBundle, e_index: nat, mf: MapFunction): (r: IslandBundle)
    requires IslandBundleValid(eb)
    requires e_index < |eb.es| && eb.es[e_index].Some?
    requires mf.Valid()
    requires
      var e := eb.es[e_index].value;
      assert e.mf.Valid() by {reveal IslandBundleValid();}
      MapFunctionsEquiv(e.mf, mf)
    ensures IslandBundleValid(r)
  {
    var e := eb.es[e_index].value;
    assert CircuitValid(eb.c) && EntityValid(eb.c, e) by {
      reveal IslandBundleValid();
    }
    var new_e := EntitySwapMF(eb.c, e, mf);
    var new_eb := IslandBundle(
      eb.c,
      eb.bg,
      eb.es[e_index := Some(new_e)],
      eb.NodeEquiv
      );
    assert IslandBundleValid(new_eb) by {
      reveal IslandBundleValid();
    }
    new_eb
  }

  function IBInsert(ib: IslandBundle, ei: EntityInserter): (r: (IslandBundle, nat))
    requires IslandBundleValid(ib)
    requires ei.Valid()
    ensures IslandBundleValid(r.0)
    ensures r.1 < |r.0.es|
    ensures r.0.es[r.1].Some?
    ensures SimpleInsertion(ib.c, r.0.c, r.0.es[r.1].value)
  {
    reveal IslandBundleValid();
    ei.ValidForCircuit(ib.c);
    var (new_c, e) := ei.fn(ib.c);
    AddEntity(ib, new_c, e)
  }

  function InsertTwoInSeries(c: Circuit, ei_a: EntityInserter, ei_b: EntityInserter): (r: (Circuit, Entity))
    requires CircuitValid(c)
    requires ei_a.Valid()
    requires ei_b.Valid()
    requires ei_a.rf.output_width == ei_b.rf.input_width
    ensures SimpleInsertion(c, r.0, r.1)
    ensures
      reveal EntityInserter.Valid();
      CombineSeriesRF(ei_a.rf, ei_b.rf).MFConsistent(r.1.mf)
  {
    var join_width := ei_a.rf.output_width;

    var ib := IslandBundleFromCircuit(c);
    var (ib_a, ref_a) := IBInsert(ib, ei_a);
    var e_a := ib_a.es[ref_a].value;
    assert ei_a.rf.Valid() && ei_a.rf.MFConsistent(e_a.mf) by {
      reveal EntityInserter.Valid();
      ei_a.ValidForCircuit(ib.c);
    }
    assert |e_a.mf.outputs| == join_width by {
      reveal EntityInserter.Valid();
      reveal RFunction.MFConsistent();
    }

    var (ib_b, ref_b) := IBInsert(ib_a, ei_b);
    assert e_a == ib_b.es[ref_a].value;
    var e_b := ib_b.es[ref_b].value;
    assert |e_b.mf.inputs| == join_width by {
      reveal EntityInserter.Valid();
      reveal RFunction.MFConsistent();
    }
    assert ei_b.rf.Valid() && ei_b.rf.MFConsistent(e_b.mf) by {
      reveal EntityInserter.Valid();
      ei_b.ValidForCircuit(ib_a.c);
    }

    assert CombineSeriesEntitiesRequirements(ib_b.c, e_a, e_b) by {
      reveal IslandBundleValid();
    }
    var (ib_combined, ref_combined) := IBCombineSeriesEntities(ib_b, ref_a, ref_b);
    var e_combined := ib_combined.es[ref_combined].value;
    assert e_combined.mf == SeriesCombiner(e_a.mf, e_b.mf).mf();

    assert CombineSeriesRF(ei_a.rf, ei_b.rf).MFConsistent(e_combined.mf) by {
      reveal RFunction.MFConsistent();
      reveal MapFunction.Valid();
    }

    reveal IslandBundleValid();

    (ib_combined.c, e_combined)
  }

}
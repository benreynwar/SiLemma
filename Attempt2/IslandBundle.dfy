module IslandBundle {

  import opened Std.Wrappers

  import opened Circ
  import opened Entity
  import opened ConservedSubcircuit
  import opened Utils
  import opened Connection
  import opened ConnectionEval
  import opened Subcircuit

  // All nodes in the circuit are in exactly one Equiv.
  // This helps with reasoning about the circuit when adding stuff.

  datatype IslandBundle = IslandBundle(
    c: Circuit,
    es: seq<Option<Entity>>,
    NodeEquiv: map<CNode, nat>
  )

  ghost opaque predicate IslandBundleValid(eb: IslandBundle) {
    && CircuitValid(eb.c)
    && (forall e :: e in eb.es && e.Some? ==> EntityValid(eb.c, e.value))
    // All Equivs are islands (i.e. not connections in or out)
    && (forall e :: e in eb.es && e.Some? ==> IsIsland(eb.c, e.value.sc))
    // NodeEquiv points to an Equiv in the eb.es seq.
    && (forall n :: n in eb.NodeEquiv ==> eb.NodeEquiv[n] < |eb.es|)
    // All nodes in an Equiv must be pointed to from this NodeEquiv map
    && (forall index: nat :: index < |eb.es| && eb.es[index].Some? ==>
        (forall n :: n in eb.es[index].value.sc ==> n in eb.NodeEquiv && eb.NodeEquiv[n] == index))
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
      eb.es + [Some(new_e)],
      AddMaps(eb.NodeEquiv, new_node_equiv)
    );
    (new_eb, |eb.es|)
  }

  function AddEntity(eb: IslandBundle, new_c: Circuit, new_e: Entity): (r: (IslandBundle, nat))
    requires IslandBundleValid(eb)
    requires CircuitConserved(eb.c, new_c)
    requires CircuitUnconnected(eb.c, new_c)
    requires CircuitValid(new_c)
    requires EntityValid(new_c, new_e)
    requires IsIsland(new_c, new_e.sc)
    requires forall n :: n in new_e.sc ==> n !in eb.NodeEquiv
    requires new_c.NodeKind.Keys == eb.c.NodeKind.Keys + new_e.sc
    ensures IslandBundleValid(r.0)
    ensures r.1 < |r.0.es|
    ensures r.0.es[r.1].Some?
    ensures r.0.es[r.1].value == new_e
  {
    AddEntityCorrect(eb, new_c, new_e);
    AddEntityImpl(eb, new_c, new_e)
  }

  function ComposeEquivsImpl(
      eb: IslandBundle, new_c: Circuit, e1_index: nat, e2_index: nat,
      connection: map<NP, NP>): (r: IslandBundle)
    requires IslandBundleValid(eb)
    requires CircuitConserved(eb.c, new_c)
    requires CircuitUnconnected(eb.c, new_c)
    requires CircuitValid(new_c)
    requires e1_index != e2_index
    requires e1_index < |eb.es| && eb.es[e1_index].Some?
    requires e2_index < |eb.es| && eb.es[e2_index].Some?
    requires ScValid(eb.c, eb.es[e1_index].value.sc)
    requires ScValid(eb.c, eb.es[e2_index].value.sc)
    requires ConnectionValid(eb.c, eb.es[e1_index].value, eb.es[e2_index].value, connection)
  {
    assert CircuitValid(eb.c) by {
      reveal IslandBundleValid();
    }
    var e1 := eb.es[e1_index].value;
    var e2 := eb.es[e2_index].value;
    assert SetsNoIntersection(e1.sc, e2.sc) by {
      IslandBundleToSetsNoIntersection(eb, e1_index, e2_index);
    }
    assert ScValid(eb.c, e1.sc) &&  ScValid(eb.c, e2.sc) by {
      reveal IslandBundleValid();
      reveal ScValid();
    }
    assert EntityValid(eb.c, e1) && EntityValid(eb.c, e2) by {
      reveal IslandBundleValid();
    }


    assert IsIsland(eb.c, e2.sc) && IsIsland(eb.c, e1.sc) by {
      reveal IslandBundleValid();
    }
    var (new_c, new_e) := ConnectEntities(eb.c, e1, e2, connection);
    var new_es := seq(|eb.es|, (index: nat) requires index < |eb.es| => (
      if (index == e1_index || index == e2_index) then None else eb.es[index])) + [Some(new_e)];
    var new_index := |new_es|-1;
    var new_node_equiv := (map key | key in eb.NodeEquiv.Keys :: if key in new_e.sc then new_index else eb.NodeEquiv[key]);
    var new_eb := IslandBundle(
      new_c,
      new_es,
      new_node_equiv
    );
    new_eb
  }

}
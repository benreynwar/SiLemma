module Inserters.AndTree{

  import opened Std.Wrappers

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Utils
  import opened Entity
  import opened MapFunction
  import opened ConnectionEval
  import opened Connection
  import opened IslandBundle
  import opened Subcircuit
  import opened MapConnection
  import opened CombineParallel
  import opened CombineSeries

  import opened And
  import opened Ident
  import opened Const

  function SubTreeSizes(n: nat): (r: (nat, nat))
    requires n > 2
    ensures r.0 + r.1 == n
    ensures r.0 > 0
    ensures r.1 > 0
    ensures r.1 >= r.0
  {
    var p := if n % 2 == 0 then n/2 else (n-1)/2;
    var q := n - p;
    (p, q)
  }

  function AndTreeBehav(a: seq<bool>): bool
  {
    if |a| == 0 then
      true
    else if |a| == 1 then
      a[0]
    else if |a| == 2 then
      a[0] && a[1]
    else
      var n := |a|;
      var p := SubTreeSizes(n).0;
      AndTreeBehav(a[..p]) && AndTreeBehav(a[p..])
  }

  function AndTreeSF(n: nat, si: SI): (so: SO)
    requires |si.inputs| == n
    requires |si.state| == 0
  {
    SO([AndTreeBehav(si.inputs)], [])
  }

  ghost predicate MFReqs(n: nat, mf_a: MapFunction, mf_b: MapFunction, mf_and: MapFunction, mf_combined: MapFunction)
  {
    && n > 2
    && var p := SubTreeSizes(n).0;
    && AndTreeMFValid(p, mf_a)
    && AndTreeMFValid(n-p, mf_b)
    && AndMFValid(mf_and)
    && AndTreeMFValid(n, mf_combined)
    && mf_a.NPs() !! mf_b.NPs()
    && mf_combined.inputs == mf_a.inputs + mf_b.inputs
    && mf_and.inputs == mf_and.inputs == mf_a.outputs + mf_b.outputs
    && mf_combined.outputs == mf_and.outputs
  }

  ghost predicate AndTreeMFValid(n: nat, mf: MapFunction)
  {
    && mf.Valid()
    && (|mf.inputs| == n)
    && (|mf.state| == 0)
    && (|mf.outputs| == 1)
    && (forall si :: SIValid(si, mf.inputs, mf.state) ==> (
      && mf.sf.requires(si)
      && (mf.sf(si) == AndTreeSF(n, si))))
  }

  function AndTreeMFImpl(n: nat, inputs: seq<NP>, output: NP): (mf: MapFunction)
    requires |inputs| == n
    requires Seq.HasNoDuplicates(inputs)
    requires output !in inputs
    ensures mf.Valid()
    ensures AndTreeMFValid(n, mf)
  {
    reveal MapFunction.Valid();
    reveal Seq.HasNoDuplicates();
    reveal Seq.ToSet();
    MapFunction(
      inputs,
      [output],
      [],
      (si: SI) requires SIValid(si, inputs, []) => AndTreeSF(n, si)
    )
  }

  function AndTreeMFFromEntities(c: Circuit, n: nat, e_left: Entity, e_right: Entity, e_and: Entity): (mf: MapFunction)
    requires
      && n > 2
      && var p := SubTreeSizes(n).0;
      && c.Valid()
      && (e_left.sc !! e_right.sc)
      && (e_left.sc !! e_and.sc)
      && (e_right.sc !! e_and.sc)
      && EntityValid(c, e_left)
      && EntityValid(c, e_right)
      && EntityValid(c, e_and)
      && AndTreeMFValid(p, e_left.mf)
      && AndTreeMFValid(n-p, e_right.mf)
      //&& AndTreeMFValid(n, mf)
      && AndMFValid(e_and.mf)
      //&& mf.Valid()
      //&& (mf.inputs == e_left.mf.inputs + e_right.mf.inputs)
      //&& (mf.outputs == e_and.mf.outputs)
    ensures
      && reveal Seq.ToSet();
      && (e_left.mf.NPs() !! e_right.mf.NPs())
      && var mf_top := ParallelCombiner(e_left.mf, e_right.mf).mf();
      && var series_combiner := SeriesCombiner(mf_top, e_and.mf);
      && series_combiner.Valid()
      && var mf_final := series_combiner.mf();
      && mf_final.Valid()
      && mf.Valid()
      && AndTreeMFValid(n, mf)
      && MapFunctionsEquiv(mf_final, mf)
  {
    assert e_left.sc !! e_right.sc;
    assert e_left.sc !! e_and.sc;
    assert e_right.sc !! e_and.sc;
    assert EntityValid(c, e_left) && EntityValid(c, e_right) && EntityValid(c, e_and) by {
      reveal IslandBundleValid();
    }
    FAllInSc(c, e_left);
    FAllInSc(c, e_right);
    FAllInSc(c, e_and);
    ScNoIntersectionNPsNoIntersection(e_left.sc, e_right.sc, e_left.mf.NPs(), e_right.mf.NPs());
    ScNoIntersectionNPsNoIntersection(e_left.sc, e_and.sc, e_left.mf.NPs(), e_and.mf.NPs());
    ScNoIntersectionNPsNoIntersection(e_right.sc, e_and.sc, e_right.mf.NPs(), e_and.mf.NPs());
    assert e_and.mf.outputs[0] !in e_left.mf.inputs + e_right.mf.inputs by {
      reveal Seq.ToSet();
      assert Seq.ToSet(e_and.mf.outputs) <= e_and.mf.NPs();
      assert Seq.ToSet(e_left.mf.inputs) <= e_left.mf.NPs();
      assert Seq.ToSet(e_right.mf.inputs) <= e_right.mf.NPs();
      assert e_and.mf.outputs[0] !in Seq.ToSet(e_left.mf.inputs) + Seq.ToSet(e_right.mf.inputs);
      assert e_and.mf.outputs[0] !in Seq.ToSet(e_left.mf.inputs + e_right.mf.inputs);
      assert e_and.mf.outputs[0] !in e_left.mf.inputs + e_right.mf.inputs;
    }
    assert Seq.HasNoDuplicates(e_left.mf.inputs + e_right.mf.inputs) by {
      reveal MapFunction.Valid();
      NoDuplicatesInConcat(e_left.mf.inputs, e_right.mf.inputs);
    }
    var mf := AndTreeMFImpl(n, e_left.mf.inputs + e_right.mf.inputs, e_and.mf.outputs[0]);
    AndTreeMFCorrect(n, e_left.mf, e_right.mf, e_and.mf, mf);
    mf
  }

  lemma AndTreeMFCorrect(n: nat, mf_left: MapFunction, mf_right: MapFunction, mf_and: MapFunction, mf: MapFunction)
    // Show the equivalence of a map function that gets built by doing combine parallel and combine series
    // and the simpler map function that we'd like to replace it with.
    requires
      && n > 2
      && var p := SubTreeSizes(n).0;
      && AndTreeMFValid(p, mf_left)
      && AndTreeMFValid(n-p, mf_right)
      && AndTreeMFValid(n, mf)
      && AndMFValid(mf_and)
      && mf_left.NPs() !! mf_right.NPs()
      && mf_left.NPs() !! mf_and.NPs()
      && mf_right.NPs() !! mf_and.NPs()
      && mf.Valid()
      && mf.inputs == mf_left.inputs + mf_right.inputs
      && mf.outputs == mf_and.outputs
    ensures
      && reveal Seq.ToSet();
      && var mf_top := ParallelCombiner(mf_left, mf_right).mf();
      && var series_combiner := SeriesCombiner(mf_top, mf_and);
      && series_combiner.Valid()
      && var mf_final := series_combiner.mf();
      && mf_final.Valid()
      && MapFunctionsEquiv(mf_final, mf)
  {
    var p := SubTreeSizes(n).0;
    reveal Seq.ToSet();
    var mf_top := ParallelCombiner(mf_left, mf_right).mf();
    var series_combiner := SeriesCombiner(mf_top, mf_and);
    assert series_combiner.Valid() by {
      assert mf_top.Valid();
      assert mf_and.Valid();
      assert mf_top.NPs() <= mf_left.NPs() + mf_right.NPs() by {
        reveal  Seq.ToSet();
      }
      assert (mf_top.NPs() !! mf_and.NPs());
      assert (Seq.ToSet(mf_top.state) !! Seq.ToSet(mf_and.state));
      assert (|mf_top.outputs| == |mf_and.inputs|);
    }
    var mf_final := series_combiner.mf();
    assert mf_final.inputs == mf.inputs;
    assert mf_final.outputs == mf.outputs;
    assert mf_final.state == mf.state;
    forall fi: FI | FIValid(fi, mf.inputs, mf.state)
      ensures mf_final.f(fi) == mf.f(fi)
    {
      var si := mf.fi2si(fi);
      assert mf.sf(si) == AndTreeSF(n, si);
      var si_left := SI(si.inputs[..p], []);
      var si_right := SI(si.inputs[p..], []);
      reveal MapFunction.Valid();
      assert |si_left.inputs| == |mf_left.inputs|;
      assert |si_left.state| == |mf_left.state|;
      var so_left := mf_left.sf(si_left);
      var so_right := mf_right.sf(si_right);
      var so_top := mf_top.sf(si);
      assert so_top == SO(so_left.outputs + so_right.outputs, []);
      var si_and := SI(so_left.outputs + so_right.outputs, []);
      assert SIValid(si_and, mf_and.inputs, mf_and.state);
      var so_and := mf_and.sf(si_and);
      var so := SO(so_and.outputs, []);

      assert so == mf_final.sf(si);

      assert mf_final.sf(si) == mf.sf(si);
      assert mf_final.f(fi) == mf.f(fi);
    }
    reveal MapFunctionsEquiv();
  }

  opaque function InsertAndTreeHelper(c: Circuit, n: nat): (r: (Circuit, Entity, MapFunction))
    requires c.Valid()
    requires n > 2
    ensures r.0.Valid()
    ensures EntityValid(r.0, r.1)
    ensures CircuitUnconnected(c, r.0)
    ensures CircuitConserved(c, r.0)
    ensures IsIsland(r.0, r.1.sc)
    ensures r.0.NodeKind.Keys == c.NodeKind.Keys + r.1.sc
    ensures c.NodeKind.Keys !! r.1.sc
    ensures |r.2.inputs| == n
    ensures |r.2.outputs| == 1
    ensures r.2.Valid()
    ensures MapFunctionsEquiv(r.1.mf, r.2)
    ensures AndTreeMFValid(n, r.2)
    decreases n, 0
  {
    reveal SimpleInsertion();

    var p := SubTreeSizes(n).0;
    var eb1 := IslandBundleFromCircuit(c);

    // Insert the left part of the tree.
    var (c1, e_left) := InsertAndTreeImpl(c, p);
    var (eb2, ref_left) := AddEntity(eb1, c1, e_left);

    // Insert the right part of the tree.
    var (c2, e_right) := InsertAndTreeImpl(c1, n-p);
    var (eb3, ref_right) := AddEntity(eb2, c2, e_right);

    // Insert an 'and' connecting them.
    var (c3, e_and) := InsertAnd(c2);
    var (eb4, ref_and) := AddEntity(eb3, c3, e_and);

    // Join the left and rights parts in parallel
    assert CombineParallelEntitiesRequirements(eb4.c, e_left, e_right) by {
      reveal IslandBundleValid();
    }
    var (eb5, ref_top) := IBCombineParallelEntities(eb4, ref_left, ref_right);
    var e_top := eb5.es[ref_top].value;

    // Join the and on

    assert CombineSeriesEntitiesRequirements(eb5.c, e_top, e_and) by {
      reveal IslandBundleValid();
      assert EntityValid(eb5.c, e_top);
      assert e_and == eb5.es[ref_and].value;
      assert EntityValid(eb5.c, e_and);
    }
    var (eb6, ref_final) := IBCombineSeriesEntities(eb5, ref_top, ref_and);
    var e_final := eb6.es[ref_final].value;

    var mf := AndTreeMFFromEntities(eb4.c, n, e_left, e_right, e_and);

    assert CircuitUnconnected(c, eb6.c) by {
      reveal IslandBundleValid();
    }
    assert CircuitConserved(c, eb6.c) by {
      reveal IslandBundleValid();
    }

    assert eb6.c.NodeKind.Keys == c.NodeKind.Keys + e_final.sc by {
      calc {
        c1.NodeKind.Keys == c.NodeKind.Keys + e_left.sc;
        c2.NodeKind.Keys == c1.NodeKind.Keys + e_right.sc;
        c2.NodeKind.Keys == c.NodeKind.Keys + e_left.sc + e_right.sc;
        c3.NodeKind.Keys == c2.NodeKind.Keys + e_and.sc;
        c3.NodeKind.Keys == c.NodeKind.Keys + e_and.sc + e_left.sc + e_right.sc;
        eb5.c.NodeKind.Keys == c.NodeKind.Keys + e_and.sc + e_left.sc + e_right.sc;
        {assert e_top.sc == e_left.sc + e_right.sc;}
        eb5.c.NodeKind.Keys == c.NodeKind.Keys + e_and.sc + e_top.sc;
        eb6.c.NodeKind.Keys == c.NodeKind.Keys + e_and.sc + e_top.sc;
        {assert e_final.sc == e_top.sc + e_and.sc;}
        eb6.c.NodeKind.Keys == c.NodeKind.Keys + e_final.sc;
      }
    }

    assert eb6.c.Valid() by {
      reveal IslandBundleValid();
    }
    assert EntityValid(eb6.c, e_final) && IsIsland(eb6.c, e_final.sc) by {
      reveal IslandBundleValid();
    }
    assert |e_final.mf.inputs| == n && |e_final.mf.outputs| == 1 by {
      assert |e_left.mf.inputs| == p;
      assert |e_right.mf.inputs| == n - p;
      assert |e_top.mf.inputs| == n;
    }

    (eb6.c, e_final, mf)
  }

  opaque function InsertAndTreeImpl(c: Circuit, n: nat): (r: (Circuit, Entity))
    requires c.Valid()
    ensures r.0.Valid()
    ensures EntityValid(r.0, r.1)
    ensures CircuitUnconnected(c, r.0)
    ensures CircuitConserved(c, r.0)
    ensures IsIsland(r.0, r.1.sc)
    ensures r.0.NodeKind.Keys == c.NodeKind.Keys + r.1.sc
    ensures c.NodeKind.Keys !! r.1.sc
    ensures AndTreeMFValid(n, r.1.mf)
    decreases n, 1
  {
    if n == 0 then
      InsertConst(c, true)
    else if n == 1 then
      InsertIdent(c)
    else if n == 2 then
      InsertAnd(c)
    else
      var p := SubTreeSizes(n).0;

      var (new_c, e, mf) := InsertAndTreeHelper(c, n);

      // Swap out the map function for a simpler one.
      var new_e := EntitySwapMF(new_c, e, mf);
      assert new_e.mf == mf;

      reveal IslandBundleValid();
      assert CircuitUnconnected(c, new_c);
      assert CircuitConserved(c, new_c);

      (new_c, new_e)
  }

}
module Build.AndTree {

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

  import opened AndBuilder
  import opened IdentBuilder
  import opened ConstBuilder

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
      var p := if n % 2 == 0 then n/2 else (n-1)/2;
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
    && var p := if n % 2 == 0 then n/2 else (n-1)/2;
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
  function {:vcs_split_on_every_assert} InsertAndTreeImpl(c: Circuit, n: nat): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntityValid(r.0, r.1)
    ensures CircuitUnconnected(c, r.0)
    ensures CircuitConserved(c, r.0)
    ensures IsIsland(r.0, r.1.sc)
    ensures r.0.NodeKind.Keys == c.NodeKind.Keys + r.1.sc
    ensures c.NodeKind.Keys !! r.1.sc
    ensures |r.1.mf.inputs| == n
    decreases n
  {
    if n == 0 then
      InsertConst(c, true)
    else if n == 1 then
      InsertIdent(c)
    else if n == 2 then
      InsertAnd(c)
    else
      var p := if n % 2 == 0 then n/2 else (n-1)/2;
      var eb1 := IslandBundleFromCircuit(c);

      // Insert the left part of the tree.
      var (c1, e_left) := InsertAndTreeImpl(c, p);
      assert c1.NodeKind.Keys == c.NodeKind.Keys + e_left.sc;
      var (eb2, ref_left) := AddEntity(eb1, c1, e_left);
      assert EntityValid(c1, e_left);
      assert e_left == eb2.es[ref_left].value;

      // Insert the right part of the tree.
      var (c2, e_right) := InsertAndTreeImpl(c1, n-p);
      assert c2.NodeKind.Keys == c1.NodeKind.Keys + e_right.sc;
      var (eb3, ref_right) := AddEntity(eb2, c2, e_right);
      assert EntityValid(c2, e_right);
      assert EntityValid(c2, e_left) by {
        reveal IslandBundleValid();
      }
      assert e_left == eb3.es[ref_left].value;
      assert e_right == eb3.es[ref_right].value;

      // Insert an 'and' connecting them.
      var (c3, e_and) := InsertAnd(c2);
      var (eb4, ref_and) := AddEntity(eb3, c3, e_and);

      // Join the left and rights parts in parallel
      assert CombineParallelEntitiesRequirements(eb4.c, e_left, e_right) by {
        reveal IslandBundleValid();
      }
      var (eb5, ref_top) := IBCombineParallelEntities(eb4, ref_left, ref_right);
      // Join the and on
      var e_top := eb5.es[ref_top].value;
      assert e_and == eb5.es[ref_and].value;
      assert CombineSeriesEntitiesRequirements(eb5.c, e_top, e_and) by {
        reveal IslandBundleValid();
      }
      var (eb6, ref_final) := IBCombineSeriesEntities(eb5, ref_top, ref_and);

      var e_final := eb6.es[ref_final].value;

      reveal IslandBundleValid();
      assert CircuitUnconnected(c, eb6.c);
      assert CircuitConserved(c, eb6.c);

      (eb6.c, e_final)
  }

}
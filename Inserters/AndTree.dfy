module Inserters.AndTree{

  import opened Std.Wrappers

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Utils
  import opened Scuf
  import opened MapFunction
  import opened ConnectionEval
  import opened Connection
  import opened Subcircuit
  import opened MapConnection
  import opened ModifiersSeries
  import opened Modifiers.Merge
  import opened Modifiers.SwitchUF

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

  function AndTreeStep1UpdateFunction(n: nat): (uf: UpdateFunction)
    requires n > 2
    ensures uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      n, 2, 0,
      (si: SI) requires |si.inputs| == n && |si.state| == 0 =>
        var p := SubTreeSizes(n).0;
        var si1 := SI(si.inputs[..p], []);
        var si2 := SI(si.inputs[p..], []);
        SO(AndTreeSF(p, si1).outputs + AndTreeSF(n-p, si2).outputs, [])
    )
  }

  function AndTreeUpdateFunction(n: nat): (uf: UpdateFunction)
    ensures uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      n, 1, 0,
      (si: SI) requires |si.inputs| == n && |si.state| == 0 => AndTreeSF(n, si)
    )
  }

  lemma LemmaAndTreeUpdateFunction(n: nat)
    ensures
      UpdateFunctionsEquiv(AndTreeInserterImpl(n).uf, AndTreeUpdateFunction(n))
    decreases n, 1
  {
    reveal UpdateFunctionsEquiv();
    var uf1 := AndTreeInserterImpl(n).uf;
    var uf2 := AndTreeUpdateFunction(n);
    if n == 0 {
      assert UpdateFunctionsEquiv(uf1, uf2);
    } else if n == 1 {
      assert UpdateFunctionsEquiv(uf1, uf2);
    } else if n == 2 {
      assert UpdateFunctionsEquiv(uf1, uf2);
    } else {
      assert n > 2;
      var p := SubTreeSizes(n).0;
      var z_left := AndTreeInserter(p);
      var z_right := AndTreeInserter(n - p);
      var z_left_and_right := MergeModifier(z_left, z_right);
      assert UpdateFunctionsEquiv(AndTreeStep1UpdateFunction(n), z_left_and_right.uf) by {
        reveal MergeUpdateFunctions();
      }
      var z_and := AndInserter();
      var z := SeriesModifier(z_left_and_right, z_and);
      reveal SeriesModifier();
      reveal SeriesUpdateFunction();
      assert UpdateFunctionsEquiv(uf1, uf2);
    }
  }

  function AndTreeInserterImpl(n: nat): (z: ScufInserter)
    ensures z.Valid()
    ensures z.uf.Valid()
    decreases n, 0
  {
    if n == 0 then
      ConstInserter(true)
    else if n == 1 then
      IdentInserter()
    else if n == 2 then
      AndInserter()
    else
      var p := SubTreeSizes(n).0;
      var z_left := AndTreeInserter(p);
      var z_right := AndTreeInserter(n - p);
      var z_left_and_right := MergeModifier(z_left, z_right);
      var z_and := AndInserter();
      var z := SeriesModifier(z_left_and_right, z_and);
      z
  }

  function AndTreeInserter(n: nat): (z: ScufInserter)
    ensures z.Valid()
    decreases n, 2
  {
    var uf := AndTreeUpdateFunction(n);
    var z_almost := AndTreeInserterImpl(n);
    LemmaAndTreeUpdateFunction(n);
    reveal UpdateFunctionsEquiv();
    var z := SwitchUFModifier(z_almost, uf);
    z
  }
}
module Modifiers_ManyParallel {

  import opened Std.Wrappers
  import Std.Collections.Seq

  import opened MapFunction
  import opened MapConnection
  import opened Utils
  import opened Circ
  import opened Scuf
  import opened Subcircuit
  import opened Connection
  import opened ConservedSubcircuit
  import opened Inserters.Null
  import opened Modifiers.Merge
  import opened Modifiers.SwitchUF

  lemma ManyParallelSFOne(uf: UpdateFunction, si: SI)
    requires uf.Valid()
    requires |si.inputs| == uf.input_width 
    requires |si.state| == uf.state_width
    ensures
      reveal UpdateFunction.Valid();
      ManyParallelSF(uf, 1, si) == uf.sf(si)
  {
    var nm1_si := SI(si.inputs[uf.input_width..], si.state[uf.state_width..]);
    var n_si := SI(si.inputs[..uf.input_width], si.state[..uf.state_width]);
    var nm1_so := ManyParallelSF(uf, 0, nm1_si);
    assert |nm1_so.outputs| == 0;
    assert |nm1_so.state| == 0;
    reveal UpdateFunction.Valid();
    var n_so := uf.sf(n_si);
    var so := SO(n_so.outputs + nm1_so.outputs, n_so.state + nm1_so.state);
    assert n_si == si;
    assert uf.sf(n_si) == SO(n_so.outputs, n_so.state);
    assert so == uf.sf(si);
  }

  function ManyParallelSF(uf: UpdateFunction, n: nat, si: SI): (so: SO)
    requires |si.inputs| == uf.input_width * n
    requires |si.state| == uf.state_width * n
    requires uf.Valid()
    ensures |so.outputs| == uf.output_width * n
    ensures |so.state| == uf.state_width * n
    decreases n
  {
    if n == 0 then
      SO([], [])
    else
      var nm1_si := SI(si.inputs[uf.input_width..], si.state[uf.state_width..]);
      var n_si := SI(si.inputs[..uf.input_width], si.state[..uf.state_width]);
      var nm1_so := ManyParallelSF(uf, n-1, nm1_si);
      reveal UpdateFunction.Valid();
      var n_so := uf.sf(n_si);
      SO(n_so.outputs + nm1_so.outputs, n_so.state + nm1_so.state)
  }

  function UpdateFunctionByMerge(uf: UpdateFunction, n: nat): (new_uf: UpdateFunction)
    requires uf.Valid()
    ensures new_uf.Valid()
  {
    if n == 0 then
      NullUpdateFunction()
    else if n == 1 then
      uf
    else
      var uf_other := UpdateFunctionByMerge(uf, n-1);
      var new_uf := MergeUpdateFunctions(uf, uf_other);
      new_uf
  }

  opaque function ManyParallelUpdateFunction(uf: UpdateFunction, n: nat): (new_uf: UpdateFunction)
    requires uf.Valid()
    ensures new_uf.Valid()
    ensures new_uf.input_width == n * uf.input_width
    ensures new_uf.output_width == n * uf.output_width
    ensures new_uf.state_width == n * uf.state_width
  {
    var new_uf := UpdateFunction(
      n * uf.input_width,
      n * uf.output_width,
      n * uf.state_width,
      (si: SI) requires |si.inputs| == n * uf.input_width && |si.state| == n * uf.state_width
        => ManyParallelSF(uf, n, si)
    );
    assert new_uf.Valid() by {
      reveal UpdateFunction.Valid();
    }
    new_uf
  }

  lemma ManyParallelUpdateFunctionCorrect(z: ScufInserter, n: nat)
    requires z.Valid()
    ensures
      reveal ScufInserter.Valid();
      var uf1 := ManyParallelUpdateFunction(z.uf, n);
      var uf2 := ManyParallelInserterImpl(z, n).uf;
      UpdateFunctionsEquiv(uf1, uf2)
    decreases n, 1
  {
    reveal ScufInserter.Valid();
    reveal UpdateFunction.Valid();
    var uf1 := ManyParallelUpdateFunction(z.uf, n);
    var uf2 := ManyParallelInserterImpl(z, n).uf;
    assert uf1.input_width == uf2.input_width;
    assert uf1.output_width == uf2.output_width;
    assert uf1.state_width == uf2.state_width;
    reveal UpdateFunctionsEquiv();
    reveal ManyParallelUpdateFunction();
    if n == 0 {
      assert UpdateFunctionsEquiv(uf1, uf2);
    } else if n == 1 {
      assert uf2 == z.uf;
      forall si: SI | |si.inputs| == uf1.input_width && |si.state| == uf1.state_width
        ensures uf1.sf(si) == uf2.sf(si)
      {
        ManyParallelSFOne(z.uf, si);
      }
      assert UpdateFunctionsEquiv(uf1, uf2);
    } else {
      assert uf2 == MergeUpdateFunctions(z.uf, ManyParallelUpdateFunction(z.uf, n-1)) by {
        var z_other := ManyParallelInserter(z, n-1);
        var z_merged := MergeModifier(z, z_other);
        assert z_merged.uf == uf2;
      }
      forall si: SI | |si.inputs| == uf1.input_width && |si.state| == uf1.state_width
        ensures uf1.sf(si) == uf2.sf(si)
      {
        assert uf1.sf.requires(si);
        assert uf2.sf.requires(si);
        assert uf1.sf(si) == ManyParallelSF(z.uf, n, si);
        var si_this := SI(si.inputs[..z.uf.input_width], si.state[..z.uf.state_width]);
        var so_this := z.uf.sf(si_this);
        var si_other := SI(si.inputs[z.uf.input_width..], si.state[z.uf.state_width..]);
        var uf1_other := ManyParallelUpdateFunction(z.uf, n-1);
        var uf2_other := ManyParallelInserterImpl(z, n-1).uf;
        var so1_other := uf1_other.sf(si_other);
        var so2_other := uf2_other.sf(si_other);
        ManyParallelUpdateFunctionCorrect(z, n-1);
        assert so1_other == so2_other;
        var so1_combined := SO(so_this.outputs + so1_other.outputs, so_this.state + so1_other.state);
        assert so1_combined == uf1.sf(si);
        assert so1_combined == uf2.sf(si) by {
          reveal MergeUpdateFunctions();
          assert uf2 == MergeUpdateFunctions(z.uf, uf1_other);
        }
        assert uf1.sf(si) == uf2.sf(si);
      }
      assert UpdateFunctionsEquiv(uf1, uf2);
    }
    assert UpdateFunctionsEquiv(uf1, uf2);
  }

  function ManyParallelInserterImpl(z: ScufInserter, n: nat): (new_z: ScufInserter)
    requires z.Valid()
    ensures new_z.Valid()
    ensures new_z.uf.input_width == z.uf.input_width * n
    ensures new_z.uf.output_width == z.uf.output_width * n
    ensures new_z.uf.state_width == z.uf.state_width * n
    decreases n, 0
  {
    reveal ScufInserter.Valid();
    var new_z := if n == 0 then
      var z_null := NullInserter();
      z_null
    else if n == 1 then
      z
    else
      var z_other := ManyParallelInserter(z, n-1);
      var z_merged := MergeModifier(z, z_other);
      z_merged;
    new_z
  }

  opaque function ManyParallelInserter(z: ScufInserter, n: nat): (new_z: ScufInserter)
    requires z.Valid()
    ensures new_z.Valid()
    ensures
      && z.uf.Valid()
      && (new_z.uf == ManyParallelUpdateFunction(z.uf, n))
    decreases n, 2
  {
    var z_almost := ManyParallelInserterImpl(z, n);
    reveal ScufInserter.Valid();
    var new_uf := ManyParallelUpdateFunction(z.uf, n);
    reveal MergeUpdateFunctions();
    ManyParallelUpdateFunctionCorrect(z, n);
    var new_z := SwitchUFModifier(z_almost, new_uf);
    new_z
  }
}
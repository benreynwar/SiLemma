module CombineManyParallel {

  import opened Std.Wrappers
  import Std.Collections.Seq

  import opened MapFunction
  import opened MapConnection
  import opened Utils
  import opened Circ
  import opened Entity
  import opened Subcircuit
  import opened Connection
  import opened IslandBundle
  import opened ConservedSubcircuit
  import opened CombineParallel

  ghost predicate CombineManyParallelEntitiesRequirements(ib: IslandBundle, rf: RFunction) {
    && IslandBundleValid(ib)
    && rf.Valid()
    && (forall e :: e in ib.es ==> e.Some?)
    && (forall e :: e in ib.es ==> rf.MFConsistent(e.value.mf))
  }

  function ManyParallelSF(rf: RFunction, n: nat, si: SI): (so: SO)
    requires |si.inputs| == rf.input_width * n
    requires |si.state| == rf.state_width * n
    requires rf.Valid()
    decreases n
  {
    if n == 0 then
      SO([], [])
    else
      var nm1_si := SI(si.inputs[..(n-1)*rf.input_width], si.state[..(n-1)*rf.state_width]);
      var n_si := SI(si.inputs[(n-1)*rf.input_width..], si.state[(n-1)*rf.state_width..]);
      var nm1_so := ManyParallelSF(rf, n-1, nm1_si);
      reveal RFunction.Valid();
      var n_so := rf.sf(n_si);
      SO(nm1_so.outputs + n_so.outputs, nm1_so.state + n_so.state)
  }

  opaque ghost predicate MFIsParallelCopies(mf: MapFunction, rf: RFunction, n: nat)
    requires mf.Valid()
    requires rf.Valid()
  {
    && (|mf.inputs| == rf.input_width * n)
    && (|mf.outputs| == rf.output_width * n)
    && (|mf.state| == rf.state_width * n)
    && (forall si: SI :: SIValid(si, mf.inputs, mf.state) ==>
      reveal MapFunction.Valid();
      var so := mf.sf(si);
      so == ManyParallelSF(rf, n, si))
  }

  lemma MaintainsMFIsParallelCopies(mf_old: MapFunction, mf_inserted: MapFunction, rf: RFunction, n: nat)
    requires n > 0
    requires mf_old.Valid()
    requires mf_inserted.Valid()
    requires rf.Valid()
    requires MFIsParallelCopies(mf_old, rf, n-1)
    requires rf.MFConsistent(mf_inserted)
    requires mf_old.NPs() !! mf_inserted.NPs()
    requires Seq.ToSet(mf_old.state) !! Seq.ToSet(mf_inserted.state)
    ensures
      var combiner := ParallelCombiner(mf_old, mf_inserted);
      var mf_combined := combiner.mf();
      MFIsParallelCopies(mf_combined, rf, n)      
  {
    reveal RFunction.MFConsistent();
    reveal MFIsParallelCopies();
    var combiner := ParallelCombiner(mf_old, mf_inserted);
    var mf := combiner.mf();
    assert (|mf.inputs| == rf.input_width * n);
    assert (|mf.outputs| == rf.output_width * n);
    assert (|mf.state| == rf.state_width * n);
    forall si: SI | SIValid(si, mf.inputs, mf.state)
      ensures mf.sf(si) == ManyParallelSF(rf, n, si)
    {
      reveal MapFunction.Valid();
    }
  }

  lemma MFIsParallelCopiesForSingle(c: Circuit, ei: EntityInserter)
    requires c.Valid()
    requires ei.Valid()
    ensures
      reveal EntityInserter.Valid();
      reveal SimpleInsertion();
      MFIsParallelCopies(ei.fn(c).1.mf, ei.rf, 1)
  {
    reveal EntityInserter.Valid();
    reveal RFunction.Valid();
    reveal RFunction.MFConsistent();
    reveal MFIsParallelCopies();
    var mf := ei.fn(c).1.mf;
    var rf := ei.rf;
    forall si: SI | SIValid(si, mf.inputs, mf.state)
      ensures mf.sf(si) == ManyParallelSF(rf, 1, si)
    {
      reveal MapFunction.Valid();
      var so := mf.sf(si);
      var chunked_inputs := ChunkSeq(si.inputs, 1, rf.input_width);
      ChunkSeqSingle(si.inputs);
      assert chunked_inputs == [si.inputs];
      var chunked_state := ChunkSeq(si.state, 1, rf.state_width);
      ChunkSeqSingle(si.state);
      assert chunked_state == [si.state];
      var many_si := seq(1, (index: nat) requires index < 1 => SI(chunked_inputs[index], chunked_state[index]));
      assert many_si == [si];
      var many_so := seq(1, (index: nat) requires index < 1 => rf.sf(many_si[index]));
      assert many_so == [so] by  {
        calc {
          many_so;
          seq(1, (index: nat) requires index < 1 => rf.sf(many_si[index]));
          [rf.sf(many_si[0])];
          [rf.sf(si)];
          [mf.sf(si)];
          [so];
        }
      }
      var chunked_outputs := seq(1, (index: nat) requires index < 1 => many_so[index].outputs);
      assert chunked_outputs == [so.outputs];
      var chunked_new_state := seq(1, (index: nat) requires index < 1 => many_so[index].state);
      assert chunked_new_state == [so.state];
      var so_outputs := UnchunkSeq(chunked_outputs, 1, rf.output_width);
      assert so_outputs == so.outputs;
      var so_state := UnchunkSeq(chunked_new_state, 1, rf.state_width);
      assert so_state == so.state;
      var so_other := SO(so_outputs, so_state);
      assert so_other == so;
      assert so_other == ManyParallelSF(rf, 1, si);
    }
    reveal SimpleInsertion();
    assert MFIsParallelCopies(ei.fn(c).1.mf, ei.rf, 1) by {
      reveal MFIsParallelCopies();
    }

  }

  opaque function InsertInParallel(c: Circuit, ei: EntityInserter, n: nat): (r: (Circuit, Entity))
    requires c.Valid()
    requires ei.Valid()
    ensures SimpleInsertion(c, r.0, r.1)
    ensures
      reveal EntityInserter.Valid();
      reveal SimpleInsertion();
      MFIsParallelCopies(r.1.mf, ei.rf, n)
  {
    reveal EntityInserter.Valid();
    reveal MFIsParallelCopies();
    reveal SimpleInsertion();
    if n == 0 then
      var r := (c, NullEntity);
      NullEntityValid(c);
      assert EntityValid(r.0, r.1);
      assert CircuitUnconnected(c, r.0) by {
        reveal CircuitUnconnected();
      }
      assert CircuitConserved(c, r.0) by {
        reveal CircuitConserved();
      }
      assert IsIsland(r.0, r.1.sc) by {
        reveal IsIsland();
      }
      assert MFIsParallelCopies(r.1.mf, ei.rf, n);
      r
    else if n == 1 then
      var r := ei.fn(c);
      assert EntityValid(r.0, r.1);
      assert CircuitUnconnected(c, r.0);
      assert CircuitConserved(c, r.0);
      assert IsIsland(r.0, r.1.sc);
      MFIsParallelCopiesForSingle(c, ei);
      r
    else
      var ib1 := IslandBundleFromCircuit(c);

      var (c_intermed, e_intermed) := InsertInParallel(c, ei, n-1);
      var (ib2, ref_intermed) := AddEntity(ib1, c_intermed, e_intermed);

      var (new_c, e_inserted) := ei.fn(c_intermed);
      var (ib3, ref_inserted) := AddEntity(ib2, new_c, e_inserted);

      assert CombineParallelEntitiesRequirements(ib3.c, e_intermed, e_inserted) by {
        reveal IslandBundleValid();
      }
      var (ib4, ref_combined) := IBCombineParallelEntities(ib3, ref_intermed, ref_inserted);
      var e_combined := ib4.es[ref_combined].value;
      assert ib4.c.Valid() by {
        reveal IslandBundleValid();
      }
      assert EntityValid(ib4.c, e_combined) by {
        reveal IslandBundleValid();
      }
      assert CircuitUnconnected(c, ib4.c) by {
        reveal IslandBundleValid();
      }
      assert CircuitConserved(c, ib4.c) by {
        reveal IslandBundleValid();
      }
      assert ib4.c.NodeKind.Keys == c.NodeKind.Keys + e_combined.sc by {reveal IslandBundleValid();}
      assert c.NodeKind.Keys !! e_combined.sc by {reveal IslandBundleValid();}
      assert IsIsland(ib4.c, e_combined.sc) by {reveal IslandBundleValid();}
      MaintainsMFIsParallelCopies(e_intermed.mf, e_inserted.mf, ei.rf, n);
      var r := (ib4.c, e_combined);
      assert MFIsParallelCopies(r.1.mf, ei.rf, n);
      assert EntityValid(r.0, r.1);
      r
  }
}
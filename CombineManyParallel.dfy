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

  //function ChunkedInputs(ib: IslandBundle): (r: seq<seq<NP>>)
  //  requires IslandBundleValid(ib)
  //  requires (forall e :: e in ib.es ==> e.Some?)
  //  ensures NoDuplicatesNoIntersections(r)
  //{
  //  var chunked_inputs := seq(|ib.es|, (index: nat) requires index < |ib.es| => ib.es[index].value.mf.inputs);
  //  assert NoDuplicatesNoIntersections(chunked_inputs) by {
  //    forall index: nat | index < |ib.es|
  //      ensures Seq.HasNoDuplicates(ib.es[index].value.mf.inputs)
  //    {
  //      reveal MapFunction.Valid();
  //      reveal IslandBundleValid();
  //      var mf := ib.es[index].value.mf;
  //    }
  //    forall index1: nat, index2: nat | index1 < |ib.es| && index2 < |ib.es| && index1 != index2
  //      ensures SeqsNoIntersection(ib.es[index1].value.mf.inputs, ib.es[index2].value.mf.inputs)
  //    {
  //      reveal IslandBundleValid();
  //      var e1 := ib.es[index1].value;
  //      var e2 := ib.es[index2].value;
  //      assert e1.sc !! e2.sc;
  //      FInputsInSc(ib.c, e1);
  //      FInputsInSc(ib.c, e2);
  //      ScNoIntersectionNPsNoIntersection(e1.sc, e2.sc, Seq.ToSet(e1.mf.inputs), Seq.ToSet(e2.mf.inputs));
  //    }
  //  }
  //  chunked_inputs
  //}

  //function ChunkedOutputs(ib: IslandBundle): (r: seq<seq<NP>>)
  //  requires IslandBundleValid(ib)
  //  requires (forall e :: e in ib.es ==> e.Some?)
  //  ensures NoDuplicatesNoIntersections(r)
  //{
  //  var chunked_outputs := seq(|ib.es|, (index: nat) requires index < |ib.es| => ib.es[index].value.mf.outputs);
  //  assert NoDuplicatesNoIntersections(chunked_outputs) by {
  //    forall index: nat | index < |ib.es|
  //      ensures Seq.HasNoDuplicates(ib.es[index].value.mf.outputs)
  //    {
  //      reveal MapFunction.Valid();
  //      reveal IslandBundleValid();
  //      var mf := ib.es[index].value.mf;
  //    }
  //    forall index1: nat, index2: nat | index1 < |ib.es| && index2 < |ib.es| && index1 != index2
  //      ensures SeqsNoIntersection(ib.es[index1].value.mf.outputs, ib.es[index2].value.mf.outputs)
  //    {
  //      reveal IslandBundleValid();
  //      var e1 := ib.es[index1].value;
  //      var e2 := ib.es[index2].value;
  //      assert e1.sc !! e2.sc;
  //      FOutputsInSc(ib.c, e1);
  //      FOutputsInSc(ib.c, e2);
  //      ScNoIntersectionNPsNoIntersection(e1.sc, e2.sc, Seq.ToSet(e1.mf.outputs), Seq.ToSet(e2.mf.outputs));
  //    }
  //  }
  //  chunked_outputs
  //}

  //function ChunkedState(ib: IslandBundle): (r: seq<seq<CNode>>)
  //  requires IslandBundleValid(ib)
  //  requires (forall e :: e in ib.es ==> e.Some?)
  //  ensures NoDuplicatesNoIntersections(r)
  //{
  //  var chunked_state := seq(|ib.es|, (index: nat) requires index < |ib.es| => ib.es[index].value.mf.state);
  //  assert NoDuplicatesNoIntersections(chunked_state) by {
  //    forall index: nat | index < |ib.es|
  //      ensures Seq.HasNoDuplicates(ib.es[index].value.mf.state)
  //    {
  //      reveal MapFunction.Valid();
  //      reveal IslandBundleValid();
  //    }
  //    forall index1: nat, index2: nat | index1 < |ib.es| && index2 < |ib.es| && index1 != index2
  //      ensures SeqsNoIntersection(ib.es[index1].value.mf.state, ib.es[index2].value.mf.state)
  //    {
  //      reveal IslandBundleValid();
  //      var e1 := ib.es[index1].value;
  //      var e2 := ib.es[index2].value;
  //      assert e1.sc !! e2.sc;
  //      StateInSc(ib.c, e1);
  //      StateInSc(ib.c, e2);
  //    }
  //  }
  //  chunked_state
  //}

  //function ChunkedStateONPs(ib: IslandBundle): (r: seq<seq<NP>>)
  //  requires IslandBundleValid(ib)
  //  requires (forall e :: e in ib.es ==> e.Some?)
  //  ensures NoDuplicatesNoIntersections(r)
  //{
  //  var chunked_state_onps := seq(|ib.es|, (index: nat) requires index < |ib.es| => StateONPsSeq(ib.es[index].value.mf.state));
  //  assert NoDuplicatesNoIntersections(chunked_state_onps) by {
  //    forall index: nat | index < |ib.es|
  //      ensures Seq.HasNoDuplicates(StateONPsSeq(ib.es[index].value.mf.state))
  //    {
  //      reveal MapFunction.Valid();
  //      reveal IslandBundleValid();
  //      StateONPsSeqNoDuplicates(ib.es[index].value.mf.state);
  //    }
  //    forall index1: nat, index2: nat | index1 < |ib.es| && index2 < |ib.es| && index1 != index2
  //      ensures SeqsNoIntersection(StateONPsSeq(ib.es[index1].value.mf.state), StateONPsSeq(ib.es[index2].value.mf.state))
  //    {
  //      reveal IslandBundleValid();
  //      var e1 := ib.es[index1].value;
  //      var e2 := ib.es[index2].value;
  //      StateInSc(ib.c, e1);
  //      StateInSc(ib.c, e2);
  //      SeqsNoIntersectionEquiv(e1.mf.state, e2.mf.state);
  //      SeqsNoIntersectionEquiv(StateONPsSeq(e1.mf.state), StateONPsSeq(e2.mf.state));
  //    }
  //  }
  //  chunked_state_onps
  //}

  //function ChunkedStateINPs(ib: IslandBundle): (r: seq<seq<NP>>)
  //  requires IslandBundleValid(ib)
  //  requires (forall e :: e in ib.es ==> e.Some?)
  //  ensures NoDuplicatesNoIntersections(r)
  //{
  //  var chunked_state_inps := seq(|ib.es|, (index: nat) requires index < |ib.es| => StateINPsSeq(ib.es[index].value.mf.state));
  //  assert NoDuplicatesNoIntersections(chunked_state_inps) by {
  //    forall index: nat | index < |ib.es|
  //      ensures Seq.HasNoDuplicates(StateINPsSeq(ib.es[index].value.mf.state))
  //    {
  //      reveal MapFunction.Valid();
  //      reveal IslandBundleValid();
  //      StateINPsSeqNoDuplicates(ib.es[index].value.mf.state);
  //    }
  //    forall index1: nat, index2: nat | index1 < |ib.es| && index2 < |ib.es| && index1 != index2
  //      ensures SeqsNoIntersection(StateINPsSeq(ib.es[index1].value.mf.state), StateINPsSeq(ib.es[index2].value.mf.state))
  //    {
  //      reveal IslandBundleValid();
  //      var e1 := ib.es[index1].value;
  //      var e2 := ib.es[index2].value;
  //      StateInSc(ib.c, e1);
  //      StateInSc(ib.c, e2);
  //      SeqsNoIntersectionEquiv(e1.mf.state, e2.mf.state);
  //      SeqsNoIntersectionEquiv(StateINPsSeq(e1.mf.state), StateINPsSeq(e2.mf.state));
  //    }
  //  }
  //  chunked_state_inps
  //}

  //lemma ChunkedNoIntersections(ib: IslandBundle)
  //  requires IslandBundleValid(ib)
  //  requires (forall e :: e in ib.es ==> e.Some?)
  //  ensures
  //    var chunked_inputs := ChunkedInputs(ib);
  //    var chunked_outputs := ChunkedOutputs(ib);
  //    var chunked_state_inps := ChunkedStateINPs(ib);
  //    var chunked_state_onps := ChunkedStateONPs(ib);
  //    forall index1: nat, index2: nat :: index1 < |ib.es| && index2 < |ib.es| ==> (
  //      && SeqsNoIntersection(chunked_inputs[index1], chunked_outputs[index2])
  //      && SeqsNoIntersection(chunked_state_onps[index1], chunked_inputs[index2])
  //      && SeqsNoIntersection(chunked_state_inps[index1], chunked_outputs[index2])
  //    )
  //  {
  //    var chunked_inputs := ChunkedInputs(ib);
  //    var chunked_outputs := ChunkedOutputs(ib);
  //    var chunked_state_inps := ChunkedStateINPs(ib);
  //    var chunked_state_onps := ChunkedStateONPs(ib);
  //    forall index1: nat, index2: nat | index1 < |ib.es| && index2 < |ib.es|
  //      ensures SeqsNoIntersection(chunked_inputs[index1], chunked_outputs[index2])
  //      ensures SeqsNoIntersection(chunked_state_onps[index1], chunked_inputs[index2])
  //      ensures SeqsNoIntersection(chunked_state_inps[index1], chunked_outputs[index2])
  //    {
  //      var e1 := ib.es[index1].value;
  //      var e2 := ib.es[index2].value;
  //      if (index1 == index2) {
  //        reveal IslandBundleValid();
  //        reveal MapFunction.Valid();
  //      } else {
  //        reveal IslandBundleValid();
  //        FAllInSc(ib.c, e1);
  //        FAllInSc(ib.c, e2);
  //        reveal NPsInSc();
  //        reveal MapFunction.Valid();
  //        StateONPsSeqSame(e1.mf.state);
  //        StateINPsSeqSame(e1.mf.state);
  //        ScNoIntersectionNPsNoIntersection(e1.sc, e2.sc, Seq.ToSet(chunked_inputs[index1]), Seq.ToSet(chunked_outputs[index2]));
  //        ScNoIntersectionNPsNoIntersection(e2.sc, e1.sc, Seq.ToSet(chunked_inputs[index2]), Seq.ToSet(chunked_state_onps[index1]));
  //        ScNoIntersectionNPsNoIntersection(e2.sc, e1.sc, Seq.ToSet(chunked_outputs[index2]), Seq.ToSet(chunked_state_inps[index1]));
  //      }
  //    }
  //  }

  //lemma UnchunkedStateINPsONPsEquiv(ib: IslandBundle, rf: RFunction)
  //  requires CombineManyParallelEntitiesRequirements(ib, rf)
  //  ensures
  //    var chunked_state := ChunkedState(ib);
  //    var state := UnchunkSeq(chunked_state, |ib.es|, rf.state_width);
  //    var chunked_state_inps := ChunkedStateINPs(ib);
  //    var chunked_state_onps := ChunkedStateONPs(ib);
  //    && (StateINPsSeq(state) == UnchunkSeq(chunked_state_inps, |ib.es|, rf.state_width))
  //    && (StateONPsSeq(state) == UnchunkSeq(chunked_state_onps, |ib.es|, rf.state_width))
  //{
  //}

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
    requires CircuitValid(c)
    requires ei.Valid()
    ensures
      reveal EntityInserter.Valid();
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

  }

  opaque function InsertInParallel(c: Circuit, ei: EntityInserter, n: nat): (r: (Circuit, Entity))
    requires CircuitValid(c)
    requires ei.Valid()
    ensures SimpleInsertion(c, r.0, r.1)
    ensures
      reveal EntityInserter.Valid();
      MFIsParallelCopies(r.1.mf, ei.rf, n)
  {
    reveal EntityInserter.Valid();
    reveal MFIsParallelCopies();
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
      assert CircuitValid(ib4.c) by {
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
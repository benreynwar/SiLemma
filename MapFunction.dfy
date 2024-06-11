module MapFunction {

  import Std.Collections.Seq

  import opened Circ
  import opened Utils
  //import opened MapConnection

  datatype FI = FI(
    inputs: map<NP, bool>,
    state: map<CNode, bool>
  )

  datatype FO = FO(
    outputs: map<NP, bool>,
    state: map<CNode, bool>
  )

  datatype SI = SI(
    inputs: seq<bool>,
    state: seq<bool>
  )

  datatype SO = SO(
    outputs: seq<bool>,
    state: seq<bool>
  )

  predicate FIValid(fi: FI, inputs: seq<NP>, state: seq<CNode>)
  {
    && fi.inputs.Keys == Seq.ToSet(inputs)
    && fi.state.Keys == Seq.ToSet(state)
  }

  predicate FOValid(fo: FO, outputs: seq<NP>, state: seq<CNode>)
  {
    && fo.outputs.Keys == Seq.ToSet(outputs)
    && fo.state.Keys == Seq.ToSet(state)
  }

  ghost predicate SIValid(si: SI, inputs: seq<NP>, state: seq<CNode>)
  {
    && Seq.HasNoDuplicates(inputs)
    && Seq.HasNoDuplicates(state)
    && |si.inputs| == |inputs|
    && |si.state| == |state|
  }

  ghost predicate SOValid(so: SO, outputs: seq<NP>, state: seq<CNode>)
  {
    && Seq.HasNoDuplicates(outputs)
    && Seq.HasNoDuplicates(state)
    && |so.outputs| == |outputs|
    && |so.state| == |state|
  }

  datatype MapFunction = MapFunction(
    inputs: seq<NP>,
    outputs: seq<NP>,
    state: seq<CNode>,
    sf: SI --> SO
  ) {

    ghost opaque predicate Valid()
    {
      && (forall si: SI :: SIValid(si, inputs, state) ==> (
          && sf.requires(si)
          && SOValid(sf(si), outputs, state)
      ))
      && Seq.HasNoDuplicates(inputs)
      && Seq.HasNoDuplicates(outputs)
      && Seq.HasNoDuplicates(state)
      && SeqsNoIntersection(inputs, outputs)
      && SeqsNoIntersection(inputs, StateONPsSeq(state))
      && SeqsNoIntersection(outputs, StateINPsSeq(state))
    }

    function NPs(): set<NP>
    {
      Seq.ToSet(inputs) + Seq.ToSet(outputs) + StateONPs(state) + StateINPs(state)
    }

    lemma InputsHasNoDuplicates()
      requires Valid()
      ensures Seq.HasNoDuplicates(inputs)
    {
      reveal Valid();
    }

    lemma OutputsHasNoDuplicates()
      requires Valid()
      ensures Seq.HasNoDuplicates(outputs)
    {
      reveal Valid();
    }

    function si2fi(si: SI): (fi: FI)
      requires SIValid(si, inputs, state)
      ensures FIValid(fi, inputs, state)
    {
      reveal Seq.HasNoDuplicates();
      var i := SeqsToMap(inputs, si.inputs);
      assert i.Keys == Seq.ToSet(inputs);
      var s := SeqsToMap(state, si.state);
      FI(i, s)
    }
    
    function so2fo(so: SO): (fo: FO)
      requires SOValid(so, outputs, state)
      ensures FOValid(fo, outputs, state)
    {
      var o := SeqsToMap(outputs, so.outputs);
      var s := SeqsToMap(state, so.state);
      FO(o, s)
    }

    function fo2so(fo: FO): (so: SO)
      requires Valid()
      requires FOValid(fo, outputs, state)
      ensures SOValid(so, outputs, state)
    {
      var o := seq(|outputs|, (index: nat) requires index < |outputs| =>
        reveal Seq.ToSet();
        fo.outputs[outputs[index]]);
      var s := seq(|state|, (index: nat) requires index < |state| =>
        reveal Seq.ToSet();
        fo.state[state[index]]);
      reveal Valid();
      reveal Seq.HasNoDuplicates();
      OutputsHasNoDuplicates();
      SO(o, s)
    }

    function fi2si(fi: FI): (si: SI)
      requires Valid()
      requires FIValid(fi, inputs, state)
      ensures SIValid(si, inputs, state)
    {
      var i := seq(|inputs|, (index: nat) requires index < |inputs| =>
        reveal Seq.ToSet();
        fi.inputs[inputs[index]]);
      var s := seq(|state|, (index: nat) requires index < |state| =>
        reveal Seq.ToSet();
        fi.state[state[index]]);
      reveal Valid();
      reveal Seq.HasNoDuplicates();
      InputsHasNoDuplicates();
      SI(i, s)
    }

    lemma fi2si2fi(fi: FI)
      requires Valid()
      requires FIValid(fi, inputs, state)
      ensures si2fi(fi2si(fi)) == fi
    {
      var si := fi2si(fi);
      assert si.inputs == seq(|inputs|, (index: nat) requires index < |inputs| =>
        reveal Seq.ToSet();
        fi.inputs[inputs[index]]);
      var fi_next := si2fi(si);
      assert fi_next.inputs == SeqsToMap(inputs, si.inputs);
      forall np | np in fi.inputs
        ensures fi_next.inputs[np] == fi.inputs[np]
      {
        reveal Seq.ToSet();
        assert np in inputs;
        var index := Seq.IndexOf(inputs, np);
        assert si.inputs[index] == fi.inputs[np];
        reveal MapMatchesSeqs();
        reveal SeqsToMap();
        assert fi_next.inputs[np] == si.inputs[index];
      }
      assert fi_next.inputs == fi.inputs;

      assert fi_next.state == SeqsToMap(state, si.state);
      forall n | n in fi.state
        ensures fi_next.state[n] == fi.state[n]
      {
        reveal Seq.ToSet();
        assert n in state;
        var index := Seq.IndexOf(state, n);
        assert si.state[index] == fi.state[n];
        reveal MapMatchesSeqs();
        reveal SeqsToMap();
        assert fi_next.state[n] == si.state[index];
      }
      assert fi_next.inputs == fi.inputs;
    }

    lemma fo2so2fo(fo: FO)
      requires Valid()
      requires FOValid(fo, outputs, state)
      ensures so2fo(fo2so(fo)) == fo
    {
      var so := fo2so(fo);
      assert so.outputs == seq(|outputs|, (index: nat) requires index < |outputs| =>
        reveal Seq.ToSet();
        fo.outputs[outputs[index]]);
      var fo_next := so2fo(so);
      assert fo_next.outputs == SeqsToMap(outputs, so.outputs);
      forall np | np in fo.outputs
        ensures fo_next.outputs[np] == fo.outputs[np]
      {
        reveal Seq.ToSet();
        assert np in outputs;
        var index := Seq.IndexOf(outputs, np);
        assert so.outputs[index] == fo.outputs[np];
        reveal MapMatchesSeqs();
        reveal SeqsToMap();
        assert fo_next.outputs[np] == so.outputs[index];
      }
      assert fo_next.outputs == fo.outputs;

      assert fo_next.state == SeqsToMap(state, so.state);
      forall n | n in fo.state
        ensures fo_next.state[n] == fo.state[n]
      {
        reveal Seq.ToSet();
        assert n in state;
        var index := Seq.IndexOf(state, n);
        assert so.state[index] == fo.state[n];
        reveal MapMatchesSeqs();
        reveal SeqsToMap();
        assert fo_next.state[n] == so.state[index];
      }
      assert fo_next.outputs == fo.outputs;
    }

    lemma si2fi2si(si: SI)
      requires Valid()
      requires SIValid(si, inputs, state)
      ensures fi2si(si2fi(si)) == si
    {
      reveal MapMatchesSeqs();
      reveal SeqsToMap();
    }

    lemma so2fo2so(so: SO)
      requires Valid()
      requires SOValid(so, outputs, state)
      ensures fo2so(so2fo(so)) == so
    {
      reveal MapMatchesSeqs();
      reveal SeqsToMap();
    }

    function f(fi: FI): (fo: FO)
      requires Valid()
      requires FIValid(fi, inputs, state)
      ensures FOValid(fo, outputs, state)
    {
      var si := fi2si(fi);
      assert SIValid(si, inputs, state);
      reveal Valid();
      var so := sf(si);
      var fo := so2fo(so);
      fo
    }

    lemma NotInBothOutputsAndStateINPs(np: NP)
      requires Valid()
      ensures !(np in outputs && np in StateINPs(state))
    {
      reveal Valid();
      StateINPsSeqSame(state);
      reveal Seq.ToSet();
    }

    lemma NotInBothInputsAndStateONPs(np: NP)
      requires Valid()
      ensures !(np in inputs && np in StateONPs(state))
    {
      reveal Valid();
      StateONPsSeqSame(state);
      reveal Seq.ToSet();
    }

  }

  function StateINPsSeq(state: seq<CNode>): seq<NP>
  {
    seq(|state|, (i: nat) requires i < |state| => NP(state[i], INPUT_0))
  }

  lemma StateINPsSeqNoDuplicates(state: seq<CNode>)
    requires Seq.HasNoDuplicates(state)
    ensures Seq.HasNoDuplicates(StateINPsSeq(state))
  {
    reveal Seq.HasNoDuplicates();
  }

  lemma StateINPsSeqSame(state: seq<CNode>)
    requires Seq.HasNoDuplicates(state)
    ensures Seq.ToSet(StateINPsSeq(state)) == StateINPs(state)
  {
    reveal Seq.HasNoDuplicates();
    reveal Seq.ToSet();
    if |state| == 0 {
    } else {
      var s := state[0];
      var smaller_state := state[1..];
      StateINPsSeqSame(smaller_state);
      assert s !in smaller_state;
      var smaller_inps_set := StateINPs(smaller_state);
      var smaller_inps_seq := StateINPsSeq(smaller_state);
      assert Seq.ToSet(smaller_inps_seq) == smaller_inps_set;
      assert StateINPsSeq(state) == [NP(s, INPUT_0)] + smaller_inps_seq;
      assert StateINPs(state) == {NP(s, INPUT_0)} + smaller_inps_set;
    }
  }

  lemma StateONPsSeqSame(state: seq<CNode>)
    requires Seq.HasNoDuplicates(state)
    ensures Seq.ToSet(StateONPsSeq(state)) == StateONPs(state)
  {
    reveal Seq.HasNoDuplicates();
    reveal Seq.ToSet();
    if |state| == 0 {
    } else {
      var s := state[0];
      var smaller_state := state[1..];
      StateONPsSeqSame(smaller_state);
      assert s !in smaller_state;
      var smaller_onps_set := StateONPs(smaller_state);
      var smaller_onps_seq := StateONPsSeq(smaller_state);
      assert Seq.ToSet(smaller_onps_seq) == smaller_onps_set;
      assert StateONPsSeq(state) == [NP(s, OUTPUT_0)] + smaller_onps_seq;
      assert StateONPs(state) == {NP(s, OUTPUT_0)} + smaller_onps_set;
    }
  }

  function StateONPsSeq(state: seq<CNode>): seq<NP>
  {
    seq(|state|, (i: nat) requires i < |state| => NP(state[i], OUTPUT_0))
  }

  lemma StateONPsSeqNoDuplicates(state: seq<CNode>)
    requires Seq.HasNoDuplicates(state)
    ensures Seq.HasNoDuplicates(StateONPsSeq(state))
  {
    reveal Seq.HasNoDuplicates();
  }

  lemma StateONPsSeqContains(state: seq<CNode>, n: CNode)
    ensures (n in state) == (NP(n, OUTPUT_0) in StateONPsSeq(state))
  {
    if n in state {
      var index: nat :| index < |state| && state[index] == n;
      assert StateONPsSeq(state)[index] == NP(n, OUTPUT_0);
    } else {
    }
  }

  lemma StateONPsSeqNoIntersection(state1: seq<CNode>, state2: seq<CNode>)
    requires SeqsNoIntersection(state1, state2)
    ensures SeqsNoIntersection(StateONPsSeq(state1), StateONPsSeq(state2))
  {
    reveal Seq.ToSet();
    assert forall x: CNode, y: CNode :: x in Seq.ToSet(state1) && y in Seq.ToSet(state2) ==> x != y;
    assert forall x: CNode :: (x in Seq.ToSet(state1)) == (x in state1);
    assert forall x: CNode :: (x in Seq.ToSet(state2)) == (x in state2);
    assert forall x: CNode, y: CNode :: x in state1 && y in state2 ==> x != y;
    forall x: CNode
      ensures (x in state1) == (NP(x, OUTPUT_0) in StateONPsSeq(state1))
    {
      StateONPsSeqContains(state1, x);
    }
    assert forall x: CNode :: (x in state1) == (NP(x, OUTPUT_0) in StateONPsSeq(state1));
    assert forall x: CNode, y: CNode :: (NP(x, OUTPUT_0) in StateONPsSeq(state1)) && (NP(y, OUTPUT_0) in StateONPsSeq(state2)) ==> x != y;
  }

  function StateINPs(state: seq<CNode>): set<NP>
  {
    (set n | n in state :: NP(n, INPUT_0))
  }

  function StateONPs(state: seq<CNode>): set<NP>
  {
    (set n | n in state :: NP(n, OUTPUT_0))
  }

  function StateONPsFromSet(state: set<CNode>): set<NP>
  {
    (set n | n in state :: NP(n, OUTPUT_0))
  }

  function MFLookupOutput(mf: MapFunction, fi: FI, np: NP): bool
    requires mf.Valid()
    requires FIValid(fi, mf.inputs, mf.state)
    requires np in mf.outputs
  {
    reveal mf.Valid();
    var fo := mf.f(fi);
    assert FOValid(fo, mf.outputs, mf.state);
    reveal Seq.ToSet();
    fo.outputs[np]
  }

  function MFLookupState(mf: MapFunction, fi: FI, np: NP): bool
    requires mf.Valid()
    requires FIValid(fi, mf.inputs, mf.state)
    requires np in StateINPs(mf.state)
  {
    reveal mf.Valid();
    var fo := mf.f(fi);
    assert FOValid(fo, mf.outputs, mf.state);
    reveal Seq.ToSet();
    fo.state[np.n]
  }

  function MFLookup(mf: MapFunction, fi: FI, np: NP): bool
    requires mf.Valid()
    requires FIValid(fi, mf.inputs, mf.state)
    requires np in mf.outputs || np in StateINPs(mf.state)
  {
    assert !((np in mf.outputs) && (np in StateINPs(mf.state))) by {
      reveal mf.Valid();
      reveal Seq.ToSet();
      StateINPsSeqSame(mf.state);
    }
    if (np in mf.outputs) then
      MFLookupOutput(mf, fi, np)
    else
      MFLookupState(mf, fi, np)
  }

  opaque ghost predicate MapFunctionsEquiv(mf1: MapFunction, mf2: MapFunction)
    requires mf1.Valid()
    requires mf2.Valid()
  {
    reveal MapFunction.Valid();
    && mf1.inputs == mf2.inputs
    && mf1.outputs == mf2.outputs
    && mf1.state == mf2.state
    && forall fi: FI :: FIValid(fi, mf1.inputs, mf1.state) ==> (
      mf1.f(fi) == mf2.f(fi)
    )
  }

  opaque ghost predicate MapFunctionsSFEquiv(mf1: MapFunction, mf2: MapFunction)
    requires mf1.Valid()
    requires mf2.Valid()
  {
    reveal MapFunction.Valid();
    && mf1.inputs == mf2.inputs
    && mf1.outputs == mf2.outputs
    && mf1.state == mf2.state
    && forall si: SI :: SIValid(si, mf1.inputs, mf1.state) ==> (
      mf1.sf(si) == mf2.sf(si)
    )
  }

  lemma MapFunctionsEquivSFEquiv(mf1: MapFunction, mf2: MapFunction)
    requires mf1.Valid()
    requires mf2.Valid()
    requires MapFunctionsSFEquiv(mf1, mf2)
    ensures MapFunctionsEquiv(mf1, mf2)
  {
    reveal MapFunctionsSFEquiv();
    reveal MapFunction.Valid();
    forall fi: FI | FIValid(fi, mf1.inputs, mf1.state)
      ensures mf1.f(fi) == mf2.f(fi)
    {
      var si1 := mf1.fi2si(fi);
      var si2 := mf2.fi2si(fi);
      mf1.fi2si2fi(fi);
      mf2.fi2si2fi(fi);
      assert si1 == si2;
      var so1 := mf1.sf(si1);
      var so2 := mf2.sf(si2);
      assert so1 == so2;
      var fo1 := mf1.f(fi);
      var fo2 := mf2.f(fi);
      assert fo1 == mf1.so2fo(so1);
      assert fo2 == mf2.so2fo(so2);
      assert fo1 == fo2;
    }
    reveal MapFunctionsEquiv();
  }

  datatype RFunction = RFunction(
    input_width: nat,
    output_width: nat,
    state_width: nat,
    sf: SI --> SO
  ) {
    predicate SIValid(si: SI)
    {
      && (|si.inputs| == input_width)
      && (|si.state| == state_width)
    }
    predicate SOValid(so: SO)
    {
      && (|so.outputs| == output_width)
      && (|so.state| == state_width)
    }

    opaque ghost predicate Valid()
    {
      && forall si: SI :: SIValid(si) ==> (sf.requires(si) && SOValid(sf(si)))
    }

    lemma SFBehaves(si: SI)
      requires Valid()
      requires SIValid(si)
      ensures sf.requires(si)
      ensures SOValid(sf(si))
    {
      reveal Valid();
    }

    opaque ghost predicate MFConsistent(mf: MapFunction)
      requires Valid()
    {
      reveal Valid();
      && (|mf.inputs| == input_width)
      && (|mf.outputs| == output_width)
      && (|mf.state| == state_width)
      && (forall si :: SIValid(si) ==> mf.sf.requires(si) && mf.sf(si) == sf(si))
    }
  }

  opaque ghost predicate RFunctionEquiv(rf1: RFunction, rf2: RFunction)
    requires rf1.Valid()
    requires rf2.Valid()
  {
    reveal RFunction.Valid();
    && rf1.input_width == rf2.input_width
    && rf1.output_width == rf2.output_width
    && rf1.state_width == rf2.state_width
    && (forall si: SI :: rf1.SIValid(si) ==> rf1.sf(si) == rf2.sf(si))
  }

  const NullMF := MapFunction(
    [], [], [],
    (si: SI) requires |si.inputs| == 0 && |si.state| == 0 => SO([], []))

  lemma NullMFValid()
    ensures NullMF.Valid()
  {
    reveal MapFunction.Valid();
    reveal Seq.ToSet();
    reveal Seq.HasNoDuplicates();
  }

}
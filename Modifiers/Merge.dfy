module Modifiers.Merge {
  
  import opened Circ
  import opened Scuf
  import opened MapFunction
  import opened ConservedSubcircuit
  import opened Subcircuit
  import opened Utils
  import opened Eval
  import opened Path
  import opened Path2

  predicate ScufMapsCanMerge(mp1: ScufMap, mp2: ScufMap)
  {
    && SeqsNoIntersection(mp1.inputs, mp2.inputs)
    && SeqsNoIntersection(mp1.outputs, mp2.outputs)
    && SeqsNoIntersection(mp1.inputs, mp2.outputs)
    && SeqsNoIntersection(mp1.outputs, mp2.inputs)
    && SeqsNoIntersection(mp1.state, mp2.state)
    && SeqsNoIntersection(mp1.inputs, StateONPsSeq(mp2.state))
    && SeqsNoIntersection(mp2.inputs, StateONPsSeq(mp1.state))
    && SeqsNoIntersection(mp1.outputs, StateINPsSeq(mp2.state))
    && SeqsNoIntersection(mp2.outputs, StateINPsSeq(mp1.state))
  }

  function MergeScufMaps(mp1: ScufMap, mp2: ScufMap): (mp: ScufMap)
    requires mp1.Valid()
    requires mp2.Valid()
    requires ScufMapsCanMerge(mp1, mp2)
    ensures mp.Valid()
  {
    var inputs := mp1.inputs + mp2.inputs;
    var outputs := mp1.outputs + mp2.outputs;
    var state := mp1.state + mp2.state;
    assert Seq.HasNoDuplicates(inputs) by {
      NoDuplicatesInConcat(mp1.inputs, mp2.inputs);
    }
    assert Seq.HasNoDuplicates(outputs) by {
      NoDuplicatesInConcat(mp1.outputs, mp2.outputs);
    }
    assert Seq.HasNoDuplicates(state) by {
      NoDuplicatesInConcat(mp1.state, mp2.state);
    }
    assert SeqsNoIntersection(inputs, outputs) by {
      ConcatSeqsNoIntersection(mp1.inputs, mp2.inputs, mp1.outputs, mp2.outputs);
    }
    assert SeqsNoIntersection(inputs, StateONPsSeq(state)) by {
      ConcatSeqsNoIntersection(mp1.inputs, mp2.inputs, StateONPsSeq(mp1.state), StateONPsSeq(mp2.state));
      assert StateONPsSeq(state) == StateONPsSeq(mp1.state) + StateONPsSeq(mp2.state);
    }
    assert SeqsNoIntersection(outputs, StateINPsSeq(state)) by {
      ConcatSeqsNoIntersection(mp1.outputs, mp2.outputs, StateINPsSeq(mp1.state), StateINPsSeq(mp2.state));
      assert StateINPsSeq(state) == StateINPsSeq(mp1.state) + StateINPsSeq(mp2.state);
    }
    ScufMap(inputs, outputs, state)
  }

  function MergeSF(uf1: UpdateFunction, uf2: UpdateFunction, si: SI): (so: SO)
    requires uf1.Valid()
    requires uf2.Valid()
    requires |si.inputs| == uf1.input_width + uf2.input_width
    requires |si.state| == uf1.state_width + uf2.state_width
    ensures |so.outputs| == uf1.output_width + uf2.output_width
    ensures |so.state| == uf1.state_width + uf2.state_width
  {
    var si1 := SI(si.inputs[..uf1.input_width], si.state[..uf1.state_width]);
    var si2 := SI(si.inputs[uf1.input_width..], si.state[uf1.state_width..]);
    reveal UpdateFunction.Valid();
    var so1 := uf1.sf(si1);
    var so2 := uf2.sf(si2);
    var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
    so
  }

  function MergeUpdateFunctions(uf1: UpdateFunction, uf2: UpdateFunction): (uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    ensures uf.Valid()
  {
    var input_width := uf1.input_width + uf2.input_width;
    var output_width := uf1.output_width + uf2.output_width;
    var state_width := uf1.state_width + uf2.state_width;
    reveal UpdateFunction.Valid();
    UpdateFunction(
      input_width, output_width, state_width,
      (si: SI) requires |si.inputs| == input_width && |si.state| == state_width => MergeSF(uf1, uf2, si)
    )
  }

  //lemma MergeUpdateFunctionProperties(uf1: UpdateFunction, uf2: UpdateFunction)
  //      EvalOk(MFLookup(s1, fi1, np));
  //      EvalOk(MFLookup(s, fi, np));

  lemma MergeF1Properties(c: Circuit, s1: Scuf, s2: Scuf, np: NP, fi: FI)
    requires MergeRequirements(c, s1, s2)
    requires np in s1.mp.outputs || np in StateINPs(s1.mp.state)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var s := MergeScufsImpl(c, s1, s2);
      var fi1 := MergeFI1(c, s1, s2, fi);
      && (MFLookup(s, fi, np) == MFLookup(s1, fi1, np))
  {
    reveal Seq.ToSet();
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var si1 := SI(si.inputs[..s1.uf.input_width], si.state[..s1.uf.state_width]);
    var si2 := SI(si.inputs[s1.uf.input_width..], si.state[s1.uf.state_width..]);
    reveal UpdateFunction.Valid();
    reveal NPsInSc();
    s1.mp.si2fi2si(si1);
    s2.mp.si2fi2si(si2);
    reveal SeqsToMap();
    reveal MapMatchesSeqs();
    reveal MapToSeq();
  }

  lemma MergeF2Properties(c: Circuit, s1: Scuf, s2: Scuf, np: NP, fi: FI)
    requires MergeRequirements(c, s1, s2)
    requires np in s2.mp.outputs || np in StateINPs(s2.mp.state)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var s := MergeScufsImpl(c, s1, s2);
      var fi2 := MergeFI2(c, s1, s2, fi);
      && (MFLookup(s, fi, np) == MFLookup(s2, fi2, np))
  {
    reveal Seq.ToSet();
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var si1 := SI(si.inputs[..s1.uf.input_width], si.state[..s1.uf.state_width]);
    var si2 := SI(si.inputs[s1.uf.input_width..], si.state[s1.uf.state_width..]);
    reveal UpdateFunction.Valid();
    reveal NPsInSc();
    s1.mp.si2fi2si(si1);
    s2.mp.si2fi2si(si2);
    reveal SeqsToMap();
    reveal MapMatchesSeqs();
    reveal MapToSeq();
    var fi2 := MergeFI2(c, s1, s2, fi);
    var so2 := s2.uf.sf(si2);
    var fo2 := s2.mp.so2fo(so2);
    var so := s.uf.sf(si);
    var fo := s.mp.so2fo(so);
    MergeFO1FO2Properties(c, s1, s2, fi);
    if np in s2.mp.outputs {
      assert MFLookup(s2, fi2, np) == fo2.outputs[np];
      assert MFLookup(s, fi, np) == fo.outputs[np];
    } else {
      assert MFLookup(s2, fi2, np) == fo2.state[np.n];
      assert MFLookup(s, fi, np) == fo.state[np.n];
    }
    assert (MFLookup(s, fi, np) == MFLookup(s2, fi2, np));
  }

  lemma ScufsNoIntersectionMapsCanMerge(c: Circuit, s1: Scuf, s2: Scuf)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires s1.sc !! s2.sc
    ensures ScufMapsCanMerge(s1.mp, s2.mp)
  {
    FInputsInSc(c, s1);
    FInputsInSc(c, s2);
    FOutputsInSc(c, s1);
    FOutputsInSc(c, s2);
    reveal NPsInSc();
    reveal Seq.ToSet();
  }

  ghost predicate MergeRequirements(c: Circuit, s1: Scuf, s2: Scuf)
  {
    && c.Valid()
    && s1.Valid(c)
    && s2.Valid(c)
    && s1.sc !! s2.sc
    && IsIsland(c, s1.sc)
    && IsIsland(c, s2.sc)
  }

  lemma IslandScufsAllInputsAdd(c: Circuit, s1: Scuf, s2:Scuf)
    requires MergeRequirements(c, s1, s2)
    ensures
      reveal ScValid();
      AllInputs(c, s1.sc + s2.sc) == AllInputs(c, s1.sc) + AllInputs(c, s2.sc)
  {
    reveal UnconnInputs();
    reveal ConnInputs();
    reveal ScValid();
    assert UnconnInputs(c, s1.sc + s2.sc) == UnconnInputs(c, s1.sc) + UnconnInputs(c, s2.sc);
    IsIslandNoInputs(c, s1.sc);
    IsIslandNoInputs(c, s2.sc);
    assert ConnInputs(c, s1.sc + s2.sc) == ConnInputs(c, s1.sc) + ConnInputs(c, s2.sc) by {
      assert ConnInputs(c, s1.sc + s2.sc) <= ConnInputs(c, s1.sc) + ConnInputs(c, s2.sc);
      assert ConnInputs(c, s1.sc + s2.sc) >= ConnInputs(c, s1.sc) + ConnInputs(c, s2.sc) by {
      }
    }
  }

  lemma MergeFICircuitValid(c: Circuit, s1: Scuf, s2: Scuf, np: NP, fi: FI)
    requires MergeRequirements(c, s1, s2)
    requires np in s1.mp.outputs || np in s2.mp.outputs ||
             np in StateINPs(s1.mp.state) || np in StateINPs(s2.mp.state)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var s := MergeScufsImpl(c, s1, s2);
      assert NPValid(c, np) by {
        ScufFOutputsAreValid(c, s1);
        ScufFOutputsAreValid(c, s2);
      }
      && FICircuitValid(c, fi)
  {
    reveal Seq.ToSet();
    var s := MergeScufsImpl(c, s1, s2);
    assert FICircuitValid(c, fi) by {
      reveal Circuit.Valid();
      ScufFInputsAreValid(c, s1);
      ScufFInputsAreValid(c, s2);
      assert s.mp.inputs == s1.mp.inputs + s2.mp.inputs;
      assert forall np :: np in s.mp.inputs ==> INPValid(c, np);
      assert (forall np :: np in fi.inputs.Keys ==> INPValid(c, np));
      reveal AllSeq();
      reveal ScValid();
      reveal Scuf.SomewhatValid();
      assert Seq.ToSet(s1.mp.state) == AllSeq(c, s1.sc);
      assert Seq.ToSet(s2.mp.state) == AllSeq(c, s2.sc);
      assert (forall n :: n in fi.state.Keys ==> n in c.NodeKind);
      assert forall n :: n in AllSeq(c, s1.sc) ==> c.NodeKind[n].CSeq?;
      assert forall n :: n in Seq.ToSet(s1.mp.state) ==> c.NodeKind[n].CSeq?;
      assert forall n :: n in Seq.ToSet(s2.mp.state) ==> c.NodeKind[n].CSeq?;
      assert forall n :: n in s1.mp.state ==> c.NodeKind[n].CSeq?;
      assert forall n :: n in s2.mp.state ==> c.NodeKind[n].CSeq?;
      assert (forall n :: n in fi.state.Keys ==> c.NodeKind[n].CSeq?);
      reveal FICircuitValid();
    }
  }

  function MergeFI1(c: Circuit, s1: Scuf, s2: Scuf, fi: FI): (fi1: FI)
    requires MergeRequirements(c, s1, s2)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
  {
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var si1 := SI(si.inputs[..s1.uf.input_width], si.state[..s1.uf.state_width]);
    var fi1 := s1.mp.si2fi(si1);
    fi1
  }

  function MergeFI2(c: Circuit, s1: Scuf, s2: Scuf, fi: FI): (fi1: FI)
    requires MergeRequirements(c, s1, s2)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
  {
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var si2 := SI(si.inputs[s1.uf.input_width..], si.state[s1.uf.state_width..]);
    var fi2 := s2.mp.si2fi(si2);
    fi2
  }

  function MergeFO1(c: Circuit, s1: Scuf, s2: Scuf, fi: FI): (fo1: FO)
    requires MergeRequirements(c, s1, s2)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
  {
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var si1 := SI(si.inputs[..s1.uf.input_width], si.state[..s1.uf.state_width]);
    reveal UpdateFunction.Valid();
    var so1 := s1.uf.sf(si1);
    var fo1 := s1.mp.so2fo(so1);
    fo1
  }

  function MergeFO2(c: Circuit, s1: Scuf, s2: Scuf, fi: FI): (fo2: FO)
    requires MergeRequirements(c, s1, s2)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
  {
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var si2 := SI(si.inputs[s1.uf.input_width..], si.state[s1.uf.state_width..]);
    reveal UpdateFunction.Valid();
    var so2 := s2.uf.sf(si2);
    var fo2 := s2.mp.so2fo(so2);
    fo2
  }

  function MergeFO(c: Circuit, s1: Scuf, s2: Scuf, fi: FI): (fo: FO)
    requires MergeRequirements(c, s1, s2)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
  {
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var so := s.uf.sf(si);
    var fo := s.mp.so2fo(so);
    fo
  }

  lemma MergeFI1FI2Properties(c: Circuit, s1: Scuf, s2: Scuf, fi: FI)
    requires MergeRequirements(c, s1, s2)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var fi1 := MergeFI1(c, s1, s2, fi);
      var fi2 := MergeFI2(c, s1, s2, fi);
      && fi.inputs == fi1.inputs + fi2.inputs
      && fi.state == fi1.state + fi2.state
  {
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var si1 := SI(si.inputs[..s1.uf.input_width], si.state[..s1.uf.state_width]);
    var si2 := SI(si.inputs[s1.uf.input_width..], si.state[s1.uf.state_width..]);
    assert si.inputs == si1.inputs + si2.inputs;
    assert si.state == si1.state + si2.state;
    var fi1 := s1.mp.si2fi(si1);
    var fi2 := s2.mp.si2fi(si2);
    reveal SeqsToMap();
    assert Seq.ToSet(s1.mp.inputs) !! Seq.ToSet(s2.mp.inputs) by {
      FInputsInSc(c, s1);
      FInputsInSc(c, s2);
      reveal NPsInSc();
    }
    SeqsToMapAdd(s1.mp.inputs, si1.inputs, s2.mp.inputs, si2.inputs);
    SeqsToMapAdd(s1.mp.state, si1.state, s2.mp.state, si2.state);
    s.mp.fi2si2fi(fi);
  }

  lemma MergeFO1FO2Properties(c: Circuit, s1: Scuf, s2: Scuf, fi: FI)
    requires MergeRequirements(c, s1, s2)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var fo1 := MergeFO1(c, s1, s2, fi);
      var fo2 := MergeFO2(c, s1, s2, fi);
      var fo := MergeFO(c, s1, s2, fi);
      && fo.outputs == fo1.outputs + fo2.outputs
      && fo.state == fo1.state + fo2.state
  {
    var s := MergeScufsImpl(c, s1, s2);
    var si := s.mp.fi2si(fi);
    var so := s.uf.sf(si);
    var si1 := SI(si.inputs[..s1.uf.input_width], si.state[..s1.uf.state_width]);
    var si2 := SI(si.inputs[s1.uf.input_width..], si.state[s1.uf.state_width..]);
    reveal UpdateFunction.Valid();
    var so1 := s1.uf.sf(si1);
    var so2 := s2.uf.sf(si2);
    assert so.outputs == so1.outputs + so2.outputs;
    assert so.state == so1.state + so2.state;
    var fo1 := s1.mp.so2fo(so1);
    var fo2 := s2.mp.so2fo(so2);
    reveal SeqsToMap();
    assert Seq.ToSet(s1.mp.outputs) !! Seq.ToSet(s2.mp.outputs) by {
      FOutputsInSc(c, s1);
      FOutputsInSc(c, s2);
      reveal NPsInSc();
    }
    SeqsToMapAdd(s1.mp.outputs, so1.outputs, s2.mp.outputs, so2.outputs);
    SeqsToMapAdd(s1.mp.state, so1.state, s2.mp.state, so2.state);
    s.mp.fi2si2fi(fi);
  }

  lemma MergeNoPathBetweenOutputsAndInputs(c: Circuit, s1: Scuf, s2: Scuf, np: NP)
    requires MergeRequirements(c, s1, s2)
    ensures
      var s1_outputs := Seq.ToSet(s1.mp.outputs) + StateINPs(s1.mp.state);
      var s2_inputs := Seq.ToSet(s2.mp.inputs) + StateONPs(s2.mp.state);
      !PathExistsBetweenNPSets(c, s1_outputs, s2_inputs)
  {
    var s1_outputs := Seq.ToSet(s1.mp.outputs) + StateINPs(s1.mp.state);
    var s2_inputs := Seq.ToSet(s2.mp.inputs) + StateONPs(s2.mp.state);
    forall np_1: NP, np_2: NP | np_1 in s1_outputs && np_2 in s2_inputs
      ensures !PathExists(c, np_1, np_2)
    {
      reveal ScValid();
      FOutputsInSc(c, s1);
      FOutputsInSc(c, s2);
      reveal NPsInSc();
      assert np_1.n in s1.sc;
      assert np_2.n in s2.sc;
      NoPathOutOfIsland(c, s1.sc, np_1, np_2);
    }
    reveal PathExists();
    reveal PathExistsBetweenNPSets();
  }

  lemma MergeEvaluatesCorrectly(c: Circuit, s1: Scuf, s2: Scuf, np: NP, fi: FI)
    requires MergeRequirements(c, s1, s2)
    requires np in s1.mp.outputs || np in s2.mp.outputs ||
             np in StateINPs(s1.mp.state) || np in StateINPs(s2.mp.state)
    requires
      var s := MergeScufsImpl(c, s1, s2);
      FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var s := MergeScufsImpl(c, s1, s2);
      assert NPValid(c, np) by {
        ScufFOutputsAreValid(c, s1);
        ScufFOutputsAreValid(c, s2);
      }
      && FICircuitValid(c, fi)
      && (Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np)))
  {
    reveal Seq.ToSet();
    var s := MergeScufsImpl(c, s1, s2);
    MergeFICircuitValid(c, s1, s2, np, fi);
    var si := s.mp.fi2si(fi);
    var si1 := SI(si.inputs[..s1.uf.input_width], si.state[..s1.uf.state_width]);
    var si2 := SI(si.inputs[s1.uf.input_width..], si.state[s1.uf.state_width..]);
    var fi1 := s1.mp.si2fi(si1);
    var fi2 := s2.mp.si2fi(si2);
    assert NPValid(c, np) by {
      ScufFOutputsAreValid(c, s1);
      ScufFOutputsAreValid(c, s2);
    }
    reveal s.EvaluatesCorrectly();
    if np in s1.mp.outputs || np in StateINPs(s1.mp.state) {
      ScufValidFiValidToFICircuitValid(c, s1, fi1);
      assert Evaluate(c, np, fi1) == EvalOk(MFLookup(s1, fi1, np));
    } else {
      ScufValidFiValidToFICircuitValid(c, s2, fi2);
      assert Evaluate(c, np, fi2) == EvalOk(MFLookup(s2, fi2, np));
    }
    // No paths from the output of one scuf to the input of the other.
    MergeNoPathBetweenOutputsAndInputs(c, s1, s2, np);
    MergeNoPathBetweenOutputsAndInputs(c, s2, s1, np);
    assert fi.inputs.Keys == fi1.inputs.Keys + fi2.inputs.Keys;
    assert fi1.inputs.Keys !! fi2.inputs.Keys by {
      FInputsInSc(c, s1);
      FInputsInSc(c, s2);
      reveal NPsInSc();
    }
    MergeFI1FI2Properties(c, s1, s2, fi);
    if np in s1.mp.outputs || np in StateINPs(s1.mp.state) {
      var state_onps := StateONPsFromSet(fi2.state.Keys);
      assert !PathExistsToNPSet(c, np, fi2.inputs.Keys) && !PathExistsToNPSet(c, np, state_onps) by {
        var s1_outputs := Seq.ToSet(s1.mp.outputs) + StateINPs(s1.mp.state);
        var s2_inputs := Seq.ToSet(s2.mp.inputs) + StateONPs(s2.mp.state);
        reveal PathExistsToNPSet();
        reveal PathExistsBetweenNPSets();
        NoPathExistsBetweenNPSetsToToNPSet(c, s1_outputs, s2_inputs, np);
        NoPathExistsToNPSubSet(c, np, s2_inputs, fi2.inputs.Keys);
        NoPathExistsToNPSubSet(c, np, s2_inputs, StateONPsFromSet(fi2.state.Keys));
      }
      EvaluateReduceFI(c, np, fi, fi2.inputs.Keys, fi2.state.Keys);
      assert fi1.inputs.Keys == fi.inputs.Keys - fi2.inputs.Keys;
      assert forall x: NP :: x in fi1.inputs && x in fi.inputs ==> fi1.inputs[x] == fi.inputs[x];
      assert fi1.inputs == fi.inputs - fi2.inputs.Keys;
      assert fi1 == FI(fi.inputs - fi2.inputs.Keys, fi.state - fi2.state.Keys);
      calc {
        Evaluate(c, np, fi);
        Evaluate(c, np, fi1);
        EvalOk(MFLookup(s1, fi1, np));
        {
          MergeF1Properties(c, s1, s2, np, fi);
        }
        EvalOk(MFLookup(s, fi, np));
      }
    } else {
      var state_onps := StateONPsFromSet(fi1.state.Keys);
      assert !PathExistsToNPSet(c, np, fi1.inputs.Keys) && !PathExistsToNPSet(c, np, state_onps) by {
        var s2_outputs := Seq.ToSet(s2.mp.outputs) + StateINPs(s2.mp.state);
        var s1_inputs := Seq.ToSet(s1.mp.inputs) + StateONPs(s1.mp.state);
        reveal PathExistsToNPSet();
        reveal PathExistsBetweenNPSets();
        NoPathExistsBetweenNPSetsToToNPSet(c, s2_outputs, s1_inputs, np);
        NoPathExistsToNPSubSet(c, np, s1_inputs, fi1.inputs.Keys);
        NoPathExistsToNPSubSet(c, np, s1_inputs, StateONPsFromSet(fi1.state.Keys));
      }
      EvaluateReduceFI(c, np, fi, fi1.inputs.Keys, fi1.state.Keys);
      assert fi2.inputs.Keys == fi.inputs.Keys - fi1.inputs.Keys;
      assert forall x: NP :: x in fi2.inputs && x in fi.inputs ==> fi2.inputs[x] == fi.inputs[x];
      assert fi2.inputs == fi.inputs - fi1.inputs.Keys;
      assert fi2 == FI(fi.inputs - fi1.inputs.Keys, fi.state - fi1.state.Keys);
      calc {
        Evaluate(c, np, fi);
        Evaluate(c, np, fi2);
        EvalOk(MFLookup(s2, fi2, np));
        {
          MergeF2Properties(c, s1, s2, np, fi);
        }
        EvalOk(MFLookup(s, fi, np));
      }
    }

  }

  function MergeScufsImpl(c: Circuit, s1: Scuf, s2: Scuf): (s: Scuf)
    requires MergeRequirements(c, s1, s2)
    ensures s.MapValid()
  {
    var sc := s1.sc + s2.sc;
    assert ScufMapsCanMerge(s1.mp, s2.mp) by {
      ScufsNoIntersectionMapsCanMerge(c, s1, s2);
    }
    var mp := MergeScufMaps(s1.mp, s2.mp);
    var uf := MergeUpdateFunctions(s1.uf, s2.uf);
    var s := Scuf(sc, mp, uf);
    reveal NPsInSc();
    reveal Seq.ToSet();
    s
  }

  function MergeScufs(c: Circuit, s1: Scuf, s2: Scuf): (s: Scuf)
    requires MergeRequirements(c, s1, s2)
    ensures s.Valid(c)
  {
    var s := MergeScufsImpl(c, s1, s2);
    var mp := s.mp;
    var uf := s.uf;
    var sc := s.sc;
    assert s.Valid(c) by {
      assert s.MapValid();
      assert ScValid(c, s.sc) by {
        reveal ScValid();
      }
      assert s.SomewhatValid(c) by {
        assert ScValid(c, sc);
        reveal Seq.ToSet();
        reveal AllONPs();
        reveal ConnOutputs();
        reveal ConnInputs();
        reveal UnconnInputs();
        reveal AllSeq();
        reveal ScValid();
        reveal Scuf.SomewhatValid();
        assert (AllONPs(c, sc) >= Seq.ToSet(mp.outputs) >= ConnOutputs(c, sc)) by {
          assert AllONPs(c, sc) == AllONPs(c, s1.sc) + AllONPs(c, s2.sc);
          assert Seq.ToSet(mp.outputs) == Seq.ToSet(s1.mp.outputs) + Seq.ToSet(s2.mp.outputs);
          assert ConnOutputs(c, sc) <= ConnOutputs(c, s1.sc) + ConnOutputs(c, s2.sc);
          assert AllONPs(c, sc) >= Seq.ToSet(mp.outputs);
          assert Seq.ToSet(mp.outputs) >= ConnOutputs(c, sc);
        }
        assert (Seq.ToSet(mp.inputs) == AllInputs(c, sc)) by {
          assert Seq.ToSet(mp.inputs) == Seq.ToSet(s1.mp.inputs) + Seq.ToSet(s2.mp.inputs);
          IslandScufsAllInputsAdd(c, s1, s2);
          assert AllInputs(c, sc) == AllInputs(c, s1.sc) + AllInputs(c, s2.sc);
        }
        assert (Seq.ToSet(mp.state) == AllSeq(c, sc)) by {
          assert Seq.ToSet(mp.state) == Seq.ToSet(s1.mp.state) + Seq.ToSet(s2.mp.state);
          assert AllSeq(c, sc) == AllSeq(c, s1.sc) + AllSeq(c, s2.sc);
        }
      }
      assert s.EvaluatesCorrectly(c) by {
        reveal Seq.ToSet();
        forall np | np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state)
          ensures ONPValid(c, np) || INPValid(c, np)
        {
          ScufFInputsAreValid(c, s);
          ScufFOutputsAreValid(c, s);
        }
        forall fi: FI | FIValid(fi, s.mp.inputs, s.mp.state)
          ensures FICircuitValid(c, fi)
          ensures forall np :: np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state) ==>
            Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np))
        {
          assert FICircuitValid(c, fi) by {ScufValidFiValidToFICircuitValid(c, s, fi);}
          forall np | np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state)
            ensures Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np))
          {
            MergeEvaluatesCorrectly(c, s1, s2, np, fi);
            assert Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np));
          }
        }
        reveal Scuf.EvaluatesCorrectly();
      }
    }
    s
  }

  function MergeInserter(c: Circuit, z1: ScufInserter, z2: ScufInserter): (r: (Circuit, Scuf))
    requires c.Valid()
    requires z1.Valid()
    requires z2.Valid()
  {
    var (new_c, s1, s2) := InsertTwo(c, z1, z2);
    reveal DualInsertion();
    var s := MergeScufs(new_c, s1, s2);
    (new_c, s)
  }

  function MergeModifier(z1: ScufInserter, z2: ScufInserter): (r: ScufInserter)
    requires z1.Valid()
    requires z2.Valid()
  {
    reveal ScufInserter.Valid();
    var uf := MergeUpdateFunctions(z1.uf, z2.uf);
    ScufInserter(
      uf,
      (c: Circuit) requires c.Valid() => MergeInserter(c, z1, z2)
    )
  }

}
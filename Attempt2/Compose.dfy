module Compose {

  import opened Circ
  import opened Utils
  import opened MapFunction
  import opened Equiv

  ghost opaque predicate ComposedValid(c: Circuit, e1: Equiv, e2: Equiv) {
    CircuitValid(c) &&
    EquivValid(c, e1) &&
    EquivValid(c, e2) &&
    EquivTrue(c, e1) &&
    EquivTrue(c, e2) &&
    SetsNoIntersection(e1.sc, e2.sc) &&
    ScValid(c, e1.sc) && // unnecessary but EquivValid is opaque
    ScValid(c, e2.sc) && // unnecessary but EquivValid is opaque
    (NPBetweenSubcircuits(c, e1.sc, e2.sc) == {})
  }

  lemma {:vcs_split_on_every_assert} SetsNoIntersectionFromComposedValid(c: Circuit, e1: Equiv, e2: Equiv)
  requires ComposedValid(c, e1, e2)
  ensures SetsNoIntersection(e1.sc, e2.sc)
  ensures SetsNoIntersection(e1.inputs, e2.inputs)
  ensures SetsNoIntersection(e1.outputs, e2.outputs)
  ensures SetsNoIntersection(e1.inputs, e2.outputs)
  ensures SetsNoIntersection(e1.outputs, e2.inputs)
  {
    reveal ComposedValid();
    reveal ScValid();
    reveal EquivValid();
    reveal NPsValidAndInSc();
  }

  lemma CircuitValidFromComposedValid(c: Circuit, e1: Equiv, e2: Equiv)
  requires ComposedValid(c, e1, e2)
  ensures CircuitValid(c)
  {
    reveal ComposedValid();
  }


  function ComposeEquiv(c: Circuit, e1: Equiv, e2: Equiv): (r: Equiv)
    requires ComposedValid(c, e1, e2)
    ensures EquivValid(c, r)
  {
    reveal ComposedValid();
    reveal EquivValid();
    var combined_input_keys := ComposeEquivInputs(c, e1, e2);
    var e := Equiv(
      CombineSets(e1.sc, e2.sc),
      combined_input_keys,
      e1.outputs + e2.outputs,
      (combined_inputs: map<NP, bool>) requires combined_inputs.Keys == combined_input_keys => ComposeEquivF(c, e1, e2, combined_inputs)
    );
    assert ScValid(c, e.sc) by {reveal ScValid();}
    assert (ScInputBoundary(c, e.sc) == e.inputs) by {
      ComposeEquivInputsCorrect(c, e1, e2);
    }
    assert SetsNoIntersection(e.inputs, e.outputs) by {
      SetsNoIntersectionFromComposedValid(c, e1, e2);
    }
    assert NPsValidAndInSc(c, e.sc, e.outputs) by {reveal NPsValidAndInSc();}
    assert NPsValidAndInSc(c, e.sc, e.inputs) by {reveal NPsValidAndInSc();}
    assert MapFunctionValid(EtoMf(e)) by {reveal MapFunctionValid();}
    assert EquivScOutputsInOutputs(c, e.sc, e.outputs) by {reveal EquivScOutputsInOutputs();}
    assert EquivValid(c, e);
    e
  }

  function ComposeEquivInputs(c: Circuit, e1: Equiv, e2: Equiv): (r: set<NP>)
    requires ComposedValid(c, e1, e2)
    ensures forall np :: np in e1.inputs ==> np in r
  {
    reveal ComposedValid();
    reveal EquivValid();
    (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc)
  }

  lemma {:vcs_split_on_every_assert} ComposeEquivInputsCorrectHelper(c: Circuit, e1: Equiv, e2: Equiv)
    requires ComposedValid(c, e1, e2)
    ensures
      ScValid(c, e1.sc) &&
      ScValid(c, e2.sc) &&
      ScValid(c, e1.sc + e2.sc) &&
      NPBetweenSubcircuitsComplement(c, e1.sc + e2.sc, e1.sc + e2.sc) ==
        NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
        NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
        NPBetweenSubcircuits(c, e2.sc, e1.sc)
  {
    reveal ComposedValid();
    assert ScValid(c, e1.sc);
    assert ScValid(c, e2.sc);
    assert ScValid(c, e1.sc + e2.sc) by {reveal ScValid();}
    assert NPBetweenSubcircuitsComplement(c, e1.sc + e2.sc, e1.sc + e2.sc) ==
        NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) + NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
        NPBetweenSubcircuits(c, e2.sc, e1.sc) - NPBetweenSubcircuits(c, e1.sc, e2.sc);
    assert NPBetweenSubcircuits(c, e1.sc, e2.sc) == {};
  }

  lemma ComposeEquivInputsCorrect(c: Circuit, e1: Equiv, e2: Equiv)
    requires ComposedValid(c, e1, e2)
    ensures ScValid(c, e1.sc + e2.sc)
    ensures
      ScInputBoundary(c, e1.sc + e2.sc) == ComposeEquivInputs(c, e1, e2)
  {
    reveal ComposedValid();
    assert ScValid(c, e1.sc + e2.sc) && ScValid(c, e1.sc) && ScValid(c, e2.sc) by {
      reveal ScValid();
    }
    var ui := UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc);
    var nb :=  NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
               NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
               NPBetweenSubcircuits(c, e2.sc, e1.sc);
    calc {
      ComposeEquivInputs(c, e1, e2);
      (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
      {reveal EquivValid();}
      ScInputBoundary(c, e1.sc) + ScInputBoundary(c, e2.sc)
        - NPBetweenSubcircuits(c, e2.sc, e1.sc);
      NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
        UnconnectedINPs(c, e1.sc) + InternalInputs(c, e1.sc) +
        NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) +
        UnconnectedINPs(c, e2.sc) + InternalInputs(c, e2.sc) -
        NPBetweenSubcircuits(c, e2.sc, e1.sc);
      UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc) +
        NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
        NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
        NPBetweenSubcircuits(c, e2.sc, e1.sc);
      {
        // Need to show that the terms in NPBetweenSubcircuits are not in Unconnected or Internal.
        assert forall np :: np in UnconnectedINPs(c, e1.sc + e2.sc) ==> np !in c.PortSource;
        reveal CircuitValid();
        assert forall np :: np in InternalInputs(c, e1.sc + e2.sc) ==> np !in c.PortSource;
        assert forall np :: np in NPBetweenSubcircuits(c, e2.sc, e1.sc) ==> np in c.PortSource;
      }
      UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc) +
        (NPBetweenSubcircuitsComplement(c, e1.sc, e1.sc) +
        NPBetweenSubcircuitsComplement(c, e2.sc, e2.sc) -
        NPBetweenSubcircuits(c, e2.sc, e1.sc));
      {ComposeEquivInputsCorrectHelper(c, e1, e2);}
      UnconnectedINPs(c, e1.sc + e2.sc) + InternalInputs(c, e1.sc + e2.sc) +
        NPBetweenSubcircuitsComplement(c, e1.sc + e2.sc, e1.sc + e2.sc);
      ScInputBoundary(c, e1.sc + e2.sc);
    }
  }

  lemma ONPNotInKnownsNotInKnowns2(c: Circuit, onp: NP, e1: Equiv, e2: Equiv, knowns: map<NP, bool>)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires onp !in knowns
    requires ONPValid(c, onp)
    ensures onp !in CalculateE2Inputs(c, e1, e2, knowns)
  {
    reveal ComposedValid();
    reveal GoodKnownKeys();
    assert (onp !in (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc));
    var knowns_2 := CalculateE2Inputs(c, e1, e2, knowns);
    var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
    assert forall np :: np in knowns_2 ==> np in e2_inputs_from_e1_keys || np in knowns;
    assert onp !in e2_inputs_from_e1_keys by {
      reveal CircuitValid();
    }
  }

  opaque predicate GoodKnownKeys(c: Circuit, e1: Equiv, e2: Equiv, knowns: map<NP, bool>)
    requires ComposedValid(c, e1, e2)
  {
    knowns.Keys == ComposeEquivInputs(c, e1, e2)
  }

  lemma InE1ButNotE1InputsNotInKnowns(c: Circuit, e1: Equiv, e2: Equiv, knowns: map<NP, bool>, np: NP)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires np.n in e1.sc
    requires np !in e1.inputs
    ensures np !in knowns
  {
    reveal ComposedValid();
    reveal GoodKnownKeys();
    reveal ScValid();
    InThisNotInThat(np.n, e1.sc, e2.sc);
    assert np.n !in e2.sc;
    assert knowns.Keys == (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
    reveal EquivValid();
    reveal NPsValidAndInSc();
    assert np !in e2.inputs;
  }

  lemma InE2ButNotE2InputsNotInKnowns(c: Circuit, e1: Equiv, e2: Equiv, knowns: map<NP, bool>, np: NP)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    requires np.n in e2.sc
    requires np !in e2.inputs
    ensures np !in knowns
  {
    reveal ComposedValid();
    reveal GoodKnownKeys();
    reveal ScValid();
    InThisNotInThat(np.n, e2.sc, e1.sc);
    assert np.n !in e1.sc;
    assert knowns.Keys == (e1.inputs + e2.inputs) - NPBetweenSubcircuits(c, e2.sc, e1.sc);
    reveal EquivValid();
    reveal NPsValidAndInSc();
    assert np !in e2.inputs;
  }

  function CalculateE2Inputs(c: Circuit, e1: Equiv, e2: Equiv, knowns: map<NP, bool>): (r: map<NP, bool>)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
  {
    reveal ComposedValid();
    reveal EquivValid();
    reveal CircuitValid();
    reveal GoodKnownKeys();
    var mf1 := EtoMf(e1);
    var mf2 := EtoMf(e2);
    assert MapFunctionValid(mf1);
    assert MapFunctionValid(mf2);
    var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
    var e2_inputs_from_e1 := (map np | np in e2_inputs_from_e1_keys :: np := c.PortSource[np]);
    assert forall np :: np in e2_inputs_from_e1_keys ==> np in e2.inputs;
    assert forall np :: np in e2_inputs_from_e1.Values ==> np in e1.outputs by {
      reveal EquivScOutputsInOutputs();
    }
    assert SetsNoIntersection(mf1.inputs+mf1.outputs, mf2.inputs+mf2.outputs) by {
      reveal NPsValidAndInSc();
    }
    GetInputs2(mf1, mf2, e2_inputs_from_e1, knowns)
  }

  lemma CalculateE2InputsKeysCorrect(c: Circuit, e1: Equiv, e2: Equiv, knowns: map<NP, bool>)
    requires ComposedValid(c, e1, e2)
    requires GoodKnownKeys(c, e1, e2, knowns)
    ensures
      CalculateE2Inputs(c, e1, e2, knowns).Keys == e2.inputs
  {
  }

  function ComposeEquivF(c: Circuit, e1: Equiv, e2: Equiv, combined_inputs: map<NP, bool>): (r: map<NP, bool>)
    requires ComposedValid(c, e1, e2)
    requires combined_inputs.Keys == ComposeEquivInputs(c, e1, e2)
  {
    reveal ComposedValid();
    reveal EquivValid();
    var mf1 := MapFunction(e1.inputs, e1.outputs, e1.f);
    var mf2 := MapFunction(e2.inputs, e2.outputs, e2.f);
    assert MapFunctionValid(mf1);
    assert MapFunctionValid(mf2);
    var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
    var e2_inputs_from_e1 := (map np | np in e2_inputs_from_e1_keys :: np := c.PortSource[np]);
    assert forall np :: np in e2_inputs_from_e1_keys ==> np in e2.inputs by {
      reveal CircuitValid();
    }
    assert forall np :: np in e2_inputs_from_e1.Values ==> np in e1.outputs by {
      reveal EquivScOutputsInOutputs();
      reveal CircuitValid();
    }
    assert SetsNoIntersection(mf1.inputs+mf1.outputs, mf2.inputs+mf2.outputs) by {
      reveal NPsValidAndInSc();
    }
    ComposeMapFunction(mf1, mf2, e2_inputs_from_e1, combined_inputs)
  }
}
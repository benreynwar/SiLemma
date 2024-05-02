module Compose {

  import opened Circ
  //import opened Eval
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

  lemma SetsNoIntersectionFromComposedValid(c: Circuit, e1: Equiv, e2: Equiv)
  requires ComposedValid(c, e1, e2)
  ensures SetsNoIntersection(e1.sc, e2.sc)
  {
    reveal ComposedValid();
  }

  lemma CircuitValidFromComposedValid(c: Circuit, e1: Equiv, e2: Equiv)
  requires ComposedValid(c, e1, e2)
  ensures CircuitValid(c)
  {
    reveal ComposedValid();
  }


  function {:vcs_split_on_every_assert} ComposeEquiv(c: Circuit, e1: Equiv, e2: Equiv): (r: Equiv)
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
    e
  }

  function ComposeEquivInputs(c: Circuit, e1: Equiv, e2: Equiv): (r: set<NP>)
    requires ComposedValid(c, e1, e2)
    ensures forall np :: np in e1.inputs ==> np in r
  {
    reveal ComposedValid();
    reveal EquivValid();
    (set np | np in (e1.inputs + e2.inputs) && np !in NPBetweenSubcircuits(c, e2.sc, e1.sc))
  }

  lemma ComposeEquivInputsCorrect(c: Circuit, e1: Equiv, e2: Equiv)
    requires ComposedValid(c, e1, e2)
    ensures ScValid(c, e1.sc + e2.sc)
    ensures
      ScInputBoundary(c, e1.sc + e2.sc) == ComposeEquivInputs(c, e1, e2)
  {
    reveal ComposedValid();
    reveal EquivValid();
  }

  function CalculateE2Inputs(c: Circuit, e1: Equiv, e2: Equiv, knowns: map<NP, bool>): (r: map<NP, bool>)
    requires ComposedValid(c, e1, e2)
    requires knowns.Keys == ComposeEquivInputs(c, e1, e2)
  {
    reveal ComposedValid();
    reveal EquivValid();
    var mf1 := MapFunction(e1.inputs, e1.outputs, e1.f);
    var mf2 := MapFunction(e2.inputs, e2.outputs, e2.f);
    assert MapFunctionValid(mf1);
    assert MapFunctionValid(mf2);
    var e2_inputs_from_e1_keys := NPBetweenSubcircuits(c, e2.sc, e1.sc);
    var e2_inputs_from_e1 := (map np | np in e2_inputs_from_e1_keys :: np := c.PortSource[np]);
    GetInputs2(mf1, mf2, e2_inputs_from_e1, knowns)
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
    ComposeMapFunction(mf1, mf2, e2_inputs_from_e1, combined_inputs)
  }
}

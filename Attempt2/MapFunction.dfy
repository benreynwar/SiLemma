module MapFunction {

  import opened Circ
  import opened Utils

  datatype MapFunction = MapFunction(
    inputs: set<NP>,
    outputs: set<NP>,
    f: map<NP, bool> --> map<NP, bool>
  )

  ghost opaque predicate MapFunctionValid(mf: MapFunction)
  {
    (forall x: map<NP, bool> :: x.Keys == mf.inputs ==> mf.f.requires(x)) &&
    (forall x: map<NP, bool> :: x.Keys == mf.inputs ==> mf.f(x).Keys == mf.outputs) &&
    SetsNoIntersection(mf.inputs, mf.outputs)
  }

  function GetInputs2(
      mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, knowns: map<NP, bool>): map<NP, bool>
    requires MapFunctionValid(mf1)
    requires MapFunctionValid(mf2)
    requires forall np :: np in connection.Keys ==> np in mf2.inputs
    requires forall np :: np in connection.Values ==> np in mf1.outputs
    requires SetsNoIntersection(mf1.inputs + mf1.outputs, mf2.inputs + mf2.outputs)
    requires
        var b: set<NP> := (mf1.inputs + mf2.inputs - connection.Keys);
        knowns.Keys == b
  {
    reveal MapFunctionValid();
    var inputs := mf1.inputs + mf2.inputs - connection.Keys;
    var outputs := mf1.outputs + mf2.outputs;
    assert forall np :: np in mf1.inputs ==> np in knowns;
    var inputs_1 := ExtractMap(knowns, mf1.inputs);
    var outputs_1 := mf1.f(inputs_1);
    assert outputs_1.Keys == mf1.outputs;
    var connected := (map np | np in connection :: np := outputs_1[connection[np]]);
    assert connected.Keys == connection.Keys;
    var combined_map := AddMaps(knowns, connected);
    assert combined_map.Keys == mf1.inputs + mf2.inputs;
    var inputs_2 := ExtractMap(combined_map, mf2.inputs);
    inputs_2
  }

  function ComposeMapFunction(
      mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, knowns: map<NP, bool>): map<NP, bool>
    requires MapFunctionValid(mf1)
    requires MapFunctionValid(mf2)
    requires forall np :: np in connection.Keys ==> np in mf2.inputs
    requires forall np :: np in connection.Values ==> np in mf1.outputs
    requires SetsNoIntersection(mf1.inputs + mf1.outputs, mf2.inputs + mf2.outputs)
    requires
        var b: set<NP> := (mf1.inputs + mf2.inputs - connection.Keys);
        knowns.Keys == b
  {
    reveal MapFunctionValid();
    assert knowns.Keys == mf1.inputs + mf2.inputs - connection.Keys;
    ManyInThisNotInThat(connection.Keys, mf2.inputs + mf2.outputs, mf1.inputs + mf1.outputs);
    assert forall np :: np in connection.Keys ==> np !in mf1.inputs;
    assert forall np :: np in mf1.inputs ==> np in knowns;
    var inputs_1 := ExtractMap(knowns, mf1.inputs);
    var outputs_1 := mf1.f(inputs_1);
    var inputs_2 := GetInputs2(mf1, mf2, connection, knowns);
    var outputs_2 := mf2.f(inputs_2);
    var combined_outputs := AddMaps(outputs_1, outputs_2);
    combined_outputs
  }

}
module MapFunction {

  import opened Circ
  import opened Utils

  datatype FI = FI(
    inputs: map<NP, bool>,
    state: map<NP, bool>
  )

  datatype FO = FO(
    outputs: map<NP, bool>,
    state: map<NP, bool>
  )

  predicate FIValid(fi: FI, input_keys: set<NP>, state_keys: set<CNode>)
  {
    && fi.inputs.Keys == input_keys
    && fi.state.Keys == StateONPs(state_keys)
  }

  predicate FOValid(fo: FO, output_keys: set<NP>, state_keys: set<CNode>)
  {
    && fo.outputs.Keys == output_keys
    && fo.state.Keys == StateINPs(state_keys)
  }

  datatype MapFunction = MapFunction(
    inputs: set<NP>,
    outputs: set<NP>,
    state: set<CNode>,
    f: FI --> FO
  )

  function StateINPs(state: set<CNode>): set<NP>
  {
    (set n | n in state :: NP(n, INPUT_0))
  }

  function StateONPs(state: set<CNode>): set<NP>
  {
    (set n | n in state :: NP(n, OUTPUT_0))
  }

  ghost opaque predicate MapFunctionValid(mf: MapFunction)
  {
    && (forall fi: FI :: FIValid(fi, mf.inputs, mf.state) ==> (
        && mf.f.requires(fi)
        && FOValid(mf.f(fi), mf.outputs, mf.state)
    ))
    && SetsNoIntersection(mf.inputs, mf.outputs)
    && SetsNoIntersection(mf.outputs, StateINPs(mf.state))
    && SetsNoIntersection(mf.inputs, StateONPs(mf.state))
  }

  function MFLookup(mf: MapFunction, fi: FI, np: NP): bool
    requires MapFunctionValid(mf)
    requires FIValid(fi, mf.inputs, mf.state)
    requires np in mf.outputs || np in StateINPs(mf.state)
  {
    reveal MapFunctionValid();
    var fo := mf.f(fi);
    if np in mf.outputs then
      fo.outputs[np]
    else
      fo.state[np]
  }

  function GetInputs2(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, fi: FI): map<NP, bool>
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    requires FIValid(fi, mf1.inputs + (mf2.inputs - connection.Keys), mf1.state + mf2.state)
    requires connection.Keys <= mf2.inputs
    requires connection.Values <= mf1.outputs
  {
    reveal MapFunctionValid();
    var fi_1 := ConnectFI1FromFI(mf1, mf2, connection, fi);
    var fo_1 := mf1.f(fi_1);
    var connected := (map np | np in connection :: np := fo_1.outputs[connection[np]]);
    assert connected.Keys == connection.Keys;
    assert fi.inputs.Keys == mf1.inputs + (mf2.inputs - connection.Keys);
    assert connection.Keys <= mf2.inputs;
    SubsetsNoIntersection(MFNPs(mf1), MFNPs(mf2), mf1.inputs, connection.Keys);
    var combined_inputs := AddMaps(fi.inputs, connected);
    assert combined_inputs.Keys == mf1.inputs + mf2.inputs;
    var inputs_2 := ExtractMap(combined_inputs, mf2.inputs);
    inputs_2
  }

  function MFNPs(mf: MapFunction): set<NP>
  {
    mf.inputs + mf.outputs + StateINPs(mf.state) + StateONPs(mf.state)
  }

  ghost predicate ConnectMapFunctionRequirement(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>)
  {
    && MapFunctionValid(mf1)
    && MapFunctionValid(mf2)
    && (forall np :: np in connection.Keys ==> np in mf2.inputs)
    && (forall np :: np in connection.Values ==> np in mf1.outputs)
    && SetsNoIntersection(MFNPs(mf1), MFNPs(mf2))
    && SetsNoIntersection(mf1.state, mf2.state)
  }

  opaque function ConnectMapFunction(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>): (mf: MapFunction)
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    ensures MapFunctionValid(mf)
    ensures mf.inputs == mf1.inputs + (mf2.inputs - connection.Keys)
    ensures mf.state == mf1.state + mf2.state
    ensures mf.outputs == mf1.outputs + mf2.outputs
  {
    var new_inputs := mf1.inputs + (mf2.inputs - connection.Keys);
    var new_outputs := mf1.outputs + mf2.outputs;
    var new_state := mf1.state + mf2.state;
    var new_f: FI --> FO := (fi: FI) requires FIValid(fi, new_inputs, new_state) => 
      ConnectMapFunctionF(mf1, mf2, connection, fi);
    var mf := MapFunction(new_inputs, new_outputs, new_state, new_f);
    assert forall fi: FI :: FIValid(fi, mf.inputs, mf.state) ==> (
        && mf.f.requires(fi)
        && FOValid(mf.f(fi), mf.outputs, mf.state)
    );
    reveal MapFunctionValid();
    assert SetsNoIntersection(mf1.inputs, mf1.outputs);
    assert SetsNoIntersection(mf2.inputs, mf2.outputs);
    assert SetsNoIntersection(mf.inputs, mf.outputs);
    assert StateINPs(mf.state) == StateINPs(mf1.state) + StateINPs(mf2.state);
    assert StateONPs(mf.state) == StateONPs(mf1.state) + StateONPs(mf2.state);
    assert SetsNoIntersection(mf1.inputs, StateONPs(mf1.state));
    SubsetsNoIntersection(MFNPs(mf1), MFNPs(mf2), mf1.inputs, StateONPs(mf2.state));
    assert SetsNoIntersection(mf1.inputs, StateONPs(mf2.state));
    assert SetsNoIntersection(mf2.outputs, StateINPs(mf2.state));
    SetsNoIntersectionSymm(MFNPs(mf2), MFNPs(mf1));
    SubsetsNoIntersection(MFNPs(mf2), MFNPs(mf1), mf2.outputs, StateINPs(mf1.state));
    assert SetsNoIntersection(mf2.outputs, StateINPs(mf1.state));
    assert SetsNoIntersection(mf.outputs, StateINPs(mf.state));
    assert SetsNoIntersection(mf.inputs, StateONPs(mf.state));
    assert MapFunctionValid(mf);
    mf
  }

  function ConnectFI1FromFI(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, fi: FI): (fi_1: FI)
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    requires FIValid(fi, mf1.inputs + (mf2.inputs - connection.Keys), mf1.state+mf2.state)
    ensures FIValid(fi_1, mf1.inputs, mf1.state)
  {
    FI(ExtractMap(fi.inputs, mf1.inputs), ExtractMap(fi.state, StateONPs(mf1.state)))
  }

  function ConnectFI2FromFI(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, fi: FI): (fi_2: FI)
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    requires FIValid(fi, mf1.inputs + (mf2.inputs - connection.Keys), mf1.state+mf2.state)
    ensures FIValid(fi_2, mf2.inputs, mf2.state)
  {
    FI(GetInputs2(mf1, mf2, connection, fi), ExtractMap(fi.state, StateONPs(mf2.state)))
  }

  lemma {:vcs_split_on_every_assert} ConnectMapFunctionMF1Preserved(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, fi: FI, np: NP)
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    requires FIValid(fi, mf1.inputs + (mf2.inputs - connection.Keys), mf1.state+mf2.state)
    requires np in mf1.outputs || np in StateINPs(mf1.state)
    ensures
      var fi_1 := ConnectFI1FromFI(mf1, mf2, connection, fi);
      var mf := ConnectMapFunction(mf1, mf2, connection);
      MFLookup(mf1, fi_1, np) == MFLookup(mf, fi, np)
  {
    var mf := ConnectMapFunction(mf1, mf2, connection);
    var fi_1 := ConnectFI1FromFI(mf1, mf2, connection, fi);
    var fi_2 := ConnectFI2FromFI(mf1, mf2, connection, fi);
    reveal MapFunctionValid();
    var fo_1 := mf1.f(fi_1);
    var fo_2 := mf2.f(fi_2);
    OutputsNoIntersection(mf1, mf2, connection);
    reveal ConnectMapFunction();
    assert mf.f(fi) == FO(AddMaps(fo_1.outputs, fo_2.outputs), AddMaps(fo_1.state, fo_2.state));
    if np in mf1.outputs {
      assert np in mf.outputs;
      assert MFLookup(mf, fi, np) == fo_1.outputs[np];
      assert MFLookup(mf1, fi_1, np) == fo_1.outputs[np];
    } else {
      assert np in StateINPs(mf1.state);
      assert np in StateINPs(mf.state);
      assert np !in mf.outputs;
      assert MFLookup(mf, fi, np) == fo_1.state[np];
      assert MFLookup(mf1, fi_1, np) == fo_1.state[np];
    }
  }

  lemma ConnectMapFunctionMF2Preserved(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, fi: FI, np: NP)
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    requires FIValid(fi, mf1.inputs + (mf2.inputs - connection.Keys), mf1.state+mf2.state)
    requires np in mf2.outputs || np in StateINPs(mf2.state)
    ensures
      var fi_1 := ConnectFI1FromFI(mf1, mf2, connection, fi);
      var fi_2 := ConnectFI2FromFI(mf1, mf2, connection, fi);
      var mf := ConnectMapFunction(mf1, mf2, connection);
      && MFLookup(mf2, fi_2, np) == MFLookup(mf, fi, np)
  {
    reveal MapFunctionValid();
    reveal ConnectMapFunction();
    var fi_1 := ConnectFI1FromFI(mf1, mf2, connection, fi);
    var fi_2 := ConnectFI2FromFI(mf1, mf2, connection, fi);
    reveal MapFunctionValid();
    var fo_1 := mf1.f(fi_1);
    var fo_2 := mf2.f(fi_2);
    OutputsNoIntersection(mf1, mf2, connection);
  }

  lemma OutputsNoIntersection(mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>)
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    ensures SetsNoIntersection(mf1.outputs, mf2.outputs)
    ensures SetsNoIntersection(StateINPs(mf1.state), StateINPs(mf2.state))
  {
    reveal MapFunctionValid();
    assert SetsNoIntersection(mf1.state, mf2.state);
    assert SetsNoIntersection(mf1.outputs, mf2.outputs) by {
      SubsetsNoIntersection(MFNPs(mf1), MFNPs(mf2), mf1.outputs, mf2.outputs);
    }
    assert SetsNoIntersection(StateINPs(mf1.state), StateINPs(mf2.state)) by {
      if exists np :: np in StateINPs(mf1.state) && np in StateINPs(mf2.state) {
        var np :| np in StateINPs(mf1.state) && np in StateINPs(mf2.state);
        assert np.n in mf1.state;
        assert np.n in mf2.state;
        assert np.n in mf1.state * mf2.state;
        assert false;
      }
    }
  }

  function ConnectMapFunctionF(
      mf1: MapFunction, mf2: MapFunction, connection: map<NP, NP>, fi: FI): (fo: FO)
    requires ConnectMapFunctionRequirement(mf1, mf2, connection)
    requires FIValid(fi, mf1.inputs + (mf2.inputs - connection.Keys), mf1.state + mf2.state)
    ensures FOValid(fo, mf1.outputs + mf2.outputs, mf1.state + mf2.state)
  {
    var fi_1 := ConnectFI1FromFI(mf1, mf2, connection, fi);
    var fi_2 := ConnectFI2FromFI(mf1, mf2, connection, fi);
    reveal MapFunctionValid();
    var fo_1 := mf1.f(fi_1);
    var fo_2 := mf2.f(fi_2);
    OutputsNoIntersection(mf1, mf2, connection);
    FO(AddMaps(fo_1.outputs, fo_2.outputs), AddMaps(fo_1.state, fo_2.state))
  }

  ghost predicate MapFunctionsEquiv(mf1: MapFunction, mf2: MapFunction)
    requires MapFunctionValid(mf1)
    requires MapFunctionValid(mf2)
  {
    reveal MapFunctionValid();
    && mf1.inputs == mf2.inputs
    && mf1.outputs == mf2.outputs
    && mf1.state == mf2.state
    && forall fi: FI :: FIValid(fi, mf1.inputs, mf1.state) ==> (
      mf1.f(fi) == mf2.f(fi)
    )
  }
}
module Build.AndBuilder {

  import opened Circ
  import opened Eval
  import opened Utils
  import opened Entity
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened MapFunction

  datatype AndInstance = AndInstance(
    inputs: seq<NP>,
    outputs: seq<NP>,
    state: seq<CNode>)
  {
  }

  function AndSF(n: nat, si: SI): (so: SO)
    requires |si.inputs| == 2
    requires |si.state| == 0
  {
    SO([si.inputs[0] && si.inputs[1]], [])
  }

  //trait {:termination false} Model<Inputs, Outputs, State> {
  //  function Behav(inputs: Inputs, state: State): (r: (Outputs, State))
  //  function SC(): set<CNode>
  //  function InputsToMap(inputs: Inputs): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == Inputs()
  //  function OutputsToMap(outputs: Outputs): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == Outputs()
  //  function OldStateToMap(state: State): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == StateONPs(State())
  //  function NewStateToMap(state: State): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == StateINPs(State())
  //  function MapToInputs(mapped: map<NP, bool>): (inputs: Inputs)
  //    requires mapped.Keys == Inputs()
  //  function MapToOutputs(mapped: map<NP, bool>): (outputs: Outputs)
  //    requires mapped.Keys == Outputs()
  //  function MapToNewState(mapped: map<NP, bool>): (state: State)
  //    requires mapped.Keys == StateINPs(State())
  //  function MapToOldState(mapped: map<NP, bool>): (state: State)
  //    requires mapped.Keys == StateONPs(State())
  //  predicate UniqueElements()
  //  function Inputs(): set<NP>
  //  function Outputs(): set<NP>
  //  function State(): set<CNode>
  //  function OldStateNPs(): set<NP>
  //  {
  //    StateONPs(State())
  //  }
  //  function NewStateNPs(): set<NP>
  //  {
  //    StateINPs(State())
  //  }
  //  function MapBehav(fi: FI): (fo: FO)
  //    requires FIValid(fi, Inputs(), State())
  //    ensures FOValid(fo, Outputs(), State())
  //  {
  //    var inputs := MapToInputs(fi.inputs);
  //    var state := MapToOldState(fi.state);
  //    var (outputs, new_state) := Behav(inputs, state);
  //    var outputs_map := OutputsToMap(outputs);
  //    var state_map := NewStateToMap(new_state);
  //    FO(outputs_map, state_map)
  //  }
  //  function MF(): MapFunction
  //  {
  //    MapFunction(
  //      Inputs(), Outputs(), State(),
  //      (fi: FI) requires FIValid(fi, Inputs(), State()) => MapBehav(fi)
  //    )
  //  }
  //  function E(): Entity
  //  {
  //    Entity(SC(), MF())
  //  }
  //}

  //// A generic trait used to bundle some constants, functions and lemmas together.
  //trait {:termination false} Flattenable<T> {

  //  // I don't want to specify the value of length here.
  //  const length: nat := 2

  //  function tobits(a: T): (r: seq<bool>)
  //    ensures |r| == length
  //  function frombits(bs: seq<bool>): (r: T)
  //    requires |bs| == length
  //  lemma flattenable(a: T)
  //    ensures frombits(tobits(a)) == a
  //}

  //// An example datatype that I want to be able to apply these functions and lemmas to.
  //datatype AndInputs = AndInputs(
  //  i_0: bool,
  //  i_1: bool
  //  )

  //// An implementation of these functions and lemmas for this type.
  //datatype FlattenableAndInputs extends Flattenable<AndInputs> = FlattenableAndInputs() {

  //  // I want to specify the value of length here.
  //  //const length: nat := 2

  //  function tobits(a: AndInputs): (r: seq<bool>)
  //    ensures |r| == length
  //  {
  //    [a.i_0, a.i_1]
  //  }

  //  function frombits(bs: seq<bool>): (r: AndInputs)
  //    requires |bs| == length
  //  {
  //    AndInputs(bs[0], bs[1])
  //  }

  //  lemma flattenable(a: AndInputs)
  //    ensures frombits(tobits(a)) == a
  //  {
  //    var bs := tobits(a);
  //    assert |bs| == length;
  //    assert frombits(bs) == a;
  //  }
  //}

  //// Some example uses where the bundle of functions and lemmas can be used for
  //// any type. The specifc implementations are passed in as f.

  //function ExampleFlattener<X>(x: X, f: Flattenable<X>): seq<bool>
  //{
  //  f.tobits(x)
  //}

  //function ExampleUnflattener<X>(b: seq<bool>, f: Flattenable<X>): X
  //  requires |b| == f.length
  //{
  //  f.frombits(b)
  //}

  //lemma ExampleCorrect<X>(x: X, f: Flattenable<X>)
  //  ensures f.frombits(f.tobits(x)) == x
  //{
  //  f.flattenable(x);
  //}

  //datatype AndOutputs = AndOutputs(
  //  o: bool
  //  )

  //datatype AndState = AndState()

  //datatype AndInputMapping = AndInputMapping(
  //  i_0: NP,
  //  i_1: NP
  //  )

  //datatype AndOutputMapping = AndOutputMapping(
  //  o: NP
  //  )

  //datatype AndStateMapping = AndStateMapping()

  //function AndBehav(inputs: AndInputs, state: AndState): (r: (AndOutputs, AndState))
  //{
  //  (AndOutputs(inputs.i_0 && inputs.i_1), AndState())
  //}

  //datatype And extends Model<AndInputs, AndOutputs, AndState> =
  //  And(im: AndInputMapping, om: AndOutputMapping, sm: AndStateMapping,
  //      sc: set<CNode>) {
  //  function Behav(inputs: AndInputs, state: AndState): (r: (AndOutputs, AndState))
  //  {
  //    AndBehav(inputs, state)
  //  }
  //  function SC(): set<CNode> { sc }
  //  function InputsToMap(inputs: AndInputs): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == Inputs()
  //  {
  //    map[im.i_0 := inputs.i_0, im.i_1 := inputs.i_1]
  //  }
  //  function OutputsToMap(outputs: AndOutputs): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == Outputs()
  //  {
  //    map[om.o := outputs.o]
  //  }
  //  function OldStateToMap(state: AndState): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == StateONPs(State())
  //  {
  //    map[]
  //  }
  //  function NewStateToMap(state: AndState): (mapped: map<NP, bool>)
  //    ensures mapped.Keys == StateINPs(State())
  //  {
  //    map[]
  //  }
  //  function MapToInputs(mapped: map<NP, bool>): (inputs: AndInputs)
  //    requires mapped.Keys == Inputs()
  //  {
  //   AndInputs(mapped[im.i_0], mapped[im.i_1])
  //  }
  //  function MapToOutputs(mapped: map<NP, bool>): (outputs: AndOutputs)
  //    requires mapped.Keys == Outputs()
  //  {
  //   AndOutputs(mapped[om.o])
  //  }
  //  function MapToNewState(mapped: map<NP, bool>): (state: AndState)
  //    requires mapped.Keys == StateINPs(State())
  //  {
  //   AndState()
  //  }
  //  function MapToOldState(mapped: map<NP, bool>): (state: AndState)
  //    requires mapped.Keys == StateONPs(State())
  //  {
  //   AndState()
  //  }
  //  predicate UniqueElements()
  //  {
  //    && im.i_0 != im.i_1
  //    && im.i_0 != om.o
  //    && im.i_1 != om.o
  //  }
  //  function Inputs(): set<NP>
  //  {
  //    {im.i_0, im.i_1}
  //  }
  //  function Outputs(): set<NP>
  //  {
  //    {om.o}
  //  }
  //  function State(): set<CNode>
  //  {
  //    {}
  //  }
  //  function All(): set<NP>
  //  {
  //    Inputs() + Outputs() + StateINPs(State()) + StateONPs(State())
  //  }
  //}

  function InsertAndImpl(c: Circuit): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntitySomewhatValid(r.0, r.1)
    ensures r.1.mf.Valid()
  {
    reveal CircuitValid();
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CAnd],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var i_1 := NP(new_node, INPUT_1);
    var o_0 := NP(new_node, OUTPUT_0);
    var inputs := [i_0, i_1];
    var outputs := [o_0];
    var state := [];
    var mf := MapFunction(inputs, outputs, state, (si: SI) requires SIValid(si, inputs, state) =>
      reveal Seq.ToSet();
      SO([si.inputs[0] && si.inputs[1]], []));
    var e := Entity({new_node}, mf);
    assert EntitySomewhatValid(new_c, e) by {
      reveal EntitySomewhatValid();
      reveal Seq.ToSet();
      reveal ScValid();
      reveal ConnOutputs();
      reveal ConnInputs();
      reveal UnconnInputs();
      reveal AllONPs();
      reveal AllSeq();
      assert ScValid(new_c, e.sc);
      assert forall np: NP :: np.n in e.sc ==> np !in c.PortSource.Values;
    }
    assert mf.Valid() by {
      reveal MapFunction.Valid();
      reveal Seq.ToSet();
      reveal Seq.HasNoDuplicates();
    }
    (new_c, e)
  }

  lemma InsertAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, e) := InsertAndImpl(c);
      && EntityValid(new_c, e)
  {
    var (new_c, e) := InsertAndImpl(c);
    var o := e.mf.outputs[0];
    var i_0 := e.mf.inputs[0];
    var i_1 := e.mf.inputs[1];
    var path := [e.mf.outputs[0]];
    assert PathValid(new_c, path) && PathValid(new_c, [o, i_0]) && PathValid(new_c, [o, i_1]) by {
      reveal PathValid();
    }
    LengthOneNoDuplicates(path);
    assert CircuitValid(new_c);
    reveal Seq.ToSet();
    forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
      ensures
        var iv_0 := fi.inputs[i_0];
        var iv_1 := fi.inputs[i_1];
        && FICircuitValid(new_c, fi)
        && (EvaluateONP(new_c, o, fi) == EvalOk(iv_0 && iv_1))
    {
      var iv_0 := fi.inputs[i_0];
      var iv_1 := fi.inputs[i_1];
      assert Seq.HasNoDuplicates(path);
      assert FICircuitValid(new_c, fi) by {
        reveal MapFunction.Valid();
        reveal FICircuitValid();
      }
      assert EvaluateONP(new_c, o, fi) == EvaluateONPBinary(new_c, [o], fi);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [o, i_0], fi) == EvalOk(iv_0);
      assert EvaluateINPInner(new_c, [o, i_1], fi) == EvalOk(iv_1);
      assert EvaluateONPBinary(new_c, [o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONPInner(new_c, [o], fi) == EvalOk(iv_0 && iv_1);
      assert EvaluateONP(new_c, o, fi) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o, fi) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o, fi) == EvalOk(e.mf.f(fi).outputs[o]) by {
        reveal MapMatchesSeqs();
      }
    }
    assert ScValid(new_c, e.sc) by {
      reveal EntitySomewhatValid();
    }
    assert EntityEvaluatesCorrectly(new_c, e) by {
      reveal EntityEvaluatesCorrectly();
      reveal MapMatchesSeqs();
    }
    assert EntityValid(new_c, e);
  }

  lemma InsertAndConserves(c: Circuit)
    requires CircuitValid(c)
    ensures CircuitConserved(c, InsertAndImpl(c).0)
    ensures CircuitUnconnected(c, InsertAndImpl(c).0)
    ensures
      var (new_c, e) := InsertAndImpl(c);
      IsIsland(new_c, e.sc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    var (new_c, e) := InsertAndImpl(c);
    reveal CircuitValid();
    assert (forall np :: np in c.PortSource.Keys ==> np.n !in e.sc);
    assert (forall np :: np in c.PortSource.Values ==> np.n !in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n in e.sc ==> new_c.PortSource[np].n in e.sc);
    assert (forall np :: np in new_c.PortSource && np.n !in e.sc ==> new_c.PortSource[np].n !in e.sc);
    reveal IsIsland();
  }

  function InsertAnd(c: Circuit): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures
      var (new_c, e) := r;
      && r == InsertAndImpl(c)
      && CircuitValid(r.0)
      && EntityValid(new_c, e)
      && CircuitConserved(c, r.0)
      && CircuitUnconnected(c, r.0)
      && IsIsland(new_c, e.sc)
  {
    InsertAndCorrect(c);
    InsertAndConserves(c);
    InsertAndImpl(c)
  }

}

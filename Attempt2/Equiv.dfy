module Equiv {

  import opened Circ
  import opened Utils
  import opened MapFunction
  import opened Eval

  // An equivalence maps a subcircuit and a node in that subcircuit to a function.
  datatype Equiv = Equiv(
    sc: set<CNode>,
    inputs: set<NP>,
    outputs: set<NP>,
    f: map<NP, bool> --> map<NP, bool>
  )

  function EtoMf(e: Equiv): (r: MapFunction)
  {
    MapFunction(e.inputs, e.outputs, e.f)
  }

  lemma EValidMfValid(c: Circuit, e: Equiv)
    requires EquivValid(c, e)
    ensures MapFunctionValid(EtoMf(e))
  {
    reveal EquivValid();
  }

  function SwapEquivF(c: Circuit, e: Equiv, f: map<NP, bool> --> map<NP, bool>): (r: Equiv)
    requires EquivValid(c, e)
    requires (forall knowns: map<NP, bool> :: (knowns.Keys == e.inputs) ==> f.requires(knowns))
    requires (forall knowns: map<NP, bool> :: (knowns.Keys == e.inputs) ==> f(knowns).Keys == e.outputs)
    ensures EquivValid(c, r)
  {
    reveal EquivValid();
    Equiv(e.sc, e.inputs, e.outputs, f)
  }

  ghost opaque predicate EquivValid(c: Circuit, e: Equiv)
  {
    ScValid(c, e.sc) &&
    (ScInputBoundary(c, e.sc) == e.inputs) &&
    SetsNoIntersection(e.inputs, e.outputs) &&
    (forall np :: np in e.outputs ==> (INPValid(c, np) || ONPValid(c, np)) && np.n in e.sc) &&
    (forall knowns: map<NP, bool> :: (knowns.Keys == e.inputs) ==> e.f.requires(knowns)) &&
    (forall knowns: map<NP, bool> :: (knowns.Keys == e.inputs) ==> e.f(knowns).Keys == e.outputs) &&
    // But it is possible to have outputs that are not on output boundary (i.e. we plan to connect them in the future)
    (forall np :: np in ScOutputBoundary(c, e.sc) ==> np in e.outputs)
  }

  ghost predicate EquivTrue(c: Circuit, e: Equiv)
    requires CircuitValid(c)
    requires EquivValid(c, e)
  {
    reveal EquivValid();
    forall knowns: map<NP, bool> :: (knowns.Keys == e.inputs) ==>
      forall np :: np in e.outputs ==>
        Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np])
  }

}
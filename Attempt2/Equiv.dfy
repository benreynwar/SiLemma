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
    requires MapFunctionValid(MapFunction(e.inputs, e.outputs, f))
    ensures EquivValid(c, r)
  {
    reveal EquivValid();
    Equiv(e.sc, e.inputs, e.outputs, f)
  }

  opaque predicate NPsValidAndInSc(c: Circuit, sc: set<CNode>, nps: set<NP>)
  {
    (forall np :: np in nps ==> NPValid(c, np) && np.n in sc)
  }

  opaque predicate EquivScOutputsInOutputs(c: Circuit, sc: set<CNode>, outputs: set<NP>)
  {
    (forall np :: np in ScOutputBoundary(c, sc) ==> np in outputs)
  }

  ghost opaque predicate EquivValid(c: Circuit, e: Equiv)
  {
    && ScValid(c, e.sc)
    && (ScInputBoundary(c, e.sc) == e.inputs)
    && SetsNoIntersection(e.inputs, e.outputs)
    && NPsValidAndInSc(c, e.sc, e.outputs)
    && NPsValidAndInSc(c, e.sc, e.inputs)
    && MapFunctionValid(EtoMf(e))
    && EquivScOutputsInOutputs(c, e.sc, e.outputs)
  }

  ghost opaque predicate EquivTrue(c: Circuit, e: Equiv)
    requires CircuitValid(c)
    requires EquivValid(c, e)
  {
    reveal CircuitValid();
    reveal EquivValid();
    reveal MapFunctionValid();
    reveal NPsValidAndInSc();
    forall knowns: map<NP, bool> :: (knowns.Keys == e.inputs) ==>
      forall np :: np in e.outputs ==>
        Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np])
  }

}
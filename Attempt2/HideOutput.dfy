module HideOutput {

  import opened Circ
  import opened Equiv
  import opened Utils
  import opened MapFunction

  function EquivHideOutput(c: Circuit, e: Equiv, remove: set<NP>): (r: Equiv)
    requires CircuitValid(c)
    requires EquivValid(c, e)
    requires forall np :: np in remove ==> np !in ScOutputBoundary(c, e.sc)
    ensures EquivValid(c, r)
    ensures EquivTrue(c, e) ==> EquivTrue(c, r)
  {
    reveal CircuitValid();
    reveal EquivValid();
    reveal EquivTrue();
    reveal ScValid();
    reveal NPsValidAndInSc();
    reveal EquivScOutputsInOutputs();
    reveal MapFunctionValid();
    Equiv(e.sc, e.inputs, e.outputs - remove, (x: map<NP, bool>) requires x.Keys == e.inputs => e.f(x) - remove)
  }

}
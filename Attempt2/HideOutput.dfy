module HideOutput {

  import opened Circ
  import opened Equiv
  import opened Utils

  function EquivHideOutput(c: Circuit, e: Equiv, remove: set<NP>): (r: Equiv)
    requires CircuitValid(c)
    requires EquivValid(c, e)
    requires forall np :: np in remove ==> np !in ScOutputBoundary(c, e.sc)
    ensures EquivValid(c, r)
    ensures EquivTrue(c, e) ==> EquivTrue(c, r)
  {
    reveal EquivValid();
    Equiv(e.sc, e.inputs, e.outputs - remove, (x: map<NP, bool>) requires x.Keys == e.inputs => e.f(x) - remove)
  }

}
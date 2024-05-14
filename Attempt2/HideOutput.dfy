module HideOutput {

  import opened Circ
  import opened Entity
  import opened Utils
  //import opened MapFunction

  function EntityHideOutput(c: Circuit, e: Entity, remove: set<NP>): (r: Entity)
    requires CircuitValid(c)
    requires EntityValid(c, e)
    requires forall np :: np in remove ==> np !in ScOutputBoundary(c, e.sc)
    ensures EntityValid(c, r)
  {
    reveal CircuitValid();
    reveal ScValid();
    reveal EntityFValid();
    Entity(
      e.sc, e.finputs, e.foutputs - remove,
      (x: map<NP, bool>) requires x.Keys == e.finputs => e.f(x) - remove)
  }

}
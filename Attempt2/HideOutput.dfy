module HideOutput {

  import opened Circ
  import opened Entity
  import opened Utils
  import opened MapFunction

  function EntityHideOutput(c: Circuit, e: Entity, remove: set<NP>): (r: Entity)
    requires CircuitValid(c)
    requires EntityValid(c, e)
    requires forall np :: np in remove ==> np !in ScOutputBoundary(c, e.sc)
    ensures EntityValid(c, r)
  {
    reveal CircuitValid();
    reveal ScValid();
    reveal MapFunctionValid();
    Entity(
      e.sc, MapFunction(e.mf.inputs, e.mf.outputs - remove, e.mf.state,
      (fi: FI) requires FIValid(fi, e.mf.inputs, e.mf.state) =>
        var fo := e.mf.f(fi);
        FO(fo.outputs, fo.state - remove)))
  }

}
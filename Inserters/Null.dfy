module Inserters.Null {

  import opened Circ
  import opened Scuf
  import opened MapFunction
  import opened ConservedSubcircuit
  import opened Subcircuit

  function NullScufMap(): (mp: ScufMap)
    ensures mp.Valid()
  {
    reveal Seq.HasNoDuplicates();
    reveal Seq.ToSet();
    ScufMap([], [], [])
  }

  function NullScuf(): (s: Scuf)
  {
    Scuf({}, NullScufMap(), NullUpdateFunction())
  }

  function NullInserter(): (z: ScufInserter)
    ensures z.Valid()
  {
    reveal ScufInserter.Valid();
    reveal SimpleInsertion();
    var z := ScufInserter(NullUpdateFunction(), (c: Circuit) => (c, NullScuf()));
    assert z.Valid() by {
      assert z.uf.Valid();
      forall c: Circuit | c.Valid()
        ensures z.SpecificValid(c)
      {
        reveal IsIsland();
        reveal CircuitUnconnected();
        reveal CircuitConserved();
        reveal Circuit.Valid();
        reveal ScValid();
        reveal Scuf.SomewhatValid();
        reveal Scuf.EvaluatesCorrectly();
        reveal NPsInSc();
        reveal Seq.ToSet();
      }
    }
    z
  }
}

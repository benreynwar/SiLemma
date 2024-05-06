module Connecting {

  import opened Circ
  import opened ConservedSubcircuit
  import opened Utils
  import opened Equiv
  import opened Compose
  import opened ComposeEval

  lemma ConnectPreservesSubcircuit(c: Circuit, inp: NP, onp: NP, sc: set<CNode>)
    requires CircuitValid(c)
    requires ScValid(c, sc)
    requires inp !in c.PortSource
    requires INPValid(c, inp)
    requires ONPValid(c, onp)
    requires !(inp.n in sc && onp.n in sc)
    ensures
      var r := Connect(c, inp, onp);
      SubcircuitConserved(c, r, sc)
  {
    reveal CircuitValid();
    reveal ScValid();
    reveal SubcircuitConserved();
  }

  function ConnectMany(c: Circuit, connection: map<NP, NP>): (r: Circuit)
    requires CircuitValid(c)
    requires forall np :: np in connection.Keys ==> np !in c.PortSource
    requires forall np :: np in connection.Keys ==> INPValid(c, np)
    requires forall np :: np in connection.Values ==> ONPValid(c, np)
    ensures CircuitValid(r)
  {
    reveal CircuitValid();
    var new_c := Circuit(
      c.NodeKind,
      AddMaps(c.PortSource, connection)
    );
    assert (forall np :: np in new_c.PortSource.Values ==> ONPValid(c, np));
    assert (forall np :: np in new_c.PortSource.Keys ==> INPValid(c, np));
    new_c
  }

  lemma ConnectManyScOutputBoundary(c: Circuit, connection: map<NP, NP>, sc: set<CNode>)
    requires CircuitValid(c)
    requires forall np :: np in connection.Keys ==> np !in c.PortSource
    requires forall np :: np in connection.Keys ==> INPValid(c, np)
    requires forall np :: np in connection.Values ==> ONPValid(c, np)
    // No connections from the sc
    requires forall np :: np in connection.Keys ==> np.n !in sc
    ensures
      var new_c := ConnectMany(c, connection);
      var new_outputs := (set np | np in connection.Values && np.n in sc :: np);

      ScOutputBoundary(c, sc) + new_outputs == ScOutputBoundary(new_c, sc)
  {
  }

  lemma ConnectManyConservesSubcircuit(c: Circuit, connection: map<NP, NP>, sc: set<CNode>)
    requires CircuitValid(c)
    requires ScValid(c, sc)
    requires forall np :: np in connection.Keys ==> np !in c.PortSource
    requires forall np :: np in connection.Keys ==> INPValid(c, np)
    requires forall np :: np in connection.Values ==> ONPValid(c, np)
    // It shouldn't effect an equiv as long as it doesnt create an internal connection in the equiv or
    requires forall np :: (np in connection.Keys && np.n in sc) ==> connection[np].n !in sc
    ensures SubcircuitConserved(c, ConnectMany(c, connection), sc)
  {
    reveal CircuitValid();
    reveal SubcircuitConserved();
    reveal ScValid();
  }

  function ConnectEquivs(c: Circuit, e1: Equiv, e2: Equiv, connection: map<NP, NP>): (r: (Circuit, Equiv))
    requires CircuitValid(c)
    requires EquivValid(c, e1) && EquivTrue(c, e1)
    requires EquivValid(c, e2) && EquivTrue(c, e2)
    requires SetsNoIntersection(e1.sc, e2.sc)
    requires ScValid(c, e1.sc)
    requires ScValid(c, e2.sc)
    requires (NPBetweenSubcircuits(c, e1.sc, e2.sc) == {})
    requires forall np :: np in connection.Keys ==> np !in c.PortSource
    requires forall np :: np in connection.Keys ==> (np in e2.inputs) && INPValid(c, np)
    requires forall np :: np in connection.Values ==> np in e1.outputs && ONPValid(c, np)
    //requires forall np :: np in outputs_to_remove ==> np in (e1.outputs + e2.outputs)
    ensures CircuitValid(r.0)
    ensures EquivValid(r.0, r.1) && EquivTrue(r.0, r.1)
    ensures SubcircuitConserved(c, r.0, SubcircuitComplement(c, e1.sc+e2.sc))
    ensures SubcircuitUnconnected(c, r.0, SubcircuitComplement(c, e1.sc+e2.sc))
  {
    var new_c := ConnectMany(c, connection);
    reveal CircuitValid();
    reveal EquivValid();
    reveal ScValid();
    reveal NPsValidAndInSc();
    reveal EquivScOutputsInOutputs();
    ConnectManyConservesSubcircuit(c, connection, e1.sc);
    ConnectManyConservesSubcircuit(c, connection, e2.sc);
    EquivConserved(c, new_c, e1);
    EquivConserved(c, new_c, e2);
    reveal ComposedValid();
    var intermed_e := ComposeEquiv(new_c, e1, e2);
    ComposeEquivCorrect(new_c, e1, e2);
    (new_c, intermed_e)
  }

}
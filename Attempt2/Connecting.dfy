module Connecting {

  import opened Circ
  import opened ConservedSubcircuit

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
    var ca := c;
    var cb := Connect(c, inp, onp);
    assert (forall n :: n in sc ==> n in ca.NodeKind && n in cb.NodeKind);
    assert (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n]);
    assert (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n]);
    assert (forall np: NP :: (np in ScInputBoundary(ca, sc)) == (np in ScInputBoundary(cb, sc)));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc ==> (np in ca.PortSource) == (np in cb.PortSource));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc && np in ca.PortSource ==> ca.PortSource[np] == cb.PortSource[np]);
  }


}
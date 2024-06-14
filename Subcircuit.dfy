module Subcircuit {

  import opened Circ
  import opened Utils

  opaque predicate NPsInSc(sc: set<CNode>, nps: set<NP>)
  {
    forall np :: np in nps ==> np.n in sc
  }

  opaque predicate NPsNotInSc(sc: set<CNode>, nps: set<NP>)
  {
    forall np :: np in nps ==> np.n !in sc
  }

  lemma ScNoIntersectionNPsNoIntersection(sca: set<CNode>, scb: set<CNode>, npsa: set<NP>, npsb: set<NP>)
    requires SetsNoIntersection(sca, scb)
    requires NPsInSc(sca, npsa)
    requires NPsInSc(scb, npsb)
    ensures SetsNoIntersection(npsa, npsb)
  {
    reveal NPsInSc();
    if exists np :: np in npsa && np in npsb {
      var np :| np in npsa && np in npsb;
      assert np.n in sca;
      assert np.n in scb;
      assert np.n in sca * scb;
      assert false;
    }
  }

  opaque predicate NPsValid(c: Circuit, nps: set<NP>)
  {
    forall np :: np in nps ==> NPValid(c, np)
  }

  opaque predicate INPsValid(c: Circuit, nps: set<NP>)
  {
    forall np :: np in nps ==> INPValid(c, np)
  }

  opaque predicate ONPsValid(c: Circuit, nps: set<NP>)
  {
    forall np :: np in nps ==> ONPValid(c, np)
  }

  lemma INPsAndONPsNoIntersection(c: Circuit, inps: set<NP>, onps: set<NP>)
    requires INPsValid(c, inps)
    requires ONPsValid(c, onps)
    ensures SetsNoIntersection(inps, onps)
  {
    reveal INPsValid();
    reveal ONPsValid();
  }

  opaque function ConnInputs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires c.Valid()
    requires ScValid(c, sc)
    ensures NPsInSc(sc, r)
    ensures INPsValid(c, r)
  {
    reveal Circuit.Valid();
    reveal NPsInSc();
    reveal INPsValid();
    (set np: NP | np.n in sc && np in c.PortSource && c.PortSource[np].n !in sc :: np)
  }

  opaque function UnconnInputs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires c.Valid()
    requires ScValid(c, sc)
    ensures NPsInSc(sc, r)
    ensures INPsValid(c, r)
  {
    reveal NPsInSc();
    reveal ScValid();
    reveal INPsValid();
    (set np: NP | np in AllNPFromNodes(c, sc) && INPValid(c, np) && np !in c.PortSource :: np)
  }

  lemma UnconnInputsAdd(c: Circuit, sc1: set<CNode>, sc2: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sc1)
    requires ScValid(c, sc2)
    ensures ScValid(c, sc1 + sc2)
    ensures UnconnInputs(c, sc1) + UnconnInputs(c, sc2) == UnconnInputs(c, sc1 + sc2)
  {
    reveal ScValid();
    reveal UnconnInputs();
  }

  opaque function ConnOutputs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires c.Valid()
    ensures NPsInSc(sc, r)
    ensures ONPsValid(c, r)
  {
    reveal NPsInSc();
    reveal ONPsValid();
    reveal Circuit.Valid();
    (set np: NP | np.n !in sc && np in c.PortSource && c.PortSource[np].n in sc ::
      c.PortSource[np])
  }

  opaque function AllSeq(c: Circuit, sc: set<CNode>): (r: set<CNode>)
    requires ScValid(c, sc)
    ensures r <= sc
  {
    reveal ScValid();
    (set n | (n in sc) && c.NodeKind[n].CSeq? :: n)
  }
    

  opaque function SeqInputs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires ScValid(c, sc)
    ensures NPsInSc(sc, r)
    ensures ONPsValid(c, r)
  {
    reveal NPsInSc();
    reveal ScValid();
    reveal ONPsValid();
    (set n | (n in sc) && c.NodeKind[n].CSeq? :: NP(n, OUTPUT_0))
  }

  opaque function SeqOutputs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires ScValid(c, sc)
    ensures NPsInSc(sc, r)
    ensures INPsValid(c, r)
  {
    reveal NPsInSc();
    reveal ScValid();
    reveal INPsValid();
    (set n | (n in sc) && c.NodeKind[n].CSeq? :: NP(n, INPUT_0))
  }

  opaque function AllINPs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires ScValid(c, sc)
    ensures NPsInSc(sc, r)
    ensures INPsValid(c, r)
  {
    reveal NPsInSc();
    reveal ScValid();
    reveal INPsValid();
    (set np | np in AllNPFromNodes(c, sc) && INPValid(c, np) :: np)
  }

  opaque function AllONPs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires ScValid(c, sc)
    ensures NPsInSc(sc, r)
    ensures ONPsValid(c, r)
  {
    reveal NPsInSc();
    reveal ScValid();
    reveal ONPsValid();
    (set np | np in AllNPFromNodes(c, sc) && ONPValid(c, np) :: np)
  }
  
  function AllInputs(c: Circuit, sc: set<CNode>): (r: set<NP>)
    requires c.Valid()
    requires ScValid(c, sc)
    ensures NPsInSc(sc, r)
    ensures INPsValid(c, r)
  {
    reveal NPsInSc();
    reveal ScValid();
    reveal INPsValid();
    reveal ONPsValid();
    UnconnInputs(c, sc) + ConnInputs(c, sc)
  }

  function ConnFromTo(c: Circuit, sca: set<CNode>, scb: set<CNode>): (r: set<NP>)
    requires c.Valid()
    requires ScValid(c, sca)
    requires ScValid(c, scb)
    ensures NPsInSc(scb, r)
  {
    reveal NPsInSc();
    reveal ScValid();
    (set np: NP | (np.n in scb) && (np in c.PortSource) && (c.PortSource[np].n in sca) :: np)
  }

  opaque predicate NoConnFromTo(c: Circuit, sca: set<CNode>, scb: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sca)
    requires ScValid(c, scb)
  {
    |ConnFromTo(c, sca, scb)| == 0
  }

  function Complement(c: Circuit, sc: set<CNode>): set<CNode>
  {
    c.NodeKind.Keys - sc
  }

  lemma InScOrComplement(c: Circuit, sc: set<CNode>, n: CNode)
    requires c.Valid()
    requires ScValid(c, sc)
    requires NodeValid(c, n)
    ensures
      var sccomp := SubcircuitComplement(c, sc);
      ((n in sc) || (n in sccomp)) &&
      !((n in sc) && (n in sccomp))
  {
    var sccomp := SubcircuitComplement(c, sc);
    reveal Circuit.Valid();
    reveal ScValid();
    assert (n in sc) || (n in sccomp);
    assert !((n in sc) && (n in sccomp));
  }

  opaque ghost predicate IsIsland(c: Circuit, sc: set<CNode>)
  {
    && (forall np :: np in c.PortSource && np.n in sc ==> c.PortSource[np].n in sc)
    && (forall np :: np in c.PortSource && np.n !in sc ==> c.PortSource[np].n !in sc)
  }

  lemma IsIslandNoConns(c: Circuit, sc1: set<CNode>, sc2: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sc1)
    requires ScValid(c, sc2)
    requires SetsNoIntersection(sc1, sc2)
    requires IsIsland(c, sc1)
    ensures NoConnFromTo(c, sc1, sc2) && NoConnFromTo(c, sc2, sc1)
  {
    reveal Circuit.Valid();
    reveal ScValid();
    reveal IsIsland();
    reveal NoConnFromTo();
    if |ConnFromTo(c, sc1, sc2)| > 0 {
      var np :| np in ConnFromTo(c, sc1, sc2);
      assert np.n in sc2 && np in c.PortSource && c.PortSource[np].n in sc1;
      NotInBoth(np.n, sc1, sc2);
      assert false;
    }
    if |ConnFromTo(c, sc2, sc1)| > 0 {
      var np :| np in ConnFromTo(c, sc2, sc1);
      assert np.n in sc1 && np in c.PortSource && c.PortSource[np].n in sc2;
      NotInBoth(c.PortSource[np].n, sc1, sc2);
      assert np.n in sc1 && np in c.PortSource && c.PortSource[np].n !in sc1;
      assert false;
    }
  }

  lemma NoConnsToComplementIsIsland(c: Circuit, sc: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sc)
    requires
      var sccomp := SubcircuitComplement(c, sc);
      NoConnFromTo(c, sc, sccomp) && NoConnFromTo(c, sccomp, sc)
    ensures
      IsIsland(c, sc)
  {
    reveal Circuit.Valid();
    reveal ScValid();
    reveal NoConnFromTo();
    reveal IsIsland();
    var sccomp := SubcircuitComplement(c, sc);
    assert |ConnFromTo(c, sc, sccomp)| == 0;
    assert |ConnFromTo(c, sccomp, sc)| == 0;
    forall np: NP | np in c.PortSource
      ensures np.n in sc ==> c.PortSource[np].n in sc
      ensures np.n !in sc ==> c.PortSource[np].n !in sc
    {
      InScOrComplement(c, sc, np.n);
      assert ONPValid(c, c.PortSource[np]);
      InScOrComplement(c, sc, c.PortSource[np].n);

      if (np.n in sccomp) && (c.PortSource[np].n in sc) {
        assert np in ConnFromTo(c, sc, sccomp);
      }
      assert !((np.n in sccomp) && (c.PortSource[np].n in sc));
      if (np.n in sc) && (c.PortSource[np].n in sccomp) {
        assert np in ConnFromTo(c, sccomp, sc);
      }
      assert !((np.n in sc) && (c.PortSource[np].n in sccomp));

      if np.n in sc {
        assert c.PortSource[np].n in sc;
      } else {
        assert c.PortSource[np].n !in sc;
      }
    }
  }

  lemma SubcircuitComplementOwnInverse(c: Circuit, sc: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sc)
    ensures SubcircuitComplement(c, SubcircuitComplement(c, sc)) == sc
  {
    reveal Circuit.Valid();
    reveal ScValid();
  }


  lemma IsIslandComplementIsIsland(c: Circuit, sc: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sc)
    requires IsIsland(c, sc)
    ensures IsIsland(c, SubcircuitComplement(c, sc))
  {
    reveal IsIsland();
    reveal Circuit.Valid();
    reveal ScValid();
    var sccomp := SubcircuitComplement(c, sc);
    IsIslandNoConns(c, sc, sccomp);
    assert NoConnFromTo(c, sc, sccomp);
    assert NoConnFromTo(c, sccomp, sc);
    SubcircuitComplementOwnInverse(c, sc);
    assert sc == SubcircuitComplement(c, sccomp);
    NoConnsToComplementIsIsland(c, sccomp);
  }

  lemma IsIslandNoOutputs(c: Circuit, sc: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sc)
    requires IsIsland(c, sc)
    ensures |ConnOutputs(c, sc)| == 0
  {
    reveal Circuit.Valid();
    reveal ScValid();
    reveal IsIsland();
    reveal ConnOutputs();
  }

  lemma IsIslandNoInputs(c: Circuit, sc: set<CNode>)
    requires c.Valid()
    requires ScValid(c, sc)
    requires IsIsland(c, sc)
    ensures |ConnInputs(c, sc)| == 0
  {
    reveal Circuit.Valid();
    reveal ScValid();
    reveal IsIsland();
    reveal ConnInputs();
  }

  opaque predicate PathInSubcircuit(path: seq<NP>, sc: set<CNode>)
  {
    forall np :: np in path ==> np.n in sc
  }
}
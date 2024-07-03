module ConservedSubcircuit {

  import opened Circ
  import opened Eval
  import opened Scuf
  import opened Utils
  import opened Subcircuit
  import opened MapFunction

  ghost opaque predicate CircuitConserved(ca: Circuit, cb: Circuit)
  {
    && (forall n :: n in ca.NodeKind ==> n in cb.NodeKind)
    && (forall n :: n in ca.NodeKind ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np in ca.PortSource ==>
      np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np.n in ca.NodeKind && np !in ca.PortSource && np in cb.PortSource ==>
      cb.PortSource[np].n !in ca.NodeKind)
  }

  ghost opaque predicate CircuitUnconnected(ca: Circuit, cb: Circuit)
  {
    && (forall np :: np in cb.PortSource && np !in ca.PortSource ==>
        np.n !in ca.NodeKind && cb.PortSource[np].n !in ca.NodeKind)
  }

  lemma CircuitConservedUnconnectedTransitive(ca: Circuit, cb: Circuit, cc: Circuit)
    requires CircuitConserved(ca, cb)
    requires CircuitConserved(cb, cc)
    requires CircuitUnconnected(ca, cb)
    requires CircuitUnconnected(cb, cc)
    ensures CircuitConserved(ca, cc)
    ensures CircuitUnconnected(ca, cc)
  {
    reveal CircuitConserved();
    reveal CircuitUnconnected();
  }

  lemma CircuitConservedToSubcircuitConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    requires ca.Valid()
    requires cb.Valid()
    requires CircuitConserved(ca, cb)
    requires ScValid(ca, sc)
    ensures SubcircuitConserved(ca, cb, sc)
  {
    reveal Circuit.Valid();
    reveal CircuitConserved();
    reveal SubcircuitConserved();
    reveal ScValid();
  }

  lemma CircuitConservedTransitive(ca: Circuit, cb: Circuit, cc: Circuit)
    requires CircuitConserved(ca, cb)
    requires CircuitConserved(cb, cc)
    ensures CircuitConserved(ca, cc)
  {
    reveal CircuitConserved();
  }

  ghost opaque predicate NoNewExternalConnections(ca: Circuit, cb: Circuit, sc: set<CNode>)
  {
    && (forall np: NP :: np.n in sc && np !in ca.PortSource && np in cb.PortSource ==> cb.PortSource[np].n in sc)
    && (forall np: NP :: np.n !in sc && np !in ca.PortSource && np in cb.PortSource ==> cb.PortSource[np].n !in sc)
  }

  ghost opaque predicate NoNewInternalConnections(ca: Circuit, cb: Circuit, sc: set<CNode>)
  {
    && (forall np: NP :: np.n in sc && np !in ca.PortSource && np in cb.PortSource ==> cb.PortSource[np].n !in sc)
  }

  ghost opaque predicate SubcircuitWeaklyConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    // New internal connections can be made in the subcircuit.
    requires ScValid(ca, sc)
  {
    reveal ScValid();
    && (forall n :: n in sc ==> n in cb.NodeKind)
    && (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np.n in sc && np in ca.PortSource ==>
        np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
  }

  ghost opaque predicate SubcircuitConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    // The internal connections of the subcircuit remain unchanged.
    requires ScValid(ca, sc)
  {
    reveal ScValid();
    && (forall n :: n in sc ==> n in cb.NodeKind)
    && (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np.n in sc && np in ca.PortSource ==>
        np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np.n in sc && np !in ca.PortSource && np in cb.PortSource ==>
        cb.PortSource[np].n !in sc)
  }

  ghost opaque predicate SubcircuitStronglyConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    // The internal and external connections of the subcircuit remain unchanged.
    requires ScValid(ca, sc)
  {
    reveal ScValid();
    && (forall n :: n in sc ==> n in cb.NodeKind)
    && (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np.n in sc && np in ca.PortSource ==>
        np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np in ca.PortSource && ca.PortSource[np].n in sc ==> np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np in cb.PortSource && cb.PortSource[np].n in sc ==> np in ca.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np.n in sc && np !in ca.PortSource ==> np !in cb.PortSource)
    && (forall np: NP :: np.n in sc && np !in ca.PortSource.Values ==> np !in cb.PortSource.Values)
  }

  lemma ScufSomewhatValidConserved(ca: Circuit, cb: Circuit, e: Scuf)
    requires ca.Valid()
    requires cb.Valid()
    requires e.SomewhatValid(ca)
    requires ScValid(ca, e.sc)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures e.SomewhatValid(cb)
  {
    reveal SubcircuitConserved();
    reveal e.SomewhatValid();
    reveal ScValid();
    reveal ConnOutputs();
    reveal SeqOutputs();
    reveal AllONPs();
    reveal AllINPs();
    reveal SeqInputs();
    reveal UnconnInputs();
    reveal ConnInputs();
    reveal Circuit.Valid();
    reveal AllSeq();
  }

  lemma ScufSomewhatValidRelaxInputsConserved(ca: Circuit, cb: Circuit, e: Scuf)
    requires ca.Valid()
    requires cb.Valid()
    requires e.SomewhatValidRelaxInputs(ca)
    requires ScValid(ca, e.sc)
    requires SubcircuitWeaklyConserved(ca, cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures e.SomewhatValidRelaxInputs(cb)
  {
    reveal SubcircuitWeaklyConserved();
    reveal e.SomewhatValidRelaxInputs();
    reveal ScValid();
    reveal ConnOutputs();
    reveal SeqOutputs();
    reveal AllONPs();
    reveal AllINPs();
    reveal SeqInputs();
    reveal UnconnInputs();
    reveal ConnInputs();
    reveal Circuit.Valid();
    reveal AllSeq();
  }


  ghost opaque predicate SubcircuitUnconnected(ca: Circuit, cb: Circuit, sc: set<CNode>)
  {
    && (forall np :: np in cb.PortSource && np !in ca.PortSource ==> np.n !in sc && cb.PortSource[np].n !in sc)
  }

  lemma IsIslandConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    requires ca.Valid()
    requires ScValid(ca, sc)
    requires IsIsland(ca, sc)
    requires CircuitConserved(ca, cb)
    requires CircuitUnconnected(ca, cb)
    ensures IsIsland(cb, sc)
  {
    reveal Circuit.Valid();
    reveal ScValid();
    reveal IsIsland();
    reveal CircuitConserved();
    reveal CircuitUnconnected();
  }
  
  lemma CircuitConservedSubcircuitConserved(ca: Circuit, cb: Circuit)
    requires ca.Valid()
    requires cb.Valid()
    requires CircuitConserved(ca, cb)
    ensures
      && ScValid(ca, ca.NodeKind.Keys)
      && SubcircuitConserved(ca, cb, ca.NodeKind.Keys)
  {
    reveal Circuit.Valid();
    reveal CircuitConserved();
    reveal SubcircuitConserved();
    reveal ScValid();
    var sc := ca.NodeKind.Keys;
    var nps := AllNPFromNodes(ca, sc);
    assert nps == AllNPFromNodes(cb, sc);

    // There may be some things in cb that are no longer unconnected.
    var newly_connected := (set np | np in nps && np in cb.PortSource && np !in ca.PortSource :: np);

    calc {
      ScInputBoundary(ca, sc);
      NPBetweenSubcircuitsComplement(ca, sc, sc) + UnconnectedINPs(ca, sc) + InternalInputs(ca, sc);
      (NPBetweenSubcircuitsComplement(cb, sc, sc) - newly_connected) + UnconnectedINPs(ca, sc) + InternalInputs(ca, sc);
      (NPBetweenSubcircuitsComplement(cb, sc, sc) - newly_connected) + (UnconnectedINPs(cb, sc) + newly_connected) + InternalInputs(ca, sc);
      {assert forall np :: np in newly_connected ==> np in NPBetweenSubcircuitsComplement(cb, sc, sc) && np !in UnconnectedINPs(cb, sc);}
      NPBetweenSubcircuitsComplement(cb, sc, sc) + UnconnectedINPs(cb, sc) + InternalInputs(ca, sc);
      NPBetweenSubcircuitsComplement(cb, sc, sc) + UnconnectedINPs(cb, sc) + InternalInputs(cb, sc);
      ScInputBoundary(cb, sc);
    }
    assert ScInputBoundary(ca, sc) == ScInputBoundary(cb, sc);
    assert (forall np: NP :: (np in ScInputBoundary(ca, sc)) == (np in ScInputBoundary(cb, sc)));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc ==> (np in ca.PortSource) == (np in cb.PortSource));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc && np in ca.PortSource ==> ca.PortSource[np] == cb.PortSource[np]);
  }

  ghost predicate ConservedValid(ca: Circuit, cb: Circuit, e: Scuf, fi: FI)
  {
    && ca.Valid()
    && cb.Valid()
    && e.ValidRelaxInputs(ca)
    && SubcircuitWeaklyConserved(ca, cb, e.sc)
    && (Seq.ToSet(e.mp.inputs) == fi.inputs.Keys)
    && (Seq.ToSet(e.mp.state) == fi.state.Keys)
    && OutputsInFOutputs(cb, e)
  }

  lemma EvaluateINPInnerConserved(
    ca: Circuit, cb: Circuit, e: Scuf, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires forall np :: np in path ==> np.n in e.sc
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    requires INPValid(ca, Seq.Last(path))
    ensures PathValid(cb, path)
    ensures
      && ca.Valid()
      && cb.Valid()
      && INPValid(cb, Seq.Last(path))
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && EvaluateINPInnerRequirements(ca, path, fi)
      && EvaluateINPInnerRequirements(cb, path, fi)
      && (EvaluateINPInner(ca, path, fi) == EvaluateINPInner(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 2
  {
    reveal PathValid();
    reveal Circuit.Valid();
    reveal SubcircuitWeaklyConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var head := Seq.Last(path);
    var tail := Seq.DropLast(path);
    if head in fi.inputs {
      assert EvaluateINPInner(ca, path, fi) == EvaluateINPInner(cb, path, fi);
    } else {
      assert head !in e.mp.inputs by {
        reveal Seq.ToSet();
      }
      StaysInSc(ca, e, head);
      assert fi.inputs.Keys == Seq.ToSet(e.mp.inputs);
      if head in ca.PortSource {
        var onp := ca.PortSource[head];
        if onp in path {
        } else {
          reveal Circuit.Valid();
          NodesNotInPathDecreases(ca, path, onp);
          StillHasNoDuplicates(path, onp);
          assert onp.n in e.sc;
          EvaluateONPInnerConserved(ca, cb, e, path + [onp], fi);
        }
      } else {
      }
    }
  }

  lemma EvaluateONPBinaryConserved(ca: Circuit, cb: Circuit, e: Scuf, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires ONPValid(ca, Seq.Last(path))
    requires Seq.Last(path).n !in fi.state
    requires forall np :: np in path ==> np.n in e.sc
    requires
      var nk := ca.NodeKind[Seq.Last(path).n];
      nk.CXor? || nk.CAnd?
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    ensures PathValid(cb, path)
    ensures
      && ca.Valid()
      && cb.Valid()
      && ONPValid(cb, Seq.Last(path))
      && var nk := cb.NodeKind[Seq.Last(path).n];
      && (nk.CXor? || nk.CAnd?)
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (EvaluateONPBinary(ca, path, fi) == EvaluateONPBinary(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal PathValid();
    reveal Circuit.Valid();
    reveal SubcircuitWeaklyConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var nk := ca.NodeKind[path[|path|-1].n];
    var head := path[|path|-1];
    assert NodeValid(ca, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path {
    } else if inp_1 in path {
    } else {
      NodesNotInPathDecreases(ca, path, inp_0);
      NodesNotInPathDecreases(ca, path, inp_1);
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_0], fi);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_1], fi);
    }
  }

  lemma EvaluateONPUnaryConserved(ca: Circuit, cb: Circuit, e: Scuf, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires ONPValid(ca, path[|path|-1])
    requires path[|path|-1].n !in fi.state
    requires
      var nk := ca.NodeKind[path[|path|-1].n];
      nk.CInv? || nk.CIden?
    requires PathValid(ca, path)
    requires forall np :: np in path ==> np.n in e.sc
    requires Seq.HasNoDuplicates(path)
    ensures PathValid(cb, path)
    ensures
      && ca.Valid()
      && cb.Valid()
      && ONPValid(cb, Seq.Last(path))
      && var nk := cb.NodeKind[Seq.Last(path).n];
      && (nk.CInv? || nk.CIden?)
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (EvaluateONPUnary(ca, path, fi) == EvaluateONPUnary(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal PathValid();
    reveal Circuit.Valid();
    reveal SubcircuitWeaklyConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(ca, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_0], fi);
    }
  }

  lemma FICircuitValidFromConservedValid(ca: Circuit, cb: Circuit, e: Scuf, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    ensures FICircuitValid(ca, fi) && FICircuitValid(cb, fi)
  {
    ScufValidFiValidToFICircuitValid(ca, e, fi);
    ScufSomewhatValidRelaxInputsConserved(ca, cb, e);
    ScufValidFiValidToFICircuitValid(cb, e, fi);
  }

  lemma EvaluateONPInnerConserved(ca: Circuit, cb: Circuit, e: Scuf, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires EvaluateONPInnerRequirements(ca, path, fi)
    requires forall np :: np in path ==> np.n in e.sc
    ensures PathValid(cb, path)
    ensures
      && ca.Valid()
      && cb.Valid()
      && ONPValid(cb, Seq.Last(path))
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (EvaluateONPInner(ca, path, fi) == EvaluateONPInner(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 4
  {
    reveal PathValid();
    reveal Circuit.Valid();
    reveal SubcircuitWeaklyConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var head := path[|path|-1];
    if head.n in fi.state {
    } else {
      var nk := ca.NodeKind[head.n];
      match nk
        case CXor() => EvaluateONPBinaryConserved(ca, cb, e, path, fi);
        case CAnd() => EvaluateONPBinaryConserved(ca, cb, e, path, fi);
        case CInv() => EvaluateONPUnaryConserved(ca, cb, e, path, fi);
        case CIden() => EvaluateONPUnaryConserved(ca, cb, e, path, fi);
        case CConst(b) => {}
        case CSeq() => {}
    }
  }

  lemma EvaluateConserved(ca: Circuit, cb: Circuit, e: Scuf, o: NP, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires o.n in e.sc
    requires INPValid(ca, o) || ONPValid(ca, o)
    ensures INPValid(cb, o) || ONPValid(cb, o)
    ensures
      && ca.Valid()
      && cb.Valid()
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (Evaluate(ca, o, fi) == Evaluate(cb, o, fi))
  {
    reveal PathValid();
    reveal Circuit.Valid();
    reveal SubcircuitConserved();
    assert PathValid(ca, [o]);
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    LengthOneNoDuplicates([o]);
    if INPValid(ca, o) {
      EvaluateINPInnerConserved(ca, cb, e, [o], fi);
    } else {
      EvaluateONPInnerConserved(ca, cb, e, [o], fi);
    }
  }

  lemma ScufConserved3(ca: Circuit, cb: Circuit, e: Scuf)
    requires ca.Valid()
    requires cb.Valid()
    requires CircuitConserved(ca, cb)
    requires CircuitUnconnected(ca, cb)
    requires e.Valid(ca)
    ensures e.Valid(cb)
  {
    CircuitConservedToSubcircuitConserved(ca, cb, e.sc);
    assert SubcircuitWeaklyConserved(ca, cb, e.sc) by {
      reveal SubcircuitConserved();
      reveal SubcircuitWeaklyConserved();
    }
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    reveal ScValid();
    reveal Scuf.SomewhatValid();
    reveal ConnOutputs();
    assert Seq.ToSet(e.mp.outputs) >= ConnOutputs(ca, e.sc);
    assert Seq.ToSet(e.mp.outputs) >= ConnOutputs(cb, e.sc);
    ScufConserved(ca, cb, e);
  }

  //lemma ScufConserved2(ca: Circuit, cb: Circuit, e: Scuf)
  //  requires ca.Valid()
  //  requires cb.Valid()
  //  requires CircuitConserved(ca, cb)
  //  requires e.Valid(ca)
  //  requires ScValid(cb, e.sc)
  //  requires OutputsInFOutputs(cb, e)
  //  ensures e.Valid(cb)
  //{
  //  CircuitConservedToSubcircuitConserved(ca, cb, e.sc);
  //  assert SubcircuitWeaklyConserved(ca, cb, e.sc) by {
  //    reveal SubcircuitConserved();
  //    reveal SubcircuitWeaklyConserved();
  //  }
  //  reveal CircuitConserved();
  //  reveal CircuitUnconnected();
  //  reveal ScValid();
  //  ScufConserved(ca, cb, e);
  //}

  lemma ScufConserved(ca: Circuit, cb: Circuit, e: Scuf)
    requires ca.Valid()
    requires cb.Valid()
    requires e.Valid(ca)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires ScValid(cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures e.Valid(cb)
  {
    reveal Circuit.Valid();
    reveal ScValid();
    reveal SubcircuitConserved();
    reveal SubcircuitWeaklyConserved();

    assert ScValid(ca, e.sc);
    assert ScValid(cb, e.sc) by {
      reveal ScValid();
    }

    ScufSomewhatValidConserved(ca, cb, e);
    e.SomewhatValidToRelaxInputs(ca);
    e.SomewhatValidToRelaxInputs(cb);

    if e.Valid(ca) {
      forall fi: FI | FIValid(fi, e.mp.inputs, e.mp.state)
        ensures forall np :: np in (Seq.ToSet(e.mp.outputs) + StateINPs(e.mp.state)) ==> (
          && NPValid(ca, np)
          && NPValid(cb, np)
          && FICircuitValid(ca, fi)
          && FICircuitValid(cb, fi)
          && (Evaluate(ca, np, fi) == Evaluate(cb, np, fi))
        )
      {
        ScufValidFiValidToFICircuitValid(ca, e, fi);
        ScufValidFiValidToFICircuitValid(cb, e, fi);
        forall np | np in (Seq.ToSet(e.mp.outputs) + StateINPs(e.mp.state))
          ensures
            && NPValid(ca, np) && NPValid(cb, np)
            && (Evaluate(ca, np, fi) == Evaluate(cb, np, fi))
        {
          ScufFOutputsAreValid(ca, e);
          FOutputsInSc(ca, e);
          reveal NPsInSc();
          assert NPValid(ca, np) by {
            reveal Scuf.SomewhatValid();
            reveal AllONPs();
            reveal AllSeq();
            reveal ONPsValid();
          }
          EvaluateConserved(ca, cb, e, np, fi);
          assert Evaluate(ca, np, fi) == Evaluate(cb, np, fi);
        }
      }
    }

    assert e.uf.Valid() by {
      reveal UpdateFunction.Valid();
    }
    assert ScValid(cb, e.sc);
    assert e.EvaluatesCorrectly(cb) by {
      reveal Scuf.EvaluatesCorrectly();
    }
  }

  lemma ScufWeaklyConserved(ca: Circuit, cb: Circuit, s: Scuf)
    requires ca.Valid()
    requires cb.Valid()
    requires s.ValidRelaxInputs(ca)
    requires SubcircuitWeaklyConserved(ca, cb, s.sc)
    requires OutputsInFOutputs(cb, s)
    ensures s.ValidRelaxInputs(cb)
  {
    assert s.MapValid();
    assert ScValid(cb, s.sc) by {
      reveal SubcircuitWeaklyConserved();
      reveal ScValid();
    }
    assert s.SomewhatValidRelaxInputs(cb) by {
      ScufSomewhatValidRelaxInputsConserved(ca, cb, s);
    }
    assert s.EvaluatesCorrectly(cb) by {
      reveal Scuf.EvaluatesCorrectly();
      reveal Seq.ToSet();
      forall fi: FI | FIValid(fi, s.mp.inputs, s.mp.state)
        ensures
        forall np :: np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state) ==>
          && FICircuitValid(cb, fi)
          && np.n in s.sc && NPValid(ca, np) && NPValid(cb, np)
          && (Evaluate(cb, np, fi) == EvalOk(MFLookup(s, fi, np)))
      {
        assert ConservedValid(ca, cb, s, fi);
        assert FICircuitValid(cb, fi) by {ScufValidFiValidToFICircuitValid(cb, s, fi);}
        forall np | np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state)
          ensures np.n in s.sc && NPValid(ca, np) && NPValid(cb, np)
          ensures Evaluate(cb, np, fi) == EvalOk(MFLookup(s, fi, np))
        {
          assert np.n in s.sc && NPValid(ca, np) by {
            FOutputsInSc(ca, s);
            ScufFOutputsAreValid(ca, s);
            reveal NPsInSc();
          }
          EvaluateConserved(ca, cb, s, np, fi);
          assert Evaluate(ca, np, fi) == Evaluate(cb, np, fi);
          assert Evaluate(cb, np, fi) == EvalOk(MFLookup(s, fi, np));
        }
      }
    }
  }

  opaque ghost predicate SimpleInsertion(c: Circuit, new_c: Circuit, e: Scuf)
  {
    && new_c.Valid()
    && e.Valid(new_c)
    && IsIsland(new_c, e.sc)
    && CircuitUnconnected(c, new_c)
    && CircuitConserved(c, new_c)
    && (new_c.NodeKind.Keys == c.NodeKind.Keys + e.sc)
    && (c.NodeKind.Keys !! e.sc)
  }

  opaque ghost predicate DualInsertion(c: Circuit, new_c: Circuit, s1: Scuf, s2: Scuf)
  {
    && new_c.Valid()
    && s1.Valid(new_c)
    && s2.Valid(new_c)
    && IsIsland(new_c, s1.sc)
    && IsIsland(new_c, s2.sc)
    && (s1.sc !! s2.sc)
    && CircuitUnconnected(c, new_c)
    && CircuitConserved(c, new_c)
    && (new_c.NodeKind.Keys == c.NodeKind.Keys + s1.sc + s2.sc)
    && (c.NodeKind.Keys !! s1.sc)
  }

  lemma TwoSimpleInsertionIsDualInsertion(c: Circuit, c1: Circuit, c2: Circuit, s1: Scuf, s2: Scuf)
    requires SimpleInsertion(c, c1, s1)
    requires SimpleInsertion(c1, c2, s2)
    ensures DualInsertion(c, c2, s1, s2)
  {
    reveal SimpleInsertion();
    reveal DualInsertion();
    ScufConserved3(c1, c2, s1);
    IsIslandConserved(c1, c2, s1.sc);
    assert c2.Valid();
    assert s1.Valid(c2);
    assert s2.Valid(c2);
    assert IsIsland(c2, s1.sc);
    assert IsIsland(c2, s2.sc);
    assert (s1.sc !! s2.sc);
    CircuitConservedUnconnectedTransitive(c, c1, c2);
    assert CircuitConserved(c, c2);
    assert (c2.NodeKind.Keys == c.NodeKind.Keys + s1.sc + s2.sc);
    assert (c.NodeKind.Keys !! s1.sc);
  }

  datatype ScufInserter = ScufInserter(
    uf: UpdateFunction,
    fn: Circuit --> (Circuit, Scuf)
  ) {

    ghost predicate SpecificValid(c: Circuit)
      requires c.Valid()
      requires uf.Valid()
    {
      && fn.requires(c)
      && var (new_c, e) := fn(c);
      && (e.uf == uf)
      && SimpleInsertion(c, new_c, e)
    }

    opaque ghost predicate Valid() {
      && uf.Valid()
      && (forall c: Circuit :: c.Valid() ==> SpecificValid(c))
    }

    lemma ValidForCircuit(c: Circuit)
      requires Valid()
      requires c.Valid()
      ensures uf.Valid()
      ensures SpecificValid(c)
    {
      reveal Valid();
    }

    lemma FnOutputsValid(c: Circuit)
      requires Valid()
      requires c.Valid()
      ensures
        reveal Valid();
        var (new_c, s) := fn(c);
        && new_c.Valid()
        && s.Valid(new_c)
    {
      reveal Valid();
      reveal SimpleInsertion();
    }
  }

  lemma StillSimpleInsertionAfterScufSwapMF(old_c: Circuit, new_c: Circuit, e: Scuf, uf: UpdateFunction)
    requires SimpleInsertion(old_c, new_c, e)
    requires uf.Valid()
    requires
      reveal SimpleInsertion();
      UpdateFunctionsEquiv(e.uf, uf)
    ensures
      reveal SimpleInsertion();
      var new_e := ScufSwapUF(new_c, e, uf);
      SimpleInsertion(old_c, new_c, new_e)
  {
    reveal SimpleInsertion();
  }

  function InsertTwo(c: Circuit, z1: ScufInserter, z2: ScufInserter): (r: (Circuit, Scuf, Scuf))
    requires c.Valid()
    requires z1.Valid()
    requires z2.Valid()
    ensures DualInsertion(c, r.0, r.1, r.2)
  {
    reveal SimpleInsertion();
    z1.ValidForCircuit(c);
    var (c1, s1) := z1.fn(c);
    z2.ValidForCircuit(c1);
    var (c2, s2) := z2.fn(c1);
    TwoSimpleInsertionIsDualInsertion(c, c1, c2, s1, s2);
    (c2, s1, s2)
  }
  


}
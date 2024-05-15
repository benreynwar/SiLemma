module ConservedSubcircuit {

  import opened Circ
  import opened Eval
  import opened Entity
  import opened Utils
  import opened Subcircuit
  import opened MapFunction

  ghost opaque predicate CircuitConserved(ca: Circuit, cb: Circuit)
  {
    && (forall n :: n in ca.NodeKind ==> n in cb.NodeKind)
    && (forall n :: n in ca.NodeKind ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np in ca.PortSource ==> np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np.n in ca.NodeKind && np !in ca.PortSource && np in cb.PortSource ==> cb.PortSource[np].n !in ca.NodeKind)
  }

  ghost opaque predicate CircuitUnconnected(ca: Circuit, cb: Circuit)
  {
    && (forall np :: np in cb.PortSource && np !in ca.PortSource ==> np.n !in ca.NodeKind && cb.PortSource[np].n !in ca.NodeKind)
  }

  lemma CircuitConservedToSubcircuitConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires ScValid(ca, sc)
    ensures SubcircuitConserved(ca, cb, sc)
  {
    reveal CircuitValid();
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

  ghost opaque predicate SubcircuitConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
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

  lemma EntitySomewhatValidConserved(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires EntitySomewhatValid(ca, e)
    requires ScValid(ca, e.sc)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires ScValid(cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures EntitySomewhatValid(cb, e)
  {
    reveal SubcircuitConserved();
    reveal EntitySomewhatValid();
    reveal ScValid();
    reveal ConnOutputs();
    reveal SeqOutputs();
    reveal AllONPs();
    //reveal OutputsInFOutputs();
    reveal AllINPs();
    reveal SeqInputs();
    reveal UnconnInputs();
    reveal ConnInputs();
    reveal CircuitValid();
  }


  ghost opaque predicate SubcircuitUnconnected(ca: Circuit, cb: Circuit, sc: set<CNode>)
  {
    && (forall np :: np in cb.PortSource && np !in ca.PortSource ==> np.n !in sc && cb.PortSource[np].n !in sc)
  }

  lemma IsIslandConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    requires CircuitValid(ca)
    requires ScValid(ca, sc)
    requires IsIsland(ca, sc)
    requires CircuitConserved(ca, cb)
    requires CircuitUnconnected(ca, cb)
    ensures IsIsland(cb, sc)
  {
    reveal CircuitValid();
    reveal ScValid();
    reveal IsIsland();
    reveal CircuitConserved();
    reveal CircuitUnconnected();
  }
  
  lemma CircuitConservedSubcircuitConserved(ca: Circuit, cb: Circuit)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    ensures
      && ScValid(ca, ca.NodeKind.Keys)
      && SubcircuitConserved(ca, cb, ca.NodeKind.Keys)
  {
    reveal CircuitValid();
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

  ghost predicate ConservedValid(ca: Circuit, cb: Circuit, e: Entity, fi: FI)
  {
    && CircuitValid(ca)
    && CircuitValid(cb)
    && EntityValid(ca, e)
    && SubcircuitConserved(ca, cb, e.sc)
    && (e.mf.inputs == fi.inputs.Keys)
    && (StateONPs(e.mf.state) == fi.state.Keys)
  }

  lemma EvaluateINPInnerConserved(
    ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires forall np :: np in path ==> np.n in e.sc
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    requires INPValid(ca, Seq.Last(path))
    ensures PathValid(cb, path)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      INPValid(cb, Seq.Last(path)) &&
      EvaluateINPInner(ca, path, fi) == EvaluateINPInner(cb, path, fi)
    decreases |NodesNotInPath(ca, path)|, 2
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    var head := Seq.Last(path);
    var tail := Seq.DropLast(path);
    if head in fi.inputs {
      assert EvaluateINPInner(ca, path, fi) == EvaluateINPInner(cb, path, fi);
    } else {
      StaysInSc(ca, e, head);
      assert fi.inputs.Keys == e.mf.inputs;
      if head in ca.PortSource {
        var onp := ca.PortSource[head];
        if onp in path {
        } else {
          reveal CircuitValid();
          NodesNotInPathDecreases(ca, path, onp);
          StillHasNoDuplicates(path, onp);
          assert onp.n in e.sc;
          EvaluateONPInnerConserved(ca, cb, e, path + [onp], fi);
        }
      } else {
      }
    }
  }

  lemma EvaluateONPBinaryConserved(ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires ONPValid(ca, Seq.Last(path))
    requires Seq.Last(path) !in fi.inputs
    requires forall np :: np in path ==> np.n in e.sc
    requires
      var nk := ca.NodeKind[Seq.Last(path).n];
      nk.CXor? || nk.CAnd?
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    ensures PathValid(cb, path)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      ONPValid(cb, Seq.Last(path)) &&
      var nk := cb.NodeKind[Seq.Last(path).n];
      (nk.CXor? || nk.CAnd?) &&
      EvaluateONPBinary(ca, path, fi) == EvaluateONPBinary(cb, path, fi)
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
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

  lemma EvaluateONPUnaryConserved(ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires ONPValid(ca, path[|path|-1])
    requires path[|path|-1] !in fi.inputs
    requires ca.NodeKind[path[|path|-1].n].CInv?
    requires PathValid(ca, path)
    requires forall np :: np in path ==> np.n in e.sc
    requires Seq.HasNoDuplicates(path)
    ensures PathValid(cb, path)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      ONPValid(cb, Seq.Last(path)) &&
      var nk := cb.NodeKind[Seq.Last(path).n];
      nk.CInv? &&
      EvaluateONPUnary(ca, path, fi) == EvaluateONPUnary(cb, path, fi)
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(ca, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_0], fi);
    }
  }

  lemma EvaluateONPInnerConserved(ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires EvaluateONPInnerRequirements(ca, path)
    requires forall np :: np in path ==> np.n in e.sc
    ensures PathValid(cb, path)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      ONPValid(cb, Seq.Last(path)) &&
      EvaluateONPInner(ca, path, fi) == EvaluateONPInner(cb, path, fi)
    decreases |NodesNotInPath(ca, path)|, 4
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    var head := path[|path|-1];
    if head in fi.inputs {
    } else {
      var nk := ca.NodeKind[head.n];
      match nk
        case CXor() => EvaluateONPBinaryConserved(ca, cb, e, path, fi);
        case CAnd() => EvaluateONPBinaryConserved(ca, cb, e, path, fi);
        case CInv() => EvaluateONPUnaryConserved(ca, cb, e, path, fi);
        case CConst(b) => {}
        case CSeq() => {}
    }
  }

  lemma EvaluateConserved(ca: Circuit, cb: Circuit, e: Entity, o: NP, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires o.n in e.sc
    requires INPValid(ca, o) || ONPValid(ca, o)
    ensures INPValid(cb, o) || ONPValid(cb, o)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      (Evaluate(ca, o, fi) == Evaluate(cb, o, fi))
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    assert PathValid(ca, [o]);
    LengthOneNoDuplicates([o]);
    if INPValid(ca, o) {
      EvaluateINPInnerConserved(ca, cb, e, [o], fi);
    } else {
      EvaluateONPInnerConserved(ca, cb, e, [o], fi);
    }
  }

  lemma ScInputBoundaryConserved(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires forall n :: n in e.sc ==> n in ca.NodeKind
  {
    assert CircuitValid(ca);
    reveal CircuitValid();
    reveal CircuitConserved();
    reveal ScValid();
  }

  lemma ScOutputBoundaryConserved(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires CircuitUnconnected(ca, cb)
    requires EntityValid(ca, e)
    ensures ScOutputBoundary(ca, e.sc) == ScOutputBoundary(cb, e.sc)
  {
    reveal CircuitValid();
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    reveal ScValid();
  }

  lemma EntityConserved2(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires EntityValid(ca, e)
    requires ScValid(cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures EntityValid(cb, e)
  {
    CircuitConservedToSubcircuitConserved(ca, cb, e.sc);
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    reveal ScValid();
    EntityConserved(ca, cb, e);
  }

  lemma EntityConserved(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires EntityValid(ca, e)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires ScValid(cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures EntityValid(cb, e)
  {
    reveal CircuitValid();
    reveal ScValid();
    reveal SubcircuitConserved();

    assert ScValid(ca, e.sc);
    assert ScValid(cb, e.sc) by {
      reveal ScValid();
    }

    if EntityValid(ca, e) {
      forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
        ensures forall np :: np in e.mf.outputs ==>
          && NPValid(ca, np) && NPValid(cb, np)
          && (Evaluate(ca, np, fi) == Evaluate(cb, np, fi))
      {
        forall np | np in e.mf.outputs
          ensures
            && NPValid(ca, np) && NPValid(cb, np)
            && (Evaluate(ca, np, fi) == Evaluate(cb, np, fi))
        {
          EntityFOutputsAreValid(ca, e);
          FOutputsInSc(ca, e);
          reveal NPsInSc();
          EvaluateConserved(ca, cb, e, np, fi);
          assert Evaluate(ca, np, fi) == Evaluate(cb, np, fi);
        }
      }
    }

    EntitySomewhatValidConserved(ca, cb, e);
    assert EntitySomewhatValid(cb, e);
    assert MapFunctionValid(e.mf) by {
      reveal MapFunctionValid();
    }
    assert ScValid(cb, e.sc);
    assert EntityEvaluatesCorrectly(cb, e) by {
      reveal EntityEvaluatesCorrectly();
    }
  }
}
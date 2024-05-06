module ConservedSubcircuit {

  import opened Circ
  import opened Eval
  import opened Equiv
  import opened Utils
  import opened MapFunction

  // To show that the rest of the graph is unchanged I need to show that
  // there is a set of nodes which have the same n.
  // There are no connections from those nodes to anything new without getting blocked by a known.
  // The result of an Evaluate should be the same.

  // We define a subgraph as all the nodes in the subgraph together with all the INPs that form the
  // upper boundary (not really necessary, can probably simplify in the future)
  datatype Subcircuit = Subcircuit(
    nodes: set<CNode>,
    boundary: set<NP>
  )

  // What kind of changes would I like to categorize
  // 1) This subcircuit has it's internal stucture left alone.
  // 2) This subcircuit has no new connections in.
  // 3) This subcircuit has no new connections out.
  // 4) This subcircuit is totally left alone (i.e. not change or connections in or out) (1 + 2 + 3)


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
  {
    reveal ScValid();
    && (forall n :: n in sc ==> n in ca.NodeKind && n in cb.NodeKind)
    && (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: (np in ScInputBoundary(ca, sc)) == (np in ScInputBoundary(cb, sc)))
    && (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc ==> (np in ca.PortSource) == (np in cb.PortSource))
    && (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc && np in ca.PortSource ==> ca.PortSource[np] == cb.PortSource[np])
  }

  ghost opaque predicate SubcircuitUnconnected(ca: Circuit, cb: Circuit, sc: set<CNode>)
  {
    && (forall np :: np in cb.PortSource && np !in ca.PortSource ==> np.n !in sc && cb.PortSource[np].n !in sc)
  }

  ghost opaque predicate SubcircuitIsIsland(c: Circuit, sc: set<CNode>)
  {
    && (forall np :: np in c.PortSource && np.n in sc ==> c.PortSource[np].n in sc)
    && (forall np :: np in c.PortSource && np.n !in sc ==> c.PortSource[np].n !in sc)
  }
  
  lemma CircuitConservedSubcircuitConserved(ca: Circuit, cb: Circuit)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    ensures SubcircuitConserved(ca, cb, ca.NodeKind.Keys)
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
    //NPBetweenSubcircuitsComplement(c, sc, sc) + UnconnectedINPs(c, sc) + InternalInputs(c, sc)
    assert (forall np: NP :: (np in ScInputBoundary(ca, sc)) == (np in ScInputBoundary(cb, sc)));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc ==> (np in ca.PortSource) == (np in cb.PortSource));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc && np in ca.PortSource ==> ca.PortSource[np] == cb.PortSource[np]);
  }

  ghost opaque predicate ConservedValid(ca: Circuit, cb: Circuit, e: Equiv, known: map<NP, bool>)
  {
    CircuitValid(ca) && CircuitValid(cb) &&
    EquivValid(ca, e) && EquivValid(cb, e) &&
    SubcircuitConserved(ca, cb, e.sc) &&
    (forall np :: np in e.inputs ==> np in known) &&
    (forall np :: np in known ==> np.n in e.sc)
  }

  lemma EvaluateINPInnerConserved(
    ca: Circuit, cb: Circuit, e: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, e, knowns)
    requires |path| > 0
    requires forall np :: np in path ==> np.n in e.sc
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    requires INPValid(ca, Seq.Last(path))
    ensures PathValid(cb, path)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      INPValid(cb, Seq.Last(path)) &&
      EvaluateINPInner(ca, path, knowns) == EvaluateINPInner(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 2
  {
    reveal ConservedValid();
    reveal EquivValid();
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    var head := Seq.Last(path);
    var tail := Seq.DropLast(path);
    if head in knowns {
      assert EvaluateINPInner(ca, path, knowns) == EvaluateINPInner(cb, path, knowns);
    } else {
      if head in ca.PortSource {
        var onp := ca.PortSource[head];
        if onp in path {
        } else {
          reveal CircuitValid();
          NodesNotInPathDecreases(ca, path, onp);
          StillHasNoDuplicates(path, onp);
          EvaluateONPInnerConserved(ca, cb, e, path + [onp], knowns);
        }
      } else {
      }
    }
  }

  lemma EvaluateONPBinaryConserved(
      ca: Circuit, cb: Circuit, e: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, e, knowns)
    requires |path| > 0
    requires ONPValid(ca, Seq.Last(path))
    requires Seq.Last(path) !in knowns
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
      EvaluateONPBinary(ca, path, knowns) == EvaluateONPBinary(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal ConservedValid();
    reveal EquivValid();
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
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_0], knowns);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_1], knowns);
    }
  }

  lemma EvaluateONPUnaryConserved(
      ca: Circuit, cb: Circuit, e: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, e, knowns)
    requires |path| > 0
    requires ONPValid(ca, path[|path|-1])
    requires path[|path|-1] !in knowns
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
      EvaluateONPUnary(ca, path, knowns) == EvaluateONPUnary(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal ConservedValid();
    reveal EquivValid();
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(ca, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_0], knowns);
    }
  }

  lemma EvaluateONPInnerConserved(
      ca: Circuit, cb: Circuit, e: Equiv, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, e, knowns)
    requires EvaluateONPInnerRequirements(ca, path, knowns)
    requires forall np :: np in path ==> np.n in e.sc
    ensures PathValid(cb, path)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      ONPValid(cb, Seq.Last(path)) &&
      EvaluateONPInner(ca, path, knowns) == EvaluateONPInner(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 4
  {
    reveal ConservedValid();
    reveal EquivValid();
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    var head := path[|path|-1];
    if head in knowns {
    } else {
      var nk := ca.NodeKind[head.n];
      match nk
        case CXor() => EvaluateONPBinaryConserved(ca, cb, e, path, knowns);
        case CAnd() => EvaluateONPBinaryConserved(ca, cb, e, path, knowns);
        case CInv() => EvaluateONPUnaryConserved(ca, cb, e, path, knowns);
        case CConst(b) => {}
        case CInput() => {}
        case CSeq() => {}
    }
  }

  lemma EvaluateConserved(ca: Circuit, cb: Circuit, e: Equiv, o: NP, known: map<NP, bool>)
    requires ConservedValid(ca, cb, e, known)
    requires o.n in e.sc
    requires INPValid(ca, o) || ONPValid(ca, o)
    ensures INPValid(cb, o) || ONPValid(cb, o)
    ensures
      CircuitValid(ca) && CircuitValid(cb) &&
      (Evaluate(ca, o, known) == Evaluate(cb, o, known))
  {
    reveal ConservedValid();
    reveal EquivValid();
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    assert PathValid(ca, [o]);
    LengthOneNoDuplicates([o]);
    if INPValid(ca, o) {
      EvaluateINPInnerConserved(ca, cb, e, [o], known);
    } else {
      EvaluateONPInnerConserved(ca, cb, e, [o], known);
    }
  }

  lemma ScInputBoundaryConserved(ca: Circuit, cb: Circuit, e: Equiv)
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

  lemma ScOutputBoundaryConserved(ca: Circuit, cb: Circuit, e: Equiv)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires CircuitUnconnected(ca, cb)
    requires EquivValid(ca, e)
    ensures ScOutputBoundary(ca, e.sc) == ScOutputBoundary(cb, e.sc)
  {
    reveal CircuitValid();
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    reveal EquivValid();
    reveal EquivScOutputsInOutputs();
    reveal ScValid();
  }


  lemma EquivConserved2(ca: Circuit, cb: Circuit, e: Equiv)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires CircuitUnconnected(ca, cb)
    requires EquivValid(ca, e)
    ensures EquivValid(cb, e)
    ensures EquivValid(ca, e) ==> EquivTrue(ca, e) == EquivTrue(cb, e)
  {
    reveal EquivValid();
    CircuitConservedToSubcircuitConserved(ca, cb, e.sc);
    assert EquivScOutputsInOutputs(ca, e.sc, e.outputs);
    reveal EquivScOutputsInOutputs();
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    reveal ScValid();
    EquivConserved(ca, cb, e);
  }

  lemma EquivConserved(ca: Circuit, cb: Circuit, e: Equiv)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires EquivScOutputsInOutputs(ca, e.sc, e.outputs)
    requires EquivScOutputsInOutputs(cb, e.sc, e.outputs)
    ensures EquivValid(ca, e) == EquivValid(cb, e)
    ensures EquivValid(ca, e) ==> EquivTrue(ca, e) == EquivTrue(cb, e)
  {
    reveal EquivScOutputsInOutputs();
    reveal CircuitValid();
    reveal EquivValid();
    reveal EquivTrue();
    reveal ConservedValid();

    reveal ScValid();
    reveal NPsValidAndInSc();
    reveal SubcircuitConserved();

    assert ScValid(ca, e.sc) == ScValid(cb, e.sc);

    assert EquivValid(ca, e) == EquivValid(cb, e);
    if EquivValid(ca, e) {
      forall knowns: map<NP, bool> | knowns.Keys == e.inputs
        ensures forall np :: np in e.outputs ==> Evaluate(ca, np, knowns) == Evaluate(cb, np, knowns)
      {
        forall np | np in e.outputs
          ensures Evaluate(ca, np, knowns) == Evaluate(cb, np, knowns)
        {
          EvaluateConserved(ca, cb, e, np, knowns);
          assert Evaluate(ca, np, knowns) == Evaluate(cb, np, knowns);
        }
      }
    }
  }
}
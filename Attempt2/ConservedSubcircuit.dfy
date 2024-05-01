module ConservedSubcircuit {

  import opened Circ
  import opened Eval

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

  predicate SubcircuitValid(c: Circuit, sc: Subcircuit)
  {
    (forall np :: np in sc.boundary ==> INPValid(c, np) || ONPValid(c, np)) &&
    (forall n :: n in sc.nodes ==> n in c.NodeKind) &&
    (forall np :: np in sc.boundary ==> np.n in sc.nodes) &&
    (forall np: NP :: np.n in sc.nodes && np in c.PortSource && np !in sc.boundary ==>
      c.PortSource[np].n in sc.nodes)
  }

  ghost predicate SubcircuitConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
  {
    (forall n :: n in sc ==> n in  ca.NodeKind && n in cb.NodeKind) &&
    (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n]) &&
    (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n]) &&
    (forall np: NP :: (np in ScInputBoundary(ca, sc)) == (np in ScInputBoundary(cb, sc))) &&
    (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc ==> (np in ca.PortSource) == (np in cb.PortSource)) &&
    (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc && np in ca.PortSource ==> ca.PortSource[np] == cb.PortSource[np])
  }

  ghost predicate ConservedValid(ca: Circuit, cb: Circuit, e: Equiv, known: map<NP, bool>)
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
    requires INPValid(ca, path[|path|-1])
    ensures PathValid(cb, path)
    ensures
      EvaluateINPInner(ca, path, knowns) == EvaluateINPInner(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 2
  {
    reveal EquivValid();
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in knowns {
    } else {
      if head in ca.PortSource {
        var onp := ca.PortSource[head];
        if onp in path {
        } else {
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
    requires ONPValid(ca, path[|path|-1])
    requires path[|path|-1] !in knowns
    requires forall np :: np in path ==> np.n in e.sc
    requires
      var nk := ca.NodeKind[path[|path|-1].n];
      nk.CXor? || nk.CAnd?
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    ensures PathValid(cb, path)
    ensures EvaluateONPBinary(ca, path, knowns) == EvaluateONPBinary(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal EquivValid();
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
    ensures EvaluateONPUnary(ca, path, knowns) == EvaluateONPUnary(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal EquivValid();
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
    ensures EvaluateONPInner(ca, path, knowns) == EvaluateONPInner(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 4
  {
    reveal EquivValid();
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
    ensures Evaluate(ca, o, known) == Evaluate(cb, o, known)
  {
    reveal EquivValid();
    assert PathValid(ca, [o]);
    LengthOneNoDuplicates([o]);
    if INPValid(ca, o) {
      EvaluateINPInnerConserved(ca, cb, e, [o], known);
    } else {
      EvaluateONPInnerConserved(ca, cb, e, [o], known);
    }
  }

  lemma EquivConserved(ca: Circuit, cb: Circuit, e: Equiv)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires forall np :: np in ScOutputBoundary(ca, e.sc) ==> np in e.outputs
    requires forall np :: np in ScOutputBoundary(cb, e.sc) ==> np in e.outputs
    ensures EquivValid(ca, e) == EquivValid(cb, e)
    ensures EquivValid(ca, e) ==> EquivTrue(ca, e) == EquivTrue(cb, e)
  {
    reveal EquivValid();
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
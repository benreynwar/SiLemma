module Eval {

  import opened Circ

  function EvaluateINPInner(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires |path| > 0
    requires INPValid(c, path[|path|-1])
    requires PathValid(c, path)
    requires Seq.HasNoDuplicates(path)
    decreases |NodesNotInPath(c, path)|, 2
  {
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in tail then
      EvalError({}, {path})
    else if head in knowns then
      EvalOk(knowns[head])
    else
      if head in c.PortSource then
        var onp := c.PortSource[head];
        if onp in path then
          EvalError({}, {path + [onp]})
        else
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          EvaluateONPInner(c, path + [onp], knowns)
      else
        EvalError({head}, {})
  }

  lemma NodesNotInPathDecreases(c: Circuit, p: seq<NP>, np: NP)
    requires PathValid(c, p)
    requires Seq.HasNoDuplicates(p)
    requires np !in p
    requires INPValid(c, np) || ONPValid(c, np)
    ensures
      var new_p := p + [np];
      |NodesNotInPath(c, new_p)| < |NodesNotInPath(c, p)|
  {
    var new_p := p + [np];
    var all_np := AllNP(c);
    var nodes_in_path := Seq.ToSet(p);
    var new_nodes_in_path := Seq.ToSet(new_p);
    reveal Seq.ToSet();
    assert new_nodes_in_path == nodes_in_path + {np};
  }

  function EvaluateONPBinary(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires |path| > 0
    requires ONPValid(c, path[|path|-1])
    requires path[|path|-1] !in knowns
    requires
      var nk := c.NodeKind[path[|path|-1].n];
      nk.CXor? || nk.CAnd?
    requires PathValid(c, path)
    requires Seq.HasNoDuplicates(path)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var nk := c.NodeKind[path[|path|-1].n];
    var head := path[|path|-1];
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path then
      EvalError({}, {path + [inp_0]})
    else if inp_1 in path then
      EvalError({}, {path + [inp_1]})
    else
      NodesNotInPathDecreases(c, path, inp_0);
      NodesNotInPathDecreases(c, path, inp_1);
      var new_path_0 := path + [inp_0];
      var new_path_1 := path + [inp_1];
      assert PathValid(c, new_path_0);
      assert PathValid(c, new_path_1);
      assert |NodesNotInPath(c, path + [inp_0])| < |NodesNotInPath(c, path)|;
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      var iv_0 := EvaluateINPInner(c, path + [inp_0], knowns);
      var iv_1 := EvaluateINPInner(c, path + [inp_1], knowns);
      match iv_0
        case EvalError(missing_0, loops_0) => (
          match iv_1
            case EvalError(missing_1, loops_1) =>
              EvalError(missing_0 + missing_1, loops_0 + loops_1)
            case EvalOk(b1) =>
              EvalError(missing_0, loops_0)
        )
        case EvalOk(b0) => (
          match iv_1
            case EvalError(missing_1, loops_1) =>
              EvalError(missing_1, loops_1)
            case EvalOk(b1) =>
              if nk.CXor? then
                EvalOk(Xor(b0, b1))
              else
                EvalOk(b0 && b1)
        )
  }

  function EvaluateONPUnary(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires |path| > 0
    requires ONPValid(c, path[|path|-1])
    requires path[|path|-1] !in knowns
    requires c.NodeKind[path[|path|-1].n].CInv?
    requires PathValid(c, path)
    requires Seq.HasNoDuplicates(path)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path then
      EvalError({}, {path + [inp_0]})
    else
      var new_path := path + [inp_0];
      assert PathValid(c, new_path);
      NodesNotInPathDecreases(c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      var iv_0 := EvaluateINPInner(c, new_path, knowns);
      match iv_0
        case EvalError(missing_0, loops_0) =>
          EvalError(missing_0, loops_0)
        case EvalOk(b0) =>
          EvalOk(!b0)
  }

  function EvaluateONPInner(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires |path| > 0
    requires ONPValid(c, path[|path|-1])
    requires PathValid(c, path)
    requires Seq.HasNoDuplicates(path)
    decreases |NodesNotInPath(c, path)|, 4
  {
    var head := path[|path|-1];
    if head in knowns then
      EvalOk(knowns[head])
    else
      var nk := c.NodeKind[head.n];
      match nk
        case CXor() => EvaluateONPBinary(c, path, knowns)
        case CAnd() => EvaluateONPBinary(c, path, knowns)
        case CInv() => EvaluateONPUnary(c, path, knowns)
        case CConst(b) => EvalOk(b)
        case CInput() => EvalError({head}, {})
        case CSeq() => EvalError({head}, {})
  }

  lemma LengthOneNoDuplicates<X>(s: seq<X>)
    requires |s| == 1
    ensures Seq.HasNoDuplicates(s)
  {
    reveal Seq.HasNoDuplicates();
  }

  function EvaluateONP(c: Circuit, np: NP, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires ONPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    EvaluateONPInner(c, path, knowns)
  }

  function EvaluateINP(c: Circuit, np: NP, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires INPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    EvaluateINPInner(c, path, knowns)
  }
  
  function Evaluate(c: Circuit, np: NP, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires ONPValid(c, np) || INPValid(c, np)
  {
    if ONPValid(c, np) then
      EvaluateONP(c, np, knowns)
    else
      EvaluateINP(c, np, knowns)
  }

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

  ghost predicate SubcircuitConserved(ca: Circuit, cb: Circuit, sc: Subcircuit)
    requires SubcircuitValid(ca, sc)
    requires SubcircuitValid(cb, sc)
  {
    (forall n :: n in sc.nodes ==> ca.NodeKind[n] == cb.NodeKind[n]) &&
    (forall np: NP :: np.n in sc.nodes ==> ((np in ca.PortSource) == (np in cb.PortSource)) || np in sc.boundary) &&
    (forall np: NP :: np.n in sc.nodes && np in ca.PortSource && np !in sc.boundary ==>
      ca.PortSource[np] == cb.PortSource[np])
  }

  ghost predicate ConservedValid(ca: Circuit, cb: Circuit, sc: Subcircuit, known: map<NP, bool>)
  {
    CircuitValid(ca) && CircuitValid(cb) &&
    SubcircuitValid(ca, sc) && SubcircuitValid(cb, sc) &&
    SubcircuitConserved(ca, cb, sc) &&
    (forall np :: np in sc.boundary ==> np in known) &&
    (forall np :: np in known ==> np.n in sc.nodes)
  }

  lemma EvaluateINPInnerConserved(
    ca: Circuit, cb: Circuit, sc: Subcircuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, sc, knowns)
    requires |path| > 0
    requires forall np :: np in path ==> np.n in sc.nodes
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    requires INPValid(ca, path[|path|-1])
    ensures
      EvaluateINPInner(ca, path, knowns) == EvaluateINPInner(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 2
  {
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in tail {
    } else if head in knowns {
    } else {
      if head in ca.PortSource {
        var onp := ca.PortSource[head];
        if onp in path {
        } else {
          NodesNotInPathDecreases(ca, path, onp);
          StillHasNoDuplicates(path, onp);
          EvaluateONPInnerConserved(ca, cb, sc, path + [onp], knowns);
        }
      } else {
      }
    }
  }

  lemma EvaluateONPBinaryConserved(
      ca: Circuit, cb: Circuit, sc: Subcircuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, sc, knowns)
    requires |path| > 0
    requires ONPValid(ca, path[|path|-1])
    requires path[|path|-1] !in knowns
    requires forall np :: np in path ==> np.n in sc.nodes
    requires
      var nk := ca.NodeKind[path[|path|-1].n];
      nk.CXor? || nk.CAnd?
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    ensures EvaluateONPBinary(ca, path, knowns) == EvaluateONPBinary(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 3
  {
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
      EvaluateINPInnerConserved(ca, cb, sc, path + [inp_0], knowns);
      EvaluateINPInnerConserved(ca, cb, sc, path + [inp_1], knowns);
    }
  }

  lemma EvaluateONPUnaryConserved(
      ca: Circuit, cb: Circuit, sc: Subcircuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, sc, knowns)
    requires |path| > 0
    requires ONPValid(ca, path[|path|-1])
    requires path[|path|-1] !in knowns
    requires ca.NodeKind[path[|path|-1].n].CInv?
    requires PathValid(ca, path)
    requires forall np :: np in path ==> np.n in sc.nodes
    requires Seq.HasNoDuplicates(path)
    ensures EvaluateONPUnary(ca, path, knowns) == EvaluateONPUnary(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 3
  {
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(ca, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      EvaluateINPInnerConserved(ca, cb, sc, path + [inp_0], knowns);
    }
  }


  lemma EvaluateONPInnerConserved(
      ca: Circuit, cb: Circuit, sc: Subcircuit, path: seq<NP>, knowns: map<NP, bool>)
    requires ConservedValid(ca, cb, sc, knowns)
    requires forall np :: np in path ==> np.n in sc.nodes
    requires |path| > 0
    requires ONPValid(ca, path[|path|-1])
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    ensures EvaluateONPInner(ca, path, knowns) == EvaluateONPInner(cb, path, knowns)
    decreases |NodesNotInPath(ca, path)|, 4
  {
    var head := path[|path|-1];
    if head in knowns {
    } else {
      var nk := ca.NodeKind[head.n];
      match nk
        case CXor() => EvaluateONPBinaryConserved(ca, cb, sc, path, knowns);
        case CAnd() => EvaluateONPBinaryConserved(ca, cb, sc, path, knowns);
        case CInv() => EvaluateONPUnaryConserved(ca, cb, sc, path, knowns);
        case CConst(b) => {}//EvalOk(b)
        case CInput() => {}//EvalError({head}, {})
        case CSeq() => {}//EvalError({head}, {})
    }
  }

  lemma EvaluateConserved(ca: Circuit, cb: Circuit, sc: Subcircuit, o: NP, known: map<NP, bool>)
    requires ConservedValid(ca, cb, sc, known)
    requires o.n in sc.nodes
    requires INPValid(ca, o) || ONPValid(ca, o)
    ensures Evaluate(ca, o, known) == Evaluate(cb, o, known)
  {
    assert PathValid(ca, [o]);
    LengthOneNoDuplicates([o]);
    if INPValid(ca, o) {
      EvaluateINPInnerConserved(ca, cb, sc, [o], known);
    } else {
      EvaluateONPInnerConserved(ca, cb, sc, [o], known);
    }
  }

  lemma EquivConserved(ca: Circuit, cb: Circuit, sc: Subcircuit, np: NP, f: map<NP, bool> --> bool)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires SubcircuitValid(ca, sc)
    requires SubcircuitValid(cb, sc)
    requires SubcircuitConserved(ca, cb, sc)
    requires forall knowns: map<NP, bool> :: knowns.Keys == sc.boundary ==> f.requires(knowns)
    requires INPValid(ca, np) || ONPValid(ca, np)
    requires np.n in sc.nodes
    requires Equiv(ca, np, sc.boundary, f)
    ensures Equiv(cb, np, sc.boundary, f)
  {
    forall knowns: map<NP, bool> | knowns.Keys == sc.boundary
      ensures Evaluate(ca, np, knowns) == Evaluate(cb, np, knowns)
    {
      EvaluateConserved(ca, cb, sc, np, knowns);
      assert Evaluate(ca, np, knowns) == Evaluate(cb, np, knowns);
    }
  }

  ghost predicate Equiv(c: Circuit, o: NP, input_nps: set<NP>, f: map<NP, bool> --> bool)
    requires CircuitValid(c)
    requires ONPValid(c, o) || INPValid(c, o)
    requires forall np :: np in input_nps ==> ONPValid(c, np) || INPValid(c, np)
    requires forall knowns: map<NP, bool> :: knowns.Keys == input_nps ==> f.requires(knowns)
  {
    forall knowns: map<NP, bool> :: knowns.Keys == input_nps ==>
      (forall np :: np in input_nps ==> np in knowns) &&
      Evaluate(c, o, knowns) == EvalOk(f(knowns))
  }

  ghost predicate EquivValid(c: Circuit, e: Equiv2)
    requires CircuitValid(c)
  {
    (ONPValid(c, e.output) || INPValid(c, e.output)) &&
    (forall np :: np in e.inputs ==> ONPValid(c, np) || INPValid(c, np)) &&
    (forall knowns: map<NP, bool> :: knowns.Keys == e.inputs ==> e.f.requires(knowns))
  }

  ghost predicate EquivTrue(c: Circuit, e: Equiv2)
    requires CircuitValid(c)
    requires EquivValid(c, e)
  {
    forall knowns: map<NP, bool> :: knowns.Keys == e.inputs ==>
      (forall np :: np in e.inputs ==> np in knowns) &&
      Evaluate(c, e.output, knowns) == EvalOk(e.f(knowns))
  }

  datatype Equiv2 = Equiv2(
    output: NP,
    inputs: set<NP>,
    f: map<NP, bool> --> bool
  )

  //lemma ConnectConservesEquiv(c: Circuit, inp: NP, onp: NP, e: Equiv2)
  //  requires CircuitValid(c)
  //  requires INPValid(c, inp)
  //  requires ONPValid(c, onp)
  //  requires EquivValid(c, e)
  //  requires EquivTrue(c, e)
  //  ensures
  //    var r := Connect(c, inp, onp);
  //    CircuitValid(r) &&
  //    EquivValid(r, e) &&
  //    EquivTrue(r, e)
  //{
  //  // This is true because we know that when we Evaluate we get EvalOK.
  //  // This mean we never tried to move back from a unconnected node.
  //  // So adding a connection can't affect anything.
  //  var new_c := Circuit(
  //    c.NodeKind,
  //    c.PortSource[inp := onp]
  //  );
  //  assert forall np :: np in new_c.PortSource.Keys ==> (np in c.PortSource.Keys) || np == inp;
  //  assert forall np :: np in new_c.PortSource.Keys ==> INPValid(new_c, np);
  //  assert forall np :: np in new_c.PortSource.Values ==> (np in c.PortSource.Values) || np == onp;
  //  assert CircuitValid(new_c);
  //}

}
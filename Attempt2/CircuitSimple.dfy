module CircuitSimple {

  import Std.Collections.Seq

  datatype CNodeKind = 
    | CXor()
    | CAnd()
    | CInv()
      // A contant 0 or 1
    | CConst(value: bool)
      // An input to the circuit.
    | CInput()
      // An output from the circuit.
    | COutput()
      // A register.
    | CSeq()

  newtype CNode = nat
  newtype CPort = nat

  const INPUT_0: CPort := 0
  const INPUT_1: CPort := 2
  const OUTPUT_0: CPort := 1

  datatype NP = NP(n: CNode, p: CPort)

  datatype Circuit = Circuit(
    NodeKind: map<CNode, CNodeKind>,
    PortSource: map<NP, NP>
  )

  predicate CircuitValid(c: Circuit)
  {
    (forall np :: np in c.PortSource.Values ==> ONPValid(c, np)) &&
    (forall np :: np in c.PortSource.Keys ==> INPValid(c, np))
  }

  function GetNewNodeInternal(c: Circuit, m: CNode, remaining_nodes: set<CNode>): (r: CNode)
    ensures r !in c.NodeKind
    requires forall n :: n in c.NodeKind && n >= m ==> n in remaining_nodes
    decreases |remaining_nodes|
  {
    if m in c.NodeKind then
      var new_remaining_nodes := remaining_nodes - {m};
      GetNewNodeInternal(c, m+1, new_remaining_nodes)
    else
      m
  }

  function GetNewNode(c: Circuit): (r: CNode)
    ensures r !in c.NodeKind
  {
    GetNewNodeInternal(c, 0, c.NodeKind.Keys)
  }

  function InsertAndImpl(c: Circuit): (r: (Circuit, (NP, NP), NP, map<NP,bool> --> bool))
    {
    var new_node := GetNewNode(c);
    assert new_node !in c.NodeKind;
    var new_c := Circuit(
      NodeKind := c.NodeKind[new_node := CAnd],
      PortSource := c.PortSource
    );
    var i_0 := NP(new_node, INPUT_0);
    var i_1 := NP(new_node, INPUT_1);
    var o_0 := NP(new_node, OUTPUT_0);
    var f: map<NP, bool> --> bool := x requires i_0 in x && i_1 in x => x[i_0] && x[i_1];
    (new_c, (i_0, i_1), o_0, f)
  }

  lemma InsertAndCorrect(c: Circuit)
    requires CircuitValid(c)
    ensures
      var (new_c, (i_0, i_1), o_0, f) := InsertAndImpl(c);
      Equiv(new_c, o_0, {i_0, i_1}, f)
  {
    var (new_c, (i_0, i_1), o_0, f) := InsertAndImpl(c);
    var path := [o_0];
    LengthOneNoDuplicates(path);
    assert CircuitValid(new_c);
    forall knowns: map<NP, bool> | knowns.Keys == {i_0, i_1}
      ensures
        var iv_0 := knowns[i_0];
        var iv_1 := knowns[i_1];
        EvaluateONP(new_c, o_0, knowns) == EvalOk(iv_0 && iv_1)
    {
      var iv_0 := knowns[i_0];
      var iv_1 := knowns[i_1];
      assert Seq.HasNoDuplicates(path);
      assert EvaluateONP(new_c, o_0, knowns) == EvaluateONPBinary(new_c, [o_0], knowns);
      reveal Seq.HasNoDuplicates();
      assert EvaluateINPInner(new_c, [o_0, i_0], knowns) == EvalOk(iv_0);
      assert EvaluateINPInner(new_c, [o_0, i_1], knowns) == EvalOk(iv_1);
      assert EvaluateONPBinary(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
      assert EvaluateONPInner(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
      assert EvaluateONP(new_c, o_0, knowns) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o_0, knowns) == EvalOk(iv_0 && iv_1);
      assert Evaluate(new_c, o_0, knowns) == EvalOk(f(knowns));
    }
    assert Equiv(new_c, o_0, {i_0, i_1}, f);
  }

  function InsertAnd(c: Circuit): (r: (Circuit, (NP, NP), NP, map<NP,bool> --> bool))
    requires CircuitValid(c)
    ensures
      var (new_c, (i_0, i_1), o_0, f) := r;
      r == InsertAndImpl(c) &&
      Equiv(new_c, o_0, {i_0, i_1}, f)
  {
    InsertAndCorrect(c);
    InsertAndImpl(c)
  }

  predicate NodeValid(c: Circuit, node: CNode)
  {
    node in c.NodeKind
  }

  function AllNPfromNode(c: Circuit, node: CNode): (r: set<NP>)
    requires NodeValid(c, node)
    ensures forall np :: (INPValid(c, np) || ONPValid(c, np)) && np.n == node ==> np in r
  {
    var nk := c.NodeKind[node];
    match nk
      case CXor() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CAnd() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CInv() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
      case CConst(b) => {NP(node, OUTPUT_0)}
      case CInput() => {NP(node, OUTPUT_0)}
      case COutput() => {NP(node, INPUT_0)}
      case CSeq() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
  }

  ghost function AllNPInternal(c: Circuit, nodes: set<CNode>, nps: set<NP>): (r: set<NP>)
    requires forall n :: n in nodes ==> NodeValid(c, n)
    requires forall np :: np in nps ==> INPValid(c, np) || ONPValid(c, np)
    requires forall np :: (INPValid(c, np) || ONPValid(c, np)) && np.n !in nodes ==> np in nps
    ensures forall np :: np in r ==> INPValid(c, np) || ONPValid(c, np)
    ensures forall np :: INPValid(c, np) || ONPValid(c, np) ==> np in r
  {
    if |nodes| == 0 then
      nps
    else
      var node :| node in nodes;
      var new_nodes := nodes - {node};
      AllNPInternal(c, new_nodes, nps + AllNPfromNode(c, node))
  }

  ghost function AllNP(c: Circuit): set<NP>
    ensures forall np :: np in AllNP(c) ==> INPValid(c, np) || ONPValid(c, np)
    ensures forall np :: INPValid(c, np) || ONPValid(c, np) ==> np in AllNP(c)
  {
    var all_nodes := (set n | n in c.NodeKind);
    AllNPInternal(c, all_nodes, {})
  }

  predicate PathValid(c: Circuit, p: seq<NP>)
  {
    forall np :: np in p ==> INPValid(c, np) || ONPValid(c, np)
  }

  ghost function NodesNotInPath(c: Circuit, p: seq<NP>): set<NP>
    requires PathValid(c, p)
  {
    var all_np := AllNP(c);
    var nodes_in_path := Seq.ToSet(p);
    var nodes_not_in_path := all_np - nodes_in_path;
    nodes_not_in_path
  }

  datatype EvalResult =
    | EvalOk(bool)
    | EvalError(missing: set<NP>, loops: set<seq<NP>>)

  predicate OutputPortValid(nk: CNodeKind, p: CPort)
  {
    match nk
      case CXor() => p == OUTPUT_0
      case CAnd() => p == OUTPUT_0
      case CInv() => p == OUTPUT_0
      case CConst(b) => p == OUTPUT_0
      case CInput() => p == OUTPUT_0
      case COutput() => false
      case CSeq() => p == OUTPUT_0
  }

  predicate InputPortValid(nk: CNodeKind, p: CPort)
  {
    match nk
      case CXor() => p == INPUT_0 || p == INPUT_1
      case CAnd() => p == INPUT_0 || p == INPUT_1
      case CInv() => p == INPUT_0
      case CConst(b) => false
      case CInput() => false
      case COutput() => p == INPUT_0
      case CSeq() => p == INPUT_0
  }

  predicate ONPValid(c: Circuit, np: NP)
  {
    np.n in c.NodeKind &&
    var nk := c.NodeKind[np.n];
    OutputPortValid(nk, np.p)
  }

  predicate INPValid(c: Circuit, np: NP)
  {
    np.n in c.NodeKind &&
    var nk := c.NodeKind[np.n];
    InputPortValid(nk, np.p)
  }

  function Xor(a: bool, b: bool): bool
  {
    (a && !b) || (!a && b)
  }

  lemma StillHasNoDuplicates<X>(s: seq<X>, x: X)
    requires Seq.HasNoDuplicates(s)
    requires x !in s
    ensures Seq.HasNoDuplicates(s + [x])
  {
    reveal Seq.HasNoDuplicates();
  }

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

  function Connect(c: Circuit, inp: NP, onp: NP): (r: Circuit)
    requires CircuitValid(c)
    requires INPValid(c, inp)
    requires ONPValid(c, onp)
    ensures CircuitValid(r)
  {
    var new_c := Circuit(
      c.NodeKind,
      c.PortSource[inp := onp]
    );
    assert forall np :: np in new_c.PortSource.Keys ==> (np in c.PortSource.Keys) || np == inp;
    assert forall np :: np in new_c.PortSource.Keys ==> INPValid(new_c, np);
    assert forall np :: np in new_c.PortSource.Values ==> (np in c.PortSource.Values) || np == onp;
    assert CircuitValid(new_c);
    new_c
  }

  function InsertThreeAnd(c: Circuit): (r: (Circuit, (NP, NP, NP), NP))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
  {
    var (c, (ai_0, ai_1), ao_0, a_f) := InsertAnd(c);
    var (c, (bi_0, bi_1), bo_0, b_f) := InsertAnd(c);
    var c := Connect(c, bi_1, ao_0);
    (c, (ai_0, ai_1, bi_0), bo_0)
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

  function Replace(np: NP, f: map<NP, bool> -> bool, g: map<NP, bool> -> bool): (r: map<NP, bool> -> bool)
  {
    x =>
      var np_val := g(x);
      var new_x := x[np := np_val];
      f(new_x)
  }

  lemma ConnectHelper(
      c: Circuit,
      o: NP,
      // Stuff that o depends on.
      o_deps: set<NP>,
      m: NP,
      // Stuff that m depends on.
      m_deps: set<NP>,
      // f maps the o_deps to o
      o_f: map<NP, bool> -> bool,
      // g maps the m_deps to m
      m_f: map<NP, bool> -> bool
      )
    requires CircuitValid(c)
    requires INPValid(c, o) || ONPValid(c, o)
    requires INPValid(c, m) || ONPValid(c, m)
    requires forall np :: np in o_deps ==> INPValid(c, np) || ONPValid(c, np)
    requires forall np :: np in m_deps ==> INPValid(c, np) || ONPValid(c, np)
    requires m in o_deps
    requires o !in m_deps
    requires m !in m_deps
    requires o !in o_deps
    requires Equiv(c, o, o_deps, o_f)
    requires Equiv(c, m, m_deps, m_f)
    ensures
      var new_o_f := Replace(m, o_f, m_f);
      var new_o_deps := o_deps - {m} + m_deps;
      Equiv(c, o, new_o_deps, new_o_f)
  {
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
    (forall np: NP :: np.n in sc.nodes ==> (np in ca.PortSource) == (np in cb.PortSource)) &&
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

  lemma EquivConserved(ca: Circuit, cb: Circuit, sc: Subcircuit, f: map<NP, bool> --> bool)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires SubcircuitValid(ca, sc)
    requires SubcircuitValid(cb, sc)
    requires SubcircuitConserved(ca, cb, sc)
    requires forall knowns: map<NP, bool> :: knowns.Keys == sc.boundary ==> f.requires(knowns)
    requires forall np: NP :: np.n in sc.nodes && (INPValid(ca, np) || ONPValid(ca, np)) ==>
      Equiv(ca, np, sc.boundary, f)
    ensures forall np: NP :: np.n in sc.nodes && (INPValid(ca, np) || ONPValid(ca, np)) ==>
      Equiv(cb, np, sc.boundary, f)
  {
    forall np: NP | np.n in sc.nodes && (INPValid(ca, np) || ONPValid(ca, np))
      ensures Equiv(cb, np, sc.boundary, f);
    {
      forall knowns: map<NP, bool> | knowns.Keys == sc.boundary
        ensures Evaluate(ca, np, knowns) == Evaluate(cb, np, knowns);
      {
        EvaluateConserved(ca, cb, sc, np, knowns);
        assert Evaluate(ca, np, knowns) == Evaluate(cb, np, knowns);
      }
    }
  }

  //lemma InsertAndConversEquiv(c: Circuit, np: NP, input_nps: set<NP>, f: map<NP, bool> --> bool)
  //  requires CircuitValid(c)
  //  requires INPValid(c, np) || ONPValid(c, np)
  //  requires forall np :: np in input_nps ==> INPValid(c, np) || ONPValid(c, np)
  //  requires forall x: map<NP, bool> :: x.Keys == input_nps ==> f.requires(x)
  //  requires Equiv(c, np, input_nps, f)
  //  ensures
  //    var (new_c, (i_0, i_1), o_0, f) := InsertAnd(c);
  //    Equiv(new_c, np, input_nps, f)
  //{
  //  var (new_c, (i_0, i_1), o_0, f) := InsertAnd(c);
  //  forall knowns: map<NP, bool> | knowns.Keys == input_nps
  //    ensures Evaluate(new_c, np, knowns) == Evaluate(new_c, np, knowns);
  //  {
  //    assert Evaluate(new_c, np, knowns) == Evaluate(c, np, knowns);
  //  }
  //  assert Equiv(new_c, np, input_nps, f);
  //}

  //lemma InsertThreeAndCorrect(c: Circuit)
  //  requires CircuitValid(c)
  //  ensures
  //    var (new_c, (i_0, i_1, i_2), o_0) := InsertThreeAnd(c);
  //    var f: map<NP, bool> --> bool :=
  //      knowns requires (i_0 in knowns) && (i_1 in knowns) && (i_2 in knowns) =>
  //      knowns[i_0] && knowns[i_1] && knowns[i_2];
  //{
  //  var (new_c, (i_0, i_1, i_2), o_0) := InsertThreeAnd(c);
  //  var (c_1, (ai_0, ai_1), ao_0, a_f) := InsertAnd(c);
  //  var (c_2, (bi_0, bi_1), bo_0, b_f) := InsertAnd(c_1);
  //  assert Equiv(c_2, ao_0, {ai_0, ai_1}, a_f);
  //  assert Equiv(c_2, bo_0, {bi_0, bi_1}, b_f);
  //  var c_3 := Connect(c_2, bi_1, ao_0);
  //  assert (new_c, (i_0, i_1, i_2), o_0) == (c_3, (ai_0, ai_1, bi_0), bo_0);

  //  ////var path := [o_0];

  //  ////LengthOneNoDuplicates(path);
  //  ////assert CircuitValid(new_c);
  //  //forall iv_0: bool, iv_1: bool, iv_2: bool
  //  //  ensures EvaluateONP(new_c, o_0, map[i_0 := iv_0, i_1 := iv_1, i_2 := iv_2])
  //  //    == EvalOk(iv_0 && iv_1 && iv_2)
  //  //{
  //  //  var knowns := map[i_0 := iv_0, i_1 := iv_1, i_2 := iv_2];
  //  //  assert Seq.HasNoDuplicates(path);
  //  //  assert EvaluateONP(new_c, o_0, knowns) == EvaluateONPAnd(new_c, [o_0], knowns);
  //  //  reveal Seq.HasNoDuplicates();
  //  //  assert EvaluateINPInner(new_c, [o_0, i_0], knowns) == EvalOk(iv_0);
  //  //  assert EvaluateINPInner(new_c, [o_0, i_1], knowns) == EvalOk(iv_1);
  //  //  assert EvaluateINPInner(new_c, [o_0, i_2], knowns) == EvalOk(iv_2);
  //  //  assert EvaluateONPAnd(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
  //  //  assert EvaluateONPInner(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
  //  //}
  //}

}
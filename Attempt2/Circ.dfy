module Circ {

  import Std.Collections.Seq

  datatype CNodeKind = 
    | CXor()
    | CAnd()
    | CInv()
      // A contant 0 or 1
    | CConst(value: bool)
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

  opaque predicate CircuitValid(c: Circuit)
  {
    && (forall np :: np in c.PortSource.Values ==> ONPValid(c, np))
    && (forall np :: np in c.PortSource.Keys ==> INPValid(c, np))
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

  predicate NodeValid(c: Circuit, node: CNode)
  {
    node in c.NodeKind
  }

  function AllNPfromNode(c: Circuit, node: CNode): (r: set<NP>)
    requires NodeValid(c, node)
    ensures forall np :: NPValid(c, np) && np.n == node ==> np in r
  {
    var nk := c.NodeKind[node];
    match nk
      case CXor() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CAnd() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CInv() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
      case CConst(b) => {NP(node, OUTPUT_0)}
      case CSeq() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
  }

  function AllNPFromNodes(c: Circuit, nodes: set<CNode>): (r: set<NP>)
    requires forall n :: n in nodes ==> NodeValid(c, n)
    ensures forall np :: np in r ==> NPValid(c, np) && np.n in nodes
    ensures forall np :: NPValid(c, np) && (np.n in nodes) ==> np in r
  {
    if |nodes| == 0 then
      {}
    else
      var node :| node in nodes;
      var new_nodes := nodes - {node};
      AllNPfromNode(c, node) + AllNPFromNodes(c, new_nodes)
  }

  function AllNPInternal(c: Circuit, nodes: set<CNode>, nps: set<NP>): (r: set<NP>)
    requires forall n :: n in nodes ==> NodeValid(c, n)
    requires forall np :: np in nps ==> NPValid(c, np)
    requires forall np :: NPValid(c, np) && np.n !in nodes ==> np in nps
    ensures forall np :: np in r <==> NPValid(c, np)
  {
    if |nodes| == 0 then
      nps
    else
      var node :| node in nodes;
      var new_nodes := nodes - {node};
      AllNPInternal(c, new_nodes, nps + AllNPfromNode(c, node))
  }

  function AllNP(c: Circuit): set<NP>
    ensures forall np :: np in AllNP(c) <==> NPValid(c, np)
  {
    var all_nodes := (set n | n in c.NodeKind);
    AllNPInternal(c, all_nodes, {})
  }

  function AllNodes(c: Circuit): set<CNode>
  {
    c.NodeKind.Keys
  }

  opaque predicate PathValid(c: Circuit, p: seq<NP>)
  {
    forall np :: np in p ==> NPValid(c, np)
  }

  lemma AppendPathValid(c: Circuit, p: seq<NP>, np: NP)
    requires PathValid(c, p)
    requires NPValid(c, np)
    ensures PathValid(c, p + [np])
  {
    reveal PathValid();
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

  datatype SimpleEvalResult =
    | SimpleEvalOk(bool)
    | SimpleEvalError

  function Simpl(er: EvalResult): (r: SimpleEvalResult)
  {
    match er
    case EvalOk(b) => SimpleEvalOk(b)
    case EvalError(missings, loops) => SimpleEvalError
  }

  predicate OutputPortValid(nk: CNodeKind, p: CPort)
  {
    match nk
      case CXor() => p == OUTPUT_0
      case CAnd() => p == OUTPUT_0
      case CInv() => p == OUTPUT_0
      case CConst(b) => p == OUTPUT_0
      case CSeq() => p == OUTPUT_0
  }

  predicate InputPortValid(nk: CNodeKind, p: CPort)
  {
    match nk
      case CXor() => p == INPUT_0 || p == INPUT_1
      case CAnd() => p == INPUT_0 || p == INPUT_1
      case CInv() => p == INPUT_0
      case CConst(b) => false
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

  lemma NotBothINPValidONPValid(c: Circuit, np: NP)
    ensures !(INPValid(c, np) && ONPValid(c, np))
  {
  }

  predicate NPValid(c: Circuit, np: NP)
  {
    INPValid(c, np) || ONPValid(c, np)
  }

  function Connect(c: Circuit, inp: NP, onp: NP): (r: Circuit)
    requires CircuitValid(c)
    requires inp !in c.PortSource
    requires INPValid(c, inp)
    requires ONPValid(c, onp)
    ensures CircuitValid(r)
  {
    reveal CircuitValid();
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

  function Replace(np: NP, f: map<NP, bool> -> bool, g: map<NP, bool> -> bool): (r: map<NP, bool> -> bool)
  {
    x =>
      var np_val := g(x);
      var new_x := x[np := np_val];
      f(new_x)
  }

  predicate SourceNotInSubcircuit(c: Circuit, sc: set<CNode>, np: NP)
    requires INPValid(c, np)
  {
    np !in c.PortSource || c.PortSource[np].n !in sc
  }

  predicate SourceInSubcircuit(c: Circuit, sc: set<CNode>, np: NP)
    requires INPValid(c, np)
  {
    np !in c.PortSource || c.PortSource[np].n in sc
  }

  function SubcircuitComplement(c: Circuit, sc: set<CNode>): (r: set<CNode>)
    ensures ScValid(c, r)
  {
    var all_nodes := AllNodes(c);
    reveal ScValid();
    all_nodes - sc
  }

  function NPBetweenSubcircuits(c: Circuit, sc1: set<CNode>, sc2: set<CNode>): set<NP>
    requires ScValid(c, sc1)
    requires ScValid(c, sc2)
  {
    (set np: NP | np.n in sc1 && np in c.PortSource && c.PortSource[np].n in sc2 :: np)
  }

  function NPBetweenSubcircuitsComplement(c: Circuit, sc1: set<CNode>, sc2: set<CNode>): set<NP>
    requires ScValid(c, sc1)
    requires ScValid(c, sc2)
  {
    (set np: NP | np.n in sc1 && np in c.PortSource && c.PortSource[np].n !in sc2 :: np)
  }

  function UnconnectedINPs(c: Circuit, sc: set<CNode>): set<NP>
    requires ScValid(c, sc)
  {
    reveal ScValid();
    var nps := AllNPFromNodes(c, sc);
    (set np | np in nps && INPValid(c, np) && np !in c.PortSource)
  }

  function InternalInputs(c: Circuit, sc: set<CNode>): set<NP>
    requires ScValid(c, sc)
  {
    reveal ScValid();
    var nps := AllNPFromNodes(c, sc);
    (set np | np in nps && ONPValid(c, np) &&
      var nk := c.NodeKind[np.n];
      nk.CSeq? :: np)
  }

  opaque predicate ScValid(c: Circuit, sc: set<CNode>)
  {
    forall n :: n in sc ==> NodeValid(c, n)
  }

  function ScInputBoundary(c: Circuit, sc: set<CNode>): set<NP>
    requires ScValid(c, sc)
  {
    NPBetweenSubcircuitsComplement(c, sc, sc) + UnconnectedINPs(c, sc) + InternalInputs(c, sc)
  }

  lemma AllINPsConnectedInternallyOrInBoundary(c: Circuit, sc: set<CNode>)
    requires CircuitValid(c)
    requires ScValid(c, sc)
    ensures
      reveal ScValid();
      var nps := AllNPFromNodes(c, sc);
      var all_inps := (set np | np in nps && INPValid(c, np) :: np);
      forall np :: np in all_inps ==> ((np in c.PortSource) && (c.PortSource[np].n in sc)) || (np in ScInputBoundary(c, sc))
  {
  }

  function ScOutputBoundary(c: Circuit, sc: set<CNode>): set<NP>
  {
    (set np: NP | (np.n !in sc) && np in c.PortSource && c.PortSource[np].n in sc :: c.PortSource[np])
  }

}
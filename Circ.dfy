module Circ {

  import Std.Collections.Seq

  datatype CNodeKind = 
    | CXor()
    | CAnd()
    | COr()
    | CInv()
    | CIden()
      // A contant 0 or 1
    | CConst(value: bool)
      // A register.
    | CSeq()

  predicate CNodeKindIsBinary(nk: CNodeKind)
  {
    nk.CXor? || nk.CAnd? || nk.COr?
  }

  predicate CNodeKindIsUnary(nk: CNodeKind)
  {
    nk.CInv? || nk.CIden?
  }

  newtype CNode = nat
  newtype CPort = nat

  const INPUT_0: CPort := 0
  const INPUT_1: CPort := 2
  const OUTPUT_0: CPort := 1

  // An `NP` is a given port on a node.
  datatype NP = NP(n: CNode, p: CPort)

  datatype Circuit = Circuit(
    NodeKind: map<CNode, CNodeKind>,
    PortSource: map<NP, NP>
  ) {
    opaque predicate Valid()
    {
      && (forall np :: np in PortSource.Values ==> ONPValid(this, np))
      && (forall np :: np in PortSource.Keys ==> INPValid(this, np))
    }
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
    // Gets a new unused `Node` identifier.
    // Used when adding nodes to the graph.
    ensures r !in c.NodeKind
  {
    GetNewNodeInternal(c, 0, c.NodeKind.Keys)
  }

  predicate NodeValid(c: Circuit, node: CNode)
  {
    node in c.NodeKind
  }

  function AllNPfromNode(c: Circuit, node: CNode): (r: set<NP>)
    // All the `NP`s on a node.
    requires NodeValid(c, node)
    ensures forall np :: NPValid(c, np) && np.n == node ==> np in r
  {
    var nk := c.NodeKind[node];
    match nk
      case CXor() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CAnd() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case COr() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CInv() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
      case CIden() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
      case CConst(b) => {NP(node, OUTPUT_0)}
      case CSeq() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
  }

  function AllNPFromNodes(c: Circuit, nodes: set<CNode>): (r: set<NP>)
    // All the `NP`s on a set of nodes.
    requires ScValid(c, nodes)
    ensures forall np :: np in r ==> NPValid(c, np) && np.n in nodes
    ensures forall np :: NPValid(c, np) && (np.n in nodes) ==> np in r
  {
    reveal ScValid();
    if |nodes| == 0 then
      {}
    else
      var node :| node in nodes;
      var new_nodes := nodes - {node};
      AllNPfromNode(c, node) + AllNPFromNodes(c, new_nodes)
  }

  lemma AllNPFromNodesAdds(c: Circuit, sc1: set<CNode>, sc2: set<CNode>)
    requires ScValid(c, sc1)
    requires ScValid(c, sc2)
    ensures
      reveal ScValid();
      AllNPFromNodes(c, sc1 + sc2) == AllNPFromNodes(c, sc1) + AllNPFromNodes(c, sc2)
    decreases |sc2|
  {
    reveal ScValid();
    if |sc2| == 0 {
    } else {
      var node :| node in sc2;
      var new_sc2 := sc2 - {node};
      var new_sc1 := sc1 + {node};
      calc {
        AllNPFromNodes(c, sc1 + sc2);
        AllNPFromNodes(c, new_sc1 + new_sc2);
        {AllNPFromNodesAdds(c, new_sc1, new_sc2);}
        AllNPFromNodes(c, new_sc1) + AllNPFromNodes(c, new_sc2);
        {
          assert AllNPFromNodes(c, sc2) == AllNPFromNodes(c, new_sc2) + AllNPfromNode(c, node);
          assert AllNPFromNodes(c, new_sc1) == AllNPFromNodes(c, sc1) + AllNPfromNode(c, node);
        }
        (AllNPFromNodes(c, sc1) - AllNPfromNode(c, node)) +
        (AllNPFromNodes(c, sc2) + AllNPfromNode(c, node));
        AllNPFromNodes(c, sc1) + AllNPFromNodes(c, sc2);
      }
    }
  }


  lemma AllNPFromNodesDependsNodeKind(ca: Circuit, cb: Circuit, nodes: set<CNode>)
    requires ca.NodeKind == cb.NodeKind
    requires ScValid(ca, nodes)
    ensures ScValid(cb, nodes)
    ensures AllNPFromNodes(ca, nodes) == AllNPFromNodes(cb, nodes)
  {
    assert ScValid(cb, nodes) by {
      reveal ScValid();
    }
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
    // Returns all the `NP` in a circuit.
    ensures forall np :: np in AllNP(c) <==> NPValid(c, np)
  {
    var all_nodes := (set n | n in c.NodeKind);
    AllNPInternal(c, all_nodes, {})
  }

  function AllNodes(c: Circuit): set<CNode>
    // Returns all the `Node` in a circuit.
  {
    c.NodeKind.Keys
  }

  predicate NPsConnected(c: Circuit, np0: NP, np1: NP)
    requires c.Valid()
    requires NPValid(c, np0)
    requires NPValid(c, np1)
  {
    if INPValid(c, np0) then
      np0 in c.PortSource && c.PortSource[np0] == np1
    else
      ONPValid(c, np0) && INPValid(c, np1) && (np0.n == np1.n)
  }

  opaque predicate PathValid(c: Circuit, p: seq<NP>)
    requires c.Valid()
    // Whether a path is valid.
    // Here this is purely determined by whether the `NP` are valid.
    // It doesn't consider connectivity at all.
  {
    && (forall index: nat :: index < |p| ==> NPValid(c, p[index]))
    && (forall index: nat :: index < |p|-1 ==> NPsConnected(c, p[index], p[index+1]))
  }

  predicate PathNonZeroValid(c: Circuit, p: seq<NP>)
    requires c.Valid()
  {
    && |p| > 0
    && PathValid(c, p)
  }

  lemma AppendPathValid(c: Circuit, p: seq<NP>, np: NP)
    requires c.Valid()
    requires PathValid(c, p)
    requires NPValid(c, np)
    requires
      reveal PathValid();
      |p| > 0 ==> NPsConnected(c, Seq.Last(p), np)
    ensures PathValid(c, p + [np])
  {
    reveal PathValid();
  }

  ghost function NodesNotInPath(c: Circuit, p: seq<NP>): set<NP>
    // All the nodes in a circuit that are not in the path.
    // When we're tracing paths in the circuit, this can help us prove termination
    // since the size of this will decrease as the path gets longer.
    requires c.Valid()
    requires PathValid(c, p)
  {
    var all_np := AllNP(c);
    var nodes_in_path := Seq.ToSet(p);
    var nodes_not_in_path := all_np - nodes_in_path;
    nodes_not_in_path
  }

  datatype EvalResult =
    // When evaluating the circuit this is the return type.
    // An error is returned if we encounter a loop or if we encounter an input that
    // is missing.
    | EvalOk(bool)
    | EvalError(missing: set<NP>, loops: set<seq<NP>>)

  datatype SimpleEvalResult =
    // Sometimes it's easier to prove this if we don't return detailed error information.
    // i.e. Makes some things equivalent that wouldn't be otherwise.
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
      case COr() => p == OUTPUT_0
      case CInv() => p == OUTPUT_0
      case CIden() => p == OUTPUT_0
      case CConst(b) => p == OUTPUT_0
      case CSeq() => p == OUTPUT_0
  }

  predicate InputPortValid(nk: CNodeKind, p: CPort)
  {
    match nk
      case CXor() => p == INPUT_0 || p == INPUT_1
      case CAnd() => p == INPUT_0 || p == INPUT_1
      case COr() => p == INPUT_0 || p == INPUT_1
      case CInv() => p == INPUT_0
      case CIden() => p == INPUT_0
      case CConst(b) => false
      case CSeq() => p == INPUT_0
  }

  predicate ONPValid(c: Circuit, np: NP)
    // Whether an `NP` is a valid output port on a node.
  {
    np.n in c.NodeKind &&
    var nk := c.NodeKind[np.n];
    OutputPortValid(nk, np.p)
  }

  predicate INPValid(c: Circuit, np: NP)
    // Whether an `NP` is a valid input port on a node.
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

  //function Connect(c: Circuit, inp: NP, onp: NP): (r: Circuit)
  //  requires c.Valid()
  //  requires inp !in c.PortSource
  //  requires INPValid(c, inp)
  //  requires ONPValid(c, onp)
  //  ensures r.Valid()
  //{
  //  reveal Circuit.Valid();
  //  var new_c := Circuit(
  //    c.NodeKind,
  //    c.PortSource[inp := onp]
  //  );
  //  assert forall np :: np in new_c.PortSource.Keys ==> (np in c.PortSource.Keys) || np == inp;
  //  assert forall np :: np in new_c.PortSource.Keys ==> INPValid(new_c, np);
  //  assert forall np :: np in new_c.PortSource.Values ==> (np in c.PortSource.Values) || np == onp;
  //  assert new_c.Valid();
  //  new_c
  //}

  //function Replace(np: NP, f: map<NP, bool> -> bool, g: map<NP, bool> -> bool): (r: map<NP, bool> -> bool)
  //{
  //  x =>
  //    var np_val := g(x);
  //    var new_x := x[np := np_val];
  //    f(new_x)
  //}

  //predicate SourceNotInSubcircuit(c: Circuit, sc: set<CNode>, np: NP)
  //  requires INPValid(c, np)
  //{
  //  np !in c.PortSource || c.PortSource[np].n !in sc
  //}

  //predicate SourceInSubcircuit(c: Circuit, sc: set<CNode>, np: NP)
  //  requires INPValid(c, np)
  //{
  //  np !in c.PortSource || c.PortSource[np].n in sc
  //}

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
    requires c.Valid()
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
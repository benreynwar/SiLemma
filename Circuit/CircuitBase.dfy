module CircuitBase {

    import opened Std.Wrappers
    import Std.Collections.Seq

    newtype CPort = nat
    const INPUT_PORT: CPort := 0
    const OUTPUT_PORT: CPort := 1

    // A node in the graph.
    newtype CNode = nat

    datatype NP = NP(n: CNode, p: CPort)

    // HPINP and HPONP can reference a port nested in the hierarchy.
    // This is useful as an intermediate when converting to a HGraph.

    datatype HPNP = HPNP(hpn: HPNode, p: CPort)

    // Represents the path taken through a hierarchy of nodes where a node can
    // represent a lower-level circuit.
    datatype HierarchyPath = HP(v: seq<CNode>)

    datatype HPNode =
        HPNode(
            hp: HierarchyPath,
            n: CNode
        )

    datatype Circuit = Circuit(
        NodeKind: CNode -> Option<CNodeKind>,
        PortSource: NP -> Option<NP>,
        // This is larger or equal to all nodes for which NodeKind(node) is Some
        // We use this help dafny prove that things are finite and terminate.
        NodeBound: CNode,
        PortBound: CPort,
        HierLevel: nat,
        PortNames: string -> Option<CNode>
    )

    datatype CNodeKind = 
        // A hierarchical node so we can design hierarchically.
      | CHier(c: Circuit)
        // A node representing combinatorial logic.
      | CComb(
          IPorts: seq<CPort>,
          OPorts: seq<CPort>,
          PathExists: (CPort, CPort) -> bool,
          Behav: map<CPort, bool> -> Option<map<CPort, bool>>,
          PortNames: string -> Option<CPort>
        )
        // A contant 0 or 1
      | CConst(value: bool)
        // An input to the circuit.
      | CInput()
        // An output from the circuit.
      | COutput()
        // A register.
      | CSeq()

    function IPorts(nk: CNodeKind): set<CPort>
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(subc) =>
            set n | n < subc.NodeBound && subc.NodeKind(n) == Some(CInput) :: n as CPort
        case CComb(iports, oports, path_exists, behav, names) => Seq.ToSet(iports)
        case CInput() => {}
        case CConst(v) => {}
        case COutput() => {0 as CPort}
        case CSeq() => {0 as CPort}
    }

    predicate IsIPort(nk: CNodeKind, p: CPort)
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(subc) => subc.NodeKind(p as CNode) == Some(CInput)
        case CComb(iports, oports, path_exists, behav, name) => p in iports
        case CInput() => false
        case CConst(v) => false
        case COutput() => p == INPUT_PORT as CPort
        case CSeq() => p == INPUT_PORT as CPort
    }

    function OPorts(nk: CNodeKind): set<CPort>
    {
        match nk
        case CHier(subc) =>
            set n | n < subc.NodeBound && subc.NodeKind(n) == Some(COutput) :: n as CPort
        case CComb(iports, oports, path_exists, behav, names) => Seq.ToSet(oports)
        case CInput() => {0 as CPort}
        case COutput() => {}
        case CConst(v) => {0 as CPort}
        case CSeq() => {0 as CPort}
    }

    predicate IsOPort(nk: CNodeKind, p: CPort)
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(subc) =>
            subc.NodeKind(p as CNode) == Some(COutput)
        case CComb(iports, oports, path_exists, behav, names) => p in oports
        case CInput() => p == OUTPUT_PORT as CPort
        case CConst(v) => p == OUTPUT_PORT as CPort
        case COutput() => false
        case CSeq() => p == OUTPUT_PORT as CPort
    }

    ghost predicate CNodeKindSomewhatValid(nk: CNodeKind)
    {
        (
        match nk
        case CComb(iports, oports, path_exists, behav, names) =>
          (forall a: CPort, b: CPort ::
              (a !in oports ==> !nk.PathExists(a, b)) &&
              (b !in iports ==> !nk.PathExists(a, b)))
        case _ => true
        ) && (
            forall p: CPort ::
                !(IsIPort(nk, p) && IsOPort(nk, p))
        )
    }

    ghost predicate CNodeKindValid(
        hier_level: nat, port_bound: CPort, nk: CNodeKind)
        decreases hier_level, 0
    {
        CNodeKindSomewhatValid(nk) &&
        (
        match nk
        case CHier(subc) =>
            (subc.HierLevel < hier_level) &&
            CircuitValid(subc)
        case _ => true
        ) && (
            forall p: CPort ::
                (IsIPort(nk, p) ==> p < port_bound) &&
                (IsOPort(nk, p) ==> p < port_bound)
        )
    }

    ghost predicate {:opaque} CircuitValid(c: Circuit)
        decreases  c.HierLevel, 2
    {
        CircuitNodeKindValid(c) &&
        CircuitPortSourceValid(c)
    }

    ghost predicate CircuitNodeKindValid(c: Circuit)
        decreases  c.HierLevel, 1
    {
        (
            forall n: CNode ::
                var maybe_nk := c.NodeKind(n);
                if maybe_nk.None? then
                    true
                else
                    CNodeKindValid(c.HierLevel, c.PortBound, maybe_nk.Extract())
        ) && (
            forall n: CNode :: n >= c.NodeBound ==> c.NodeKind(n) == None
        )
    }

    ghost predicate CircuitPortSourceValid(c: Circuit)
    {
        // For all possible ports.
        // If the port is not a valid output port then PortSource should give None.0
        // If the port is a valid output port then it should lead to a valid input
        // port.
        forall n: CNode ::
            forall p: CPort ::
                var inp := NP(n, p);
                if NPValidInput(c, inp) then
                    match c.PortSource(inp)
                    // It's ok if it doesn't connect to anything.
                    // We consider that a valid circuit, but not a complete circuit.
                    // That way we can build a circuit but it is still valid.
                    case None => true
                    case Some(onp) => NPValidOutput(c, onp)
                else
                    c.PortSource(inp) == None
    }

    ghost predicate NPValid(c: Circuit, np: NP)
    {
        NPValidInput(c, np) || NPValidOutput(c, np)
    }

    ghost predicate NPValidInput(c: Circuit, np: NP)
    {
        match c.NodeKind(np.n)
        // The node doesn't exist.
        case None => false
        case Some(nk) => IsIPort(nk, np.p)
    }

    ghost predicate NPValidOutput(c: Circuit, np: NP)
    {
        match c.NodeKind(np.n)
        case None => false
        case Some(nk) => IsOPort(nk, np.p)
    }
}
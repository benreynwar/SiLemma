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
        NodeKind: map<CNode, CNodeKind>,//CNode -> Option<CNodeKind>,
        PortSource: map<NP, NP>,
        // This is larger or equal to all nodes for which NodeKind(node) is Some
        // We use this help dafny prove that things are finite and terminate.
        //NodeBound: CNode,
        //PortBound: CPort,
        HierLevel: nat,
        PortNames: map<string, CNode>
    )

    function NodeKind(c: Circuit, n: CNode): Option<CNodeKind>
    {
        if n in c.NodeKind then
            Some(c.NodeKind[n])
        else
            None
    }

    function PortSource(c: Circuit, np: NP): Option<NP>
    {
        if np in c.PortSource then
            Some(c.PortSource[np])
        else
            None
    }

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
            set n | n in subc.NodeKind && subc.NodeKind[n] == CInput :: n as CPort
        case CComb(iports, oports, path_exists, behav, names) => Seq.ToSet(iports)
        case CInput() => {}
        case CConst(v) => {}
        case COutput() => {INPUT_PORT as CPort}
        case CSeq() => {INPUT_PORT as CPort}
    }

    predicate IsPort(nk: CNodeKind, p: CPort)
    {
        IsIPort(nk, p) || IsOPort(nk, p)
    }

    lemma InIPortsIsIPort(nk: CNodeKind, p: CPort)
        requires IsIPort(nk, p)
        ensures p in IPorts(nk)
    {
        reveal Seq.ToSet();
    }
    lemma InOPortsIsOPort(nk: CNodeKind, p: CPort)
        requires IsOPort(nk, p)
        ensures p in OPorts(nk)
    {
        reveal Seq.ToSet();
        match nk
        case CHier(subc) => {}
        case CComb(iports, oports, path_exists, behav, name) => {}
        case CInput() => {}
        case CConst(v) => {}
        case COutput() => {}
        case CSeq() => {}
    }

    predicate IsIPort(nk: CNodeKind, p: CPort)
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(subc) => NodeKind(subc, p as CNode) == Some(CInput)
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
            set n | n in subc.NodeKind && subc.NodeKind[n] == COutput :: n as CPort
        case CComb(iports, oports, path_exists, behav, names) => Seq.ToSet(oports)
        case CInput() => {OUTPUT_PORT as CPort}
        case COutput() => {}
        case CConst(v) => {OUTPUT_PORT as CPort}
        case CSeq() => {OUTPUT_PORT as CPort}
    }

    predicate IsOPort(nk: CNodeKind, p: CPort)
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(subc) =>
            NodeKind(subc, p as CNode) == Some(COutput)
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

    lemma CNodeKindNoSelfPaths(nk: CNodeKind)
        requires CNodeKindSomewhatValid(nk)
        requires nk.CComb?
        ensures forall p: CPort :: !nk.PathExists(p, p)
    {
        forall p: CPort
            ensures !nk.PathExists(p, p)
        {
            assert !(IsIPort(nk, p) && IsOPort(nk, p));
        }
    }

    ghost predicate CNodeKindValid(
        hier_level: nat, nk: CNodeKind)
        decreases hier_level, 0
    {
        CNodeKindSomewhatValid(nk) &&
        (
        match nk
        case CHier(subc) =>
            (subc.HierLevel < hier_level) &&
            CircuitValid(subc)
        case _ => true
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
        forall n: CNode ::
            var maybe_nk := NodeKind(c, n);
            if maybe_nk.None? then
                true
            else
                CNodeKindValid(c.HierLevel, maybe_nk.Extract())
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
                    match PortSource(c, inp)
                    // It's ok if it doesn't connect to anything.
                    // We consider that a valid circuit, but not a complete circuit.
                    // That way we can build a circuit but it is still valid.
                    case None => true
                    case Some(onp) => NPValidOutput(c, onp)
                else
                    PortSource(c, inp) == None
    }

    ghost predicate NPValid(c: Circuit, np: NP)
    {
        NPValidInput(c, np) || NPValidOutput(c, np)
    }

    ghost predicate NPValidInput(c: Circuit, np: NP)
    {
        match NodeKind(c, np.n)
        // The node doesn't exist.
        case None => false
        case Some(nk) => IsIPort(nk, np.p)
    }

    ghost predicate NPValidOutput(c: Circuit, np: NP)
    {
        match NodeKind(c, np.n)
        case None => false
        case Some(nk) => IsOPort(nk, np.p)
    }

    predicate CNodeIsCHier(c: Circuit, n: CNode)
    {
        NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
    }

    predicate CNodeIsCInput(c: Circuit, n: CNode)
    {
        NodeKind(c, n).Some? && NodeKind(c, n).value.CInput?
    }

    predicate CNodeIsCOutput(c: Circuit, n: CNode)
    {
        NodeKind(c, n).Some? && NodeKind(c, n).value.COutput?
    }

}
module CircuitBase {

    import Utils
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
        PortMap: PortMapping
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
          PathExists: set<(CPort, CPort)>,
          Behav: map<CPort, bool> -> Option<map<CPort, bool>>,
          PortMap: PortMapping
        )
        // A contant 0 or 1
      | CConst(value: bool)
        // An input to the circuit.
      | CInput()
        // An output from the circuit.
      | COutput()
        // A register.
      | CSeq()

    function PortMap(nk: CNodeKind): PortMapping
    {
        match nk
        case CHier(_) => nk.c.PortMap
        case CComb(_, _, _) => nk.PortMap
        case CConst(_) => PortMapping([], [], ["o"], [OUTPUT_PORT])
        case CInput() => PortMapping([], [], ["o"], [OUTPUT_PORT])
        case COutput() => PortMapping(["i"], [INPUT_PORT], [], [])
        case CSeq() => PortMapping(["i"], [INPUT_PORT], ["o"], [OUTPUT_PORT])
    }

    function PortNameToPort(nk: CNodeKind, name: string): CPort
        requires CNodeKindSomewhatValid(nk)
        requires
            var pm := PortMap(nk);
            name in pm.inames || name in pm.onames
    {
        var pm := PortMap(nk);
        assert PortMappingValid(pm);
        if name in pm.inames then
            INameToPort(pm, name)
        else
            assert name in pm.onames;
            ONameToPort(pm, name)
    }

    function IPorts(nk: CNodeKind): set<CPort>
    {
        var pm := PortMap(nk);
        Seq.ToSet(pm.iports)
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
    }

    predicate IsIPort(nk: CNodeKind, p: CPort)
    {
        var pm := PortMap(nk);
        p in pm.iports

        //match nk
        //// The port numbers of a hierarical block and just the node ids of
        //// the input and output nodes.
        //case CHier(subc) => NodeKind(subc, p as CNode) == Some(CInput)
        //case CComb(path_exists, behav, pm) => p in pm.iports
        //case CInput() => false
        //case CConst(v) => false
        //case COutput() => p == INPUT_PORT as CPort
        //case CSeq() => p == INPUT_PORT as CPort
    }

    function OPorts(nk: CNodeKind): set<CPort>
    {
        var pm := PortMap(nk);
        Seq.ToSet(pm.oports)

        //match nk
        //case CHier(subc) =>
        //    set n | n in subc.NodeKind && subc.NodeKind[n] == COutput :: n as CPort
        //case CComb(path_exists, behav, pm) => Seq.ToSet(pm.oports)
        //case CInput() => {OUTPUT_PORT as CPort}
        //case COutput() => {}
        //case CConst(v) => {OUTPUT_PORT as CPort}
        //case CSeq() => {OUTPUT_PORT as CPort}
    }

    predicate IsOPort(nk: CNodeKind, p: CPort)
    {
        var pm := PortMap(nk);
        p in pm.oports
        //match nk
        //// The port numbers of a hierarical block and just the node ids of
        //// the input and output nodes.
        //case CHier(subc) =>
        //    NodeKind(subc, p as CNode) == Some(COutput)
        //case CComb(path_exists, behav, pm) => p in pm.oports
        //case CInput() => p == OUTPUT_PORT as CPort
        //case CConst(v) => p == OUTPUT_PORT as CPort
        //case COutput() => false
        //case CSeq() => p == OUTPUT_PORT as CPort
    }

    predicate CNodeKindSomewhatValid(nk: CNodeKind)
    {
        (
        match nk
        case CComb(path_exists, behav, pm) =>
            forall pair | pair in nk.PathExists :: pair.0 in pm.oports && pair.1 in pm.iports
        case _ => true
        ) &&
        PortMappingValid(PortMap(nk))
    }

    lemma CNodeKindNoSelfPaths(nk: CNodeKind)
        requires CNodeKindSomewhatValid(nk)
        requires nk.CComb?
        ensures forall p: CPort :: (p, p) !in nk.PathExists
    {
        forall a: CPort, b: CPort | (a, b) in nk.PathExists
            ensures a != b
        {
            var pm := PortMap(nk);
            assert PortMappingValid(nk.PortMap);
            assert a in pm.oports;
            assert b in pm.iports;
            assert a !in pm.iports;
            assert a != b;
        }
    }

    predicate CNodeKindValid(
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

    predicate {:opaque} CircuitValid(c: Circuit)
        decreases  c.HierLevel, 2
    {
        CircuitNodeKindValid(c) &&
        CircuitPortSourceValid(c) &&
        CircuitPortNamesValid(c)
    }

    predicate {:opaque} CircuitPortNamesValid(c: Circuit)
    {
        (forall s :: s in c.PortMap.iports ==> s as CNode in AllCInputs(c)) &&
        (forall s :: s in AllCInputs(c) ==> s as CPort in c.PortMap.iports) &&
        (forall s :: s in c.PortMap.oports ==> s as CNode in AllCOutputs(c)) &&
        (forall s :: s in AllCOutputs(c) ==> s as CPort in c.PortMap.oports) &&
        PortMappingValid(c.PortMap)
    }

    lemma CircuitUpdatedCircuitNodeKindValid(c: Circuit, new_c: Circuit)
        requires CircuitValid(c)
        requires new_c.NodeKind == c.NodeKind
        requires new_c.HierLevel == c.HierLevel
        ensures CircuitNodeKindValid(new_c)
    {
        reveal CircuitValid();
    }

    predicate CircuitNodeKindValid(c: Circuit)
        decreases  c.HierLevel, 1
    {
        forall n: CNode | n in c.NodeKind ::
            CNodeKindValid(c.HierLevel, c.NodeKind[n])
    }

    predicate CircuitPortSourceValid(c: Circuit)
    {
        forall inp | inp in c.PortSource ::
            NPValidInput(c, inp) &&
            var onp := c.PortSource[inp];
            NPValidOutput(c, onp)
    }

    ghost predicate NPValid(c: Circuit, np: NP)
    {
        NPValidInput(c, np) || NPValidOutput(c, np)
    }

    predicate NPValidInput(c: Circuit, np: NP)
    {
        match NodeKind(c, np.n)
        // The node doesn't exist.
        case None => false
        case Some(nk) => IsIPort(nk, np.p)
    }

    function AllValidINP(c: Circuit): set<NP>
    {
        set n, p | n in c.NodeKind && p in PortMap(c.NodeKind[n]).iports :: NP(n, p)
    }

    predicate NPValidOutput(c: Circuit, np: NP)
    {
        match NodeKind(c, np.n)
        case None => false
        case Some(nk) => IsOPort(nk, np.p)
    }

    function AllValidONP(c: Circuit): set<NP>
    {
        set n, p | n in c.NodeKind && p in PortMap(c.NodeKind[n]).oports :: NP(n, p)
    }

    predicate CNodeIsCHier(c: Circuit, n: CNode)
    {
        NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
    }

    predicate CNodeIsCInput(c: Circuit, n: CNode)
    {
        NodeKind(c, n).Some? && NodeKind(c, n).value.CInput?
    }

    function AllCInputs(c: Circuit): set<CNode>
    {
        set n | n in c.NodeKind && CNodeIsCInput(c, n)
    }

    predicate CNodeIsCOutput(c: Circuit, n: CNode)
    {
        NodeKind(c, n).Some? && NodeKind(c, n).value.COutput?
    }

    function AllCOutputs(c: Circuit): set<CNode>
    {
        set n | n in c.NodeKind && CNodeIsCOutput(c, n)
    }

    datatype PortMapping =
        PortMapping(
            inames: seq<string>,
            iports: seq<CPort>,
            onames: seq<string>,
            oports: seq<CPort>
        )

    predicate PortMappingValid(m: PortMapping)
    {
        |m.inames| == |m.iports| &&
        (forall i: nat, j: nat :: i < |m.inames| && j < |m.inames| && i != j ==>
            m.inames[i] != m.inames[j] && m.iports[i] != m.iports[j]) &&
        |m.onames| == |m.oports| &&
        (forall i: nat, j: nat :: i < |m.onames| && j < |m.onames| && i != j ==>
            m.onames[i] != m.onames[j] && m.oports[i] != m.oports[j]) &&
        (forall i: nat, j: nat :: i < |m.inames| && j < |m.onames| ==>
            m.inames[i] != m.onames[j] && m.iports[i] != m.oports[j])
    }

    function INameToPort(m: PortMapping, name: string): CPort
        requires PortMappingValid(m)
        requires name in m.inames
    {
        var index := Seq.IndexOf(m.inames, name);
        m.iports[index]
    }

    lemma INameToPortCovers(m: PortMapping)
        requires PortMappingValid(m)
        ensures
            var inames: set<string> := (set k | k in m.inames);
            var iports := (set k | k in inames :: INameToPort(m, k));
            forall k :: k in iports <==> k in m.iports
    {
            var iports := seq(|m.inames|, (i: nat) requires i < |m.inames| =>
                INameToPort(m, m.inames[i]));
            assert iports == m.iports;
    }

    function ONameToPort(m: PortMapping, name: string): CPort
        requires PortMappingValid(m)
        requires name in m.onames
    {
        var index := Seq.IndexOf(m.onames, name);
        m.oports[index]
    }

    function PortMappingAddIPort(pm: PortMapping, s: string, p: CPort): (r: PortMapping)
        requires PortMappingValid(pm)
        requires s !in pm.inames
        requires s !in pm.onames
        requires p !in pm.iports
        requires p !in pm.oports
    {
        PortMapping(
            inames := pm.inames + [s],
            iports := pm.iports + [p],
            onames := pm.onames,
            oports := pm.oports
        )
    }

    function PortMappingAddOPort(pm: PortMapping, s: string, p: CPort): (r: PortMapping)
        requires PortMappingValid(pm)
        requires s !in pm.inames
        requires s !in pm.onames
        requires p !in pm.iports
        requires p !in pm.oports
        ensures PortMappingValid(r)
    {
        PortMapping(
            inames := pm.inames,
            iports := pm.iports,
            onames := pm.onames + [s],
            oports := pm.oports + [p]
        )
    }

}
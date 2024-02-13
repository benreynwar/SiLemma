include "../libraries/src/Wrappers.dfy"
include "SeqNatToNat.dfy"
include "hgraph.dfy"

module Circuit {

    import HG
    import SeqNatToNat
    import opened Wrappers

    newtype CPort = HG.HPort
    newtype CNode = nat

    newtype HNode = nat

    // A type of Node in the Circuit Graph.
    // Different from a Node in HGraph in that
    // 1) We introduce a CHier node to support hierarchical design.
    // 2) A CComb to support combinatorial primitives.
    // 3) A CSeq to model a register
    datatype CNodeKind = 
      | CHier(Circuit: Circuit)
      | CComb(
          IPorts: set<CPort>,
          OPorts: set<CPort>,
          PathExists: (CPort, CPort) -> bool,
          Behav: map<CPort, bool> -> Option<map<CPort, bool>>
        )
      | CConst(value: bool)
      | CInput()
      | COutput()
      | CSeq()

    function IPorts(nk: CNodeKind): set<CPort>
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(c) => set n | n < c.NodeBound && c.NodeKind(n) == Some(CInput) :: n as CPort
        case CComb(iports, oports, path_exists, behav) => iports
        case CInput() => {}
        case CConst(v) => {}
        case COutput() => {0 as CPort}
        case CSeq() => {0 as CPort}
    }

    function OPorts(nk: CNodeKind): set<CPort>
    {
        match nk
        case CHier(c) => set n | n < c.NodeBound && c.NodeKind(n) == Some(COutput) :: n as CPort
        case CComb(iports, oports, path_exists, behav) => oports
        case CInput() => {0 as CPort}
        case COutput() => {}
        case CConst(v) => {0 as CPort}
        case CSeq() => {0 as CPort}
    }

    // INP and ONP reference ports on a single level of the hierarchy.
    // The 'n' can point at an internal node, or at a port on the external
    // interface.
    datatype INP = INP(n: CNode, p: CPort)
    datatype ONP = ONP(n: CNode, p: CPort)

    // HPINP and HPONP can reference a port nested in the hierarchy.
    // This is useful as an intermediate when converting to a HGraph.
    datatype HPINP = HPINP(hpn: HPNode, p: CPort)
    datatype HPONP = HPONP(hpn: HPNode, p: CPort)

    ghost predicate HPINPValid(c: Circuit, hpinp: HPINP)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpinp.hpn.hp)
    }

    ghost predicate HPONPValid(c: Circuit, hponp: HPONP)
        requires CircuitValid(c)
    {
        HPNodeValid(c, hponp.hpn)
    }
    
    const MAX_HIERLEVEL := 128

    datatype Circuit = Circuit(
        //IPorts: set<CNode>,
        //OPorts: set<CNode>,
        NodeKind: CNode -> Option<CNodeKind>,
        PortSource: INP -> Option<ONP>,
        // This is larger or equal to all nodes for which NodeKind(node) is Some
        // We use this help dafny prove that things are finite and terminate.
        NodeBound: CNode,
        PortBound: CPort,
        HierLevel: nat
    )

    function CircuitIPorts(c: Circuit) : set<CNode>
    {
        set n | n < c.NodeBound && c.NodeKind(n) == Some(CInput)
    }

    function CircuitOPorts(c: Circuit) : set<CNode>
    {
        set n | n < c.NodeBound && c.NodeKind(n) == Some(COutput)
    }

    // Represents the path taken through a hierarchy of nodes where a node can
    // represent a lower-level circuit.
    datatype HierarchyPath =
        | Top
        | Level(
            n: CNode,
            parent: HierarchyPath
            )

    datatype HPNode =
        HPNode(
            hp: HierarchyPath,
            n: CNode
        )

    function HierarchyPathCircuit(c: Circuit, hp: HierarchyPath): (r: Circuit)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        decreases hp, 1
    {
        match hp
        case Top => c
        case Level(n, parent) =>
            assert HierarchyPathValid(c, parent);
            var parent_c := HierarchyPathCircuit(c, parent);
            parent_c.NodeKind(n).value.Circuit
    }

    lemma HierarchyPathCircuitValid(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures CircuitValid(HierarchyPathCircuit(c, hp))
    {
        if hp.Top? {
        } else {
            HierarchyPathCircuitValid(c, hp.parent);
        }
    }

    ghost predicate HierarchyPathValid(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        decreases hp, 0
    {
        match hp
        case Top => true
        case Level(n, parent) =>
            HierarchyPathValid(c, parent) &&
            var hp_c := HierarchyPathCircuit(c, parent);
            hp_c.NodeKind(n).Some? && hp_c.NodeKind(n).value.CHier?
    }

    ghost predicate HPNodeValid(c: Circuit, hpn: HPNode)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpn.n);
        HierarchyPathValid(c, hpn.hp) && maybe_nk.Some?
    }

    ghost predicate HPNodeIsLeaf(c: Circuit, hpn: HPNode)
        requires CircuitValid(c)
        requires HPNodeValid(c, hpn)
    {
        var hp_c := HierarchyPathCircuit(c, hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpn.n);
        !maybe_nk.value.CHier?
    }

    function ExtendHierarchyPath(c: Circuit, hp: HierarchyPath, n: CNode): (r: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        requires HierarchyPathCircuit(c, hp).NodeKind(n).Some?
        requires HierarchyPathCircuit(c, hp).NodeKind(n).value.CHier?
        ensures HierarchyPathValid(c, r)
    {
        var hp_c := HierarchyPathCircuit(c, hp);
        HierarchyPathCircuitValid(c, hp);
        assert CircuitValid(hp_c);
        var next_c := hp_c.NodeKind(n).value.Circuit;
        assert CircuitValid(next_c);
        Level(n, hp)
    }

    function CompleteHierarchyPath(c: Circuit, hp: HierarchyPath, n: CNode): (r: HPNode)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        requires HierarchyPathCircuit(c, hp).NodeKind(n).Some?
        requires !HierarchyPathCircuit(c, hp).NodeKind(n).value.CHier?
        ensures HPNodeValid(c, r)
    {
        HPNode(hp, n)
    }

    ghost predicate CNodeKindValid(c: Circuit, nk: CNodeKind)
        decreases c.HierLevel, 0
    {
        match nk
        case CHier(lower_c) =>
            (lower_c.HierLevel > nk.Circuit.HierLevel) &&
            CircuitValid(lower_c)
        case CComb(iports, oports, path_exists, behav) =>
          (forall a: CPort, b: CPort ::
              (a !in iports ==> !nk.PathExists(a, b)) &&
              (b !in oports ==> !nk.PathExists(a, b)))
          &&
          (forall a: CPort ::
              !(a in iports && a in oports))
        case _ => true
    }

    ghost predicate CircuitValid(c: Circuit)
        decreases  c.HierLevel, 1
    {
        forall n: CNode ::
            var maybe_nk := c.NodeKind(n);
            if maybe_nk.None? then
                true
            else
                CNodeKindValid(c, maybe_nk.Extract())
    }

    ghost predicate ValidINP(c: Circuit, inp: INP)
    {
        match c.NodeKind(inp.n)
        // The node doesn't exist.
        case None => false
        case Some(nk) => inp.p in IPorts(nk)
    }

    ghost predicate ValidONP(c: Circuit, onp: ONP)
    {
        match c.NodeKind(onp.n)
        case None => false
        case Some(nk) => onp.p in OPorts(nk)
    }

    ghost predicate CircuitComplete(c: Circuit)
        decreases c.HierLevel, 1
    {
        forall inp: INP :: ValidINP(c, inp) ==> c.PortSource(inp).Some?
    }

    function CNodeKindToHNodeKind(nk: CNodeKind): HG.HNodeKind
        requires nk.CComb?
    {
      HG.HNodeKind(
        (set p | p in nk.IPorts :: p as HG.HPort),
        (set p | p in nk.OPorts :: p as HG.HPort),
        (p1, p2) => nk.PathExists(p1 as CPort, p2 as CPort)
      )
    }

    lemma HierLevelDecreases(c: Circuit, n: CNode)
        requires c.NodeKind(n).Some?
        requires c.NodeKind(n).value.CHier?
        requires
            CircuitValid(c)
        ensures c.NodeKind(n).Extract().Circuit.HierLevel < c.HierLevel
    {
    }

    lemma SubCircuitValid(c: Circuit, n: CNode)
        requires
            var maybe_nk := c.NodeKind(n);
            (maybe_nk.Some?) &&
            var nk := maybe_nk.Extract();
            (nk.CHier?)
        requires
            CircuitValid(c)
        ensures CircuitValid(c.NodeKind(n).Extract().Circuit)
    {
    }


    function HGNodeToHPNode(c: Circuit, hp: HierarchyPath, n: HNode) : (r: Option<HPNode>)
        requires CircuitValid(c)
        // The Hierarchy path points to a circuit.
        // The HNode is a node within that circuit, possibly buried inside a CHier.
        // We return a HierarchyPath all the way to that node.
        requires HierarchyPathValid(c, hp)
        requires CircuitValid(HierarchyPathCircuit(c, hp))
        ensures r.None? || (HPNodeValid(c, r.value) && HPNodeIsLeaf(c, r.value))
        decreases HierarchyPathCircuit(c, hp).HierLevel
    {
        var hp_c := HierarchyPathCircuit(c, hp);
        var unpacked_n := SeqNatToNat.NatToNats(n as nat, 2);
        var n0 := unpacked_n[0] as CNode;
        var n1 := unpacked_n[1] as HNode;
        match hp_c.NodeKind(n0)
        case None => None
        case Some(nk) =>
            match nk
            case CHier(_) =>
                var new_hp := ExtendHierarchyPath(c, hp, n0);
                HierLevelDecreases(hp_c, n0);
                SubCircuitValid(hp_c, n0);
                HGNodeToHPNode(c, new_hp, n1)
            case _ =>
                var new_hpn := CompleteHierarchyPath(c, hp, n0);
                if n1 == 0 then Some(new_hpn) else None
    }

    function HierarchyPathToHGNodeInternal(hp: HierarchyPath, hn: HNode) : (r: HNode)
    {
        match hp
        case Top => hn
        case Level(n, parent) =>
            var new_hn := SeqNatToNat.NatsToNat([n as nat, hn as nat]) as HNode;
            HierarchyPathToHGNodeInternal(parent, new_hn)
    }

    function HPNodeToHGNode(hpn: HPNode) : (r: HNode)
    {
        HierarchyPathToHGNodeInternal(hpn.hp, hpn.n as HNode)
    }

    function HGINPtoHPINP(c: Circuit, inp: HG.INP) : (r: Option<HPINP>)
        requires CircuitValid(c)
        ensures r.Some? ==> HPINPValid(c, r.value)
    {
        var cp := inp.p as CPort;
        match HGNodeToHPNode(c, Top, inp.n as HNode)
            case None => None
            case Some(hp) =>
                Some(HPINP(hp, cp))
    }

    function HPINPtoHPONP(c: Circuit, hpinp: HPINP) : (r: Option<HPONP>)
        requires CircuitValid(c)
        requires HPINPValid(c, hpinp)
        ensures r.None? || HPONPValid(c, r.value)
    {
        var hp := hpinp.hpn.hp;
        var c := HierarchyPathCircuit(c, hp);
        var inp := INP(hpinp.hpn.n, hpinp.p);
        var maybe_onp: Option<ONP> := c.PortSource(inp);
            match maybe_onp
            // The input port does not connect to anything.
            case None => None
            // The input port does connect.
            case Some(onp) =>
                match c.NodeKind(onp.n)
                    // But the node it connects to doesn't exist.
                    case None => None
                    // The node it connects to does exist.
                    case Some(nk) =>
                        var hpn := HPNode(hp, onp.n);
                        Some(HPONP(hpn, onp.p))
    }

    function HPNodeToNK(c: Circuit, hpn: HPNode): CNodeKind
        requires CircuitValid(c)
        requires HPNodeValid(c, hpn)
    {
        HierarchyPathCircuit(c, hpn.hp).NodeKind(hpn.n).value
    }

    function HPONPtoHGONP(c: Circuit, onp: HPONP) : HG.ONP
        requires CircuitValid(c)
        requires HPONPValid(c, onp)
    {
        var c := HierarchyPathCircuit(c, onp.hpn.hp);
        assert CircuitValid(c);
        // We need to check if it the output port of a hiearchical node.
        // If so we need to find the appropriate internal COutput Node.
        var nk := HPNodeToNK(c, onp.hpn);
        assert nk == c.NodeKind(onp.hpn.n).value;
        match nk
        case CHier(c) =>
            var new_hp := ExtendHierarchyPath(c, onp.hpn.hp, onp.hpn.n);
            var new_n: CNode := onp.p as CNode;
            var new_hpn := HPNode(new_hp, new_n);
            var n := HPNodeToHGNode(new_hpn);
            HG.ONP(n as HG.HNode, onp.p as HG.HPort)
        case _ =>
            var n := HPNodeToHGNode(onp.hpn);
            HG.ONP(n as HG.HNode, onp.p as HG.HPort)
    }

    function MaxSubcircuitNodeBoundInternal(c: Circuit, n: CNode, max: HG.HNode): HG.HNode
        requires CircuitValid(c)
        decreases c.HierLevel, 0, n
    {
        var new_max := if n == 0 then max else MaxSubcircuitNodeBoundInternal(c, n-1, max);
        match c.NodeKind(n)
            case Some(CHier(next_c)) =>
                HierLevelDecreases(c, n);
                SubCircuitValid(c, n);
                var nb := CircuitHGNodeBound(next_c) as HG.HNode;
                if nb > new_max then max else nb
            case _ => new_max
    }

    function MaxSubcircuitNodeBound(c: Circuit): HG.HNode
        requires CircuitValid(c)
        decreases c.HierLevel, 1
    {
        MaxSubcircuitNodeBoundInternal(c, c.NodeBound, 0)
    }

    function CircuitHGNodeBound(c: Circuit): HG.HNode
        requires CircuitValid(c)
        decreases c.HierLevel, 2
    {
        // The local NodeBound get expanded.
        var subcircuit_nb := MaxSubcircuitNodeBound(c);
        // Just combine the max node bound on this level with the max node bound on the next level
        SeqNatToNat.NatsToNat([c.NodeBound as nat, subcircuit_nb as nat]) as HG.HNode
    }

    function MaxSubcircuitHGPortBoundInternal(c: Circuit, n: CNode, max: HG.HPort): HG.HPort
        requires CircuitValid(c)
        decreases c.HierLevel, 0, n
    {
        var new_max := if n == 0 then max else MaxSubcircuitHGPortBoundInternal(c, n-1, max);
        match c.NodeKind(n)
            case Some(CHier(next_c)) =>
                HierLevelDecreases(c, n);
                SubCircuitValid(c, n);
                var nb := CircuitHGPortBound(next_c);
                if nb > new_max then max else nb
            case _ => new_max
    }

    function MaxSubcircuitHGPortBound(c: Circuit): HG.HPort
        requires CircuitValid(c)
        decreases c.HierLevel, 1
    {
        MaxSubcircuitHGPortBoundInternal(c, c.NodeBound, 0)
    }

    function CircuitHGPortBound(c: Circuit): HG.HPort
        requires CircuitValid(c)
        decreases c.HierLevel, 2
    {
        // The local NodeBound get expanded.
        // Now find which of the subcircuits is biggest.
        var subcircuit_pb := MaxSubcircuitHGPortBound(c);
        var local_pb := c.PortBound as HG.HPort;
        if local_pb > subcircuit_pb then local_pb else subcircuit_pb
    }

    function GetHGINPToONP(c: Circuit, inp: HG.INP) : Option<HG.ONP>
        requires CircuitValid(c)
        requires CircuitComplete(c)
    {
        // First go to HPINP.
        // That back to HPONP.
        // Then to HGONP.
        var maybe_hpinp := HGINPtoHPINP(c, inp);
        match maybe_hpinp
        case None => None
        case Some(hpinp) =>
            var maybe_hponp := HPINPtoHPONP(c, hpinp);
            match maybe_hponp
            case None => None
            case Some(hponp) =>
                var hgonp := HPONPtoHGONP(c, hponp);
                Some(hgonp)
    }

    function GetHGNodeKind(c: Circuit, n: HG.HNode): Option<HG.HNodeKind>
        requires CircuitValid(c)
    {
        var maybe_hpn := HGNodeToHPNode(c, Top, n as HNode);
        match maybe_hpn
        case None => None
        case Some(hpn) =>
            var level_c := HierarchyPathCircuit(c, hpn.hp);
            var nk := level_c.NodeKind(hpn.n).value;
            assert !nk.CHier?;
            match nk
            case CComb(iports, oports, path_exists, behav) =>
                Some(HG.HNodeKind(
                    set p | p in iports :: p as HG.HPort,
                    set p | p in oports :: p as HG.HPort,
                    (a, b) => path_exists(a as CPort, b as CPort)
                    ))
            // The HGGraph level doesn't know about values, so a constant is the same as an input.
            case CConst(v) => Some(HG.InputNodeKind)
            // If the input is at the top level then it's an input
            // but if it's buried in a hierarchical module then it's just a IdentNodeKind that connects the hiearchy levels.
            case CInput() => if hpn.hp.Top? then Some(HG.InputNodeKind) else Some(HG.IdentNodeKind)
            case COutput() => if hpn.hp.Top? then Some(HG.OutputNodeKind) else Some(HG.IdentNodeKind)
            case CSeq() => Some(HG.RegisterNodeKind)
    }

    function CircuitToHGraph(c: Circuit): (hg: HG.HGraph)
        requires CircuitValid(c)
        requires CircuitComplete(c)
    {
        HG.HGraph(
          n => GetHGNodeKind(c, n),
          inp => GetHGINPToONP(c, inp),
          CircuitHGNodeBound(c),
          CircuitHGPortBound(c)
        )
    }

    // Show that if there is a path in the Circuit there is a path in the HGraph.
    // Show that if there is not a path in the Circuit there is no path in the HGraph.

    function AndBehav(m: map<CPort, bool>): Option<map<CPort, bool> >
    {
        if (0 in m) && (1 in m) then
            Some(map[0 := m[0] && m[1]])
        else
            None
    }
    predicate BinaryPathExists(p: CPort, q: CPort)
    {
        (p in {0, 1}) && (q == 0)
    }
    const AndCNode: CNodeKind := CComb(
        IPorts := {0 as CPort, 1 as CPort},
        OPorts := {0 as CPort},
        PathExists := BinaryPathExists,
        Behav := AndBehav
    )

    function xor(b: bool, c: bool): bool
    {
        match (b, c)
          case (false, false) => false
          case (false, true) => true
          case (true, false) => true
          case (true, true) => false
    }
    function XorBehav(m: map<CPort, bool>): Option<map<CPort, bool> >
    {
        if (0 in m) && (1 in m) then
            Some(map[0 := xor(m[0], m[1])])
        else
            None
    }
    const XorCNode: CNodeKind := CComb(
        IPorts := {0 as CPort, 1 as CPort},
        OPorts := {0 as CPort},
        PathExists := BinaryPathExists,
        Behav := XorBehav
    )

    function MakeEmptyCircuit(): Circuit
    {
      Circuit(
          NodeKind := _ => None,
          PortSource := _ => None,
          NodeBound := 0,
          PortBound := 0,
          HierLevel := 0
      )
    }

    function AddIPort(g: Circuit): (Circuit, ONP)
    {
        var (c, n) := AddNode(g, CInput, map[]);
        (c, ONP(n, 0))
    }

    function AddOPort(g: Circuit, onp: ONP): Circuit
    {
        var (c, n) := AddNode(g, COutput, map[0 := onp]);
        c
    }

    function AddNode(g: Circuit, nk: CNodeKind, ip: map<CPort, ONP>): (Circuit, CNode)
    {
      var new_node := g.NodeBound;
      var c := Circuit(
          NodeKind := n => if n == new_node then Some(nk) else g.NodeKind(n),
          PortSource := (inp: INP) =>
            if inp.n == new_node then
              if inp.p in ip then
                Some(ip[inp.p])
              else
                None
            else
              g.PortSource(inp),
          NodeBound := g.NodeBound+1,
          PortBound := g.PortBound,
          HierLevel := g.HierLevel
      );
      (c, new_node)
    }

    function MakeOneBitAdder(): Circuit
    {
        var g := MakeEmptyCircuit();
        var (g, i_0) := AddIPort(g);
        var (g, i_1) := AddIPort(g);
        var (g, node_xor) := AddNode(g, XorCNode, map[0 := i_0, 1 := i_1]);
        var xor_output := ONP(node_xor, 0);
        var g := AddOPort(g, xor_output);
        var (g, node_add) := AddNode(g, AndCNode, map[0 := i_0, 1 := i_1]);
        var add_output := ONP(node_add, 0);
        var g := AddOPort(g, add_output);
        g
    }
    
    //function EvaluateINP(g: Circuit, m: map<CPort, bool>, inp: INP, seen_path: seq<NP>): bool
    //    decreases LongestPathBack(g, inp)
    //{
    //    var maybe_onp := g.PortSource(inp);
    //    assert maybe_onp.Some?;
    //    var onp := maybe_onp.value;
    //    match onp.n
    //        case HBoundary() => m[onp.p] 
    //        case HNode(n) =>
    //            var maybe_nk := g.NodeKind(n);
    //            assert maybe_nk.Some?;
    //            var nk := maybe_nk.value;
    //            match nk
    //                case CLeaf =>
    //                    var node_inputs := (map p | p in nk.IPorts :: EvaluateINP(g, m, INP(HNode(n), p)));
  
    //    true
    //}

}
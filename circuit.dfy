module Circuit {

    import SeqNatToNat
    import opened Std.Wrappers
    import Std.Collections.Seq
    import SeqExt

    newtype CPort = nat
    const INPUT_PORT: CPort := 0
    const OUTPUT_PORT: CPort := 1

    // A node in the graph.
    newtype CNode = nat

    datatype CNodeKind = 
        // A hierarchical node so we can design hierarchically.
      | CHier(c: Circuit)
        // A node representing combinatorial logic.
      | CComb(
          IPorts: set<CPort>,
          OPorts: set<CPort>,
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

    predicate CNodeIsCHier(c: Circuit, n: CNode)
        requires CircuitValid(c)
    {
        c.NodeKind(n).Some? && c.NodeKind(n).value.CHier?
    }

    function DirectSubcircuits(c: Circuit): (r: seq<Circuit>)
        requires CircuitValid(c)
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        assert forall i: CNode ::
            i < c.NodeBound && c.NodeKind(i).Some? && c.NodeKind(i).value.CHier? ==>
            var nk := c.NodeKind(i).value;
            CNodeKindValid(c.HierLevel, c.PortBound, nk);
        var all_cnodes := seq(c.NodeBound, (i: nat) requires i < c.NodeBound as nat => i as CNode);
        var all_subcircuit_cnodes := Seq.Filter(n => CNodeIsCHier(c, n), all_cnodes);
        var all_subcircuits := Seq.Map(
            i requires CNodeIsCHier(c, i) => c.NodeKind(i).value.c, all_subcircuit_cnodes);
        all_subcircuits
    }

    lemma InSubcircuitsExistsCNode(c: Circuit, subc: Circuit)
        requires CircuitValid(c)
        requires subc in DirectSubcircuits(c)
        ensures exists n: CNode :: CNodeIsCHier(c, n) && c.NodeKind(n).value.c == subc
    {
    }

    ghost function SubcircuitToCNode(c: Circuit, subc: Circuit): (r: CNode)
        requires CircuitValid(c)
        requires subc in DirectSubcircuits(c)
        ensures c.NodeKind(r).Some? && c.NodeKind(r).value.CHier?
        ensures c.NodeKind(r).value.c == subc
    {
        InSubcircuitsExistsCNode(c, subc);
        var n :| CNodeIsCHier(c, n) && c.NodeKind(n).value.c == subc;
        n
    }

    lemma AllSubcircuitsValid(c: Circuit)
        requires CircuitValid(c)
        ensures forall subc :: subc in DirectSubcircuits(c) ==>
            CircuitValid(subc) && (subc.HierLevel < c.HierLevel)
    {
        forall subc | subc in DirectSubcircuits(c)
            ensures CircuitValid(subc) && (subc.HierLevel < c.HierLevel)
        {
            SubcircuitValid(c, subc);
        }
    }

    lemma SubcircuitValid(c: Circuit, subc: Circuit)
        requires CircuitValid(c)
        requires subc in DirectSubcircuits(c)
        ensures CircuitValid(subc) && subc.HierLevel < c.HierLevel
    {
        InSubcircuitsExistsCNode(c, subc);
        var n := SubcircuitToCNode(c, subc);
        var nk := c.NodeKind(n).value;
        reveal CircuitValid();
        assert CNodeKindValid(c.HierLevel, c.PortBound, nk);
        assert CircuitValid(subc);
    }

    lemma SubcircuitInDirectSubcircuits(c: Circuit, n: CNode)
        requires CircuitValid(c)
        requires c.NodeKind(n).Some? && c.NodeKind(n).value.CHier?
        ensures c.NodeKind(n).value.c in DirectSubcircuits(c)
    {
        assert CNodeIsCHier(c, n);
        var all_cnodes := seq(c.NodeBound, (i: nat) requires i < c.NodeBound as nat => i as CNode);
        var all_subcircuit_cnodes := Seq.Filter(i => CNodeIsCHier(c, i), all_cnodes);
        var all_subcircuits := Seq.Map(
            i requires CNodeIsCHier(c, i) => c.NodeKind(i).value.c, all_subcircuit_cnodes);
        assert all_subcircuits == DirectSubcircuits(c);
        reveal CircuitValid();
        assert n < c.NodeBound;
        forall i: nat | i < c.NodeBound as nat
            ensures i as CNode in all_cnodes
        {
            assert all_cnodes[i] == i as CNode;
        }
        assert n in all_cnodes;
        SeqExt.FilterStillContains((i: CNode) => CNodeIsCHier(c, i), all_cnodes, n);
        assert n in all_subcircuit_cnodes;
        SeqExt.MapStillContains(
            (i: CNode) requires CNodeIsCHier(c, i) => c.NodeKind(i).value.c, all_subcircuit_cnodes, n);
        assert c.NodeKind(n).value.c in all_subcircuits;
    }

    ghost function HierSubcircuitsInternal(
        hier_level: nat, new_cs: seq<Circuit>, old_cs: seq<Circuit>): (r: seq<Circuit>)
        requires forall x :: x in new_cs ==> x.HierLevel < hier_level
        requires forall x :: x in new_cs ==> CircuitValid(x)
        decreases hier_level, 0, |new_cs|
     {
        if |new_cs| == 0 then
            old_cs
        else
            var head: Circuit := new_cs[0];
            var tail: seq<Circuit> := new_cs[1..];
            var expanded := HierSubcircuits(head);
            HierSubcircuitsInternal(hier_level, tail, old_cs + expanded)
     }
 
     ghost function HierSubcircuits(c: Circuit): (r: seq<Circuit>)
         requires CircuitValid(c)
         decreases c.HierLevel, 1
     {
         var direct := DirectSubcircuits(c);
         reveal CircuitValid();
         assert CircuitNodeKindValid(c);
         HierSubcircuitsInternal(c.HierLevel, direct, direct)
     }


    function HPNPtoNK(c: Circuit, hpnp: HPNP): (r: CNodeKind)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures
            reveal HPNPValidInput();
            reveal HPNPValidOutput();
            var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
            var nk := HPNPtoNK(c, hpnp);
            CNodeKindValid(hp_c.HierLevel, hp_c.PortBound, nk)
    {
        HPNPValidHPValid(c, hpnp);
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        HierarchyPathCircuitValid(c, hpnp.hpn.hp);
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var nk := hp_c.NodeKind(hpnp.hpn.n).value;
        CircuitValidCNodeKindValid(hp_c, hpnp.hpn.n);
        nk
    }


    function HPNPtoSubcircuit(c: Circuit, hpnp: HPNP): Circuit
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        requires HPNPtoNK(c, hpnp).CHier?
    {
        var nk := HPNPtoNK(c, hpnp);
        HPNPValidHPValid(c, hpnp);
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        assert CNodeKindValid(hp_c.HierLevel, hp_c.PortBound, nk);
        nk.c
    }

    function NodeToSubcircuit(c: Circuit, n: CNode): Circuit
        requires c.NodeKind(n).Some?
        requires c.NodeKind(n).value.CHier?
    {
        c.NodeKind(n).value.c
    }

    function IPorts(nk: CNodeKind): set<CPort>
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(subc) =>
            set n | n < subc.NodeBound && subc.NodeKind(n) == Some(CInput) :: n as CPort
        case CComb(iports, oports, path_exists, behav, names) => iports
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
        case CComb(iports, oports, path_exists, behav, names) => oports
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

    // INP and ONP reference ports on a single level of the hierarchy.
    // The 'n' can point at an internal node, or at a port on the external
    // interface.

    datatype NP = NP(n: CNode, p: CPort)

    // HPINP and HPONP can reference a port nested in the hierarchy.
    // This is useful as an intermediate when converting to a HGraph.

    datatype HPNP = HPNP(hpn: HPNode, p: CPort)

    predicate {:opaque} HPNPValidInput(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpnp.hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpnp.hpn.n);
        maybe_nk.Some? &&
        IsIPort(maybe_nk.value, hpnp.p)
    }

    lemma HPNPValidHPValid(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures HierarchyPathValid(c, hpnp.hpn.hp)
    {
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
    }


    predicate {:opaque} HPNPValidOutput(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpnp.hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpnp.hpn.n);
        maybe_nk.Some? &&
        IsOPort(maybe_nk.value, hpnp.p)
    }

    lemma HPNPNotBothValidInputOutput(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures !(HPNPValidOutput(c, hpnp) && HPNPValidInput(c, hpnp))
    {
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        assert HierarchyPathValid(c, hpnp.hpn.hp);
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        HierarchyPathCircuitValid(c, hpnp.hpn.hp);
        var nk := hp_c.NodeKind(hpnp.hpn.n).value;
        reveal CircuitValid();
        assert CircuitNodeKindValid(hp_c);
    }

    predicate HPNPValid(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HPNPValidInput(c, hpnp) ||
        HPNPValidOutput(c, hpnp)
    }

    const MAX_HIERLEVEL := 128

    datatype Circuit = Circuit(
        //IPorts: set<CNode>,
        //OPorts: set<CNode>,
        NodeKind: CNode -> Option<CNodeKind>,
        PortSource: NP -> Option<NP>,
        // This is larger or equal to all nodes for which NodeKind(node) is Some
        // We use this help dafny prove that things are finite and terminate.
        NodeBound: CNode,
        PortBound: CPort,
        HierLevel: nat,
        PortNames: string -> Option<CNode>
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
    datatype HierarchyPath = HP(v: seq<CNode>)
    //    | Top
    //    | Level(
    //        n: CNode,
    //        parent: HierarchyPath
    //        )

    datatype HPNode =
        HPNode(
            hp: HierarchyPath,
            n: CNode
        )

    function HPLength(hp: HierarchyPath): nat
    {
        |hp.v|
    }

    function HPTail(hp: HierarchyPath): (r: HierarchyPath)
        requires hp.v != []
        ensures |hp.v| == |r.v| + 1
    {
        HP(hp.v[..|hp.v|-1])
    }

    function HPHead(hp: HierarchyPath): CNode
        requires hp.v != []
    {
        hp.v[|hp.v|-1]
    }

    function HPHeadTail(hp: HierarchyPath): (r: (CNode, HierarchyPath))
        requires HPLength(hp) > 0
    {
        (HPHead(hp), HPTail(hp))
    }

    function HPStartChildren(hp: HierarchyPath): (r: (CNode, HierarchyPath))
        requires HPLength(hp) > 0
    {
        (hp.v[0], HP(hp.v[1..]))
    }

    function HierarchyPathSubcircuit(c: Circuit, hp: HierarchyPath): (r: Option<Circuit>)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        decreases |hp.v|, 1
    {
        if HPLength(hp) == 0 then
            None
        else
            var tail := HPTail(hp);
            var n := HPHead(hp);
            assert HierarchyPathValid(c, tail);
            var tail_c := HierarchyPathCircuit(c, tail);
            HierarchyPathCircuitValid(c, tail);
            assert CircuitValid(tail_c);
            reveal CircuitValid();
            var nk := tail_c.NodeKind(n).value;
            assert CircuitNodeKindValid(tail_c);
            assert CNodeKindValid(tail_c.HierLevel, tail_c.PortBound, nk);
            Some(tail_c.NodeKind(n).value.c)
    }

    function HierarchyPathCircuit(c: Circuit, hp: HierarchyPath): (r: Circuit)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        decreases |hp.v|, 1
    {
        if HPLength(hp) == 0 then
            c
        else
            var tail := HPTail(hp);
            var n := HPHead(hp);
            assert HierarchyPathValid(c, tail);
            var tail_c := HierarchyPathCircuit(c, tail);
            HierarchyPathCircuitValid(c, tail);
            //var cref := tail_c.NodeKind(n).value.CRef;
            //tail_c.Subcircuits[cref]
            assert CircuitValid(tail_c);
            var nk := tail_c.NodeKind(n).value;
            reveal CircuitValid();
            assert CircuitNodeKindValid(tail_c);
            assert CNodeKindValid(tail_c.HierLevel, tail_c.PortBound, nk);
            NodeToSubcircuit(tail_c, n)
    }

    lemma HierarchyPathCircuitValid(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures CircuitValid(HierarchyPathCircuit(c, hp))
        decreases |hp.v|
    {
        if HPLength(hp) == 0 {
            assert HierarchyPathCircuit(c, hp) == c;
        } else {
            var tail := HPTail(hp);
            assert HierarchyPathValid(c, tail);
            var tail_c := HierarchyPathCircuit(c, tail);
            HierarchyPathCircuitValid(c, tail);
            assert CircuitValid(tail_c);
            reveal CircuitValid();
            assert CircuitNodeKindValid(tail_c);
            var hp_c := HierarchyPathCircuit(c, hp);
            assert CircuitValid(hp_c);
        }
    }

    predicate HierarchyPathValid(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        decreases |hp.v|, 0
    {
        if HPLength(hp) == 0 then
            true
        else
            var (head, tail) := HPHeadTail(hp);
            HierarchyPathValid(c, tail) &&
            var hp_c := HierarchyPathCircuit(c, tail);
            hp_c.NodeKind(head).Some? && hp_c.NodeKind(head).value.CHier?
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
        reveal CircuitValid();
        assert CircuitNodeKindValid(hp_c);
        var next_c := NodeToSubcircuit(hp_c, n);
        assert CircuitValid(next_c);
        HP(hp.v +[n])
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

    ghost predicate CNodeKindValid(
        hier_level: nat, port_bound: CPort, nk: CNodeKind)
        decreases hier_level, 0
    {
        (
        match nk
        case CHier(subc) =>
            (subc.HierLevel < hier_level) &&
            CircuitValid(subc)
        case CComb(iports, oports, path_exists, behav, names) =>
          (forall a: CPort, b: CPort ::
              (a !in oports ==> !nk.PathExists(a, b)) &&
              (b !in iports ==> !nk.PathExists(a, b)))
          &&
          (forall a: CPort ::
              !(a in iports && a in oports))
        case _ => true
        ) && (
            forall p: CPort ::
                (IsIPort(nk, p) ==> p < port_bound) &&
                (IsOPort(nk, p) ==> p < port_bound) &&
                !(IsIPort(nk, p) && IsOPort(nk, p))
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

    ghost predicate CircuitPortSourceComplete(c: Circuit)
        requires CircuitPortSourceValid(c)
    {
        forall n: CNode ::
            forall p: CPort ::
                var inp := NP(n, p);
                if NPValidInput(c, inp) then
                    match c.PortSource(inp)
                    case None => false
                    case Some(onp) => NPValidOutput(c, onp)
                else
                    assert c.PortSource(inp) == None;
                    true
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

    lemma CircuitValidCNodeKindValid(c: Circuit, n: CNode)
        requires CircuitValid(c)
        requires c.NodeKind(n).Some?
        ensures CNodeKindValid(c.HierLevel, c.PortBound, c.NodeKind(n).value)
    {
        reveal CircuitValid();
    }

    ghost predicate {:opaque} CircuitValid(c: Circuit)
        decreases  c.HierLevel, 2
    {
        CircuitNodeKindValid(c) &&
        CircuitPortSourceValid(c)
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

    ghost predicate {:opaque} CircuitComplete(c: Circuit)
        requires CircuitValid(c)
        decreases c.HierLevel
    {
        (forall inp: NP :: NPValidInput(c, inp) ==> c.PortSource(inp).Some?) &&
        (forall n: CNode :: c.NodeKind(n).Some? && c.NodeKind(n).value.CHier? ==>
            var subc := c.NodeKind(n).value.c;
            CircuitValid(subc) &&
            (subc.HierLevel < c.HierLevel) &&
            CircuitComplete(subc)
        )
    }

    lemma HPCircuitComplete(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HierarchyPathValid(c, hp)
        ensures
            var hp_c := HierarchyPathCircuit(c, hp);
            CircuitValid(hp_c) &&
            CircuitComplete(hp_c)
        decreases |hp.v|
    {
        if |hp.v| == 0 {
        } else {
            var (head, tail) := HPHeadTail(hp);
            reveal CircuitComplete();
            HPCircuitComplete(c, tail);
        }
    }

    lemma HierLevelDecreases(c: Circuit, n: CNode)
        requires c.NodeKind(n).Some?
        requires c.NodeKind(n).value.CHier?
        requires
            CircuitValid(c)
        ensures NodeToSubcircuit(c, n).HierLevel < c.HierLevel
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
    }

    lemma SubCircuitValid(c: Circuit, n: CNode)
        requires
            var maybe_nk := c.NodeKind(n);
            (maybe_nk.Some?) &&
            var nk := maybe_nk.Extract();
            (nk.CHier?)
        requires
            CircuitValid(c)
        ensures CircuitValid(NodeToSubcircuit(c, n))
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
    }

    function {:vcs_split_on_every_assert} HPINPtoHPONP(c: Circuit, hpinp: HPNP) : (r: Option<HPNP>)
        requires CircuitValid(c)
        requires HPNPValidInput(c, hpinp)
        ensures r.None? || HPNPValid(c, r.value)
    {
        var hp := hpinp.hpn.hp;
        HPNPValidHPValid(c, hpinp);
        var parent_c := HierarchyPathCircuit(c, hp);
        HierarchyPathCircuitValid(c, hp);
        assert CircuitValid(parent_c);
        reveal HPNPValidOutput();
        reveal CircuitValid();
        assert CircuitNodeKindValid(parent_c);
        assert CircuitPortSourceValid(parent_c);
        var inp := NP(hpinp.hpn.n, hpinp.p);
        reveal HPNPValidInput();
        assert NPValidInput(parent_c, inp);
        var maybe_onp: Option<NP> := parent_c.PortSource(inp);
            match maybe_onp
            // The input port does not connect to anything.
            case None => None
            // The input port does connect.
            case Some(onp) =>
                assert NPValid(parent_c, onp);
                assert NPValidOutput(parent_c, onp);
                var nk := parent_c.NodeKind(onp.n);
                assert nk.Some?;
                assert IsOPort(nk.value, onp.p);
                var hpn := HPNode(hp, onp.n);
                var hpnp := HPNP(hpn, onp.p);
                reveal HPNPValidOutput();
                assert HPNPValidOutput(c, hpnp);
                Some(hpnp)
    }

    function HPNodeToNK(c: Circuit, hpn: HPNode): CNodeKind
        requires CircuitValid(c)
        requires HPNodeValid(c, hpn)
    {
        HierarchyPathCircuit(c, hpn.hp).NodeKind(hpn.n).value
    }

    function MaxSubcircuitNodeBoundInternal(c: Circuit, n: CNode, max: nat): nat
        requires CircuitValid(c)
        decreases c.HierLevel, 0, n
    {
        var new_max := if n == 0 then max else MaxSubcircuitNodeBoundInternal(c, n-1, max);
        match c.NodeKind(n)
            case Some(CHier(_)) =>
                HierLevelDecreases(c, n);
                SubCircuitValid(c, n);
                var next_c := NodeToSubcircuit(c, n);
                var nb := CircuitMaxNodeBound(next_c) as nat;
                if nb > new_max then max else nb
            case _ => new_max
    }

    function MaxSubcircuitNodeBound(c: Circuit): nat
        requires CircuitValid(c)
        decreases c.HierLevel, 1
    {
        MaxSubcircuitNodeBoundInternal(c, c.NodeBound, 0)
    }

    function CircuitMaxNodeBound(c: Circuit): nat
        requires CircuitValid(c)
        decreases c.HierLevel, 2
    {
        // The local NodeBound get expanded.
        var subcircuit_nb := MaxSubcircuitNodeBound(c);
        // Just combine the max node bound on this level with the max node bound on the next level
        SeqNatToNat.NatsToNat([c.NodeBound as nat, subcircuit_nb as nat])
    }

    //function Subcircuits(c: Circuit): seq<Circuit>
    //{
    //    seq(n requires 0 <= n < c.NodeBound | c.NodeKind(n).Some? && c.NodeKind(n).value.CHier? :: c.NodeKind(n).value.Circuit)
    //}

    //function MaxSubcircuitMaxPortBoundInternal(c: Circuit, n: CNode, max: nat): nat
    //    requires CircuitValid(c)
    //    decreases c.HierLevel, 0, n
    //{
    //    var new_max := if n == 0 then max else MaxSubcircuitMaxPortBoundInternal(c, n-1, max);
    //    match c.NodeKind(n)
    //        case Some(CHier(_)) =>
    //            HierLevelDecreases(c, n);
    //            SubCircuitValid(c, n);
    //            var next_c := NodeToSubcircuit(c, n);
    //            var nb := CircuitMaxPortBound(next_c);
    //            if nb > new_max then max else nb
    //        case _ => new_max
    //}

    //function MaxSubcircuitMaxPortBound(c: Circuit): nat
    //    requires CircuitValid(c)
    //    decreases c.HierLevel, 1
    //{
    //    MaxSubcircuitMaxPortBoundInternal(c, c.NodeBound, 0)
    //}

    ghost function MaxInSetInternal(a: set<nat>, max: nat): nat
    {
        if |a| == 0 then
            max
        else
            var y :| y in a;
            MaxInSetInternal(
                a - {y},
                if y > max then y else max
            )
    }

    ghost function MaxInSet(a: set<nat>): nat
        requires |a| > 0
    {
        var y :| y in a;
        MaxInSetInternal(a - {y}, y)
    }

    ghost function CircuitMaxPortBound(c: Circuit): nat
        requires CircuitValid(c)
        decreases c.HierLevel, 2
    {
        var subcircuits: seq<Circuit> := HierSubcircuits(c);
        var port_bounds := (set c: Circuit | c in subcircuits :: c.PortBound as nat);
        if |port_bounds| == 0 then
            c.PortBound as nat
        else
            var max_hier_port_bound := MaxInSet(port_bounds);
            if c.PortBound as nat > max_hier_port_bound then c.PortBound as nat else max_hier_port_bound
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

    function PortNames2to1(name: string): Option<CPort>
    {
        match name
        case "i0" => Some(0 as CPort)
        case "i1" => Some(1 as CPort)
        case "o" => Some(2 as CPort)
        case _ => None
    }

    const AndCNode: CNodeKind := CComb(
        IPorts := {0 as CPort, 1 as CPort},
        OPorts := {2 as CPort},
        PathExists := BinaryPathExists,
        Behav := AndBehav,
        PortNames := PortNames2to1
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
        Behav := XorBehav,
        PortNames := PortNames2to1
    )

    function MakeEmptyCircuit(): Circuit
    {
      Circuit(
          NodeKind := _ => None,
          PortSource := _ => None,
          NodeBound := 0,
          PortBound := 0,
          HierLevel := 0,
          PortNames := _ => None
      )
    }

    function AddIPort(g: Circuit): (Circuit, NP)
    {
        var (c, n) := AddNode(g, CInput, map[]);
        (c, NP(n, 0))
    }

    function AddOPort(g: Circuit, onp: NP): Circuit
    {
        var (c, n) := AddNode(g, COutput, map[0 := onp]);
        c
    }

    function AddNode(g: Circuit, nk: CNodeKind, ip: map<CPort, NP>): (Circuit, CNode)
        requires !nk.CHier?
    {
      var new_node := g.NodeBound;
      var c := Circuit(
          NodeKind := n => if n == new_node then Some(nk) else g.NodeKind(n),
          PortSource := (inp: NP) =>
            if inp.n == new_node then
              if inp.p in ip then
                Some(ip[inp.p])
              else
                None
            else
              g.PortSource(inp),
          NodeBound := g.NodeBound+1,
          PortBound := g.PortBound,
          HierLevel := g.HierLevel,
          PortNames := g.PortNames
      );
      (c, new_node)
    }

    function MakeOneBitAdder(): Circuit
    {
        var g := MakeEmptyCircuit();
        var (g, i_0) := AddIPort(g);
        var (g, i_1) := AddIPort(g);
        var (g, node_xor) := AddNode(g, XorCNode, map[0 := i_0, 1 := i_1]);
        var xor_output := NP(node_xor, 0);
        var g := AddOPort(g, xor_output);
        var (g, node_add) := AddNode(g, AndCNode, map[0 := i_0, 1 := i_1]);
        var add_output := NP(node_add, 0);
        var g := AddOPort(g, add_output);
        g
    }


}
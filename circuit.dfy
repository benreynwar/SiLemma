module Circuit {

    import SeqNatToNat
    import opened Std.Wrappers

    newtype CPort = nat
    const INPUT_PORT: CPort := 0
    const OUTPUT_PORT: CPort := 1

    // A node in the graph.
    newtype CNode = nat

    // A library of circuits.
    // Subcircuits are pointers into this library.
    // This is really just so we can test for equality.
    // TODO: Should NodeKinds also go in here?  Maybe just CComb.
    datatype CLib = CLib(Circuits: seq<Circuit>)

    // A pointer into CLib.
    newtype CircuitRef = nat

    datatype CNodeKind = 
        // A hierarchical node so we can design hierarchically.
      | CHier(CRef: CircuitRef)
        // A node representing combinatorial logic.
      | CComb(
          IPorts: set<CPort>,
          OPorts: set<CPort>,
          PathExists: (CPort, CPort) -> bool,
          Behav: map<CPort, bool> -> Option<map<CPort, bool>>
        )
        // A contant 0 or 1
      | CConst(value: bool)
        // An input to the circuit.
      | CInput()
        // An output from the circuit.
      | COutput()
        // A register.
      | CSeq()

    function GetSubcircuit(lib: CLib, cr: CircuitRef): Option<Circuit>
    {
        if cr as nat >= |lib.Circuits| then
            None
        else
            Some(lib.Circuits[cr as nat])
    }

    function DirectCRefs(lib: CLib, c: Circuit): (r: set<CircuitRef>)
        requires CircuitValid(lib, c)
        ensures forall x: CircuitRef :: x in r ==> x as nat < |lib.Circuits|
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, c);
        assert forall i: CNode ::
            i < c.NodeBound && c.NodeKind(i).Some? && c.NodeKind(i).value.CHier? ==>
            var nk := c.NodeKind(i).value;
            CNodeKindValid(lib, c, nk);
        (set i: CNode | i < c.NodeBound && c.NodeKind(i).Some? && c.NodeKind(i).value.CHier? :: c.NodeKind(i).value.CRef)
    }

    ghost function HierCRefsInternal(lib: CLib, hier_level: nat, new_crefs: set<CircuitRef>, old_crefs: set<CircuitRef>): (r: set<CircuitRef>)
        requires forall x: CircuitRef :: x in old_crefs ==> x as nat < |lib.Circuits|
        requires forall x: CircuitRef :: x in new_crefs ==> x as nat < |lib.Circuits|
        requires forall x :: x in new_crefs ==> lib.Circuits[x].HierLevel < hier_level
        requires forall x :: x in new_crefs ==> CircuitValid(lib, lib.Circuits[x])
        ensures forall x :: x in r ==> x as nat < |lib.Circuits|
        decreases hier_level, 0, |new_crefs|
    {
        if |new_crefs| == 0 then
            old_crefs
        else
            var y: CircuitRef :| y in new_crefs;
            var expanded := HierCRefs(lib, lib.Circuits[y]);
            HierCRefsInternal(lib, hier_level, new_crefs - {y}, old_crefs + expanded)
    }

    ghost function HierCRefs(lib: CLib, c: Circuit): (r: set<CircuitRef>)
        requires CircuitValid(lib, c)
        ensures forall x :: x in r ==> x as nat < |lib.Circuits|
        decreases c.HierLevel, 1
    {
        var direct := DirectCRefs(lib, c);
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, c);
        HierCRefsInternal(lib, c.HierLevel, direct, direct)
    }
    
    //lemma HierPathCRefInHierCRefs(lib: CLib, c: Circuit, hp: HierarchyPath)
    //    requires CircuitValid(lib, c)
    //    requires HierarchyPathValid(lib, c, hp)
    //    ensures HPLength(hp) > 0 ==> HierarchyPathCRef(lib, c, hp).value in HierCRefs(lib, c)
    //{
    //}

    function HPNPtoNK(lib: CLib, c: Circuit, hpnp: HPNP): (r: CNodeKind)
        requires CircuitValid(lib, c)
        requires HPNPValid(lib, c, hpnp)
        ensures
            reveal HPNPValidInput();
            reveal HPNPValidOutput();
            var hp_c := HierarchyPathCircuit(lib, c, hpnp.hpn.hp);
            var nk := HPNPtoNK(lib, c, hpnp);
            CNodeKindValid(lib, hp_c, nk)
    {
        HPNPValidHPValid(lib, c, hpnp);
        var hp_c := HierarchyPathCircuit(lib, c, hpnp.hpn.hp);
        HierarchyPathCircuitValid(lib, c, hpnp.hpn.hp);
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var nk := hp_c.NodeKind(hpnp.hpn.n).value;
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, hp_c);
        assert CNodeKindValid(lib, hp_c, nk);
        nk
    }


    function HPNPtoSubcircuit(lib: CLib, c: Circuit, hpnp: HPNP): Circuit
        requires CircuitValid(lib, c)
        requires HPNPValid(lib, c, hpnp)
        requires HPNPtoNK(lib, c, hpnp).CHier?
    {
        var nk := HPNPtoNK(lib, c, hpnp);
        HPNPValidHPValid(lib, c, hpnp);
        var hp_c := HierarchyPathCircuit(lib, c, hpnp.hpn.hp);
        assert CNodeKindValid(lib, hp_c, nk);
        lib.Circuits[nk.CRef]
    }

    function NodeToSubcircuit(lib: CLib, c: Circuit, n: CNode): Circuit
        requires c.NodeKind(n).Some?
        requires c.NodeKind(n).value.CHier?
        requires c.NodeKind(n).value.CRef as nat < |lib.Circuits|
    {
        lib.Circuits[c.NodeKind(n).value.CRef]
    }

    function IPorts(lib: CLib, nk: CNodeKind): set<CPort>
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(cr) =>
            var maybe_c := GetSubcircuit(lib, cr);
            (match maybe_c
            case None => {}
            case Some(subc) => set n | n < subc.NodeBound && subc.NodeKind(n) == Some(CInput) :: n as CPort
            )
        case CComb(iports, oports, path_exists, behav) => iports
        case CInput() => {}
        case CConst(v) => {}
        case COutput() => {0 as CPort}
        case CSeq() => {0 as CPort}
    }

    predicate IsIPort(lib: CLib, nk: CNodeKind, p: CPort)
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(cr) =>
            var maybe_c := GetSubcircuit(lib, cr);
            (match maybe_c
            case None() => false
            case Some(subc) => subc.NodeKind(p as CNode) == Some(CInput)
            )
        case CComb(iports, oports, path_exists, behav) => p in iports
        case CInput() => false
        case CConst(v) => false
        case COutput() => p == INPUT_PORT as CPort
        case CSeq() => p == INPUT_PORT as CPort
    }

    function OPorts(lib: CLib, nk: CNodeKind): set<CPort>
    {
        match nk
        case CHier(cr) =>
            var maybe_c := GetSubcircuit(lib, cr);
            (match maybe_c
            case None() => {}
            case Some(subc) => set n | n < subc.NodeBound && subc.NodeKind(n) == Some(COutput) :: n as CPort
            )
        case CComb(iports, oports, path_exists, behav) => oports
        case CInput() => {0 as CPort}
        case COutput() => {}
        case CConst(v) => {0 as CPort}
        case CSeq() => {0 as CPort}
    }

    predicate IsOPort(lib: CLib, nk: CNodeKind, p: CPort)
    {
        match nk
        // The port numbers of a hierarical block and just the node ids of
        // the input and output nodes.
        case CHier(cr) =>
            var maybe_c := GetSubcircuit(lib, cr);
            (match maybe_c
            case None() => false
            case Some(subc) => subc.NodeKind(p as CNode) == Some(COutput)
            )
        case CComb(iports, oports, path_exists, behav) => p in oports
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

    predicate {:opaque} HPNPValidInput(lib: CLib, c: Circuit, hpnp: HPNP)
        requires CircuitValid(lib, c)
    {
        HierarchyPathValid(lib, c, hpnp.hpn.hp) &&
        var hp_c := HierarchyPathCircuit(lib, c, hpnp.hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpnp.hpn.n);
        maybe_nk.Some? &&
        IsIPort(lib, maybe_nk.value, hpnp.p)
    }

    lemma HPNPValidHPValid(lib: CLib, c: Circuit, hpnp: HPNP)
        requires CircuitValid(lib, c)
        requires HPNPValid(lib, c, hpnp)
        ensures HierarchyPathValid(lib, c, hpnp.hpn.hp)
    {
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
    }


    predicate {:opaque} HPNPValidOutput(lib: CLib, c: Circuit, hpnp: HPNP)
        requires CircuitValid(lib, c)
    {
        HierarchyPathValid(lib, c, hpnp.hpn.hp) &&
        var hp_c := HierarchyPathCircuit(lib, c, hpnp.hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpnp.hpn.n);
        maybe_nk.Some? &&
        IsOPort(lib, maybe_nk.value, hpnp.p)
    }

    predicate HPNPValid(lib: CLib, c: Circuit, hpnp: HPNP)
        requires CircuitValid(lib, c)
    {
        HPNPValidInput(lib, c, hpnp) ||
        HPNPValidOutput(lib, c, hpnp)
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

    function HierarchyPathCRef(lib: CLib, c: Circuit, hp: HierarchyPath): (r: Option<CircuitRef>)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        decreases |hp.v|, 1
    {
        if HPLength(hp) == 0 then
            None
        else
            var tail := HPTail(hp);
            var n := HPHead(hp);
            assert HierarchyPathValid(lib, c, tail);
            var tail_c := HierarchyPathCircuit(lib, c, tail);
            HierarchyPathCircuitValid(lib, c, tail);
            assert CircuitValid(lib, tail_c);
            reveal CircuitValid();
            var nk := tail_c.NodeKind(n).value;
            assert CircuitNodeKindValid(lib, tail_c);
            assert CNodeKindValid(lib, tail_c, nk);
            Some(tail_c.NodeKind(n).value.CRef)
    }

    function HierarchyPathCircuit(lib: CLib, c: Circuit, hp: HierarchyPath): (r: Circuit)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        decreases |hp.v|, 1
    {
        if HPLength(hp) == 0 then
            c
        else
            var tail := HPTail(hp);
            var n := HPHead(hp);
            assert HierarchyPathValid(lib, c, tail);
            var tail_c := HierarchyPathCircuit(lib, c, tail);
            HierarchyPathCircuitValid(lib, c, tail);
            //var cref := tail_c.NodeKind(n).value.CRef;
            //tail_c.Subcircuits[cref]
            assert CircuitValid(lib, tail_c);
            var nk := tail_c.NodeKind(n).value;
            reveal CircuitValid();
            assert CircuitNodeKindValid(lib, tail_c);
            assert CNodeKindValid(lib, tail_c, nk);
            var cref := tail_c.NodeKind(n).value.CRef;
            assert GetSubcircuit(lib, cref).Some?;
            assert cref as nat < |lib.Circuits|;
            NodeToSubcircuit(lib, tail_c, n)
    }

    lemma HierarchyPathCircuitValid(lib: CLib, c: Circuit, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        ensures CircuitValid(lib, HierarchyPathCircuit(lib, c, hp))
        decreases |hp.v|
    {
        if HPLength(hp) == 0 {
            assert HierarchyPathCircuit(lib, c, hp) == c;
        } else {
            var tail := HPTail(hp);
            assert HierarchyPathValid(lib, c, tail);
            var tail_c := HierarchyPathCircuit(lib, c, tail);
            HierarchyPathCircuitValid(lib, c, tail);
            assert CircuitValid(lib, tail_c);
            reveal CircuitValid();
            assert CircuitNodeKindValid(lib, tail_c);
            var hp_c := HierarchyPathCircuit(lib, c, hp);
            assert CircuitValid(lib, hp_c);
        }
    }

    predicate HierarchyPathValid(lib: CLib, c: Circuit, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        decreases |hp.v|, 0
    {
        if HPLength(hp) == 0 then
            true
        else
            var (head, tail) := HPHeadTail(hp);
            HierarchyPathValid(lib, c, tail) &&
            var hp_c := HierarchyPathCircuit(lib, c, tail);
            hp_c.NodeKind(head).Some? && hp_c.NodeKind(head).value.CHier?
    }

    ghost predicate HPNodeValid(lib: CLib, c: Circuit, hpn: HPNode)
        requires CircuitValid(lib, c)
    {
        HierarchyPathValid(lib, c, hpn.hp) &&
        var hp_c := HierarchyPathCircuit(lib, c, hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpn.n);
        HierarchyPathValid(lib, c, hpn.hp) && maybe_nk.Some?
    }

    ghost predicate HPNodeIsLeaf(lib: CLib, c: Circuit, hpn: HPNode)
        requires CircuitValid(lib, c)
        requires HPNodeValid(lib, c, hpn)
    {
        var hp_c := HierarchyPathCircuit(lib, c, hpn.hp);
        var maybe_nk := hp_c.NodeKind(hpn.n);
        !maybe_nk.value.CHier?
    }

    function ExtendHierarchyPath(lib: CLib, c: Circuit, hp: HierarchyPath, n: CNode): (r: HierarchyPath)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        requires HierarchyPathCircuit(lib, c, hp).NodeKind(n).Some?
        requires HierarchyPathCircuit(lib, c, hp).NodeKind(n).value.CHier?
        ensures HierarchyPathValid(lib, c, r)
    {
        var hp_c := HierarchyPathCircuit(lib, c, hp);
        HierarchyPathCircuitValid(lib, c, hp);
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, hp_c);
        var next_c := NodeToSubcircuit(lib, hp_c, n);
        assert CircuitValid(lib, next_c);
        HP(hp.v +[n])
    }

    function CompleteHierarchyPath(lib: CLib, c: Circuit, hp: HierarchyPath, n: CNode): (r: HPNode)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        requires HierarchyPathCircuit(lib, c, hp).NodeKind(n).Some?
        requires !HierarchyPathCircuit(lib, c, hp).NodeKind(n).value.CHier?
        ensures HPNodeValid(lib, c, r)
    {
        HPNode(hp, n)
    }

    ghost predicate CNodeKindValid(lib: CLib, c: Circuit, nk: CNodeKind)
        decreases c.HierLevel, 0
    {
        (
        match nk
        case CHier(lower_cref) =>
            GetSubcircuit(lib, lower_cref).Some? &&
            var lower_c := GetSubcircuit(lib, lower_cref).value;
            (lower_c.HierLevel < c.HierLevel) &&
            CircuitValid(lib, lower_c)
        case CComb(iports, oports, path_exists, behav) =>
          (forall a: CPort, b: CPort ::
              (a !in iports ==> !nk.PathExists(a, b)) &&
              (b !in oports ==> !nk.PathExists(a, b)))
          &&
          (forall a: CPort ::
              !(a in iports && a in oports))
        case _ => true
        ) && (
            forall p: CPort ::
                (IsIPort(lib, nk, p) ==> p < c.PortBound) &&
                (IsOPort(lib, nk, p) ==> p < c.PortBound) &&
                !(IsIPort(lib, nk, p) && IsOPort(lib, nk, p))
        )
    }

    ghost predicate CircuitPortSourceValid(lib: CLib, c: Circuit)
    {
        // For all possible ports.
        // If the port is not a valid output port then PortSource should give None.0
        // If the port is a valid output port then it should lead to a valid input
        // port.
        forall n: CNode ::
            forall p: CPort ::
                var inp := NP(n, p);
                if NPValidInput(lib, c, inp) then
                    match c.PortSource(inp)
                    // It's ok if it doesn't connect to anything.
                    // We consider that a valid circuit, but not a complete circuit.
                    // That way we can build a circuit but it is still valid.
                    case None => true
                    case Some(onp) => NPValidOutput(lib, c, onp)
                else
                    c.PortSource(inp) == None
    }

    ghost predicate CircuitPortSourceComplete(lib: CLib, c: Circuit)
        requires CircuitPortSourceValid(lib, c)
    {
        forall n: CNode ::
            forall p: CPort ::
                var inp := NP(n, p);
                if NPValidInput(lib, c, inp) then
                    match c.PortSource(inp)
                    case None => false
                    case Some(onp) => NPValidOutput(lib, c, onp)
                else
                    assert c.PortSource(inp) == None;
                    true
    }

    ghost predicate CircuitNodeKindValid(lib: CLib, c: Circuit)
        decreases  c.HierLevel, 1
    {
        (
            forall n: CNode ::
                var maybe_nk := c.NodeKind(n);
                if maybe_nk.None? then
                    true
                else
                    CNodeKindValid(lib, c, maybe_nk.Extract())
        ) && (
            forall n: CNode :: n >= c.NodeBound ==> c.NodeKind(n) == None
        )

    }

    ghost predicate {:opaque} CircuitValid(lib: CLib, c: Circuit)
        decreases  c.HierLevel, 2
    {
        CircuitNodeKindValid(lib, c) &&
        CircuitPortSourceValid(lib, c)
    }

    ghost predicate NPValid(lib: CLib, c: Circuit, np: NP)
    {
        NPValidInput(lib, c, np) || NPValidOutput(lib, c, np)
    }

    ghost predicate NPValidInput(lib: CLib, c: Circuit, np: NP)
    {
        match c.NodeKind(np.n)
        // The node doesn't exist.
        case None => false
        case Some(nk) => IsIPort(lib, nk, np.p)
    }

    ghost predicate NPValidOutput(lib: CLib, c: Circuit, np: NP)
    {
        match c.NodeKind(np.n)
        case None => false
        case Some(nk) => IsOPort(lib, nk, np.p)
    }

    ghost predicate {:opaque} CircuitComplete(lib: CLib, c: Circuit)
        requires CircuitValid(lib, c)
        decreases c.HierLevel
    {
        (forall inp: NP :: NPValid(lib, c, inp) ==> c.PortSource(inp).Some?) &&
        (forall n: CNode :: c.NodeKind(n).Some? && c.NodeKind(n).value.CHier? ==>
            var subcref := c.NodeKind(n).value.CRef;
            (subcref as nat < |lib.Circuits|) &&
            var subc := lib.Circuits[subcref];
            CircuitValid(lib, subc) &&
            (subc.HierLevel < c.HierLevel) &&
            CircuitComplete(lib, subc)
        )
    }

    lemma HPCircuitComplete(lib: CLib, c: Circuit, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        requires CircuitComplete(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        ensures
            var hp_c := HierarchyPathCircuit(lib, c, hp);
            CircuitValid(lib, hp_c) &&
            CircuitComplete(lib, hp_c)
        decreases |hp.v|
    {
        if |hp.v| == 0 {
        } else {
            var (head, tail) := HPHeadTail(hp);
            reveal CircuitComplete();
            HPCircuitComplete(lib, c, tail);
        }
    }

    lemma HierLevelDecreases(lib: CLib, c: Circuit, n: CNode)
        requires c.NodeKind(n).Some?
        requires c.NodeKind(n).value.CHier?
        requires
            CircuitValid(lib, c)
        ensures c.NodeKind(n).value.CRef as nat < |lib.Circuits|
        ensures NodeToSubcircuit(lib, c, n).HierLevel < c.HierLevel
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, c);
    }

    lemma SubCircuitValid(lib: CLib, c: Circuit, n: CNode)
        requires
            var maybe_nk := c.NodeKind(n);
            (maybe_nk.Some?) &&
            var nk := maybe_nk.Extract();
            (nk.CHier?)
        requires
            CircuitValid(lib, c)
        ensures c.NodeKind(n).value.CRef as nat < |lib.Circuits|
        ensures CircuitValid(lib, NodeToSubcircuit(lib, c, n))
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, c);
    }

    function {:vcs_split_on_every_assert} HPINPtoHPONP(lib: CLib, c: Circuit, hpinp: HPNP) : (r: Option<HPNP>)
        requires CircuitValid(lib, c)
        requires HPNPValidInput(lib, c, hpinp)
        ensures r.None? || HPNPValid(lib, c, r.value)
    {
        var hp := hpinp.hpn.hp;
        HPNPValidHPValid(lib, c, hpinp);
        var parent_c := HierarchyPathCircuit(lib, c, hp);
        HierarchyPathCircuitValid(lib, c, hp);
        assert CircuitValid(lib, parent_c);
        reveal HPNPValidOutput();
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, parent_c);
        assert CircuitPortSourceValid(lib, parent_c);
        var inp := NP(hpinp.hpn.n, hpinp.p);
        reveal HPNPValidInput();
        assert NPValidInput(lib, parent_c, inp);
        var maybe_onp: Option<NP> := parent_c.PortSource(inp);
            match maybe_onp
            // The input port does not connect to anything.
            case None => None
            // The input port does connect.
            case Some(onp) =>
                assert NPValid(lib, parent_c, onp);
                assert NPValidOutput(lib, parent_c, onp);
                var nk := parent_c.NodeKind(onp.n);
                assert nk.Some?;
                assert IsOPort(lib, nk.value, onp.p);
                var hpn := HPNode(hp, onp.n);
                var hpnp := HPNP(hpn, onp.p);
                reveal HPNPValidOutput();
                assert HPNPValidOutput(lib, c, hpnp);
                Some(hpnp)
    }

    function HPNodeToNK(lib: CLib, c: Circuit, hpn: HPNode): CNodeKind
        requires CircuitValid(lib, c)
        requires HPNodeValid(lib, c, hpn)
    {
        HierarchyPathCircuit(lib, c, hpn.hp).NodeKind(hpn.n).value
    }

    function MaxSubcircuitNodeBoundInternal(lib: CLib, c: Circuit, n: CNode, max: nat): nat
        requires CircuitValid(lib, c)
        decreases c.HierLevel, 0, n
    {
        var new_max := if n == 0 then max else MaxSubcircuitNodeBoundInternal(lib, c, n-1, max);
        match c.NodeKind(n)
            case Some(CHier(_)) =>
                HierLevelDecreases(lib, c, n);
                SubCircuitValid(lib, c, n);
                var next_c := NodeToSubcircuit(lib, c, n);
                var nb := CircuitMaxNodeBound(lib, next_c) as nat;
                if nb > new_max then max else nb
            case _ => new_max
    }

    function MaxSubcircuitNodeBound(lib: CLib, c: Circuit): nat
        requires CircuitValid(lib, c)
        decreases c.HierLevel, 1
    {
        MaxSubcircuitNodeBoundInternal(lib, c, c.NodeBound, 0)
    }

    function CircuitMaxNodeBound(lib: CLib, c: Circuit): nat
        requires CircuitValid(lib, c)
        decreases c.HierLevel, 2
    {
        // The local NodeBound get expanded.
        var subcircuit_nb := MaxSubcircuitNodeBound(lib, c);
        // Just combine the max node bound on this level with the max node bound on the next level
        SeqNatToNat.NatsToNat([c.NodeBound as nat, subcircuit_nb as nat])
    }

    //function Subcircuits(c: Circuit): seq<Circuit>
    //{
    //    seq(n requires 0 <= n < c.NodeBound | c.NodeKind(n).Some? && c.NodeKind(n).value.CHier? :: c.NodeKind(n).value.Circuit)
    //}

    //function MaxSubcircuitMaxPortBoundInternal(lib: CLib, c: Circuit, n: CNode, max: nat): nat
    //    requires CircuitValid(lib, c)
    //    decreases c.HierLevel, 0, n
    //{
    //    var new_max := if n == 0 then max else MaxSubcircuitMaxPortBoundInternal(lib, c, n-1, max);
    //    match c.NodeKind(n)
    //        case Some(CHier(_)) =>
    //            HierLevelDecreases(lib, c, n);
    //            SubCircuitValid(lib, c, n);
    //            var next_c := NodeToSubcircuit(lib, c, n);
    //            var nb := CircuitMaxPortBound(lib, next_c);
    //            if nb > new_max then max else nb
    //        case _ => new_max
    //}

    //function MaxSubcircuitMaxPortBound(lib: CLib, c: Circuit): nat
    //    requires CircuitValid(lib, c)
    //    decreases c.HierLevel, 1
    //{
    //    MaxSubcircuitMaxPortBoundInternal(lib, c, c.NodeBound, 0)
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

    ghost function CircuitMaxPortBound(lib: CLib, c: Circuit): nat
        requires CircuitValid(lib, c)
        decreases c.HierLevel, 2
    {
        var crefs: set<CircuitRef> := HierCRefs(lib, c);
        var port_bounds := (set cref: CircuitRef | cref in crefs :: lib.Circuits[cref].PortBound as nat);
        if |port_bounds| == 0 then
            c.PortBound as nat
        else
            var max_hier_port_bound := MaxInSet(port_bounds);
            if c.PortBound as nat > max_hier_port_bound then c.PortBound as nat else max_hier_port_bound
    }

    function GetC(lib: CLib, cref: CircuitRef): Circuit
        requires cref as nat < |lib.Circuits|
    {
        lib.Circuits[cref]
    }

    predicate CRefValid(lib: CLib, cref: CircuitRef)
    {
        cref as nat < |lib.Circuits|
    }

    ghost predicate CRefCircuitValid(lib: CLib, cref: CircuitRef)
    {
        (cref as nat < |lib.Circuits|) &&
        CircuitValid(lib, lib.Circuits[cref])
    }

    //lemma PortBoundWithinMaxPortBound(lib: CLib, c: Circuit, hp: HierarchyPath)
    //    requires CircuitValid(lib, c)
    //    requires HierarchyPathValid(lib, c, hp)
    //    ensures
    //        var hier_c := HierarchyPathCircuit(lib, c, hp);
    //        var max_port_bound := CircuitMaxPortBound(lib, c);
    //        hier_c.PortBound as nat <= max_port_bound
    //{
    //    var all_crefs := HierCRefs(lib, c);
    //    var maybe_hier_cref := HierarchyPathCRef(lib, c, hp);
    //    assert maybe_hier_cref.None? || maybe_hier_cref.value in all_crefs;

    //}

    //ghost predicate HPPortInBound(lib: CLib, c: Circuit, hp: HierarchyPath)
    //    requires CircuitValid(lib, c)
    //    requires HierarchyPathValid(lib, c, hp)
    //{
    //    var hier_c := HierarchyPathCircuit(lib, c, hp);
    //    HierarchyPathCircuitValid(lib, c, hp);
    //    CircuitMaxPortBound(lib, hier_c) <= CircuitMaxPortBound(lib, c)
    //}

    //lemma PortBounds(lib: CLib, c: Circuit, hp: HierarchyPath)
    //    requires CircuitValid(lib, c)
    //    requires HierarchyPathValid(lib, c, hp)
    //    ensures HPPortInBound(lib, c, hp)
    //    decreases HPLength(hp)
    //{
    //    if HPLength(hp) == 0 {
    //    } else {
    //        var hier_c := HierarchyPathCircuit(lib, c, hp);
    //        HierarchyPathCircuitValid(lib, c, hp);
    //        var (head, tail) := HPHeadTail(hp);
    //        var tail_c := HierarchyPathCircuit(lib, c, tail);
    //        HierarchyPathCircuitValid(lib, c, tail);
    //        assert MaxSubcircuitMaxPortBound(lib, tail_c) >= CircuitMaxPortBound(lib, hier_c);
    //        assert CircuitMaxPortBound(lib, tail_c) >= CircuitMaxPortBound(lib, hier_c);
    //        PortBounds(lib, c, tail);
    //    }
    //}

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
        var xor_output := NP(node_xor, 0);
        var g := AddOPort(g, xor_output);
        var (g, node_add) := AddNode(g, AndCNode, map[0 := i_0, 1 := i_1]);
        var add_output := NP(node_add, 0);
        var g := AddOPort(g, add_output);
        g
    }


}
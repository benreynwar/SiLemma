module CircuitHierarchy {

    import opened CircuitBase

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
            NodeKind(hp_c, head).Some? && NodeKind(hp_c, head).value.CHier?
    }

    predicate HierarchyPathValidR(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        decreases |hp.v|, 0
    {
        if HPLength(hp) == 0 then
            true
        else
            var (start, children) := HPStartChildren(hp);
            NodeKind(c, start).Some? && NodeKind(c, start).value.CHier? &&
            reveal CircuitValid();
            assert CircuitNodeKindValid(c);
            var next_c := NodeKind(c, start).value.c;
            HierarchyPathValid(next_c, children)
    }

    lemma HPValidEquivalence(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c) 
        ensures HierarchyPathValid(c, hp) == HierarchyPathValidR(c, hp)
    {
    }

    ghost function AllValidHierarchyPathsInSubcircuits(
            c: Circuit, nodes: set<CNode>): (r: set<HierarchyPath>)
        requires CircuitValid(c)
        requires forall n :: n in nodes ==>
            NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
        ensures forall hp :: hp in r ==> HierarchyPathValid(c, hp)
        decreases c.HierLevel, 0
    {
        if |nodes| == 0 then
            {}
        else
            var n :| n in nodes;
            var nk := NodeKind(c, n).value;
            var hp_c := nk.c;
            reveal CircuitValid();
            assert CircuitNodeKindValid(c);
            assert CircuitValid(hp_c);
            var hps := AllValidHierarchyPaths(hp_c);
            //var (head, tail) := HPHeadTail(hp);
            //HierarchyPathValid(c, tail) &&
            //var hp_c := HierarchyPathCircuit(c, tail);
            //NodeKind(hp_c, head).Some? && NodeKind(hp_c, head).value.CHier?
            var r := (set hp | hp in hps :: HP(hp.v + [n]));
            assert forall hp :: hp in r ==> HPHead(hp) == n;
            assert forall hp :: hp in r ==> HierarchyPathValid(hp_c, HPTail(hp));
            assert forall hp :: hp in r ==> HierarchyPathValid(c, hp);
            r
    }

    ghost function AllValidHierarchyPaths(c: Circuit): (r: set<HierarchyPath>)
        requires CircuitValid(c)
        ensures forall hp :: hp in r ==> HierarchyPathValid(c, hp)
        decreases c.HierLevel, 1
    {
        if c.HierLevel == 0 then
            {HP([])}
        else
            var all_subcircuit_nodes := (set n | n in c.NodeKind && c.NodeKind[n].CHier? :: n);
            AllValidHierarchyPathsInSubcircuits(c, all_subcircuit_nodes)
    }

    function HPLength(hp: HierarchyPath): nat
    {
        |hp.v|
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
            var nk := NodeKind(tail_c, n).value;
            reveal CircuitValid();
            assert CircuitNodeKindValid(tail_c);
            assert CNodeKindValid(tail_c.HierLevel, nk);
            NodeToSubcircuit(tail_c, n)
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

    function NodeToSubcircuit(c: Circuit, n: CNode): Circuit
        requires NodeKind(c, n).Some?
        requires NodeKind(c, n).value.CHier?
    {
        NodeKind(c, n).value.c
    }

    predicate {:opaque} HPNodeValid(c: Circuit, hpn: HPNode)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpn.hp);
        var maybe_nk := NodeKind(hp_c, hpn.n);
        maybe_nk.Some?
    }

    ghost function AllValidHPNodesFromHPs(c: Circuit, hps: set<HierarchyPath>): (r: set<HPNode>)
        requires CircuitValid(c)
        requires forall hp :: hp in hps ==> HierarchyPathValid(c, hp)
        ensures forall hpn :: hpn in r ==> HPNodeValid(c, hpn)
    {
        if |hps| == 0 then
            {}
        else
            var hp :| hp in hps;
            var next_hps := hps - {hp};
            var next_hpns := AllValidHPNodesFromHPs(c, next_hps);
            var hp_c := HierarchyPathCircuit(c, hp);
            var this_hpns := (set n | n in hp_c.NodeKind :: HPNode(hp, n));
            assert forall hpn :: hpn in this_hpns ==> HPNodeValid(c, hpn);
            this_hpns + next_hpns
    }

    ghost function AllValidHPNodes(c: Circuit): (r: set<HPNode>)
        requires CircuitValid(c)
        ensures forall hpn :: hpn in r ==> HPNodeValid(c, hpn)
    {
        var hps := AllValidHierarchyPaths(c);
        AllValidHPNodesFromHPs(c, hps)
    }

    predicate {:opaque} HPNPValidInput(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpnp.hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        var maybe_nk := NodeKind(hp_c, hpnp.hpn.n);
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
        var maybe_nk := NodeKind(hp_c, hpnp.hpn.n);
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
        var nk := NodeKind(hp_c, hpnp.hpn.n).value;
        reveal CircuitValid();
        assert CircuitNodeKindValid(hp_c);
    }

    predicate HPNPValid(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HPNPValidInput(c, hpnp) ||
        HPNPValidOutput(c, hpnp)
    }


    function HPNPtoNK(c: Circuit, hpnp: HPNP): (r: CNodeKind)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures
            reveal HPNPValidInput();
            reveal HPNPValidOutput();
            var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
            var nk := HPNPtoNK(c, hpnp);
            CNodeKindValid(hp_c.HierLevel, nk)
    {
        HPNPValidHPValid(c, hpnp);
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        HierarchyPathCircuitValid(c, hpnp.hpn.hp);
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var nk := NodeKind(hp_c, hpnp.hpn.n).value;
        CircuitValidCNodeKindValid(hp_c, hpnp.hpn.n);
        nk
    }

    lemma CircuitValidCNodeKindValid(c: Circuit, n: CNode)
        requires CircuitValid(c)
        requires NodeKind(c, n).Some?
        ensures CNodeKindValid(c.HierLevel, NodeKind(c, n).value)
    {
        reveal CircuitValid();
    }
    ghost predicate {:opaque} CircuitComplete(c: Circuit)
        requires CircuitValid(c)
        decreases c.HierLevel
    {
        (forall inp: NP :: NPValidInput(c, inp) ==> PortSource(c, inp).Some?) &&
        (forall n: CNode :: NodeKind(c, n).Some? && NodeKind(c, n).value.CHier? ==>
            var subc := NodeKind(c, n).value.c;
            CircuitValid(subc) &&
            (subc.HierLevel < c.HierLevel) &&
            CircuitComplete(subc)
        )
    }

    function DirectSubcircuits(c: Circuit): (r: set<Circuit>)
        requires CircuitValid(c)
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        assert forall i: CNode ::
            NodeKind(c, i).Some? && NodeKind(c, i).value.CHier? ==>
            var nk := NodeKind(c, i).value;
            CNodeKindValid(c.HierLevel, nk);
        (set n: CNode | n in c.NodeKind && c.NodeKind[n].CHier? :: c.NodeKind[n].c)
    }

    predicate HPNodeInCircuit(c: Circuit, hpn: HPNode)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hpn.hp)
    {
        var hpc := HierarchyPathCircuit(c, hpn.hp);
        HierarchyPathCircuitValid(c, hpn.hp);
        NodeKind(hpc, hpn.n).Some?
    }

    function HPNodeToHPNP(c: Circuit, hpn: HPNode): set<HPNP>
        requires CircuitValid(c)
        requires HPNodeValid(c, hpn)
    {
        reveal HPNodeValid();
        var hpc := HierarchyPathCircuit(c, hpn.hp);
        HierarchyPathCircuitValid(c, hpn.hp);
        var nk := NodeKind(hpc, hpn.n).value;
        var ports := IPorts(nk) + OPorts(nk);
        set p: CPort | p in ports :: HPNP(hpn, p)
    }

    lemma HPLengthBound(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures
            var hier_c := HierarchyPathCircuit(c, hp);
            HPLength(hp) <= (c.HierLevel - hier_c.HierLevel)
        decreases HPLength(hp)
    {
        if HPLength(hp) == 0 {
        } else {
            var hier_c := HierarchyPathCircuit(c, hp);
            var (head, tail) := HPHeadTail(hp);
            var tail_c := HierarchyPathCircuit(c, tail);
            var nk := NodeKind(tail_c, head).value;
            assert nk.CHier?;
            HierarchyPathCircuitValid(c, tail);
            assert CircuitValid(tail_c);
            reveal CircuitValid();
            assert CNodeKindValid(tail_c.HierLevel, nk);
            assert tail_c.HierLevel > hier_c.HierLevel;
            HPLengthBound(c, tail);
        }
    }

    function SeqCNodeToSeqNat(a: seq<CNode>): seq<nat>
    {
        seq(|a|, i requires 0 <= i < |a| => a[i] as nat)
    }


}
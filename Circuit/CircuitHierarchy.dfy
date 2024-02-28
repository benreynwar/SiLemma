module CircuitHierarchy {

    import opened CircuitBase
    import opened CircuitValidity

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
            var nk := tail_c.NodeKind(n).value;
            reveal CircuitValid();
            assert CircuitNodeKindValid(tail_c);
            assert CNodeKindValid(tail_c.HierLevel, tail_c.PortBound, nk);
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
        requires c.NodeKind(n).Some?
        requires c.NodeKind(n).value.CHier?
    {
        c.NodeKind(n).value.c
    }

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

    lemma CircuitValidCNodeKindValid(c: Circuit, n: CNode)
        requires CircuitValid(c)
        requires c.NodeKind(n).Some?
        ensures CNodeKindValid(c.HierLevel, c.PortBound, c.NodeKind(n).value)
    {
        reveal CircuitValid();
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



}
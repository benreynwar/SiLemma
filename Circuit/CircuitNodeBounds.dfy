// Working to prove that HPNP are bounded.
module CircuitNodeBounds {

    import SeqExt
    import SeqNatToNat
    import opened Std.Wrappers
    import opened CircuitBase
    import opened CircuitHierarchy
    import Seq=Std.Collections.Seq

    lemma {:vcs_split_on_every_assert} HierBoundEncloses(
            c: Circuit, bound_f: Circuit -> nat, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures
            var hierc := HierarchyPathCircuit(c, hp);
            CircuitValid(hierc) &&
            HierBound(hierc, bound_f) <= HierBound(c, bound_f)
        decreases |hp.v|
    {
        var hierc := HierarchyPathCircuit(c, hp);
        HierarchyPathCircuitValid(c, hp);
        if |hp.v| == 0 {
            assert HierBound(hierc, bound_f) <= HierBound(c, bound_f);
        } else {
            var (head, tail) := HPHeadTail(hp);
            HierBoundEncloses(c, bound_f, tail);
            var tail_c := HierarchyPathCircuit(c, tail);
            HierarchyPathCircuitValid(c, tail);
            assert HierBound(tail_c, bound_f) <= HierBound(c, bound_f);
            assert HierBound(hierc, bound_f) <= HierBound(c, bound_f);
        }
    }

    lemma GetSubBoundsHelper(c: Circuit)
        requires CircuitValid(c)
        ensures forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subc := c.NodeKind(m).value.c;
            subc in DirectSubcircuits(c)
    {
        forall m: CNode | c.NodeKind(m).Some? && c.NodeKind(m).value.CHier?
            ensures
                var subc := c.NodeKind(m).value.c;
                subc in DirectSubcircuits(c)
        {
            SubcircuitInDirectSubcircuits(c, m);
        }

    }

    function GetSubBounds(c: Circuit, bound_f: Circuit -> nat): (r: seq<nat>)
        requires CircuitValid(c)
        ensures forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subc := c.NodeKind(m).value.c;
            CircuitValid(subc) &&
            subc.HierLevel < c.HierLevel &&
            HierBound(subc, bound_f) in r
        decreases c.HierLevel, 0
    {
        var subcs: seq<Circuit> := DirectSubcircuits(c);
        var new_bound := bound_f(c);
        AllSubcircuitsValid(c);
        var bounds := Seq.Map(
            subc requires CircuitValid(subc) && (subc.HierLevel < c.HierLevel)  =>
                HierBound(subc, bound_f),
            subcs);
        GetSubBoundsHelper(c);
        assert forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subc := c.NodeKind(m).value.c;
            assert subc in subcs;
            var index: nat :| index < |subcs| && subcs[index] == subc;
            (bounds[index] == HierBound(subc, bound_f)) &&
            (HierBound(subc, bound_f) in bounds);
        bounds
    }

    function {:vcs_split_on_every_assert} HierBound(c: Circuit, bound_f: Circuit -> nat): (r: nat)
        requires CircuitValid(c)
        ensures forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subc := c.NodeKind(m).value.c;
            CircuitValid(subc) &&
            subc.HierLevel < c.HierLevel &&
            HierBound(subc, bound_f) <= r
        ensures bound_f(c) as nat <= r
        decreases c.HierLevel, 1
    {
        var bounds := GetSubBounds(c, bound_f);
        var new_bound := bound_f(c);
        var combined_bounds := bounds + [new_bound];
        var max_bound := Seq.Max(combined_bounds);
        assert new_bound in combined_bounds;
        assert new_bound <= max_bound;
        var subcircuits := DirectSubcircuits(c);
        assert forall pb: nat :: pb in bounds+[new_bound] ==> pb <= max_bound;
        GetSubBoundsHelper(c);
        assert forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subc := c.NodeKind(m).value.c;
            (subc in subcircuits) && 
            (HierBound(subc, bound_f) in bounds + [new_bound]);
        assert forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subc := c.NodeKind(m).value.c;
            (HierBound(subc, bound_f) <= max_bound);
        max_bound
    }

    // Get a port bound
    // Show that port bound is bigger or equal to all circuit Port Bounds.

    // Port bound is determined recursively from the top Circuit.

    // Then we get a Subcircuit specified by a HP.
    // Prove that that it satisfies it by building the HP up from the start.

    function getpb(c: Circuit): nat
    {
        c.PortBound as nat
    }

    function getnb(c: Circuit): nat
    {
        c.NodeBound as nat
    }

    function HierPortBound(c: Circuit): nat
        requires CircuitValid(c)
    {
        HierBound(c, getpb)
    }

    function HierNodeBound(c: Circuit): nat
        requires CircuitValid(c)
    {
        HierBound(c, getnb)
    }

    lemma SubcircuitInHierPortBound(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures
            var hier_c := HierarchyPathCircuit(c, hp);
            hier_c.PortBound as nat <= HierPortBound(c)
    {
        HierBoundEncloses(c, getpb, hp);
    }


    lemma SubcircuitInHierNodeBound(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures
            var hier_c := HierarchyPathCircuit(c, hp);
            hier_c.NodeBound as nat <= HierNodeBound(c)
    {
        HierBoundEncloses(c, getnb, hp);
    }

    lemma HPInHierNodeBound(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures
            forall n: CNode :: (n in hp.v) ==> n as nat < HierNodeBound(c)
        decreases |hp.v|
    {
        if |hp.v| == 0 {
        } else {
            var (head, tail) := HPHeadTail(hp);
            var hier_c := HierarchyPathCircuit(c, hp);
            var tail_c := HierarchyPathCircuit(c, tail);
            HierarchyPathCircuitValid(c, tail);
            reveal CircuitValid();
            assert head <= tail_c.NodeBound;
            SubcircuitInHierNodeBound(c, tail);
            assert tail_c.NodeBound as nat <= HierNodeBound(c);
            HPInHierNodeBound(c, tail);
            assert head as nat <= HierNodeBound(c);
            assert forall n: CNode :: (n in tail.v) ==> n as nat < HierNodeBound(c);
            assert forall n: CNode :: (n in tail.v + [head]) ==> n as nat < HierNodeBound(c);
            assert tail.v + [head] == hp.v;
        }
    }

    // Show that the any valid hpnp is smaller than total bound

    function HPNPElementBound(c: Circuit): nat
        requires CircuitValid(c)
    {
        var max_node_index := HierNodeBound(c);
        var max_port_index := HierPortBound(c);
        var max_index := if max_node_index > max_port_index then max_node_index else max_port_index;
        max_index
    }

    lemma HPNPElementsInBound(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures
            forall n: CNode :: (n in hpnp.hpn.hp.v) ==> n as nat < HPNPElementBound(c)
        ensures hpnp.hpn.n as nat < HPNPElementBound(c)
        ensures hpnp.p as nat < HPNPElementBound(c)
    {
        var element_bound := HPNPElementBound(c);
        HPNPValidHPValid(c, hpnp);
        HPInHierNodeBound(c, hpnp.hpn.hp);
        var hier_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        HierarchyPathCircuitValid(c, hpnp.hpn.hp);
        SubcircuitInHierNodeBound(c, hpnp.hpn.hp);
        assert hier_c.NodeBound as nat <= element_bound;
        SubcircuitInHierPortBound(c, hpnp.hpn.hp);
        assert hier_c.PortBound as nat <= element_bound;
        reveal CircuitValid();
        assert CircuitNodeKindValid(hier_c);
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        assert hpnp.p < hier_c.PortBound;
        assert hpnp.hpn.n < hier_c.NodeBound;
    }

    function HPNPBound(c: Circuit): nat
        requires CircuitValid(c)
    {
        var max_index := HPNPElementBound(c);
        var ns := Seq.Repeat(max_index, c.HierLevel+2);
        SeqNatToNat.ArbLenNatsToNat(ns)
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



}
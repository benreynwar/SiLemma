module CircuitUtils {


    import opened CircuitBase
    import opened CircuitValidity
    import opened CircuitHierarchy
    import SeqNatToNat
    import opened Std.Wrappers
    import Std.Collections.Seq
    import SeqExt

    const MAX_HIERLEVEL := 128


    function CircuitIPorts(c: Circuit) : set<CNode>
    {
        set n | n < c.NodeBound && c.NodeKind(n) == Some(CInput)
    }

    function CircuitOPorts(c: Circuit) : set<CNode>
    {
        set n | n < c.NodeBound && c.NodeKind(n) == Some(COutput)
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

    function CompleteHierarchyPath(c: Circuit, hp: HierarchyPath, n: CNode): (r: HPNode)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        requires HierarchyPathCircuit(c, hp).NodeKind(n).Some?
        requires !HierarchyPathCircuit(c, hp).NodeKind(n).value.CHier?
        ensures HPNodeValid(c, r)
    {
        HPNode(hp, n)
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

    // Show that if there is a path in the Circuit there is a path in the HGraph.
    // Show that if there is not a path in the Circuit there is no path in the HGraph.



}
module CircuitPath {

    import opened Std.Wrappers
    import Seq = Std.Collections.Seq
    import Functions = Std.Functions
    import SeqNatToNat
    import SeqExt
    import opened Circuit
    import CircuitBounds
    import DG
    import Utils

    predicate {:opaque} HPNPOtoIConnected(c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, a)
        requires HPNPValidInput(c, b)
    {
        HPNPValidHPValid(c, a);
        var a_c := HierarchyPathCircuit(c, a.hpn.hp);
        var maybe_a_nk := a_c.NodeKind(a.hpn.n);
        match maybe_a_nk
        case None => false
        case Some(a_nk) =>
            match a_nk
            case CInput => (
                // This is an output from a CInput. It's not connected.
                if HPLength(a.hpn.hp) == 0 then
                    false
                else
                    var (hier_n, parent_hp) := HPHeadTail(a.hpn.hp);
                    // If it's an input inside a hier node, then it connects to
                    // the input port on the hier node on the next level up.
                    if parent_hp == b.hpn.hp then
                        var hier_inp := HPNP(HPNode(parent_hp, hier_n), a.hpn.n as CPort);
                        hier_inp == b
                    else
                        false
            )
            case CHier(_) => (
                reveal HPNPValidOutput();
                var lower_c := NodeToSubcircuit(a_c, a.hpn.n);
                // It's an output port from a hier node.
                // It only connects to the input into the corresponding Output node in that circuit.
                var maybe_level_nk := lower_c.NodeKind(a.p as CNode);
                match maybe_level_nk
                case Some(Output) =>
                    var new_hp := ExtendHierarchyPath(c, a.hpn.hp, a.hpn.n);
                    var hier_inp := HPNP(HPNode(new_hp, a.p as CNode), 0);
                    hier_inp == b 
                case _ => false
            )
            case CComb(_, _, path_exists, _, _) =>
                (a.hpn.hp == b.hpn.hp) &&
                (a.hpn.n == b.hpn.n) &&
                path_exists(a.p, b.p)
            case CReg => false
    }

    predicate {:opaque} HPNPItoOConnected(c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(c)
        requires HPNPValidInput(c, a)
        requires HPNPValidOutput(c, b)
    {
        HPNPValidHPValid(c, a);
        var a_c := HierarchyPathCircuit(c, a.hpn.hp);
        var inp := NP(a.hpn.n, a.p);
        var onp := NP(b.hpn.n, b.p);
        a_c.PortSource(inp) == Some(onp)
    }

    predicate {:opaque} HPNPConnected(c: Circuit,  a: HPNP, b: HPNP)
        requires CircuitValid(c)
    {
        (HPNPValidInput(c, a) && HPNPValidOutput(c, b) &&
            HPNPItoOConnected(c, a, b)) ||
        (HPNPValidOutput(c, a) && HPNPValidInput(c, b) &&
            HPNPOtoIConnected(c, a, b))
    }

    function HPNPToSeqNat(hpnp: HPNP): (r: seq<nat>)
    {
        var l := |hpnp.hpn.hp.v|;
        var hp_seq := SeqCNodeToSeqNat(hpnp.hpn.hp.v);
        hp_seq + [hpnp.hpn.n as nat, hpnp.p as nat]
    }

    function HPNPToNat(hpnp: HPNP): nat
    {
        var ns := HPNPToSeqNat(hpnp);
        SeqNatToNat.ArbLenNatsToNat(ns)
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
            var nk := tail_c.NodeKind(head).value;
            assert nk.CHier?;
            HierarchyPathCircuitValid(c, tail);
            assert CircuitValid(tail_c);
            reveal CircuitValid();
            assert CNodeKindValid(tail_c.HierLevel, tail_c.PortBound, nk);
            assert tail_c.HierLevel > hier_c.HierLevel;
            HPLengthBound(c, tail);
        }
    }

    function SeqCNodeToSeqNat(a: seq<CNode>): seq<nat>
    {
        seq(|a|, i requires 0 <= i < |a| => a[i] as nat)
    }

    lemma SeqCNodeNotEqualSeqNatNotEqual(a: seq<CNode>, b: seq<CNode>)
        ensures a != b ==> SeqCNodeToSeqNat(a) != SeqCNodeToSeqNat(b)
    {
        if a == b {
            assert forall i: nat :: i < |a| ==> a[i] == b[i];
        } else {
            if |a| == |b| {
                assert exists i: nat :: i < |a| && a[i] != b[i];
                var i: nat :| i < |a| && a[i] != b[i];
                assert SeqCNodeToSeqNat(a)[i] != SeqCNodeToSeqNat(b)[i];
            } else {
            }
        }
    }

    lemma HPNPToSeqNatUnique(a: HPNP, b: HPNP)
        ensures (a != b) ==> (HPNPToSeqNat(a) != HPNPToSeqNat(b))
    {
        var na := HPNPToSeqNat(a);
        var nb := HPNPToSeqNat(b);
        if (|a.hpn.hp.v| != |b.hpn.hp.v|) {
        } else {
            if (a != b) {
                var a_v := a.hpn.hp.v;
                var b_v := b.hpn.hp.v;
                if (a_v != b_v) {
                    assert |na| == |a_v| + 2;
                    assert a_v != b_v;
                    var a_v_n := SeqCNodeToSeqNat(a_v);
                    var b_v_n := SeqCNodeToSeqNat(b_v);
                    SeqCNodeNotEqualSeqNatNotEqual(a_v, b_v);
                    assert a_v_n != b_v_n;
                    assert na[..|a_v|] == a_v_n;
                    assert nb[..|b_v|] == b_v_n;
                } else if (a.hpn.n != b.hpn.n) {
                    assert na[|a_v|] == a.hpn.n as nat;
                } else if (a.p != b.p) {
                    assert na[|a_v|+1] == a.p as nat;
                } else {
                }
            } else {
            }
        }
    }

    lemma HPNPToNatInjective(a: HPNP, b: HPNP)
        ensures (a != b) ==> (HPNPToNat(a) != HPNPToNat(b))
    {
        HPNPToSeqNatUnique(a, b);
        SeqNatToNat.ArbLenNatsToNatUnique(HPNPToSeqNat(a), HPNPToSeqNat(b));
    }

    function {:opaque} CtoG(c: Circuit): (g: DG.Digraph<HPNP>)
        requires CircuitValid(c)
    {
        DG.Digraph(
            hpnp => HPNPValid(c, hpnp),
            (a, b) => HPNPConnected(c, a, b),
            HPNPToNat,
            CircuitBounds.HPNPBound(c)
        )
    }

    function CtoGV(c: Circuit): (g: DG.Digraph<HPNP>)
        requires CircuitValid(c)
        ensures DG.DigraphValid(g)
    {
        CtoGValid(c);
        CtoG(c)
    }
        

    lemma NoSelfConnections(c: Circuit, n: HPNP)
        requires CircuitValid(c)
        ensures !HPNPConnected(c, n, n)
    {
        reveal HPNPConnected();
        if HPNPValid(c, n) {
            HPNPValidHPValid(c, n);
            var hier_c := HierarchyPathCircuit(c, n.hpn.hp);
            HierarchyPathCircuitValid(c, n.hpn.hp);
            reveal CircuitValid();
            assert CircuitNodeKindValid(hier_c);
            if HPNPValidInput(c, n) {
                reveal HPNPValidInput();
                reveal HPNPValidOutput();
                assert !HPNPValidOutput(c, n);
                assert !HPNPConnected(c, n, n);
            } else {
            }
        } else {
            assert !HPNPValidInput(c, n);
            assert !HPNPValidOutput(c, n);
        }
    }

    lemma ConnectedNodesValid(c: Circuit, n: HPNP, m: HPNP)
        requires CircuitValid(c)
        ensures HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m)
    {
        reveal HPNPConnected();
    }

    lemma OutOfBoundInvalid(c: Circuit, n: HPNP)
        requires CircuitValid(c)
        ensures HPNPToNat(n) >= CircuitBounds.HPNPBound(c) ==> !HPNPValid(c, n)
    {
        if HPNPToNat(n) >= CircuitBounds.HPNPBound(c) {
            if HPNPValid(c, n) {
                HPNPInBound(c, n);
                assert HPNPToNat(n) < CircuitBounds.HPNPBound(c);
                assert false;
            } else {
            }
            assert !HPNPValid(c, n);
        }
    }

    lemma CtoGValid(c: Circuit)
        requires CircuitValid(c)
        ensures DG.DigraphValid(CtoG(c))
    {
        reveal CtoG();
        var g := CtoG(c);
        forall n: HPNP, m: HPNP
            ensures HPNPToNat(n) >= CircuitBounds.HPNPBound(c) ==> !HPNPValid(c, n)
            ensures !HPNPConnected(c, n, n)
            ensures HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m)
            ensures (n != m) ==> HPNPToNat(n) != HPNPToNat(m)
        {
            OutOfBoundInvalid(c, n);
            NoSelfConnections(c, n);
            ConnectedNodesValid(c, n, m);
            HPNPToNatInjective(n, m);
        }
        assert (forall n: HPNP :: HPNPToNat(n) >= CircuitBounds.HPNPBound(c) ==> !HPNPValid(c, n));
        assert (forall n: HPNP :: !HPNPConnected(c, n, n));
        assert (forall n: HPNP, m: HPNP :: HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m));
        assert (forall n: HPNP, m: HPNP :: n != m ==> HPNPToNat(n) != HPNPToNat(m));
        reveal DG.DigraphValid();
    }

    lemma HPNPAsSeqNatInBound(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures forall n: nat :: n in HPNPToSeqNat(hpnp) ==>
            n < CircuitBounds.HPNPElementBound(c)
    {
        CircuitBounds.HPNPElementsInBound(c, hpnp);
        var hpnp_as_seq := HPNPToSeqNat(hpnp);
        var element_bound := CircuitBounds.HPNPElementBound(c); 
        var hp := hpnp.hpn.hp;
        assert forall n: CNode :: n in hp.v ==> n as nat < element_bound;
        assert forall i: nat :: i < |hp.v| ==> (hp.v[i] in hp.v);
        assert forall i: nat :: i < |hp.v| ==> hp.v[i] as nat < element_bound;
        assert hpnp.hpn.n as nat < element_bound;
        assert hpnp.p as nat < element_bound;
        assert forall i: nat :: i < |hpnp_as_seq| ==>
            if i < |hp.v| then
                (hpnp_as_seq[i] == hp.v[i] as nat) &&
                (hp.v[i] as nat < element_bound) &&
                (hpnp_as_seq[i] < element_bound)
            else
                true;
        assert forall n: nat :: n in hpnp_as_seq ==> n < element_bound;
    }

    lemma HPNPInBound(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures HPNPToNat(hpnp) < CircuitBounds.HPNPBound(c)
    {
        var hpnp_as_seq := HPNPToSeqNat(hpnp);
        var element_bound := CircuitBounds.HPNPElementBound(c); 
        HPNPAsSeqNatInBound(c, hpnp);
        var len := |hpnp_as_seq|;
        var bound := SeqNatToNat.ArbLenNatsToNatBound(c.HierLevel+2, element_bound);
        assert bound == CircuitBounds.HPNPBound(c);
        assert forall n: nat :: n in hpnp_as_seq ==> n < element_bound;
        assert forall i: nat :: i < |hpnp_as_seq| ==> hpnp_as_seq[i] in hpnp_as_seq;
        assert forall i: nat :: i < |hpnp_as_seq| ==> hpnp_as_seq[i] < element_bound;
        HPNPValidHPValid(c, hpnp);
        HPLengthBound(c, hpnp.hpn.hp);
        assert HPLength(hpnp.hpn.hp) <= c.HierLevel;
        assert |hpnp_as_seq| <= c.HierLevel + 2;
        SeqNatToNat.ArbLenNatsToNatBounded(hpnp_as_seq, c.HierLevel+2, element_bound);
        assert SeqNatToNat.ArbLenNatsToNat(hpnp_as_seq) < bound;
    }
    
    ghost predicate CircuitNoLoops(c: Circuit)
        requires CircuitValid(c)
    {
        var g := CtoG(c);
        !DG.DigraphLoop(g)
    }

    lemma NoLoopsMeansNotInPath(c: Circuit, p: DG.Path<HPNP>, n: HPNP)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, p)
        requires HPNPValid(c, n)
        requires |p.v| > 0 ==> HPNPConnected(c, DG.PathEnd(p), n)
        ensures n !in p.v
    {
        var new_p := PathAppend(c, p, n);
        assert new_p == DG.Path(p.v + [n]);
        assert PathValid(c, new_p);
        DG.NoLoopsMeansNoRepeats(CtoGV(c));
        assert DG.PathNoRepeats(new_p);
        if n in p.v {
            var index: nat :| index < |p.v| && p.v[index] == n;
            assert new_p.v[index] == n;
            assert new_p.v[|new_p.v|-1] == n;
            assert !DG.PathNoRepeats(new_p);
        }
    }

    function PathAppend(c: Circuit, p: DG.Path<HPNP>, n: HPNP): (r: DG.Path<HPNP>)
        // Just a PathAppend with more friendly requirements for a circuit.
        requires CircuitValid(c)
        requires DG.PathValid(CtoGV(c), p)
        requires HPNPValid(c, n)
        requires (|p.v| > 0 ==> HPNPConnected(c, DG.PathEnd(p), n))
        ensures DG.PathValid(CtoGV(c), r)
    {
        reveal CtoG();
        DG.PathAppend(CtoGV(c), p, n)
    }

    predicate PathValid(c: Circuit, seen_path: DG.Path<HPNP>)
        requires CircuitValid(c)
    {
        DG.PathValid(CtoGV(c), seen_path)
    }

    function NumberOfRemainingNodes(c: Circuit, seen_path: DG.Path<HPNP>): nat
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, seen_path)
    {
        DG.NoLoopsMeansNoRepeats(CtoGV(c));
        DG.NumberOfRemainingNodesPath(CtoGV(c), seen_path)
    }

    lemma NumberOfRemainingNodesDecreases(c: Circuit, seen_path: DG.Path<HPNP>, n: HPNP)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, seen_path)
        requires HPNPValid(c, n)
        requires |seen_path.v| > 0 ==> HPNPConnected(c, DG.PathEnd(seen_path), n)
        ensures
            var new_p := PathAppend(c, seen_path, n);
            NumberOfRemainingNodes(c, new_p) <
            NumberOfRemainingNodes(c, seen_path)
    {
        DG.NoLoopsMeansNoRepeats(CtoGV(c));
        assert DG.PathNoRepeats(seen_path);
    }


}
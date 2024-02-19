module CircuitPath {

    import opened Std.Wrappers
    import Seq = Std.Collections.Seq
    import SeqNatToNat
    import SeqExt
    import opened Circuit
    import DG

    predicate {:opaque} HPNPOtoIConnected(c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, a)
        requires HPNPValidInput(c, b)
    {
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
            case CHier(lower_c) => (
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
            case CComb(_, _, path_exists, _) =>
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
        var a_c := HierarchyPathCircuit(c, a.hpn.hp);
        var inp := NP(a.hpn.n, a.p);
        var onp := NP(b.hpn.n, b.p);
        c.PortSource(inp) == Some(onp)
    }

    predicate {:opaque} HPNPConnected(c: Circuit,  a: HPNP, b: HPNP)
        requires CircuitValid(c)
    {
        (HPNPValidInput(c, a) && HPNPValidOutput(c, b) &&
            HPNPItoOConnected(c, a, b)) ||
        (HPNPValidOutput(c, a) && HPNPValidInput(c, b) &&
            HPNPOtoIConnected(c, a, b))
    }

    //function PadZeros(a: seq<nat>, l: nat): (r: seq<nat>)
    //    requires |a| <= l
    //    ensures |r| == l
    //{
    //    a + seq (l - |a|, i requires 0 <= i < l => 0)
    //}
    

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

    //lemma HPLengthBoundInternal(c: Circuit, hp: HierarchyPath)
    //    requires CircuitValid(c)
    //    requires HierarchyPathValid(c, hp)
    //    ensures
    //        var hier_c := HierarchyPathCircuit(c, hp);
    //        HPLength(hp) <= (c.HierLevel - hier_c.HierLevel)
    //{
    //    if HPLength(hp) == 0 {
    //    } else {
    //        var hier_c := HierarchyPathCircuit(c, hp);
    //        var (head, tail) := HPHeadTail(hp);
    //        var tail_c := HierarchyPathCircuit(c, tail);
    //        var nk := tail_c.NodeKind(head).value;
    //        assert nk.CHier?;
    //        HierarchyPathCircuitValid(c, tail);
    //        assert CircuitValid(tail_c);
    //        assert CNodeKindValid(tail_c, nk);
    //        assert tail_c.HierLevel > hier_c.HierLevel;
    //    }
    //}

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

    lemma HPNPToNatUnique(a: HPNP, b: HPNP)
        ensures (a != b) ==> (HPNPToNat(a) != HPNPToNat(b))
    {
        HPNPToSeqNatUnique(a, b);
        SeqNatToNat.ArbLenNatsToNatUnique(HPNPToSeqNat(a), HPNPToSeqNat(b));
    }

    //function HierarchyPathToNatInternal(hp: HierarchyPath, hn: nat) : (r: nat)
    //    decreases |hp.v|
    //{
    //    if HPLength(hp) == 0 then
    //        SeqNatToNat.NatsToNat([hn, 0]) as nat
    //    else
    //        var (n, parent) := HPHeadTail(hp);
    //        var new_hn := SeqNatToNat.NatsToNat([n as nat, hn]) as nat;
    //        HierarchyPathToNatInternal(parent, new_hn)
    //}

    //function HPNodeToNat(hpn: HPNode) : (r: nat)
    //{
    //    HierarchyPathToNatInternal(hpn.hp, hpn.n as nat)
    //}

    //function HPNPToNat(hpnp: HPNP) : (r: nat)
    //{
    //    SeqNatToNat.NatsToNat([HPNodeToNat(hpnp.hpn) as nat, hpnp.p as nat])
    //}

    //lemma NatsToNatUnique(a: nat, b: nat, c: nat, d: nat)
    //    requires (a, b) != (c, d)
    //    ensures SeqNatToNat.NatsToNat([a, b]) != SeqNatToNat.NatsToNat([c, d])
    //{
    //}

    //lemma NatsToNatBounded(a: nat, b: nat, c: nat, d: nat)
    //    requires (a < c) && (b < d)
    //    ensures SeqNatToNat.NatsToNat([a, b]) < SeqNatToNat.NatsToNat([c, d])
    //{
    //}

    function HPNPBound(c: Circuit): nat
    {
        0
    }

    function CtoG(c: Circuit): (g: DG.Digraph<HPNP>)
        requires CircuitValid(c)
    {
        DG.Digraph(
            hpnp => HPNPValid(c, hpnp),
            (a, b) => HPNPConnected(c, a, b),
            HPNPToNat,
            HPNPBound(c)
        )
    }

    lemma HPNPBounded(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPToNat(hpnp) >= HPNPBound(c)
        ensures !HPNPValid(c, hpnp)
    {
    }

    lemma NoSelfConnections(c: Circuit, n: HPNP)
        requires CircuitValid(c)
        ensures !HPNPConnected(c, n, n)
    {
    }

    lemma ConnectedNodesValid(c: Circuit, n: HPNP, m: HPNP)
        requires CircuitValid(c)
        ensures HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m)
    {
    }

    lemma CtoGValid(c: Circuit)
        requires CircuitValid(c)
        ensures DG.DigraphValid(CtoG(c))
    {
        var g := CtoG(c);
        forall n: HPNP, m: HPNP
            ensures HPNPToNat(n) >= HPNPBound(c) ==> !HPNPValid(c, n)
            ensures !HPNPConnected(c, n, n)
            ensures HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m)
            ensures (n != m) ==> HPNPToNat(n) != HPNPToNat(m)
        {
            HPNPBounded(c, n);
            NoSelfConnections(c, n);
            ConnectedNodesValid(c, n, m);
            HPNPToNatUnique(n, m);
        }
        assert (forall n: HPNP :: HPNPToNat(n) >= HPNPBound(c) ==> !HPNPValid(c, n));
        assert (forall n: HPNP :: !HPNPConnected(c, n, n));
        assert (forall n: HPNP, m: HPNP :: HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m));
        assert (forall n: HPNP, m: HPNP :: n != m ==> HPNPToNat(n) != HPNPToNat(m));
        reveal DG.DigraphValid();
    }

}
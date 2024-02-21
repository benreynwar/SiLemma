module CircuitPath {

    import opened Std.Wrappers
    import Seq = Std.Collections.Seq
    import SeqNatToNat
    import SeqExt
    import opened Circuit
    import CircuitBounds
    import DG

    predicate {:opaque} HPNPOtoIConnected(lib: CLib, c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(lib, c)
        requires HPNPValidOutput(lib, c, a)
        requires HPNPValidInput(lib, c, b)
    {
        var a_c := HierarchyPathCircuit(lib, c, a.hpn.hp);
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
                var lower_c := NodeToSubcircuit(lib, a_c, a.hpn.n);
                // It's an output port from a hier node.
                // It only connects to the input into the corresponding Output node in that circuit.
                var maybe_level_nk := lower_c.NodeKind(a.p as CNode);
                match maybe_level_nk
                case Some(Output) =>
                    var new_hp := ExtendHierarchyPath(lib, c, a.hpn.hp, a.hpn.n);
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

    predicate {:opaque} HPNPItoOConnected(lib: CLib, c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(lib, c)
        requires HPNPValidInput(lib, c, a)
        requires HPNPValidOutput(lib, c, b)
    {
        var a_c := HierarchyPathCircuit(lib, c, a.hpn.hp);
        var inp := NP(a.hpn.n, a.p);
        var onp := NP(b.hpn.n, b.p);
        c.PortSource(inp) == Some(onp)
    }

    predicate {:opaque} HPNPConnected(lib: CLib, c: Circuit,  a: HPNP, b: HPNP)
        requires CircuitValid(lib, c)
    {
        (HPNPValidInput(lib, c, a) && HPNPValidOutput(lib, c, b) &&
            HPNPItoOConnected(lib, c, a, b)) ||
        (HPNPValidOutput(lib, c, a) && HPNPValidInput(lib, c, b) &&
            HPNPOtoIConnected(lib, c, a, b))
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

    lemma HPLengthBound(lib: CLib, c: Circuit, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        ensures
            var hier_c := HierarchyPathCircuit(lib, c, hp);
            HPLength(hp) <= (c.HierLevel - hier_c.HierLevel)
        decreases HPLength(hp)
    {
        if HPLength(hp) == 0 {
        } else {
            var hier_c := HierarchyPathCircuit(lib, c, hp);
            var (head, tail) := HPHeadTail(hp);
            var tail_c := HierarchyPathCircuit(lib, c, tail);
            var nk := tail_c.NodeKind(head).value;
            assert nk.CHier?;
            HierarchyPathCircuitValid(lib, c, tail);
            assert CircuitValid(lib, tail_c);
            assert CNodeKindValid(lib, tail_c, nk);
            assert tail_c.HierLevel > hier_c.HierLevel;
            HPLengthBound(lib, c, tail);
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

    lemma HPNPToNatUnique(a: HPNP, b: HPNP)
        ensures (a != b) ==> (HPNPToNat(a) != HPNPToNat(b))
    {
        HPNPToSeqNatUnique(a, b);
        SeqNatToNat.ArbLenNatsToNatUnique(HPNPToSeqNat(a), HPNPToSeqNat(b));
    }

    ghost function CtoG(lib: CLib, c: Circuit): (g: DG.Digraph<HPNP>)
        requires CircuitValid(lib, c)
    {
        DG.Digraph(
            hpnp => HPNPValid(lib, c, hpnp),
            (a, b) => HPNPConnected(lib, c, a, b),
            HPNPToNat,
            CircuitBounds.HPNPBound(lib, c)
        )
    }

    lemma NoSelfConnections(lib: CLib, c: Circuit, n: HPNP)
        requires CircuitValid(lib, c)
        ensures !HPNPConnected(lib, c, n, n)
    {
        reveal HPNPConnected();
        if HPNPValid(lib, c, n) {
            var hier_c := HierarchyPathCircuit(lib, c, n.hpn.hp);
            HierarchyPathCircuitValid(lib, c, n.hpn.hp);
            assert CircuitNodeKindValid(lib, hier_c);
            if HPNPValidInput(lib, c, n) {
                assert !HPNPValidOutput(lib, c, n);
                assert !HPNPConnected(lib, c, n, n);
            } else {
            }
        } else {
            assert !HPNPValidInput(lib, c, n);
            assert !HPNPValidOutput(lib, c, n);
        }
    }

    lemma ConnectedNodesValid(lib: CLib, c: Circuit, n: HPNP, m: HPNP)
        requires CircuitValid(lib, c)
        ensures HPNPConnected(lib, c, n, m) ==> HPNPValid(lib, c, n) && HPNPValid(lib, c, m)
    {
        reveal HPNPConnected();
    }

    lemma OutOfBoundInvalid(lib: CLib, c: Circuit, n: HPNP)
        requires CircuitValid(lib, c)
        ensures HPNPToNat(n) >= CircuitBounds.HPNPBound(lib, c) ==> !HPNPValid(lib, c, n)
    {
        if HPNPToNat(n) >= CircuitBounds.HPNPBound(lib, c) {
            if HPNPValid(lib, c, n) {
                HPNPInBound(lib, c, n);
                assert HPNPToNat(n) < CircuitBounds.HPNPBound(lib, c);
                assert false;
            } else {
            }
            assert !HPNPValid(lib, c, n);
        }
    }

    lemma CtoGValid(lib: CLib, c: Circuit)
        requires CircuitValid(lib, c)
        ensures DG.DigraphValid(CtoG(lib, c))
    {
        var g := CtoG(lib, c);
        forall n: HPNP, m: HPNP
            ensures HPNPToNat(n) >= CircuitBounds.HPNPBound(lib, c) ==> !HPNPValid(lib, c, n)
            ensures !HPNPConnected(lib, c, n, n)
            ensures HPNPConnected(lib, c, n, m) ==> HPNPValid(lib, c, n) && HPNPValid(lib, c, m)
            ensures (n != m) ==> HPNPToNat(n) != HPNPToNat(m)
        {
            OutOfBoundInvalid(lib, c, n);
            NoSelfConnections(lib, c, n);
            ConnectedNodesValid(lib, c, n, m);
            HPNPToNatUnique(n, m);
        }
        assert (forall n: HPNP :: HPNPToNat(n) >= CircuitBounds.HPNPBound(lib, c) ==> !HPNPValid(lib, c, n));
        assert (forall n: HPNP :: !HPNPConnected(lib, c, n, n));
        assert (forall n: HPNP, m: HPNP :: HPNPConnected(lib, c, n, m) ==> HPNPValid(lib, c, n) && HPNPValid(lib, c, m));
        assert (forall n: HPNP, m: HPNP :: n != m ==> HPNPToNat(n) != HPNPToNat(m));
        reveal DG.DigraphValid();
    }

    lemma HPNPAsSeqNatInBound(lib: CLib, c: Circuit, hpnp: HPNP)
        requires CircuitValid(lib, c)
        requires HPNPValid(lib, c, hpnp)
        ensures forall n: nat :: n in HPNPToSeqNat(hpnp) ==>
            n < CircuitBounds.HPNPElementBound(lib, c)
    {
        CircuitBounds.HPNPElementsInBound(lib, c, hpnp);
        var hpnp_as_seq := HPNPToSeqNat(hpnp);
        var element_bound := CircuitBounds.HPNPElementBound(lib, c); 
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


    lemma HPNPInBound(lib: CLib, c: Circuit, hpnp: HPNP)
        requires CircuitValid(lib, c)
        requires HPNPValid(lib, c, hpnp)
        ensures HPNPToNat(hpnp) < CircuitBounds.HPNPBound(lib, c)
    {
        CircuitBounds.HPNPElementsInBound(lib, c, hpnp);
        var hpnp_as_seq := HPNPToSeqNat(hpnp);
        var element_bound := CircuitBounds.HPNPElementBound(lib, c); 
        HPNPAsSeqNatInBound(lib, c, hpnp);

        var len := |hpnp_as_seq|;

        var bound := SeqNatToNat.ArbLenNatsToNatBound(c.HierLevel+2, element_bound);
        assert bound == CircuitBounds.HPNPBound(lib, c);
        assert forall n: nat :: n in hpnp_as_seq ==> n < element_bound;
        assert forall i: nat :: i < |hpnp_as_seq| ==> hpnp_as_seq[i] in hpnp_as_seq;
        assert forall i: nat :: i < |hpnp_as_seq| ==> hpnp_as_seq[i] < element_bound;
        HPLengthBound(lib, c, hpnp.hpn.hp);
        assert HPLength(hpnp.hpn.hp) <= c.HierLevel;
        assert |hpnp_as_seq| <= c.HierLevel + 2;
        SeqNatToNat.ArbLenNatsToNatBounded(hpnp_as_seq, c.HierLevel+2, element_bound);
        assert SeqNatToNat.ArbLenNatsToNat(hpnp_as_seq) < bound;
    }

}
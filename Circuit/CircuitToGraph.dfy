module CircuitToGraph {

    import DG = DigraphBase
    import DP = DigraphPaths
    import opened Std.Wrappers
    import opened CircuitBase
    import opened CircuitHierarchy
    import opened CircuitHPNP
    import opened CircuitNodeBounds

    // INP and ONP reference ports on a single level of the hierarchy.
    // The 'n' can point at an internal node, or at a port on the external
    // interface.


    function {:opaque} CtoG(c: Circuit): (g: DG.Digraph<HPNP>)
        requires CircuitValid(c)
    {
        DG.Digraph(
            hpnp => HPNPValid(c, hpnp),
            (a, b) => HPNPConnected(c, a, b),
            HPNPToNat,
            NatToHPNP,
            HPNPBound(c)
        )
    }

    function CtoGV(c: Circuit): (g: DG.Digraph<HPNP>)
        requires CircuitValid(c)
        ensures DG.DigraphValid(g)
    {
        CtoGValid(c);
        CtoG(c)
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

    function NumberOfRemainingNodes(c: Circuit, seen_path: DG.Path<HPNP>): nat
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, seen_path)
    {
        DP.NoLoopsMeansNoRepeats(CtoGV(c));
        DP.NumberOfRemainingNodesPath(CtoGV(c), seen_path)
    }

    lemma NumberOfRemainingNodesDecreases(c: Circuit, seen_path: DG.Path<HPNP>, n: HPNP)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, seen_path)
        requires HPNPValid(c, n)
        requires |seen_path.v| > 0 ==> HPNPConnected(c, DP.PathEnd(seen_path), n)
        ensures
            var new_p := PathAppend(c, seen_path, n);
            NumberOfRemainingNodes(c, new_p) <
            NumberOfRemainingNodes(c, seen_path)
    {
        DP.NoLoopsMeansNoRepeats(CtoGV(c));
        assert DP.PathNoRepeats(seen_path);
    }

    lemma CtoGValid(c: Circuit)
        requires CircuitValid(c)
        ensures DG.DigraphValid(CtoG(c))
    {
        reveal CtoG();
        var g := CtoG(c);
        forall n: HPNP, m: HPNP
            ensures HPNPToNat(n) >= HPNPBound(c) ==> !HPNPValid(c, n)
            ensures !HPNPConnected(c, n, n)
            ensures HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m)
            ensures (n != m) ==> HPNPToNat(n) != HPNPToNat(m)
        {
            OutOfBoundInvalid(c, n);
            NoSelfConnections(c, n);
            ConnectedNodesValid(c, n, m);
            HPNPToNatInjective(n, m);
        }
        assert (forall n: HPNP :: HPNPToNat(n) >= HPNPBound(c) ==> !HPNPValid(c, n));
        assert (forall n: HPNP :: !HPNPConnected(c, n, n));
        assert (forall n: HPNP, m: HPNP :: HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m));
        assert (forall n: HPNP, m: HPNP :: n != m ==> HPNPToNat(n) != HPNPToNat(m));
        reveal DG.DigraphValid();
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
        requires |p.v| > 0 ==> HPNPConnected(c, DP.PathEnd(p), n)
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
    
}
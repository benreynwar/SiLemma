module CircuitToGraph {

    import DG = DigraphBase`Body
    import DP = DigraphPaths`Body
    import opened Std.Wrappers
    import opened CircuitBase
    import opened CircuitHierarchy
    import opened CircuitHPNP
    import SetExt

    // INP and ONP reference ports on a single level of the hierarchy.
    // The 'n' can point at an internal node, or at a port on the external
    // interface.

    function AllValidHPNPPairs(c: Circuit): (r: set<(HPNP, HPNP)>)
        requires CircuitValid(c)
        ensures forall a, b : HPNP :: HPNPValid(c, a) && HPNPValid(c, b) <==> (a, b) in r
    {
        var hpnps := AllValidHPNP(c);
        SetExt.SetProduct(hpnps, hpnps)
    }

    function {:opaque} CtoG(c: Circuit): (g: DG.Digraph<HPNP>)
        requires CircuitValid(c)
    {
        DG.Digraph(
            AllValidHPNP(c),
            (set n: (HPNP, HPNP) | n in AllValidHPNPPairs(c) && HPNPConnected(c, n.0, n.1):: n)
        )
    }

    lemma CtoGConnections(c: Circuit)
        requires CircuitValid(c)
        ensures 
            var g := CtoG(c);
            forall a, b: HPNP :: HPNPConnected(c, a, b) == DG.IsConnected(g, a, b)
    {
        reveal CtoG();
        reveal DG.IsConnected();
        var g := CtoG(c);
        forall n: (HPNP, HPNP)
            ensures DG.IsConnected(g, n.0, n.1) == HPNPConnected(c, n.0, n.1)
        {
            reveal HPNPConnected();
            assert HPNPConnected(c, n.0, n.1) ==> n in AllValidHPNPPairs(c);
        }
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
        assert CircuitValid(parent_c);
        reveal HPNPValidOutput();
        reveal CircuitValid();
        assert CircuitNodeKindValid(parent_c);
        assert CircuitPortSourceValid(parent_c);
        var inp := NP(hpinp.hpn.n, hpinp.p);
        reveal HPNPValidInput();
        assert NPValidInput(parent_c, inp);
        var maybe_onp: Option<NP> := PortSource(parent_c, inp);
            match maybe_onp
            // The input port does not connect to anything.
            case None => None
            // The input port does connect.
            case Some(onp) =>
                assert NPValid(parent_c, onp);
                assert NPValidOutput(parent_c, onp);
                var nk := NodeKind(parent_c, onp.n);
                assert nk.Some?;
                assert IsOPort(nk.value, onp.p);
                var hpn := HPNode(hp, onp.n);
                var hpnp := HPNP(hpn, onp.p);
                reveal HPNPValidOutput();
                assert HPNPValidOutput(c, hpnp);
                Some(hpnp)
    }

    ghost function NumberOfRemainingNodes(c: Circuit, seen_path: DG.Path<HPNP>): (r: nat)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, seen_path)
        ensures r == |AllValidHPNP(c)| - |seen_path.v|
    {
        reveal CtoG();
        var g := CtoGV(c);
        assert |g.Nodes| == |AllValidHPNP(c)|;
        DP.NoLoopsMeansNoRepeats(g);
        var r := DP.NumberOfRemainingNodesPath(g, seen_path);
        assert r == DG.NodeCount(g) - |seen_path.v|;
        r
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
        var new_p := PathAppend(c, seen_path, n);
        DP.NoLoopsMeansNoRepeats(CtoGV(c));
        assert DP.PathNoRepeats(seen_path);
        assert NumberOfRemainingNodes(c, new_p) < NumberOfRemainingNodes(c, seen_path);
    }

    lemma {:vcs_split_on_every_assert} CtoGValid(c: Circuit)
        requires CircuitValid(c)
        ensures DG.DigraphValid(CtoG(c))
    {
        reveal CtoG();
        var g := CtoG(c);
        forall n: HPNP, m: HPNP
            ensures !HPNPConnected(c, n, n)
            ensures HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m)
        {
            NoSelfConnections(c, n);
            ConnectedNodesValid(c, n, m);
        }
        assert (forall n: HPNP :: !HPNPConnected(c, n, n));
        assert (forall n: HPNP, m: HPNP :: HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m));
        reveal DG.DigraphValid();
        reveal DG.IsConnected();
        reveal DG.IsNode();
        assert DG.DigraphValid(g);
    }
    
    ghost predicate CircuitNoLoops(c: Circuit)
        requires CircuitValid(c)
    {
        var g := CtoG(c);
        !DP.DigraphLoop(g)
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
        DP.NoLoopsMeansNoRepeats(CtoGV(c));
        assert DP.PathNoRepeats(new_p);
        if n in p.v {
            var index: nat :| index < |p.v| && p.v[index] == n;
            assert new_p.v[index] == n;
            assert new_p.v[|new_p.v|-1] == n;
            assert !DP.PathNoRepeats(new_p);
        }
    }

    function {:vcs_split_on_every_assert} PathAppend(c: Circuit, p: DG.Path<HPNP>, n: HPNP): (r: DG.Path<HPNP>)
        // Just a PathAppend with more friendly requirements for a circuit.
        requires CircuitValid(c)
        requires DG.PathValid(CtoGV(c), p)
        requires HPNPValid(c, n)
        requires (|p.v| > 0 ==> HPNPConnected(c, DP.PathEnd(p), n))
        ensures DG.PathValid(CtoGV(c), r)
    {
        reveal DG.PathValid();
        reveal DG.IsNode();
        reveal DG.IsConnected();
        var g := CtoGV(c);
        reveal CtoG();
        assert |p.v| > 0 ==> DG.IsConnected(g, DP.PathEnd(p), n);
        DG.Path(p.v + [n])
    }

    ghost predicate PathValid(c: Circuit, seen_path: DG.Path<HPNP>)
        requires CircuitValid(c)
    {
        DG.PathValid(CtoGV(c), seen_path)
    }

    lemma HPNodeNotInCircuitHPNPNotInGraph(c: Circuit, hpn: HPNode)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hpn.hp)
        requires !HPNodeInCircuit(c, hpn)
        ensures forall p :: !DG.IsNode(CtoG(c), HPNP(hpn, p))
    {
        reveal CtoG();
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        reveal DG.IsNode();
    }

    lemma ValidHPNPIsNode(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures DG.IsNode(CtoGV(c), hpnp)
    {
        var g := CtoGV(c);
        reveal CtoG();
        assert HPNPValid(c, hpnp);
        assert hpnp in AllValidHPNP(c);
        reveal DG.IsNode();
        assert DG.IsNode(g, hpnp);
    }
}
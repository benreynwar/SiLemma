module CircuitBuild {

    import opened Std.Wrappers
    import opened CircuitHPNP
    import opened CircuitBase
    import opened CircuitHierarchy
    import opened CircuitToGraph
    import DG = DigraphBase
    import DP = DigraphPaths
    import DSB = DigraphStepBack
    import DC = DigraphCombine

    // Proove that there are no loops in a small circuit.
    // Take a set of HPNP.
    // Step backwards to get a new set.
    // So that after X steps the new set is empty.

    function StepBack(c: Circuit, n: HPNP): (r: set<HPNP>)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HPNPValid(c, n)
        ensures forall m :: m in r ==> HPNPValid(c, m)
    {
        if HPNPValidInput(c, n) then
            {INPtoONP(c, n)}
        else
            ONPtoINP(c, n)
    }

    lemma StepBackMatchesHPNPConnected(c: Circuit, n: HPNP)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HPNPValid(c, n)
        ensures forall m :: m in StepBack(c, n) <==> HPNPConnected(c, n, m)
    {
        reveal HPNPConnected();
        reveal HPNPItoOConnected();
        reveal HPNPOtoIConnected();
        reveal INPtoONP();
        forall m: HPNP
            ensures m in StepBack(c, n) <==> HPNPConnected(c, n, m)
        {
            HPNPNotBothValidInputOutput(c, n);
            if HPNPValid(c, m) {
                HPNPNotBothValidInputOutput(c, m);
                if HPNPValidInput(c, n) && HPNPValidOutput(c, m) {
                    var o := INPtoONP(c, n);
                    assert m in StepBack(c, n) <==> HPNPConnected(c, n, m);
                }
            }
        }
    }

    ghost function StepSetBackInternal(c: Circuit, in_ns: set<HPNP>, out_ns: set<HPNP>): (r: set<HPNP>)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires forall n :: n in in_ns ==> HPNPValid(c, n)
        requires forall n :: n in out_ns ==> HPNPValid(c, n)
        ensures forall n :: n in r ==> HPNPValid(c, n)
    {
        if |in_ns| == 0 then
            out_ns
        else
            var n :| n in in_ns;
            var connected := StepBack(c, n);
            assert forall m :: m in connected ==> HPNPValid(c, m);
            var new_in_ns := in_ns - {n};
            var new_out_ns := out_ns + connected;
            StepSetBackInternal(c, new_in_ns, new_out_ns)
    }

    lemma StepBackEquiv(c: Circuit, n: HPNP)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HPNPValid(c, n)
        ensures
            var g := CtoG(c);
            DG.DigraphValid(g) &&
            (StepBack(c, n) == DSB.StepBack(g, n))
    {
        var g := CtoG(c);
        CtoGValid(c);
        reveal CtoG();
        assert DG.DigraphValid(g);
        reveal HPNPConnected();
        reveal HPNPItoOConnected();
        reveal HPNPOtoIConnected();
        StepBackMatchesHPNPConnected(c, n);
        assert forall m :: m in DSB.StepBack(g, n) ==> DG.IsConnected(g, n, m);
        assert forall m :: m in StepBack(c, n) ==> DG.IsConnected(g, n, m);
    }

    lemma EmptyCircuitHasNoHP(hp: HierarchyPath)
        requires HPLength(hp) > 0
        ensures
            var c := MakeEmptyCircuit();
            !HierarchyPathValid(c, hp)
        decreases hp.v
    {
        var c := MakeEmptyCircuit();
        if HPLength(hp) == 1 {
            assert !HierarchyPathValid(c, hp);
        } else {
            var (head, tail) := HPHeadTail(hp);
            EmptyCircuitHasNoHP(tail);
        }
    }
    
    lemma EmptyCircuitHasNoHPNP()
        ensures
            var c := MakeEmptyCircuit();
            forall n: HPNP :: !HPNPValid(c, n)
    {
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var c := MakeEmptyCircuit();
        assert forall n: CNode :: NodeKind(c, n) == None;
        forall hpnp: HPNP
            ensures !HPNPValid(c, hpnp)
        {
            var n := hpnp.hpn.n;
            var hp := hpnp.hpn.hp;
            if HPLength(hp) == 0 {
                assert !HPNPValid(c, hpnp);
            } else {
                EmptyCircuitHasNoHP(hp);
            }
        }
    }

    lemma EmptyCircuitHasNoHPNPConnected()
        ensures
            var c := MakeEmptyCircuit();
            forall a: HPNP, b: HPNP :: !HPNPConnected(c, a, b)
    {
        var c := MakeEmptyCircuit();
        reveal CircuitValid();
        reveal HPNPConnected();
        EmptyCircuitHasNoHPNP();
        forall a: HPNP, b: HPNP
            ensures !HPNPConnected(c, a, b)
        {
            assert !HPNPValid(c, a);
            assert !HPNPValid(c, b);
        }
    }

    function MakeEmptyCircuit(): (r: Circuit)
        ensures CircuitValid(r)
    {
        reveal CircuitValid();
        var c := Circuit(
            NodeKind := map[],
            PortSource := map[],
            HierLevel := 0,
            PortNames := map[]
        );
        c
    }

    lemma EmptyCircuitProperties()
        ensures
            var c := MakeEmptyCircuit();
            CircuitValid(c) && CircuitNoLoops(c)
    {
        reveal CircuitValid();
        var c := MakeEmptyCircuit();
        var g := CtoG(c);
        EmptyDigraphProperties();
    }

    lemma EmptyDigraphProperties()
        ensures
            var c := MakeEmptyCircuit();
            var g := CtoGV(c);
            (forall n: HPNP :: !DG.IsNode(g, n)) &&
            (forall n, m: HPNP :: !DG.IsConnected(g, n, m)) &&
            (!DP.DigraphLoop(g))
    {
        var c := MakeEmptyCircuit();
        EmptyCircuitHasNoHPNP();
        var g := CtoGV(c);
        reveal CtoG();
        assert DG.DigraphValid(g);
        assert forall n: HPNP :: !HPNPValid(c, n);
        assert forall n: HPNP :: !DG.IsNode(g, n);
        EmptyCircuitHasNoHPNPConnected();
        assert forall n, m: HPNP :: !DG.IsConnected(g, n, m);
        reveal DP.DigraphLoop();
        reveal DG.PathValid();
        assert !DP.DigraphLoop(g);
    }

    function AddIPort(g: Circuit): (r: (Circuit, NP))
        requires CircuitValid(g)
        ensures CircuitValid(r.0)
    {
        var (c, n) := AddNode(g, CInput, map[]);
        (c, NP(n, 0))
    }

    function AddOPort(g: Circuit, onp: NP): (r: Circuit)
        requires CircuitValid(g)
        ensures CircuitValid(r)
    {
        var (c, n) := AddNode(g, COutput, map[0 := onp]);
        c
    }

    //function NodeKindElementBound(c: Circuit, nk: CNodeKind, n: CNode): nat
    //    requires CircuitValid(c)
    //    requires !nk.CHier?
    //{
    //    var max_index := HPNPElementBound(c);
    //    var port_bound := NKPortBound(nk) as nat;
    //    var new_max_index_intermed := if port_bound > max_index then port_bound else max_index;
    //    var new_max_index := if (n as nat)+1 > new_max_index_intermed then (n as nat)+1 else new_max_index_intermed;
    //    new_max_index
    //}

    //function NodeKindBound(c: Circuit, nk: CNodeKind, n: CNode): nat
    //    requires CircuitValid(c)
    //    requires !nk.CHier?
    //{
    //    var element_bound := NodeKindElementBound(c, nk, n);
    //    var ns := Seq.Repeat(element_bound, c.HierLevel+2);
    //    SeqNatToNat.ArbLenNatsToNat(ns)
    //}

    //lemma NodeKindBoundBinds(c: Circuit, nk: CNodeKind, hpn: HPNode)
    //    requires CircuitValid(c)
    //    requires HierarchyPathValid(c, hpn.hp)
    //    requires !nk.CHier?
    //    ensures
    //        var g := NodeKindToGraph(c, nk, hpn);
    //        var bound := NodeKindBound(c, nk, hpn.n);
    //        forall n: HPNP :: g.IsNode(n) ==> g.NodeMap(n) < bound
    //{
    //    var g := NodeKindToGraph(c, nk, hpn);
    //    var bound := NodeKindBound(c, nk, hpn.n);
    //    assert g.NodeBound == bound;
    //    assert forall hpnp :: g.IsNode(hpnp) ==> hpnp.hpn == hpn;

    //    var element_bound := NodeKindElementBound(c, nk, hpn.n);
    //    var ns := Seq.Repeat(element_bound, c.HierLevel+2);
    //    assert bound == SeqNatToNat.ArbLenNatsToNat(ns);

    //    HPElementsInBound(c, hpn.hp);
    //    assert forall n: CNode :: (n in hpn.hp.v) ==> n as nat < element_bound;
    //    assert forall e: nat :: e in SeqCNodeToSeqNat(hpn.hp.v) ==> e < element_bound;
    //    assert hpn.n as nat < element_bound;

    //    forall hpnp | g.IsNode(hpnp)
    //        ensures HPNPToNat(hpnp) < bound
    //    {
    //        assert hpnp.hpn == hpn;
    //        var hpnp_as_seqnat := HPNPToSeqNat(hpnp);
    //        assert |hpnp_as_seqnat| == |hpnp.hpn.hp.v| + 2;
    //        HPLengthBound(c, hpnp.hpn.hp);
    //        assert |hpnp.hpn.hp.v| <= c.HierLevel;
    //        assert |hpnp_as_seqnat| <= c.HierLevel + 2;
    //        assert hpnp.p as nat < element_bound;
    //        var as_nat := HPNPToSeqNat(hpnp);
    //        assert forall n: nat :: n in as_nat ==> n < element_bound;
    //        SeqNatToNat.ArbLenNatsToNatBounded(as_nat, c.HierLevel+2, element_bound);
    //        assert HPNPToNat(hpnp) < bound;
    //    }
    //}

    lemma {:vcs_split_on_every_assert} NodeKindToGraphNoLoop(c: Circuit, nk: CNodeKind, hpn: HPNode)
        requires CircuitValid(c)
        requires CNodeKindSomewhatValid(nk)
        requires HierarchyPathValid(c, hpn.hp)
        requires !nk.CHier?
        ensures !DP.DigraphLoop(NodeKindToGraph(c, nk, hpn))
    {
        var g := NodeKindToGraph(c, nk, hpn);
        if nk.CComb? {
            forall p: DG.Path<HPNP> | DG.PathValid(g, p)
                ensures !DP.PathLoop(p)
            {
                reveal DG.PathValid();
                if |p.v| > 2 {
                    assert DG.IsConnected(g, p.v[0], p.v[1]);
                    assert p.v[0].p in nk.OPorts;
                    assert p.v[1].p in nk.IPorts;
                    assert p.v[1].p !in nk.OPorts;
                    assert DG.IsConnected(g, p.v[1], p.v[2]);
                    assert false;
                } else if |p.v| == 2 {
                    assert p.v[0] != p.v[1];
                    assert !DP.PathLoop(p);
                } else {
                    assert !DP.PathLoop(p);
                }
            }
            assert !exists p: DG.Path<HPNP> :: DG.PathValid(g, p) && DP.PathLoop(p);
            reveal DP.DigraphLoop();
            assert !DP.DigraphLoop(g);
        } else {
            assert forall n, m: HPNP :: !DG.IsConnected(g, n, m);
            reveal DG.PathValid();
            forall p: DG.Path<HPNP> | DG.PathValid(g, p)
                ensures !DP.PathLoop(p)
            {
                if |p.v| > 1 {
                    assert DG.IsConnected(g, p.v[0], p.v[1]);
                    assert false;
                } else {
                    assert !DP.PathLoop(p);
                }
            }
            assert !exists p: DG.Path<HPNP> :: DG.PathValid(g, p) && DP.PathLoop(p);
            reveal DP.DigraphLoop();
            assert !DP.DigraphLoop(g);
        }
    }


    lemma {:vcs_split_on_every_assert} NodeKindToGraphValid(c: Circuit, nk: CNodeKind, hpn: HPNode)
        requires CircuitValid(c)
        requires CNodeKindSomewhatValid(nk)
        requires HierarchyPathValid(c, hpn.hp)
        requires !nk.CHier?
        ensures DG.DigraphValid(NodeKindToGraph(c, nk, hpn))
    {
        var g := NodeKindToGraph(c, nk, hpn);
        //var bound := NodeKindBound(c, nk, hpn.n);
        //assert g.NodeBound == bound;
        //NodeKindBoundBinds(c, nk, hpn);
        //assert forall n: HPNP :: g.IsNode(n) ==> g.NodeMap(n) < bound;
        //var max_index := HPNPElementBound(c);
        //assert g.NodeBound == NodeKindBound(c, nk, hpn.n);
        //assert (forall n: HPNP :: g.NodeMap(n) >= g.NodeBound ==> !g.IsNode(n));
        if nk.CComb? {
            CNodeKindNoSelfPaths(nk);
        }
        reveal DG.IsConnected();
        assert (forall n: HPNP :: !DG.IsConnected(g, n, n));
        assert (forall n: HPNP, m: HPNP :: DG.IsConnected(g, n, m) ==> DG.IsNode(g, n) && DG.IsNode(g, m));
        //HPNPToNatInjectiveAll();
        //NatToHPNPInjectiveAll();
        //forall hpnp: HPNP {
        //    HPNPToNatToHPNP(hpnp);
        //}
        //assert (forall n: HPNP, m: HPNP :: n != m ==> g.NodeMap(n) != g.NodeMap(m));
        //assert (forall n: HPNP :: g.InvNodeMap(g.NodeMap(n)) == Some(n));
        //assert Functions.Injective(g.NodeMap) && Functions.Injective(g.InvNodeMap);
        reveal DG.DigraphValid();
        assert DG.DigraphValid(g);
    }

    function NodeKindHPNPs(c: Circuit, nk: CNodeKind, hpn: HPNode): set<HPNP>
    {
        {}
    }

    function NodeKindConnections(c: Circuit, nk: CNodeKind, hpn: HPNode): set<(HPNP, HPNP)>
    {
            //(n: HPNP, m: HPNP) =>
            //    match nk
            //        case CComb(_, _, path_exists, _, _) =>
            //            n.hpn == hpn && m.hpn == hpn && path_exists(n.p, m.p)
            //        case _ => false,
        {}
    }

    function NodeKindToGraph(c: Circuit, nk: CNodeKind, hpn: HPNode): (r: DG.Digraph<HPNP>)
        requires CircuitValid(c)
        requires !nk.CHier?
    {
        DG.Digraph(
            NodeKindHPNPs(c, nk, hpn),
            NodeKindConnections(c, nk, hpn)
        )
    }

    function NewNode(c: Circuit): CNode
    {
        0
    }

    lemma AddNodeNoInputsAddDGNode(c: Circuit, nk: CNodeKind)
        // This is equivalent to adding many nodes to the digraph.
        // One node for each port (if it's not hierarchical)

        // Assume it's not Hierarchical.
        // Show that the CNode creates a subgraph.
        // Show that the subgraph contains no loops.
        // Show that the combining the subgraphs does not
        // introduce loops.
        requires CNodeKindSomewhatValid(nk)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires !nk.CHier?
        ensures
            var (new_c, n) := AddNodeNoInputs(c, nk);
            var g := CtoG(c);
            var new_g := CtoG(new_c);
            DG.DigraphValid(g) &&
            !DP.DigraphLoop(g) &&
            true
            //DG.DigraphValid(new_g) &&
            //!DP.DigraphLoop(new_g)
    {
        var new_node := NewNode(c);
        var g := CtoG(c);
        assert !DP.DigraphLoop(g);
        var hpn := HPNode(HP([]), new_node);
        var sg := NodeKindToGraph(c, nk, hpn);
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        NodeKindToGraphValid(c, nk, hpn);
        NodeKindToGraphNoLoop(c, nk, hpn);
        assert DG.DigraphValid(sg);
        assert !DP.DigraphLoop(sg);
        HPNodeNotInCircuitHPNPNotInGraph(c, hpn);
        reveal DC.DigraphsCompatible();
        reveal CtoG();
        assert DC.DigraphsCompatible(g, sg);
        CtoGValid(c);
        var new_g := DC.Combine(g, sg);
        DC.CombineValid(g, sg);
        DC.CombineNoLoops(g, sg);
        assert DG.DigraphValid(new_g);
        assert !DP.DigraphLoop(new_g);

        var (new_c, n) := AddNodeNoInputs(c, nk);
        var new_g2 := CtoG(new_c);
    }

    function AddNodeNoInputs(c: Circuit, nk: CNodeKind): (r: (Circuit, CNode))
        requires CircuitValid(c)
        requires !nk.CHier?
        requires CNodeKindSomewhatValid(nk)
        ensures CircuitValid(r.0)
    {
        reveal CircuitValid();
        var new_node := NewNode(c);
        var new_c := Circuit(
            NodeKind := c.NodeKind[new_node := nk],
            PortSource := c.PortSource,
            //NodeBound := c.NodeBound+1,
            //PortBound := if nk_port_bound > c.PortBound then nk_port_bound else c.PortBound,
            HierLevel := c.HierLevel,
            PortNames := c.PortNames
        );
        assert forall n: CNode :: (NodeKind(new_c, n) == (if (n == new_node) then
            Some(nk) else NodeKind(c, n))) ;
        assert CircuitNodeKindValid(c);
        assert CircuitNodeKindValid(new_c);
        assert CircuitPortSourceValid(new_c);
        assert CircuitValid(new_c);
        assert CNodeKindValid(new_c.HierLevel, nk);
        (new_c, new_node)
    }

    function AddNode(c: Circuit, nk: CNodeKind, ip: map<CPort, NP>): (r: (Circuit, CNode))
        requires CircuitValid(c)
        requires !nk.CHier?
        ensures CircuitValid(r.0)
    {
        reveal CircuitValid();
        var new_node := NewNode(c);
        var new_c := Circuit(
            NodeKind := c.NodeKind[new_node := nk],
            PortSource := c.PortSource, // FIXME: Should update
            //NodeKind := n => if n == new_node then Some(nk) else c.NodeKind(n),
            //PortSource := (inp: NP) =>
            //    if inp.n == new_node then
            //        if inp.p in ip then
            //            Some(ip[inp.p])
            //        else
            //            None
            //    else
            //        c.PortSource(inp),
            //NodeBound := c.NodeBound+1,
            //PortBound := c.PortBound,
            HierLevel := c.HierLevel,
            PortNames := c.PortNames
        );
        assert forall n: CNode :: (NodeKind(new_c, n) == (if (n == new_node) then
            Some(nk) else NodeKind(c, n))) ;
        assert CircuitNodeKindValid(c);
        assert CircuitPortSourceValid(c);
        (c, new_node)
    }

}
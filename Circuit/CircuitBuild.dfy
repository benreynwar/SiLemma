module CircuitBuild {

    import Std.Collections.Seq
    import opened Std.Wrappers
    import opened CircuitHPNP
    import opened CircuitBase
    import opened CircuitHierarchy
    import opened CircuitToGraph
    import DG = DigraphBase`Body
    import DP = DigraphPaths`Body
    import DSB = DigraphStepBack`Body
    import DC = DigraphCombine`Body
    import SetExt
    import SeqExt
    import MapExt

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
        reveal DG.IsConnected();
        reveal DG.IsNode();
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
        reveal CircuitPortNamesValid();
        var c := Circuit(
            NodeKind := map[],
            PortSource := map[],
            HierLevel := 0,
            PortMap := PortMapping([], [], [], [])
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
        reveal DG.IsNode();
        assert forall n: HPNP :: !DG.IsNode(g, n);
        EmptyCircuitHasNoHPNPConnected();
        reveal DG.IsConnected();
        assert forall n, m: HPNP :: !DG.IsConnected(g, n, m);
        reveal DP.DigraphLoop();
        reveal DG.PathValid();
        assert !DP.DigraphLoop(g);
    }

    function AddIPort(c: Circuit, l: string): (r: (Circuit, NP))
        requires CircuitValid(c)
        requires l !in c.PortMap.inames
        requires l !in c.PortMap.onames
        ensures CircuitValid(r.0)
    {
        reveal CircuitValid();
        reveal CircuitPortNamesValid();
        var new_node := NewNode(c);
        var new_c := Circuit(
            NodeKind := c.NodeKind[new_node := CInput],
            PortSource := c.PortSource,
            HierLevel := c.HierLevel,
            PortMap := PortMappingAddIPort(c.PortMap, l, new_node as CPort)
        );
        assert CircuitNodeKindValid(c);
        assert CircuitNodeKindValid(new_c);
        assert CircuitPortSourceValid(new_c);
        reveal CircuitPortNamesValid();
        //MapExt.ExtendedMapValues(c.IPortNames, l, new_node);
        assert CircuitPortNamesValid(new_c);
        assert CircuitValid(new_c);
        (new_c, NP(new_node, OUTPUT_PORT))
    }

    function GetInputPort(c: Circuit, n: CNode, l: string): (r: NP)
        requires CircuitValid(c)
        requires n in c.NodeKind
        requires
            var nk := c.NodeKind[n];
            var pm := PortMap(nk);
            l in pm.inames
        ensures NPValidInput(c, r)
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        var nk := c.NodeKind[n];
        assert CNodeKindSomewhatValid(nk);
        var pm := PortMap(nk);
        var p := INameToPort(pm, l);
        NP(n, p)
    }

    function GetOutputPort(c: Circuit, n: CNode, l: string): (r: NP)
        requires CircuitValid(c)
        requires n in c.NodeKind
        requires
            var nk := c.NodeKind[n];
            var pm := PortMap(nk);
            l in pm.onames
        ensures NPValidOutput(c, r)
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        var nk := c.NodeKind[n];
        assert CNodeKindSomewhatValid(nk);
        var pm := PortMap(nk);
        var p := ONameToPort(pm, l);
        NP(n, p)
    }


    function AddOPortAndConnect(c: Circuit, onp: NP, l: string): (r: Circuit)
        requires CircuitValid(c)
        requires NPValidOutput(c, onp)
        requires l !in c.PortMap.inames
        requires l !in c.PortMap.onames
        ensures CircuitValid(r)
    {
        var (new_c, n) := AddOPort(c, l);
        assert CircuitValid(new_c);
        reveal CircuitValid();
        var inp := GetInputPort(new_c, n, "i");
        assert CircuitPortSourceValid(new_c);
        var final_c := Circuit(
            NodeKind := new_c.NodeKind,
            PortSource := new_c.PortSource[inp := onp],
            HierLevel := new_c.HierLevel,
            PortMap := new_c.PortMap
        );
        CircuitUpdatedCircuitNodeKindValid(new_c, final_c);
        reveal CircuitPortNamesValid();
        assert CircuitPortNamesValid(final_c);
        assert CircuitPortSourceValid(final_c);
        assert CircuitValid(final_c);
        final_c
    }

    function AddOPort(c: Circuit, l: string): (r: (Circuit, CNode))
        requires CircuitValid(c)
        requires l !in c.PortMap.inames
        requires l !in c.PortMap.onames
        ensures CircuitValid(r.0)
    {
        reveal CircuitValid();
        reveal CircuitPortNamesValid();
        var new_node := NewNode(c);
        var new_c := Circuit(
            NodeKind := c.NodeKind[new_node := COutput],
            PortSource := c.PortSource,
            HierLevel := c.HierLevel,
            PortMap := PortMappingAddOPort(c.PortMap, l, new_node as CPort)
        );
        assert forall n: CNode :: (NodeKind(new_c, n) == (if (n == new_node) then
            Some(COutput) else NodeKind(c, n))) ;
        assert CircuitNodeKindValid(c);
        assert CircuitPortSourceValid(c);
        reveal CircuitPortNamesValid();
        //MapExt.ExtendedMapValues(c.OPortNames, l, new_node);
        assert CircuitNodeKindValid(new_c);
        assert CircuitPortSourceValid(new_c);
        assert CircuitPortNamesValid(new_c);
        assert CircuitValid(new_c);
        (new_c, new_node)
    }

    lemma {:vcs_split_on_every_assert} NodeKindToGraphNoLoop(c: Circuit, nk: CNodeKind, hpn: HPNode)
        requires CircuitValid(c)
        requires CNodeKindSomewhatValid(nk)
        requires HierarchyPathValid(c, hpn.hp)
        requires !nk.CHier?
        ensures !DP.DigraphLoop(NodeKindToGraph(c, nk, hpn))
    {
        var g := NodeKindToGraph(c, nk, hpn);
        reveal DG.IsConnected();
        if nk.CComb? {
            forall p: DG.Path<HPNP> | DG.PathValid(g, p)
                ensures !DP.PathLoop(p)
            {
                reveal DG.PathValid();
                if |p.v| > 2 {
                    assert DG.IsConnected(g, p.v[0], p.v[1]);
                    //assert p.v[0].p in nk.OPorts;
                    //assert p.v[1].p in nk.IPorts;
                    //assert p.v[1].p !in nk.OPorts;
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
        if nk.CComb? {
            CNodeKindNoSelfPaths(nk);
        }
        reveal DG.IsConnected();
        assert (forall n: HPNP :: !DG.IsConnected(g, n, n));
        assert (forall n: HPNP, m: HPNP :: DG.IsConnected(g, n, m) ==> DG.IsNode(g, n) && DG.IsNode(g, m));
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

    lemma NewNodeAttemptHelper(m: set<CNode>)
        requires forall x: CNode :: x < (|m| as CNode) ==> x in m
        ensures forall x: CNode :: x >= (|m| as CNode) ==> x !in m
    {
        if |m| == 0 {
            assert (|m| as CNode) !in m;
        } else {
            assert |m|-1 < |m|;
            assert (|m|-1) as CNode in m;
            var new_m: set<CNode> := m - {(|m|-1) as CNode};
            assert |new_m| == |m| - 1;
            NewNodeAttemptHelper(new_m);
            assert forall x: CNode :: x >= (|m|-1) as CNode ==> x !in new_m;
            assert m == new_m + {(|m|-1) as CNode};
            assert forall x: CNode :: x >= (|m| as CNode) ==> x !in m;
        }
    }

    function NewNodeAttempt(c: Circuit, n: CNode): (r: CNode)
        requires forall m :: m < n ==> NodeKind(c, m).Some?
        ensures NodeKind(c, r).None?
        requires n <= |c.NodeKind| as CNode
        decreases |c.NodeKind| - (n as nat)
    {
        if n as nat == |c.NodeKind| then
            // Show that this CNode must be available if everything smaller is
            // already in use.
            assert forall m: CNode :: m < (|c.NodeKind| as CNode) ==> NodeKind(c, m).Some?;
            assert forall m: CNode :: NodeKind(c, m).Some? ==> m in c.NodeKind;
            assert forall m: CNode :: m < (|c.NodeKind| as CNode) ==> m in c.NodeKind;
            NewNodeAttemptHelper(c.NodeKind.Keys);
            assert forall m: CNode :: m >= (|c.NodeKind| as CNode) ==> m !in c.NodeKind;
            assert n !in c.NodeKind;
            n
        else
            if n in c.NodeKind then
                NewNodeAttempt(c, n+1)
            else
                n
    }

    function NewNode(c: Circuit): (r: CNode)
        ensures NodeKind(c, r).None?
    {
        NewNodeAttempt(c, 0)
    }

    ghost function ToDigraphThenAddNKGraph(c: Circuit, nk: CNodeKind, n: CNode): (r: DG.Digraph<HPNP>)
        requires CNodeKindSomewhatValid(nk)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires !nk.CHier?
        requires NodeKind(c, n).None?
        ensures DG.DigraphValid(r)
        ensures !DP.DigraphLoop(r)
    {
        var g := CtoGV(c);
        var hpn := HPNode(HP([]), n);
        var sg := NodeKindToGraph(c, nk, hpn);
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        NodeKindToGraphValid(c, nk, hpn);
        NodeKindToGraphNoLoop(c, nk, hpn);
        assert DG.DigraphValid(g);
        assert DG.DigraphValid(sg);
        reveal CtoG();
        reveal DC.DigraphsCompatible();
        reveal DG.IsNode();
        assert DC.DigraphsCompatible(g, sg);
        DC.CombineValid(g, sg);
        assert !DP.DigraphLoop(g);
        assert !DP.DigraphLoop(sg);
        DC.CombineNoLoops(g, sg);
        DC.Combine(g, sg)
    }

    lemma AddNodeAllHPs(c: Circuit, nk: CNodeKind, new_node: CNode)
        requires CNodeKindSomewhatValid(nk)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires !nk.CHier?
        requires !nk.CInput?
        requires !nk.COutput?
        requires NodeKind(c, new_node).None?
        ensures 
            var new_c := AddNodeInternal(c, nk, new_node);
            var hps := AllValidHierarchyPaths(c);
            var new_hps := AllValidHierarchyPaths(new_c);
            hps == new_hps
        {
        }

    //lemma {:vcs_split_on_every_assert} AddNodeAllHPNodes(c: Circuit, nk: CNodeKind, new_node: CNode)
    //    requires CNodeKindSomewhatValid(nk)
    //    requires CircuitValid(c)
    //    requires CircuitNoLoops(c)
    //    requires !nk.CHier?
    //    requires !nk.CInput?
    //    requires !nk.COutput?
    //    requires NodeKind(c, new_node).None?
    //    ensures 
    //        var new_c := AddNodeInternal(c, nk, new_node);
    //        var hpns := AllValidHPNodes(c);
    //        var new_hpns := AllValidHPNodes(new_c);
    //        hpns + {HPNode(HP([]), new_node)} == new_hpns
    //    {
    //        var new_c := AddNodeInternal(c, nk, new_node);
    //        var hps := AllValidHierarchyPaths(c);
    //        AddNodeAllHPs(c, nk, new_node);
    //        var new_hpnode := HPNode(HP([]), new_node);
    //        forall hp | hp in hps
    //            ensures (AllValidHPNodesFromHP(new_c, hp) == AllValidHPNodesFromHP(c, hp) +
    //                if hp == HP([]) then {new_hpnode} else {})
    //        {
    //            if hp == HP([]) {
    //                assert AllValidHPNodesFromHP(new_c, hp) == AllValidHPNodesFromHP(c, hp)
    //                 + {new_hpnode};
    //            } else {
    //                var hp_c := HierarchyPathCircuit(c, hp);
    //                var new_hp_c := HierarchyPathCircuit(new_c, hp);
    //                assert hp_c == new_hp_c;
    //                assert AllValidHPNodesFromHP(new_c, hp) == AllValidHPNodesFromHP(c, hp);
    //            }
    //        }
    //        assert AllValidHPNodes(new_c) == AllValidHPNodes(c)+ {new_hpnode};
    //    }

    lemma {:vcs_split_on_every_assert} AddNodeHPNPStillValid(c: Circuit, nk: CNodeKind, new_node: CNode)
        requires CNodeKindSomewhatValid(nk)
        requires CircuitValid(c)
        requires !nk.CHier?
        requires !nk.CInput?
        requires !nk.COutput?
        requires NodeKind(c, new_node).None?
        ensures
            var new_c := AddNodeInternal(c, nk, new_node);
            forall hpnp:: HPNPValid(c, hpnp) ==> HPNPValid(new_c, hpnp)
    {
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
    }
            
    //lemma {:vcs_split_on_every_assert} AddNodeAllHPNPs(c: Circuit, nk: CNodeKind, new_node: CNode)
    //    requires CNodeKindSomewhatValid(nk)
    //    requires CircuitValid(c)
    //    requires CircuitNoLoops(c)
    //    requires !nk.CHier?
    //    requires !nk.CInput?
    //    requires !nk.COutput?
    //    requires NodeKind(c, new_node).None?
    //    ensures 
    //        var new_c := AddNodeInternal(c, nk, new_node);
    //        var hpnps := AllValidHPNP(c);
    //        var new_hpnps := AllValidHPNP(new_c);
    //        var nk_hpnps := NodeKindHPNPs(c, nk, HPNode(HP([]), new_node));
    //        //hpnps + nk_hpnps == new_hpnps &&
    //        true
    //    {
    //        var new_c := AddNodeInternal(c, nk, new_node);
    //        var hpns := AllValidHPNodes(c);
    //        var new_hpns := AllValidHPNodes(new_c);
    //        var added_hpn := HPNode(HP([]), new_node);
    //        AddNodeAllHPNodes(c, nk, new_node);
    //        assert hpns + {added_hpn} == new_hpns;
    //    //var r := AllValidHPNPFromHPNs(c, hpns);
    //        assert AllValidHPNP(c) == AllValidHPNPFromHPNs(c, hpns);
    //        assert AllValidHPNP(new_c) == AllValidHPNPFromHPNs(new_c, new_hpns);
    //        assert AllValidHPNPFromHPNs(new_c, new_hpns) ==
    //            AllValidHPNPFromHPNs(new_c, hpns) +
    //            AllValidHPNPFromHPNs(new_c, {added_hpn});
    //        AddNodeHPNPStillValid(c, nk, new_node);
    //        assert AllValidHPNPFromHPNs(new_c, hpns) == AllValidHPNPFromHPNs(c, hpns);
    //        assert AllValidHPNP(new_c) == AllValidHPNP(c) +
    //            AllValidHPNPFromHPNs(new_c, {added_hpn});
    //        assert AllValidHPNPFromHPNs(new_c, {added_hpn}) == AllValidHPNPFromHPN(new_c, added_hpn);

    //    }


    //lemma AddNodeDigraphEquiv(c: Circuit, nk: CNodeKind, new_node: CNode)
    //    requires CNodeKindSomewhatValid(nk)
    //    requires CircuitValid(c)
    //    requires CircuitNoLoops(c)
    //    requires !nk.CHier?
    //    requires NodeKind(c, new_node).None?
    //    //ensures
    //    //    var new_c := AddNodeNoInputs(c, nk, new_node);
    //    //    var new_g1 := CtoG(new_c);
    //    //    var new_g2 := ToDigraphThenAddNKGraph(c, nk, new_node);
    //    //    new_g1 == new_g2
    //{
    //    var new_g1 := ToDigraphThenAddNKGraph(c, nk, new_node);
    //    var new_c := AddNodeInternal(c, nk, new_node);
    //    var g := CtoG(c);
    //    var new_g2 := CtoG(new_c);
    //    // Show that for new_g2 the nodes must be in the old circuit or be in the
    //    // new added node.
    //    // The only change for new_c is that we've added a node.
    //    assert new_c.NodeKind == c.NodeKind[new_node:=nk];
    //    assert new_g2.Nodes == AllValidHPNP(new_c);
    //    assert g.Nodes == AllValidHPNP(c);
    //    AddNodeAllHPNodes(c, nk, new_node);
    //    assert AllValidHPNodes(c) + {HPNode(HP([]), new_node)} == AllValidHPNodes(new_c);
    //    reveal CtoG();
    //    assert new_g1.Nodes == new_g2.Nodes;
    //    //assert new_g1 == new_g2;
    //}

    //function AddNodeNoInputs(c: Circuit, nk: CNodeKind, new_node: CNode): (r: Circuit)
    //    requires CircuitValid(c)
    //    requires !nk.CHier?
    //    requires !nk.CInput?
    //    requires !nk.COutput?
    //    requires CNodeKindSomewhatValid(nk)
    //    requires NodeKind(c, new_node).None?
    //    ensures CircuitValid(r)
    //{
    //    reveal CircuitValid();
    //    var new_c := Circuit(
    //        NodeKind := c.NodeKind[new_node := nk],
    //        PortSource := c.PortSource,
    //        HierLevel := c.HierLevel,
    //        IPortNames := c.IPortNames,
    //        OPortNames := c.OPortNames
    //    );
    //    assert forall n: CNode :: (NodeKind(new_c, n) == (if (n == new_node) then
    //        Some(nk) else NodeKind(c, n))) ;
    //    assert CircuitNodeKindValid(c);
    //    assert CircuitNodeKindValid(new_c);
    //    assert CircuitPortSourceValid(new_c);
    //    reveal CircuitPortNamesValid();
    //    assert CircuitValid(new_c);
    //    assert CNodeKindValid(new_c.HierLevel, nk);
    //    new_c
    //}

    function AddNode(c: Circuit, nk: CNodeKind): (r: (Circuit, CNode))
        requires CircuitValid(c)
        requires !nk.CHier?
        requires !nk.CInput?
        requires !nk.COutput?
        requires CNodeKindSomewhatValid(nk)
        ensures CircuitValid(r.0)
        ensures r.1 in r.0.NodeKind
        ensures r.0.NodeKind[r.1] == nk
        ensures forall p :: NP(r.1, p) !in r.0.PortSource
    {
        var new_node := NewNode(c);
        (AddNodeInternal(c, nk, new_node), new_node)
    }

    function AddNodeInternal(c: Circuit, nk: CNodeKind, new_node: CNode): (r: Circuit)
        requires CircuitValid(c)
        requires !nk.CHier?
        requires !nk.CInput?
        requires !nk.COutput?
        requires new_node !in c.NodeKind
        requires CNodeKindSomewhatValid(nk)
        ensures CircuitValid(r)
        ensures new_node in r.NodeKind
        ensures r.NodeKind[new_node] == nk
        ensures forall p :: NP(new_node, p) !in r.PortSource
    {
        reveal CircuitValid();
        var new_c := Circuit(
            NodeKind := c.NodeKind[new_node := nk],
            PortSource := c.PortSource,
            HierLevel := c.HierLevel,
            PortMap := c.PortMap
        );
        assert forall n: CNode :: (NodeKind(new_c, n) == (if (n == new_node) then
            Some(nk) else NodeKind(c, n))) ;
        assert CircuitNodeKindValid(c);
        assert CircuitPortSourceValid(c);
        reveal CircuitPortNamesValid();
        assert CircuitPortNamesValid(new_c);
        assert CircuitPortSourceValid(new_c);
        assert CircuitNodeKindValid(new_c);
        assert CircuitValid(new_c);
        new_c
    }

    function ConnectNodes(c: Circuit, onp: NP, inp: NP): (r: Circuit)
        requires CircuitValid(c)
        requires NPValidInput(c, inp)
        requires NPValidOutput(c, onp)
        requires inp !in c.PortSource
        ensures r.NodeKind == c.NodeKind
        ensures r.HierLevel == c.HierLevel
        ensures r.PortMap == c.PortMap
        ensures CircuitValid(r)
    {
        var new_c := Circuit(
            NodeKind := c.NodeKind,
            PortSource := c.PortSource[inp := onp],
            HierLevel := c.HierLevel,
            PortMap := c.PortMap
        );
        reveal CircuitValid();
        CircuitUpdatedCircuitNodeKindValid(c, new_c);
        assert CircuitNodeKindValid(new_c);
        assert CircuitPortSourceValid(new_c);
        reveal CircuitPortNamesValid();
        assert CircuitPortNamesValid(new_c);
        assert CircuitValid(new_c);
        new_c
    }
    function ConnectNodeINPs(c: Circuit, n: CNode, m: seq<(CPort, NP)>): (r: Circuit)
        requires CircuitValid(c)
        requires n in c.NodeKind
        requires
            var nk := c.NodeKind[n];
            (forall p, onp :: (p, onp) in m ==> IsIPort(nk, p) && NPValidOutput(c, onp) && NP(n, p) !in c.PortSource)
        requires forall i1: nat, i2: nat :: i1 < |m| && i2 < |m| && i1 != i2 ==> m[i1].0 != m[i2].0
        ensures CircuitValid(r)
        ensures r.NodeKind == c.NodeKind
        ensures r.HierLevel == c.HierLevel
        ensures r.PortMap == c.PortMap
        decreases m
    {
        if |m| == 0 then
            c
        else
            var (p, onp) := m[0];
            var new_c := ConnectNodes(c, onp, NP(n, p));
            ConnectNodeINPs(new_c, n, m[1..])
    }

    function AddNodeAndConnect(c: Circuit, nk: CNodeKind, m: seq<(string, NP)>): (r: (Circuit, CNode))
        requires CircuitValid(c)
        requires (forall s: string, onp: NP :: (s, onp) in m ==> s in PortMap(nk).inames && NPValidOutput(c, onp))
        requires forall i1: nat, i2: nat :: i1 < |m| && i2 < |m| && i1 != i2 ==> m[i1].0 != m[i2].0
        requires !nk.CHier?
        requires !nk.CInput?
        requires !nk.COutput?
        requires CNodeKindSomewhatValid(nk)
    {
        var (new_c, n) := AddNode(c, nk);
        assert n in new_c.NodeKind;
        assert forall p :: NP(n, p) !in new_c.PortSource;
        assert forall i1: nat, i2: nat :: i1 < |m| && i2 < |m| && i1 != i2 ==> m[i1].0 != m[i2].0;
        var portmap := seq(|m|, (i: nat) requires i < |m| => (PortNameToPort(nk, m[i].0), m[i].1));
        var final_c := ConnectNodeINPs(new_c, n, portmap);
        (final_c, n)
    }

}
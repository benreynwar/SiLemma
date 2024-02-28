module CircuitBuild {

    import opened Std.Wrappers
    import opened Circuit
    import opened CircuitPath
    import CS = CircuitStuff
    import P = Primitives

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
            DG.NodeValid(g, n) &&
            (StepBack(c, n) == DG.StepBack(g, n))
    {
        var g := CtoG(c);
        CtoGValid(c);
        reveal CtoG();
        assert DG.DigraphValid(g);
        HPNPInBound(c, n);
        assert DG.NodeValid(g, n);
        reveal HPNPConnected();
        reveal HPNPItoOConnected();
        reveal HPNPOtoIConnected();
        StepBackMatchesHPNPConnected(c, n);
        assert forall m :: m in DG.StepBack(g, n) ==> g.IsConnected(n, m);
        assert forall m :: m in StepBack(c, n) ==> g.IsConnected(n, m);
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
        assert forall n: CNode :: c.NodeKind(n) == None;
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
            NodeKind := _ => None,
            PortSource := _ => None,
            NodeBound := 0,
            PortBound := 0,
            HierLevel := 0,
            PortNames := _ => None
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
            (forall n: HPNP :: !g.IsNode(n)) &&
            (forall n, m: HPNP :: !g.IsConnected(n, m)) &&
            (!DG.DigraphLoop(g))
    {
        var c := MakeEmptyCircuit();
        EmptyCircuitHasNoHPNP();
        var g := CtoGV(c);
        reveal CtoG();
        assert DG.DigraphValid(g);
        assert forall n: HPNP :: !HPNPValid(c, n);
        assert forall n: HPNP :: !g.IsNode(n);
        EmptyCircuitHasNoHPNPConnected();
        assert forall n, m: HPNP :: !g.IsConnected(n, m);
        reveal DG.DigraphLoop();
        reveal DG.PathValid();
        assert !DG.DigraphLoop(g);
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

    //function AddNodeEquiv(c: Circuit, nk: CNodeKind, ip: map<CPort, NP>)
    //{
    //    var new_c := AddNode(c, nk, ip);
    //}

    function AddNodeNoInputs(c: Circuit, nk: CNodeKind): (r: (Circuit, CNode))
        requires CircuitValid(c)
        requires !nk.CHier?
        requires CNodeKindSomewhatValid(nk)
        ensures CircuitValid(r.0)
    {
        reveal CircuitValid();
        var new_node := c.NodeBound;
        var nk_port_bound := NKPortBound(nk);
        var new_c := Circuit(
            NodeKind := n => if n == new_node then Some(nk) else c.NodeKind(n),
            PortSource := c.PortSource,
            NodeBound := c.NodeBound+1,
            PortBound := if nk_port_bound > c.PortBound then nk_port_bound else c.PortBound,
            HierLevel := c.HierLevel,
            PortNames := c.PortNames
        );
        assert new_node < new_c.NodeBound;
        assert forall n: CNode :: (new_c.NodeKind(n) == (if (n == new_node) then
            Some(nk) else c.NodeKind(n))) ;
        assert CircuitNodeKindValid(c);
        assert CircuitPortSourceValid(c);
        assert forall p: CPort ::
                (IsIPort(nk, p) ==> p < new_c.PortBound) &&
                (IsOPort(nk, p) ==> p < new_c.PortBound);
        assert CNodeKindValid(new_c.HierLevel, new_c.PortBound, nk);
        (new_c, new_node)
    }

    function AddNode(c: Circuit, nk: CNodeKind, ip: map<CPort, NP>): (r: (Circuit, CNode))
        requires CircuitValid(c)
        requires !nk.CHier?
        ensures CircuitValid(r.0)
    {
        reveal CircuitValid();
        var new_node := c.NodeBound;
        var new_c := Circuit(
            NodeKind := n => if n == new_node then Some(nk) else c.NodeKind(n),
            PortSource := (inp: NP) =>
                if inp.n == new_node then
                    if inp.p in ip then
                        Some(ip[inp.p])
                    else
                        None
                else
                    c.PortSource(inp),
            NodeBound := c.NodeBound+1,
            PortBound := c.PortBound,
            HierLevel := c.HierLevel,
            PortNames := c.PortNames
        );
        assert new_node < new_c.NodeBound;
        assert forall n: CNode :: (new_c.NodeKind(n) == (if (n == new_node) then
            Some(nk) else c.NodeKind(n))) ;
        assert CircuitNodeKindValid(c);
        assert CircuitPortSourceValid(c);
        (c, new_node)
    }

    function MakeOneBitAdder(): Circuit
    {
        var g := MakeEmptyCircuit();
        assert CircuitValid(g);
        var (g, i_0) := AddIPort(g);
        assert CircuitValid(g);
        var (g, i_1) := AddIPort(g);
        var (g, node_xor) := AddNode(g, P.nk_xor, map[0 := i_0, 1 := i_1]);
        var xor_output := NP(node_xor, 0);
        var g := AddOPort(g, xor_output);
        var (g, node_add) := AddNode(g, P.nk_and, map[0 := i_0, 1 := i_1]);
        var add_output := NP(node_add, 0);
        var g := AddOPort(g, add_output);
        assert CircuitValid(g);
        g
    }


}
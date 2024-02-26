module CircuitStuff {

    import opened Std.Wrappers
    import Std.Collections.Seq
    import opened Circuit
    import opened CircuitPath
    import DG

    function {:opaque} INPtoONP(c: Circuit, inp: HPNP): (onp: HPNP)
        requires CircuitValid(c)
        requires CircuitComplete(lib, c)
        requires HPNPValidInput(lib, c, inp)
        ensures HPNPValidOutput(lib, c, onp)
        ensures HPNPConnected(lib, c, inp, onp)
    {
        reveal HPNPConnected();
        reveal HPNPItoOConnected();
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var inp_c := HierarchyPathCircuit(lib, c, inp.hpn.hp);
        HPCircuitComplete(lib, c, inp.hpn.hp);
        assert CircuitComplete(lib, inp_c);
        var inp_inp := NP(inp.hpn.n, inp.p);
        reveal CircuitComplete();
        var onp_onp := inp_c.PortSource(inp_inp).value;
        var onp := HPNP(HPNode(inp.hpn.hp, onp_onp.n), onp_onp.p);
        reveal CircuitValid();
        assert HPNPItoOConnected(lib, c, inp, onp);
        onp
    }

    function {:opaque} ONPtoDeeperINP(c: Circuit, onp: HPNP): (inp: HPNP)
        requires CircuitValid(lib, c)
        requires HPNPValidOutput(lib, c, onp)
        requires HPNPtoNK(lib, c, onp).CHier?
        ensures HPNPValidInput(lib, c, inp)
        ensures HPNPConnected(lib, c, onp, inp)
    {
        HPNPValidHPValid(lib, c, onp);
        var hp_c := HierarchyPathCircuit(lib, c, onp.hpn.hp);
        HierarchyPathCircuitValid(lib, c, onp.hpn.hp);
        var nk := HPNPtoNK(lib, c, onp);
        assert CNodeKindValid(lib, hp_c.HierLevel, hp_c.PortBound, nk);
        var lower_c := HPNPtoSubcircuit(lib, c, onp);
        reveal HPNPValidOutput();
        // It's an output port from a hier node.
        // It only connects to the input into the corresponding Output node in that circuit.
        // The port number should reference an output port CNode inside the Circuit.
        var maybe_level_nk := lower_c.NodeKind(onp.p as CNode);
        assert maybe_level_nk.Some?;
        assert maybe_level_nk.value.COutput?;
        var new_hp := ExtendHierarchyPath(lib, c, onp.hpn.hp, onp.hpn.n);
        var inp := HPNP(HPNode(new_hp, onp.p as CNode), 0);
        reveal HPNPConnected();
        reveal HPNPOtoIConnected();
        assert HPNPValidOutput(lib, c, onp);
        reveal HPNPValidInput();
        assert HPNPValidInput(lib, c, inp);
        assert HPNPOtoIConnected(lib, c, onp, inp);
        assert HPNPConnected(lib, c, onp, inp);
        inp
    }

    function {:vcs_split_on_every_assert} EvaluateINP(
            c: Circuit, m: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(lib, c)
        requires CircuitComplete(lib, c)
        requires CircuitNoLoops(lib, c)
        requires |p.v| > 0
        requires HPNPValidInput(lib, c, DG.PathEnd(p))
        requires PathValid(lib, c, p)
        decreases NumberOfRemainingNodes(lib, c, p), 1
    {
        var inp := DG.PathEnd(p);
        var onp := INPtoONP(lib, c, inp);
        assert HPNPValidOutput(lib, c, onp);
        var new_p := PathAppend(lib, c, p, onp);
        NoLoopsMeansNotInPath(lib, c, p, onp);
        NumberOfRemainingNodesDecreases(lib, c, p, onp);
        EvaluateONP(lib, c, m, new_p)
    }

    function {:vcs_split_on_every_assert} EvaluateONPCInput(
            c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(lib, c)
        requires CircuitComplete(lib, c)
        requires CircuitNoLoops(lib, c)
        requires |p.v| > 0
        requires HPNPValidOutput(lib, c, DG.PathEnd(p))
        requires PathValid(lib, c, p)
        requires HPNPtoNK(lib, c, DG.PathEnd(p)).CInput?
        decreases NumberOfRemainingNodes(lib, c, p), 1
    {
        var onp := DG.PathEnd(p);
        if HPLength(onp.hpn.hp) == 0 then
            // This is an input to the top level.
            isigs(onp)
        else
            var (hier_n, parent_hp) := HPHeadTail(onp.hpn.hp);
            HPNPValidHPValid(lib, c, onp);
            assert HierarchyPathValid(lib, c, parent_hp);
            // If it's an input inside a hier node, then it connects to
            // the input port on the hier node on the next level up.
            var inp := HPNP(HPNode(parent_hp, hier_n), onp.hpn.n as CPort);
            var hier_c := HierarchyPathCircuit(lib, c, parent_hp);
            HierarchyPathCircuitValid(lib, c, parent_hp);
            var nk := hier_c.NodeKind(inp.hpn.n).value;
            reveal CircuitValid();
            reveal HPNPValidInput();
            reveal HPNPValidOutput();
            assert CircuitNodeKindValid(lib, hier_c);
            assert IsIPort(lib, nk, inp.p);
            assert HPNPValidInput(lib, c, inp);
            var g := CtoG(lib, c);
            DG.NoLoopsMeansNoRepeats(g);
            reveal HPNPConnected();
            reveal HPNPOtoIConnected();
            assert HPNPConnected(lib, c, onp, inp);
            var new_p := PathAppend(lib, c, p, inp);
            NumberOfRemainingNodesDecreases(lib, c , p, inp);
            EvaluateINP(lib, c, isigs, new_p)
    }

    function {:vcs_split_on_every_assert} EvaluateONPCHier(
            c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(lib, c)
        requires CircuitComplete(lib, c)
        requires CircuitNoLoops(lib, c)
        requires |p.v| > 0
        requires HPNPValidOutput(lib, c, DG.PathEnd(p))
        requires PathValid(lib, c, p)
        requires HPNPtoNK(lib, c, DG.PathEnd(p)).CHier?
        decreases NumberOfRemainingNodes(lib, c, p), 1
    {
        var onp := DG.PathEnd(p);
        var inp := ONPtoDeeperINP(lib, c, onp);
        var new_p := PathAppend(lib, c, p, inp);
        NumberOfRemainingNodesDecreases(lib, c, p, inp);
        EvaluateINP(lib, c, isigs, new_p)
    }

    function EvaluateONPCComb(
            c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(lib, c)
        requires CircuitComplete(lib, c)
        requires CircuitNoLoops(lib, c)
        requires PathValid(lib, c, p)
        requires |p.v| > 0
        requires HPNPValidOutput(lib, c, DG.PathEnd(p))
        requires HPNPtoNK(lib, c, DG.PathEnd(p)).CComb?
        decreases NumberOfRemainingNodes(lib, c, p), 1
    {
        true
    }

    function EvaluateONP(c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(lib, c)
        requires CircuitComplete(lib, c)
        requires CircuitNoLoops(lib, c)
        requires PathValid(lib, c, p)
        requires |p.v| > 0
        requires HPNPValidOutput(lib, c, DG.PathEnd(p))
        decreases NumberOfRemainingNodes(lib, c, p), 2
    {
        var onp := DG.PathEnd(p);
        HPNPValidHPValid(lib, c, onp);
        var hp_c := HierarchyPathCircuit(lib, c, onp.hpn.hp);
        reveal HPNPValidOutput();
        var nk := hp_c.NodeKind(onp.hpn.n).value;
        match nk
        case CInput() => EvaluateONPCInput(lib, c, isigs, p)
        case CHier(_) => EvaluateONPCHier(lib, c, isigs, p)
        case CComb(_, _, _, _, _) => EvaluateONPCComb(lib, c, isigs, p)
        case CSeq() => isigs(onp)
        case CConst(v) => v
    }

}


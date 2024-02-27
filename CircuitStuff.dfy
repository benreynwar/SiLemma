module CircuitStuff {

    import opened Std.Wrappers
    import Std.Collections.Seq
    import opened Circuit
    import opened CircuitPath
    import DG

    function {:vcs_split_on_every_assert} EvaluateINP(
            c: Circuit, m: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires CircuitNoLoops(c)
        requires |p.v| > 0
        requires HPNPValidInput(c, DG.PathEnd(p))
        requires PathValid(c, p)
        decreases NumberOfRemainingNodes(c, p), 1
    {
        var inp := DG.PathEnd(p);
        var onp := INPtoONP(c, inp);
        assert HPNPValidOutput(c, onp);
        var new_p := PathAppend(c, p, onp);
        NoLoopsMeansNotInPath(c, p, onp);
        NumberOfRemainingNodesDecreases(c, p, onp);
        EvaluateONP(c, m, new_p)
    }

    function {:vcs_split_on_every_assert} EvaluateONPCInput(
            c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires CircuitNoLoops(c)
        requires |p.v| > 0
        requires HPNPValidOutput(c, DG.PathEnd(p))
        requires PathValid(c, p)
        requires HPNPtoNK(c, DG.PathEnd(p)).CInput?
        decreases NumberOfRemainingNodes(c, p), 1
    {
        var onp := DG.PathEnd(p);
        if HPLength(onp.hpn.hp) == 0 then
            // This is an input to the top level.
            isigs(onp)
        else
            var (hier_n, parent_hp) := HPHeadTail(onp.hpn.hp);
            HPNPValidHPValid(c, onp);
            assert HierarchyPathValid(c, parent_hp);
            // If it's an input inside a hier node, then it connects to
            // the input port on the hier node on the next level up.
            var inp := CInputONPtoINP(c, onp);
            var new_p := PathAppend(c, p, inp);
            NumberOfRemainingNodesDecreases(c , p, inp);
            EvaluateINP(c, isigs, new_p)
    }

    function {:vcs_split_on_every_assert} EvaluateONPCHier(
            c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires CircuitNoLoops(c)
        requires |p.v| > 0
        requires HPNPValidOutput(c, DG.PathEnd(p))
        requires PathValid(c, p)
        requires HPNPtoNK(c, DG.PathEnd(p)).CHier?
        decreases NumberOfRemainingNodes(c, p), 1
    {
        var onp := DG.PathEnd(p);
        var inp := CHierONPtoINP(c, onp);
        var new_p := PathAppend(c, p, inp);
        NumberOfRemainingNodesDecreases(c, p, inp);
        EvaluateINP(c, isigs, new_p)
    }

    function EvaluateONPCComb(
            c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, p)
        requires |p.v| > 0
        requires HPNPValidOutput(c, DG.PathEnd(p))
        requires HPNPtoNK(c, DG.PathEnd(p)).CComb?
        decreases NumberOfRemainingNodes(c, p), 1
    {
        true
    }

    function EvaluateONP(c: Circuit, isigs: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires CircuitNoLoops(c)
        requires PathValid(c, p)
        requires |p.v| > 0
        requires HPNPValidOutput(c, DG.PathEnd(p))
        decreases NumberOfRemainingNodes(c, p), 2
    {
        var onp := DG.PathEnd(p);
        HPNPValidHPValid(c, onp);
        var hp_c := HierarchyPathCircuit(c, onp.hpn.hp);
        reveal HPNPValidOutput();
        var nk := hp_c.NodeKind(onp.hpn.n).value;
        match nk
        case CInput() => EvaluateONPCInput(c, isigs, p)
        case CHier(_) => EvaluateONPCHier(c, isigs, p)
        case CComb(_, _, _, _, _) => EvaluateONPCComb(c, isigs, p)
        case CSeq() => isigs(onp)
        case CConst(v) => v
    }

}


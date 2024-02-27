module CircuitBuild {

    import opened Std.Wrappers
    import opened Circuit
    import opened CircuitPath
    import CS = CircuitStuff

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

}
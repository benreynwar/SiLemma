module CircuitHPNP {

    import opened Std.Wrappers
    import Seq = Std.Collections.Seq
    import Functions = Std.Functions
    import SeqNatToNat
    import SeqExt
    import opened CircuitBase
    import opened CircuitHierarchy
    import Utils

    ghost function {:vcs_split_on_every_assert} AllValidHPNPFromHPNs(c: Circuit, hpns: set<HPNode>): (r: set<HPNP>)
        requires CircuitValid(c)
        requires forall hpn :: hpn in hpns ==> HPNodeValid(c, hpn)
        ensures forall hpnp :: hpnp in r <==> HPNPValid(c, hpnp) && hpnp.hpn in hpns
    {
        if |hpns| == 0 then
            {}
        else
            var hpn :| hpn in hpns;
            assert HPNodeValid(c, hpn);
            reveal HPNodeValid();
            assert HierarchyPathValid(c, hpn.hp);
            var next_hpns := hpns - {hpn};
            var next_hpnps := AllValidHPNPFromHPNs(c, next_hpns);
            var hp_c := HierarchyPathCircuit(c, hpn.hp);
            var nk := hp_c.NodeKind[hpn.n];
            var this_hpnps := (set p | p in IPorts(nk) + OPorts(nk) :: HPNP(hpn, p));
            reveal Seq.ToSet();
            assert forall hpnp :: hpnp in this_hpnps ==> IsIPort(nk, hpnp.p) || IsOPort(nk, hpnp.p);
            reveal HPNPValidInput();
            reveal HPNPValidOutput();
            assert forall hpnp :: hpnp in this_hpnps ==> HPNPValid(c, hpnp);
            this_hpnps + next_hpnps
    }

    ghost function AllValidHPNP(c: Circuit): (r: set<HPNP>)
        requires CircuitValid(c)
        ensures forall hpnp :: hpnp in r <==> HPNPValid(c, hpnp)
    {
        var hpns := AllValidHPNodes(c);
        assert forall hpn :: hpn in hpns <==> HPNodeValid(c, hpn);
        var r := AllValidHPNPFromHPNs(c, hpns);
        assert forall hpnp :: hpnp in r <==> HPNPValid(c, hpnp) && hpnp.hpn in hpns;
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        reveal HPNodeValid();
        assert forall hpnp :: HPNPValid(c, hpnp) ==> HPNodeValid(c, hpnp.hpn);
        r
    }

    function HPToHPNode(c: Circuit, hp: HierarchyPath): (r: HPNode)
        requires CircuitValid(c)
        requires |hp.v| > 0
        requires HierarchyPathValid(c, hp)
        ensures HPNodeValid(c, r)
        ensures HierarchyPathValid(c, r.hp)
        ensures
            var hier_c := HierarchyPathCircuit(c, r.hp);
            NodeKind(hier_c, r.n).Some? && NodeKind(hier_c, r.n).value.CHier?
    {
        var parent_hp := HP(hp.v[..|hp.v|-1]);
        var cs := HPToCircuitSeq(c, hp);
        var parent_cs := cs[..|cs|-1];
        HPCircuitSeqMatchHPValid(parent_cs, parent_hp);
        HPToCircuitSeqSame(c, hp, parent_hp, |parent_hp.v|);
        assert HierarchyPathValid(c, parent_hp);
        var hier_c := HierarchyPathCircuit(c, parent_hp);
        assert hier_c == cs[|cs|-2];
        var head := hp.v[|hp.v|-1];
        assert IsChildCircuit(hier_c, cs[|cs|-1], head);
        assert NodeKind(hier_c, head).Some?;
        var parent_hpn := HPNode(parent_hp, head);
        reveal HPNodeValid();
        parent_hpn
    }

    lemma CInputONPtoINPConnected(c: Circuit, onp: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, onp)
        requires HPNPtoNK(c, onp).CInput?
        requires HPLength(onp.hpn.hp) > 0
        ensures HPNPConnected(c, onp, CInputONPtoINP(c, onp))
    {
        reveal HPNPConnected();
        reveal HPNPOtoIConnected();
        var inp := CInputONPtoINP(c, onp);
        reveal ONPtoINP();
        assert HPNPOtoIConnected(c, onp, inp);
    }

    lemma HierCrossHelper(c: Circuit, hp: HierarchyPath, parent_c: Circuit, child_c: Circuit)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        requires |hp.v| > 0
        requires
            var cs := HPToCircuitSeq(c, hp);
            parent_c == cs[|cs|-2] &&
            child_c == cs[|cs|-1]
        ensures
            IsChildCircuit(parent_c, child_c, hp.v[|hp.v|-1])
        ensures
            HierarchyPathCircuit(c, hp) == child_c
        ensures
            var hp_to_parent := HP(hp.v[..|hp.v|-1]);
            HierarchyPathValid(c, hp_to_parent) &&
            HierarchyPathCircuit(c, hp_to_parent) == parent_c
    {
        var cs := HPToCircuitSeq(c, hp);
        assert parent_c == cs[|cs|-2];
        assert child_c == cs[|cs|-1];
        assert IsChildCircuit(parent_c, child_c, hp.v[|hp.v|-1]);
        var hp_to_parent := HP(hp.v[..|hp.v|-1]);
        HPCircuitSeqMatchHPValid(cs[..|cs|-1], hp_to_parent);
        assert HierarchyPathValid(c, hp_to_parent);
        HPToCircuitSeqSame(c, hp, HP(hp.v[..|hp.v|-1]), |hp.v|-1);
        assert HierarchyPathCircuit(c, hp_to_parent) == parent_c;
    }

    function {:opaque} {:vcs_split_on_every_assert} CInputONPtoINP(c: Circuit, onp: HPNP): (r: HPNP)
        // This takes an output from a CInput node, and connects it to
        // the input into a CHier node in the next level up in the hierarchy.
        requires CircuitValid(c)
        requires HPNPValidOutput(c, onp)
        requires HPNPtoNK(c, onp).CInput?
        requires HPLength(onp.hpn.hp) > 0
        ensures HPNPValidInput(c, r)
    {
        reveal HPNPValidOutput();
        var parent_hpn := HPToHPNode(c, onp.hpn.hp);
        // If it's an input inside a hier node, then it connects to
        // the input port on the hier node on the next level up.
        var cs := HPToCircuitSeq(c, onp.hpn.hp);
        var inp := HPNP(parent_hpn, onp.hpn.n as CPort);
        var onp_c := cs[|cs|-1];
        var inp_c := cs[|cs|-2];
        HierCrossHelper(c, onp.hpn.hp, inp_c, onp_c);
        reveal HPNPValidInput();
        inp
    }

    lemma CHierONPtoINPConnected(c: Circuit, onp: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, onp)
        requires HPNPtoNK(c, onp).CHier?
        ensures HPNPConnected(c, onp, CHierONPtoINP(c, onp))
    {
        reveal HPNPConnected();
        reveal HPNPOtoIConnected();
        var inp := CHierONPtoINP(c, onp);
        reveal ONPtoINP();
        assert HPNPOtoIConnected(c, onp, inp);
    }

    function {:opaque} CHierONPtoINP(c: Circuit, onp: HPNP): (inp: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, onp)
        requires HPNPtoNK(c, onp).CHier?
        ensures HPNPValidInput(c, inp)
    {
        reveal HPNPValidOutput();
        var inp_hp := ExtendHierarchyPath(c, onp.hpn.hp, onp.hpn.n);
        var cs := HPToCircuitSeq(c, inp_hp);
        var inp := HPNP(HPNode(inp_hp, onp.p as CNode), 0);
        var onp_c := cs[|cs|-2];
        var inp_c := cs[|cs|-1];
        HierCrossHelper(c, inp_hp, onp_c, inp_c);
        reveal HPNPValidInput();
        assert HPNPValidInput(c, inp);
        inp
    }

    function CCombONPtoINP(c: Circuit, n: HPNP): (r: set<HPNP>)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, n)
        requires HPNPtoNK(c, n).CComb?
        ensures forall m :: m in r ==> HPNPValid(c, m)
    {
        HPNPValidHPValid(c, n);
        var hp_c := HierarchyPathCircuit(c, n.hpn.hp);
        reveal HPNPValidOutput();
        reveal HPNPValidInput();
        var nk := NodeKind(hp_c, n.hpn.n).value;
        var inps := set p: CPort | (p in nk.IPorts && nk.PathExists(n.p, p)) :: HPNP(n.hpn, p);
        inps
    }

    function {:opaque} ONPtoINP(c: Circuit, onp: HPNP): (r: set<HPNP>)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, onp)
        ensures forall inp :: inp in r ==> HPNPValidInput(c, inp)
    {
        HPNPValidHPValid(c, onp);
        var hp_c := HierarchyPathCircuit(c, onp.hpn.hp);
        reveal HPNPValidOutput();
        var nk := NodeKind(hp_c, onp.hpn.n).value;
        match nk
        case CInput() => if HPLength(onp.hpn.hp) > 0 then {CInputONPtoINP(c, onp)} else {}
        case CHier(_) => {CHierONPtoINP(c, onp)}
        case CComb(_, _, _, _, _) => CCombONPtoINP(c, onp)
        case CSeq() => {}
        case CConst(v) => {}
    }

    predicate {:opaque} HPNPOtoIConnected(c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, a)
        requires HPNPValidInput(c, b)
    {
        HPNPValidHPValid(c, a);
        var onps := ONPtoINP(c, a);
        b in onps
    }

    lemma INPtoONPConnected(c: Circuit, inp: HPNP)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HPNPValidInput(c, inp)
        ensures HPNPConnected(c, inp, INPtoONP(c, inp))
    {
        reveal INPtoONP();
        INPtoMaybeONPConnected(c, inp);
        var onp := INPtoONP(c, inp);
    }

    function {:opaque} INPtoONP(c: Circuit, inp: HPNP): (onp: HPNP)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HPNPValidInput(c, inp)
        ensures HPNPValidOutput(c, onp)
    {
        reveal HPNPConnected();
        reveal HPNPItoOConnected();
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var inp_c := HierarchyPathCircuit(c, inp.hpn.hp);
        HPCircuitComplete(c, inp.hpn.hp);
        assert CircuitComplete(inp_c);
        var inp_inp := NP(inp.hpn.n, inp.p);
        reveal CircuitComplete();
        var onp_onp := PortSource(inp_c, inp_inp).value;
        var onp := HPNP(HPNode(inp.hpn.hp, onp_onp.n), onp_onp.p);
        reveal CircuitValid();
        var maybe_onp := INPtoMaybeONP(c, inp);
        assert maybe_onp.Some?;
        maybe_onp.value
    }

    lemma INPtoMaybeONPConnected(c: Circuit, inp: HPNP)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HPNPValidInput(c, inp)
        ensures
            var maybe_onp := INPtoMaybeONP(c, inp);
            maybe_onp.Some? ==> HPNPConnected(c, inp, maybe_onp.value)
    {
        reveal HPNPConnected();
        reveal INPtoONP();
        var onp := INPtoONP(c, inp);
        assert HPNPValidOutput(c, onp);
        reveal HPNPItoOConnected();
    }

    function INPtoMaybeONP(c: Circuit, inp: HPNP): (onp: Option<HPNP>)
        requires CircuitValid(c)
        requires HPNPValidInput(c, inp)
        ensures onp.Some? ==> HPNPValidOutput(c, onp.value)
    {
        reveal HPNPConnected();
        reveal HPNPItoOConnected();
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var inp_c := HierarchyPathCircuit(c, inp.hpn.hp);
        var inp_inp := NP(inp.hpn.n, inp.p);
        reveal CircuitComplete();
        var maybe_onp_onp := PortSource(inp_c, inp_inp);
        match maybe_onp_onp
        case None =>
            None
        case Some(onp_onp) =>
            var onp := HPNP(HPNode(inp.hpn.hp, onp_onp.n), onp_onp.p);
            reveal CircuitValid();
            assert CircuitValid(inp_c);
            assert HPNPValidOutput(c, onp);
            Some(onp)
    }

    predicate {:opaque} HPNPItoOConnected(c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(c)
        requires HPNPValidInput(c, a)
        requires HPNPValidOutput(c, b)
    {
        var maybe_inp := INPtoMaybeONP(c, a);
        match maybe_inp
        case None =>
            false
        case Some(inp) =>
            inp == b
    }

    lemma HPNPItoOConnectedINPtoONP(c: Circuit, inp: HPNP, m: HPNP)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HPNPValidInput(c, inp)
        requires HPNPValidOutput(c, m)
        ensures
            var onp := INPtoONP(c, inp);
            HPNPItoOConnected(c, inp, m) <==> m == onp
    {
        reveal INPtoONP();
        reveal HPNPItoOConnected();
    }

    predicate {:opaque} HPNPConnected(c: Circuit,  a: HPNP, b: HPNP)
        requires CircuitValid(c)
    {
        (HPNPValidInput(c, a) && HPNPValidOutput(c, b) &&
            HPNPItoOConnected(c, a, b)) ||
        (HPNPValidOutput(c, a) && HPNPValidInput(c, b) &&
            HPNPOtoIConnected(c, a, b))
    }

    function HPNPToSeqNat(hpnp: HPNP): (r: seq<nat>)
    {
        var l := |hpnp.hpn.hp.v|;
        var hp_seq := SeqCNodeToSeqNat(hpnp.hpn.hp.v);
        hp_seq + [hpnp.hpn.n as nat, hpnp.p as nat]
    }

    function SeqNatToHPNP(ns: seq<nat>): (r: Option<HPNP>)
    {
        if |ns| < 2 then
            None
        else
            var p := ns[|ns|-1];
            var n := ns[|ns|-2];
            var hp_seq := seq(|ns|-2, (i: nat) requires i < |ns| => ns[i] as CNode);
            Some(HPNP(HPNode(HP(hp_seq), n as CNode), p as CPort))
    }

    lemma NoSelfConnections(c: Circuit, n: HPNP)
        requires CircuitValid(c)
        ensures !HPNPConnected(c, n, n)
    {
        reveal HPNPConnected();
        if HPNPValid(c, n) {
            HPNPValidHPValid(c, n);
            var hier_c := HierarchyPathCircuit(c, n.hpn.hp);
            reveal CircuitValid();
            assert CircuitNodeKindValid(hier_c);
            if HPNPValidInput(c, n) {
                reveal HPNPValidInput();
                reveal HPNPValidOutput();
                assert !HPNPValidOutput(c, n);
                assert !HPNPConnected(c, n, n);
            } else {
            }
        } else {
            assert !HPNPValidInput(c, n);
            assert !HPNPValidOutput(c, n);
        }
    }

    lemma ConnectedNodesValid(c: Circuit, n: HPNP, m: HPNP)
        requires CircuitValid(c)
        ensures HPNPConnected(c, n, m) ==> HPNPValid(c, n) && HPNPValid(c, m)
    {
        reveal HPNPConnected();
    }

    function HPNPtoSubcircuit(c: Circuit, hpnp: HPNP): Circuit
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        requires HPNPtoNK(c, hpnp).CHier?
    {
        var nk := HPNPtoNK(c, hpnp);
        HPNPValidHPValid(c, hpnp);
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        assert CNodeKindValid(hp_c.HierLevel, nk);
        nk.c
    }

    function ExtendHierarchyPath(c: Circuit, hp: HierarchyPath, n: CNode): (r: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        requires
            var hp_c := HierarchyPathCircuit(c, hp);
            NodeKind(hp_c, n).Some? && NodeKind(hp_c, n).value.CHier?
        ensures HierarchyPathValid(c, r)
    {
        var cs := HPToCircuitSeq(c, hp);
        var hp_c := cs[|cs|-1];
        var next_c := NodeToSubcircuit(hp_c, n);
        var new_cs := cs + [next_c];
        reveal CircuitValid();
        assert CircuitValid(hp_c);
        assert CircuitNodeKindValid(hp_c);
        assert CircuitValid(next_c);
        var new_hp := HP(hp.v + [n]);
        assert HPCircuitSeqMatch(new_cs, new_hp);
        HPCircuitSeqMatchHPValid(new_cs, new_hp);
        new_hp
    }


    lemma HPCircuitComplete(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires HierarchyPathValid(c, hp)
        ensures
            var hp_c := HierarchyPathCircuit(c, hp);
            CircuitValid(hp_c) &&
            CircuitComplete(hp_c)
        decreases |hp.v|
    {
        if |hp.v| == 0 {
        } else {
            var (head, tail) := HPHeadTail(hp);
            HPTailValid(c, hp);
            reveal CircuitComplete();
            HPCircuitComplete(c, tail);
        }
    }

}
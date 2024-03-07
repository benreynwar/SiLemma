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
        ensures forall hpnp :: hpnp in r ==> HPNPValid(c, hpnp)
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
        ensures forall hpnp :: hpnp in r ==> HPNPValid(c, hpnp)
    {
        var hpns := AllValidHPNodes(c);
        AllValidHPNPFromHPNs(c, hpns)
    }

    function {:opaque} CInputONPtoINP(c: Circuit, onp: HPNP): (r: HPNP)
        // This takes an output from a CInput node, and connects it to
        // the input into a CHier node in the next level up in the hierarchy.
        requires CircuitValid(c)
        requires HPNPValidOutput(c, onp)
        requires HPNPtoNK(c, onp).CInput?
        requires HPLength(onp.hpn.hp) > 0
        ensures HPNPValidInput(c, r)
    {
        var (hier_n, parent_hp) := HPHeadTail(onp.hpn.hp);
        HPNPValidHPValid(c, onp);
        assert HierarchyPathValid(c, parent_hp);
        // If it's an input inside a hier node, then it connects to
        // the input port on the hier node on the next level up.
        var inp := HPNP(HPNode(parent_hp, hier_n), onp.hpn.n as CPort);
        var (hier_n, parent_hp) := HPHeadTail(onp.hpn.hp);
        HPNPValidHPValid(c, onp);
        var hier_c := HierarchyPathCircuit(c, parent_hp);
        HierarchyPathCircuitValid(c, parent_hp);
        var nk := NodeKind(hier_c, inp.hpn.n).value;
        assert HierarchyPathValid(c, parent_hp);
        reveal HPNPValidInput();
        reveal CircuitValid();
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        assert CircuitNodeKindValid(hier_c);
        assert IsIPort(nk, inp.p);
        assert HPNPValidInput(c, inp);
        inp
    }

    function {:opaque} CHierONPtoINP(c: Circuit, onp: HPNP): (inp: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, onp)
        requires HPNPtoNK(c, onp).CHier?
        ensures HPNPValidInput(c, inp)
    {
        HPNPValidHPValid(c, onp);
        var hp_c := HierarchyPathCircuit(c, onp.hpn.hp);
        HierarchyPathCircuitValid(c, onp.hpn.hp);
        var nk := HPNPtoNK(c, onp);
        assert CNodeKindValid(hp_c.HierLevel, nk);
        var lower_c := HPNPtoSubcircuit(c, onp);
        reveal HPNPValidOutput();
        // It's an output port from a hier node.
        // It only connects to the input into the corresponding Output node in that circuit.
        // The port number should reference an output port CNode inside the Circuit.
        var maybe_level_nk := NodeKind(lower_c, onp.p as CNode);
        assert maybe_level_nk.Some?;
        assert maybe_level_nk.value.COutput?;
        var new_hp := ExtendHierarchyPath(c, onp.hpn.hp, onp.hpn.n);
        var inp := HPNP(HPNode(new_hp, onp.p as CNode), 0);
        reveal HPNPConnected();
        assert HPNPValidOutput(c, onp);
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
        HierarchyPathCircuitValid(c, inp.hpn.hp);
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

    //function HPNPToNat(hpnp: HPNP): nat
    //{
    //    var ns := HPNPToSeqNat(hpnp);
    //    SeqNatToNat.ArbLenNatsToNat(ns)
    //}

    //function NatToHPNP(n: nat): Option<HPNP>
    //{
    //    var ns := SeqNatToNat.NatToArbLenNats(n);
    //    var hpnp := SeqNatToHPNP(ns);
    //    hpnp
    //}

    //lemma NatToHPNPToNat(n: nat)
    //    requires NatToHPNP(n).Some?
    //    ensures HPNPToNat(NatToHPNP(n).value) == n
    //{
    //}

    //lemma HPNPToNatToHPNP(hpnp: HPNP)
    //    ensures NatToHPNP(HPNPToNat(hpnp)) == Some(hpnp)
    //{
    //}

    //lemma SeqCNodeNotEqualSeqNatNotEqual(a: seq<CNode>, b: seq<CNode>)
    //    ensures a != b ==> SeqCNodeToSeqNat(a) != SeqCNodeToSeqNat(b)
    //{
    //    if a == b {
    //        assert forall i: nat :: i < |a| ==> a[i] == b[i];
    //    } else {
    //        if |a| == |b| {
    //            assert exists i: nat :: i < |a| && a[i] != b[i];
    //            var i: nat :| i < |a| && a[i] != b[i];
    //            assert SeqCNodeToSeqNat(a)[i] != SeqCNodeToSeqNat(b)[i];
    //        } else {
    //        }
    //    }
    //}

    //lemma HPNPToSeqNatUnique(a: HPNP, b: HPNP)
    //    ensures (a != b) ==> (HPNPToSeqNat(a) != HPNPToSeqNat(b))
    //{
    //    var na := HPNPToSeqNat(a);
    //    var nb := HPNPToSeqNat(b);
    //    if (|a.hpn.hp.v| != |b.hpn.hp.v|) {
    //    } else {
    //        if (a != b) {
    //            var a_v := a.hpn.hp.v;
    //            var b_v := b.hpn.hp.v;
    //            if (a_v != b_v) {
    //                assert |na| == |a_v| + 2;
    //                assert a_v != b_v;
    //                var a_v_n := SeqCNodeToSeqNat(a_v);
    //                var b_v_n := SeqCNodeToSeqNat(b_v);
    //                SeqCNodeNotEqualSeqNatNotEqual(a_v, b_v);
    //                assert a_v_n != b_v_n;
    //                assert na[..|a_v|] == a_v_n;
    //                assert nb[..|b_v|] == b_v_n;
    //            } else if (a.hpn.n != b.hpn.n) {
    //                assert na[|a_v|] == a.hpn.n as nat;
    //            } else if (a.p != b.p) {
    //                assert na[|a_v|+1] == a.p as nat;
    //            } else {
    //            }
    //        } else {
    //        }
    //    }
    //}

    //lemma HPNPToNatInjective(a: HPNP, b: HPNP)
    //    ensures (a != b) ==> (HPNPToNat(a) != HPNPToNat(b))
    //{
    //    HPNPToSeqNatUnique(a, b);
    //    SeqNatToNat.ArbLenNatsToNatUnique(HPNPToSeqNat(a), HPNPToSeqNat(b));
    //}

    //lemma HPNPToNatInjectiveAll()
    //    ensures Functions.Injective(HPNPToNat)
    //{
    //    forall a, b: HPNP
    //    {
    //        HPNPToNatInjective(a, b);
    //    }
    //}

    //lemma NatToHPNPInjectiveAll()
    //    ensures Functions.Injective(NatToHPNP)
    //{
    //}
        //Functions.Injective(g.NodeMap) && Functions.Injective(g.InvNodeMap)


    lemma NoSelfConnections(c: Circuit, n: HPNP)
        requires CircuitValid(c)
        ensures !HPNPConnected(c, n, n)
    {
        reveal HPNPConnected();
        if HPNPValid(c, n) {
            HPNPValidHPValid(c, n);
            var hier_c := HierarchyPathCircuit(c, n.hpn.hp);
            HierarchyPathCircuitValid(c, n.hpn.hp);
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

//    lemma OutOfBoundInvalid(c: Circuit, n: HPNP)
//        requires CircuitValid(c)
//        ensures HPNPToNat(n) >= HPNPBound(c) ==> !HPNPValid(c, n)
//    {
//        if HPNPToNat(n) >= HPNPBound(c) {
//            if HPNPValid(c, n) {
//                HPNPInBound(c, n);
//                assert HPNPToNat(n) < HPNPBound(c);
//                assert false;
//            } else {
//            }
//            assert !HPNPValid(c, n);
//        }
//    }
//
//    lemma HPNPAsSeqNatInBound(c: Circuit, hpnp: HPNP)
//        requires CircuitValid(c)
//        requires HPNPValid(c, hpnp)
//        ensures forall n: nat :: n in HPNPToSeqNat(hpnp) ==>
//            n < HPNPElementBound(c)
//    {
//        HPNPElementsInBound(c, hpnp);
//        var hpnp_as_seq := HPNPToSeqNat(hpnp);
//        var element_bound := HPNPElementBound(c); 
//        var hp := hpnp.hpn.hp;
//        assert forall n: CNode :: n in hp.v ==> n as nat < element_bound;
//        assert forall i: nat :: i < |hp.v| ==> (hp.v[i] in hp.v);
//        assert forall i: nat :: i < |hp.v| ==> hp.v[i] as nat < element_bound;
//        assert hpnp.hpn.n as nat < element_bound;
//        assert hpnp.p as nat < element_bound;
//        assert forall i: nat :: i < |hpnp_as_seq| ==>
//            if i < |hp.v| then
//                (hpnp_as_seq[i] == hp.v[i] as nat) &&
//                (hp.v[i] as nat < element_bound) &&
//                (hpnp_as_seq[i] < element_bound)
//            else
//                true;
//        assert forall n: nat :: n in hpnp_as_seq ==> n < element_bound;
//    }
//
//    lemma HPNodeInBound(c: Circuit, hpn: HPNode)
//        requires CircuitValid(c)
//        requires HPNodeValid(c, hpn)
//        //ensures hpn.n as nat < HPNPElementBound(c)
//        ensures forall e :: e in SeqCNodeToSeqNat(hpn.hp.v) ==> e < HPNPElementBound(c)
//    {
//        var element_bound := HPNPElementBound(c);
//        reveal HPNodeValid();
//        assert HierarchyPathValid(c, hpn.hp);
//        HPInHierNodeBound(c, hpn.hp);
//        var hier_c := HierarchyPathCircuit(c, hpn.hp);
//        HierarchyPathCircuitValid(c, hpn.hp);
//        SubcircuitInHierNodeBound(c, hpn.hp);
//        assert hier_c.NodeBound as nat <= element_bound;
//        SubcircuitInHierPortBound(c, hpn.hp);
//        assert hier_c.PortBound as nat <= element_bound;
//        reveal CircuitValid();
//        assert CircuitNodeKindValid(hier_c);
//        reveal HPNPValidInput();
//        reveal HPNPValidOutput();
//        //assert hpnp.p < hier_c.PortBound;
//        assert hpn.n < hier_c.NodeBound;
//        assert forall e :: e in SeqCNodeToSeqNat(hpn.hp.v) ==> e < element_bound;
//    }
//
//    lemma HPNPInBound(c: Circuit, hpnp: HPNP)
//        requires CircuitValid(c)
//        requires HPNPValid(c, hpnp)
//        ensures HPNPToNat(hpnp) < HPNPBound(c)
//    {
//        var hpnp_as_seq := HPNPToSeqNat(hpnp);
//        var element_bound := HPNPElementBound(c); 
//        HPNPAsSeqNatInBound(c, hpnp);
//        var len := |hpnp_as_seq|;
//        var bound := SeqNatToNat.ArbLenNatsToNatBound(c.HierLevel+2, element_bound);
//        assert bound == HPNPBound(c);
//        assert forall n: nat :: n in hpnp_as_seq ==> n < element_bound;
//        assert forall i: nat :: i < |hpnp_as_seq| ==> hpnp_as_seq[i] in hpnp_as_seq;
//        assert forall i: nat :: i < |hpnp_as_seq| ==> hpnp_as_seq[i] < element_bound;
//        HPNPValidHPValid(c, hpnp);
//        HPLengthBound(c, hpnp.hpn.hp);
//        assert HPLength(hpnp.hpn.hp) <= c.HierLevel;
//        assert |hpnp_as_seq| <= c.HierLevel + 2;
//        SeqNatToNat.ArbLenNatsToNatBounded(hpnp_as_seq, c.HierLevel+2, element_bound);
//        assert SeqNatToNat.ArbLenNatsToNat(hpnp_as_seq) < bound;
//    }
//
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
        var hp_c := HierarchyPathCircuit(c, hp);
        HierarchyPathCircuitValid(c, hp);
        reveal CircuitValid();
        assert CircuitNodeKindValid(hp_c);
        var next_c := NodeToSubcircuit(hp_c, n);
        assert CircuitValid(next_c);
        HP(hp.v +[n])
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
            reveal CircuitComplete();
            HPCircuitComplete(c, tail);
        }
    }

}
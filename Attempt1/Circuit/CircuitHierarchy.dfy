module CircuitHierarchy {

    import opened CircuitBase

    predicate HierarchyPathValid(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        decreases |hp.v|, 0
    {
        if HPLength(hp) == 0 then
            true
        else
            var (start, children) := HPStartChildren(hp);
            NodeKind(c, start).Some? && NodeKind(c, start).value.CHier? &&
            reveal CircuitValid();
            assert CircuitNodeKindValid(c);
            var next_c := NodeKind(c, start).value.c;
            HierarchyPathValid(next_c, children)
    }

    function HPInternalCircuit(c: Circuit, hp: HierarchyPath, pos: nat): (r: Circuit)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        requires pos <= HPLength(hp)
        ensures CircuitValid(r)
    {
        var cs := HPToCircuitSeq(c, hp);
        cs[pos]
    }

    lemma HPToCircuitSeqSame(c: Circuit, hp1: HierarchyPath, hp2: HierarchyPath, index: nat)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp1)
        requires HierarchyPathValid(c, hp2)
        requires index <= |hp1.v|
        requires index <= |hp2.v|
        requires forall i: nat :: i < index ==> hp1.v[i] == hp2.v[i]
        ensures forall i: nat :: i <= index ==> HPToCircuitSeq(c, hp1)[i] == HPToCircuitSeq(c, hp2)[i]
    {
        if index == 0 {
        } else {
            assert hp1.v[0] == hp2.v[0];
            var hp_c := Subcircuit(c, hp1.v[0]);
            HPToCircuitSeqSame(hp_c, HP(hp1.v[1..]), HP(hp2.v[1..]), index-1);
        }
    }

    predicate IsChildCircuit(parent: Circuit, child: Circuit, n: CNode)
    {
        var nk := NodeKind(parent, n);
        nk.Some? && nk.value.CHier? &&
        (child == NodeKind(parent, n).value.c)

    }

    predicate HPCircuitSeqMatch(cs: seq<Circuit>, hp: HierarchyPath)
        requires |cs| == |hp.v|+1
    {
        forall index: nat :: index < |hp.v| ==> IsChildCircuit(cs[index], cs[index+1], hp.v[index])
    }

    lemma HPCircuitSeqMatchHPValid(cs: seq<Circuit>, hp: HierarchyPath)
        requires |cs| == |hp.v| + 1
        requires HPCircuitSeqMatch(cs, hp)
        requires CircuitValid(cs[0])
        ensures HierarchyPathValid(cs[0], hp)
    {
        if |hp.v| == 0 {
        } else {
            var (start, remainder) := HPStartChildren(hp);
            assert IsChildCircuit(cs[0], cs[1], hp.v[0]);
            assert cs[1] == NodeKind(cs[0], hp.v[0]).value.c;
            reveal CircuitValid();
            assert CircuitNodeKindValid(cs[0]);
            HPCircuitSeqMatchHPValid(cs[1..], HP(hp.v[1..]));
        }
    }

    predicate {:opaque} HierLevelDecreases(cs: seq<Circuit>)
    {
        forall index: nat :: index < |cs|-1 ==>
            cs[index+1].HierLevel < cs[index].HierLevel
    }

    function HPToCircuitSeq(c: Circuit, hp: HierarchyPath): (r: seq<Circuit>)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures |r| == |hp.v|+1
        ensures r[0] == c
        ensures HPCircuitSeqMatch(r, hp)
        ensures forall d :: d in r ==> CircuitValid(d)
        ensures HierLevelDecreases(r)
        decreases c.HierLevel
    {
        reveal HierLevelDecreases();
        if |hp.v| == 0 then
            [c]
        else
            var next_c := NodeKind(c, hp.v[0]).value.c;
            reveal CircuitValid();
            assert CircuitNodeKindValid(c);
            var next_hp := HP(hp.v[1..]);
            var next_cs := HPToCircuitSeq(next_c, next_hp);
            [c] + next_cs
    }

    function Subcircuit(c: Circuit, n: CNode): (r: Circuit)
        requires CircuitValid(c)
        requires NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
        ensures CircuitValid(r)
        ensures r.HierLevel < c.HierLevel
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        NodeKind(c, n).value.c
    }

    lemma AllValidHierarchyPathsThroughSubcircuitHelper(c: Circuit, n: CNode)
        requires CircuitValid(c)
        requires NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
        ensures forall hp :: HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] == n) <==>
            hp in AllValidHierarchyPathsThroughSubcircuitInternal(c, n)
        decreases c.HierLevel, 1
    {
        var hp_c := Subcircuit(c, n);
        var hps := AllValidHierarchyPaths(hp_c);
        var this_hps := (set hp | hp in hps :: HPPrepend(c, hp_c, hp, n));
        assert this_hps == AllValidHierarchyPathsThroughSubcircuitInternal(c, n);
        forall hp | HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] == n)
            ensures hp in this_hps
        {
            var sub_hp := HP(hp.v[1..]);
            assert HierarchyPathValid(hp_c, sub_hp);
            assert sub_hp in hps;
            assert hp == HPPrepend(c, hp_c, sub_hp, n);
            assert hp in this_hps;
        }
    }


    function AllValidHierarchyPathsThroughSubcircuitInternal(c: Circuit, n: CNode): (r: set<HierarchyPath>)
        requires CircuitValid(c)
        requires NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
        decreases c.HierLevel, 0
    {
        var hp_c := Subcircuit(c, n);
        var hps := AllValidHierarchyPaths(hp_c);
        var this_hps := (set hp | hp in hps :: HPPrepend(c, hp_c, hp, n));
        this_hps
    }

    function AllValidHierarchyPathsThroughSubcircuit(c: Circuit, n: CNode): (r: set<HierarchyPath>)
        requires CircuitValid(c)
        requires NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
        ensures forall hp :: HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] == n) <==> hp in r
        decreases c.HierLevel, 2
    {
        AllValidHierarchyPathsThroughSubcircuitHelper(c, n);
        AllValidHierarchyPathsThroughSubcircuitInternal(c, n)
    }

    function AllValidHierarchyPathsInSubcircuits(
            c: Circuit, nodes: set<CNode>): (r: set<HierarchyPath>)
        requires CircuitValid(c)
        requires forall n :: n in nodes ==>
            NodeKind(c, n).Some? && NodeKind(c, n).value.CHier?
        ensures forall hp :: hp in r <==>
            HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] in nodes)
        decreases c.HierLevel, 3, |nodes|
    {
        if |nodes| == 0 then
            {}
        else
            var n :| n in nodes;
            var this_hps := AllValidHierarchyPathsThroughSubcircuit(c, n);
            var new_nodes := nodes - {n};
            var other_hps := AllValidHierarchyPathsInSubcircuits(c, new_nodes);
            assert forall hp :: HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] in new_nodes) ==> hp in other_hps;
            var r := this_hps + other_hps;
            assert forall hp :: hp in r ==> HierarchyPathValid(c, hp);
            assert forall hp :: hp in r ==>
                HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] in nodes);
            assert forall hp :: HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] in nodes) ==> hp in r;
            r
    }

    function {:vcs_split_on_every_assert} AllValidHierarchyPaths(c: Circuit): (r: set<HierarchyPath>)
        requires CircuitValid(c)
        ensures forall hp :: hp in r ==> HierarchyPathValid(c, hp)
        ensures forall hp :: HierarchyPathValid(c, hp) ==> hp in r
        decreases c.HierLevel, 4
    {
        if c.HierLevel == 0 then
            var r := {HP([])};
            HPMaxLength(c);
            assert forall hp :: HierarchyPathValid(c, hp) ==> HPLength(hp) == 0;
            r
        else
            var all_subcircuit_nodes := (set n | n in c.NodeKind && c.NodeKind[n].CHier? :: n);
            assert forall hp :: HierarchyPathValid(c, hp) && HPLength(hp) > 0 ==>
                var (start, children) := HPStartChildren(hp);
                NodeKind(c, start).Some? && NodeKind(c, start).value.CHier?;
            assert forall hp :: HierarchyPathValid(c, hp) && HPLength(hp) > 0 ==>
                var (start, children) := HPStartChildren(hp);
                start in all_subcircuit_nodes;
            var nonzero_hps := AllValidHierarchyPathsInSubcircuits(c, all_subcircuit_nodes);
            assert forall hp :: hp in nonzero_hps <==>
                HierarchyPathValid(c, hp) && HPLength(hp) > 0 && (hp.v[0] in all_subcircuit_nodes);
            assert forall hp :: HierarchyPathValid(c, hp) && HPLength(hp) > 0 ==> hp in nonzero_hps;
            var r := {HP([])} + nonzero_hps;
            assert forall hp :: HierarchyPathValid(c, hp) ==> hp in r;
            r
    }

    function HPLength(hp: HierarchyPath): nat
    {
        |hp.v|
    }

    function HierarchyPathCircuit(c: Circuit, hp: HierarchyPath): (r: Circuit)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        decreases |hp.v|, 1
        ensures CircuitValid(r)
    {
        var cs := HPToCircuitSeq(c, hp);
        cs[|cs|-1]
    }


    function HPTail(hp: HierarchyPath): (r: HierarchyPath)
        requires hp.v != []
        ensures |hp.v| == |r.v| + 1
    {
        HP(hp.v[..|hp.v|-1])
    }

    function HPAppend(c: Circuit, hp: HierarchyPath, n: CNode): (r: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        requires
            var hp_c := HierarchyPathCircuit(c, hp);
            NodeKind(hp_c, n).Some? && NodeKind(hp_c, n).value.CHier?
        ensures HierarchyPathValid(c, r)
    {
        var r := HP(hp.v + [n]);
        var cs := HPToCircuitSeq(c, hp);
        var hp_c := HierarchyPathCircuit(c, hp);
        var new_cs := cs + [NodeKind(hp_c, n).value.c];
        HPCircuitSeqMatchHPValid(new_cs, r);
        r
    }

    function HPPrepend(parent_c: Circuit, child_c: Circuit, hp: HierarchyPath, n: CNode): (r: HierarchyPath)
        requires CircuitValid(parent_c)
        requires CircuitValid(child_c)
        requires IsChildCircuit(parent_c, child_c, n)
        requires HierarchyPathValid(child_c, hp)
        ensures HierarchyPathValid(parent_c, r)
    {
        var r := HP([n] + hp.v);
        var cs := HPToCircuitSeq(child_c, hp);
        var new_cs := [parent_c] + cs;
        HPCircuitSeqMatchHPValid(new_cs, r);
        r
    }

    lemma HPTailValid(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires hp.v != []
        requires HierarchyPathValid(c, hp)
        ensures HierarchyPathValid(c, HPTail(hp))
    {
        var cs := HPToCircuitSeq(c, hp);
        var new_cs := cs[..|cs|-1];
        var tail := HP(hp.v[..|hp.v|-1]);
        assert tail == HPTail(hp);
        assert HPCircuitSeqMatch(new_cs, tail);
        HPCircuitSeqMatchHPValid(new_cs, tail);
    }

    function HPHead(hp: HierarchyPath): CNode
        requires hp.v != []
    {
        hp.v[|hp.v|-1]
    }

    function HPHeadTail(hp: HierarchyPath): (r: (CNode, HierarchyPath))
        requires HPLength(hp) > 0
    {
        (HPHead(hp), HPTail(hp))
    }

    function HPStartChildren(hp: HierarchyPath): (r: (CNode, HierarchyPath))
        requires HPLength(hp) > 0
    {
        (hp.v[0], HP(hp.v[1..]))
    }

    function NodeToSubcircuit(c: Circuit, n: CNode): Circuit
        requires NodeKind(c, n).Some?
        requires NodeKind(c, n).value.CHier?
    {
        NodeKind(c, n).value.c
    }

    predicate {:opaque} HPNodeValid(c: Circuit, hpn: HPNode)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpn.hp);
        var maybe_nk := NodeKind(hp_c, hpn.n);
        maybe_nk.Some?
    }

    function AllValidHPNodesFromHP(c: Circuit, hp: HierarchyPath): (r: set<HPNode>)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures forall hpn :: hpn in r <==> HPNodeValid(c, hpn) && (hpn.hp == hp)
    {
        reveal HPNodeValid();
        var hp_c := HierarchyPathCircuit(c, hp);
        (set n | n in hp_c.NodeKind :: HPNode(hp, n))
    }

    function AllValidHPNodesFromHPs(c: Circuit, hps: set<HierarchyPath>): (r: set<HPNode>)
        requires CircuitValid(c)
        requires forall hp :: hp in hps ==> HierarchyPathValid(c, hp)
        ensures forall hpn :: hpn in r <==> HPNodeValid(c, hpn) && (hpn.hp in hps)
    {
        if |hps| == 0 then
            {}
        else
            var hp :| hp in hps;
            var next_hps := hps - {hp};
            var next_hpns := AllValidHPNodesFromHPs(c, next_hps);
            var this_hpns := AllValidHPNodesFromHP(c, hp);
            reveal HPNodeValid();
            assert forall hpn :: hpn in this_hpns ==> HPNodeValid(c, hpn);
            this_hpns + next_hpns
    }

    function AllValidHPNodes(c: Circuit): (r: set<HPNode>)
        requires CircuitValid(c)
        ensures forall hpn :: hpn in r <==> HPNodeValid(c, hpn)
    {
        reveal HPNodeValid();
        var hps := AllValidHierarchyPaths(c);
        AllValidHPNodesFromHPs(c, hps)
    }

    predicate {:opaque} HPNPValidInput(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpnp.hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        var maybe_nk := NodeKind(hp_c, hpnp.hpn.n);
        maybe_nk.Some? &&
        IsIPort(maybe_nk.value, hpnp.p)
    }

    lemma HPNPValidHPValid(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures HierarchyPathValid(c, hpnp.hpn.hp)
    {
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
    }


    predicate {:opaque} HPNPValidOutput(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HierarchyPathValid(c, hpnp.hpn.hp) &&
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        var maybe_nk := NodeKind(hp_c, hpnp.hpn.n);
        maybe_nk.Some? &&
        IsOPort(maybe_nk.value, hpnp.p)
    }

    lemma HPNPNotBothValidInputOutput(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures !(HPNPValidOutput(c, hpnp) && HPNPValidInput(c, hpnp))
    {
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        assert HierarchyPathValid(c, hpnp.hpn.hp);
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        var nk := NodeKind(hp_c, hpnp.hpn.n).value;
        reveal CircuitValid();
        assert CircuitNodeKindValid(hp_c);
    }

    predicate HPNPValid(c: Circuit, hpnp: HPNP)
        requires CircuitValid(c)
    {
        HPNPValidInput(c, hpnp) ||
        HPNPValidOutput(c, hpnp)
    }


    function HPNPtoNK(c: Circuit, hpnp: HPNP): (r: CNodeKind)
        requires CircuitValid(c)
        requires HPNPValid(c, hpnp)
        ensures
            reveal HPNPValidInput();
            reveal HPNPValidOutput();
            var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
            var nk := HPNPtoNK(c, hpnp);
            CNodeKindValid(hp_c.HierLevel, nk)
    {
        HPNPValidHPValid(c, hpnp);
        var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        var nk := NodeKind(hp_c, hpnp.hpn.n).value;
        CircuitValidCNodeKindValid(hp_c, hpnp.hpn.n);
        nk
    }

    lemma CircuitValidCNodeKindValid(c: Circuit, n: CNode)
        requires CircuitValid(c)
        requires NodeKind(c, n).Some?
        ensures CNodeKindValid(c.HierLevel, NodeKind(c, n).value)
    {
        reveal CircuitValid();
    }
    ghost predicate {:opaque} CircuitComplete(c: Circuit)
        requires CircuitValid(c)
        decreases c.HierLevel
    {
        (forall inp: NP :: NPValidInput(c, inp) ==> PortSource(c, inp).Some?) &&
        (forall n: CNode :: NodeKind(c, n).Some? && NodeKind(c, n).value.CHier? ==>
            var subc := NodeKind(c, n).value.c;
            CircuitValid(subc) &&
            (subc.HierLevel < c.HierLevel) &&
            CircuitComplete(subc)
        )
    }

    function DirectSubcircuits(c: Circuit): (r: set<Circuit>)
        requires CircuitValid(c)
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(c);
        assert forall i: CNode ::
            NodeKind(c, i).Some? && NodeKind(c, i).value.CHier? ==>
            var nk := NodeKind(c, i).value;
            CNodeKindValid(c.HierLevel, nk);
        (set n: CNode | n in c.NodeKind && c.NodeKind[n].CHier? :: c.NodeKind[n].c)
    }

    predicate HPNodeInCircuit(c: Circuit, hpn: HPNode)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hpn.hp)
    {
        var hpc := HierarchyPathCircuit(c, hpn.hp);
        NodeKind(hpc, hpn.n).Some?
    }

    function HPNodeToHPNP(c: Circuit, hpn: HPNode): set<HPNP>
        requires CircuitValid(c)
        requires HPNodeValid(c, hpn)
    {
        reveal HPNodeValid();
        var hpc := HierarchyPathCircuit(c, hpn.hp);
        var nk := NodeKind(hpc, hpn.n).value;
        var ports := IPorts(nk) + OPorts(nk);
        set p: CPort | p in ports :: HPNP(hpn, p)
    }

    lemma HPMaxLength(c: Circuit)
        requires CircuitValid(c)
        ensures
            forall hp :: HierarchyPathValid(c, hp) ==> HPLength(hp) <= c.HierLevel
    {
        forall hp: HierarchyPath | HierarchyPathValid(c, hp)
            ensures HPLength(hp) <= c.HierLevel
        {
            HPLengthBound(c, hp);
        }
    }

    lemma HPLengthBound(c: Circuit, hp: HierarchyPath)
        requires CircuitValid(c)
        requires HierarchyPathValid(c, hp)
        ensures HPLength(hp) <= c.HierLevel
    {
        var cs := HPToCircuitSeq(c, hp);
        var hier_levels := seq(|cs|, (i: nat) requires i < |cs| => cs[i].HierLevel);
        reveal HierLevelDecreases();
        DecreasesSequenceBounded(hier_levels);
    }

    function SeqCNodeToSeqNat(a: seq<CNode>): seq<nat>
    {
        seq(|a|, i requires 0 <= i < |a| => a[i] as nat)
    }

    lemma DecreasesSequenceBounded(xs: seq<nat>)
        requires forall index: nat :: index < |xs|-1 ==> xs[index+1] < xs[index]
        requires |xs| > 0
        ensures |xs| <= xs[0]+1
    {
        if |xs| == 1 {
        } else {
            DecreasesSequenceBounded(xs[1..]);
        }
    }


}
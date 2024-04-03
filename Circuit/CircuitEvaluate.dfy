module CircuitEvaluate {

    import opened Std.Wrappers
    import Std.Collections.Seq
    import opened CircuitBase
    import opened CircuitHPNP
    import opened CircuitHierarchy
    import opened CircuitToGraph
    import DG = DigraphBase`Spec
    import DP = DigraphPaths`Spec

    function {:vcs_split_on_every_assert} EvaluateINP(
            c: Circuit, m: HPNP -> bool, p: DG.Path<HPNP>): bool
        requires CircuitValid(c)
        requires CircuitComplete(c)
        requires CircuitNoLoops(c)
        requires |p.v| > 0
        requires HPNPValidInput(c, DP.PathEnd(p))
        requires PathValid(c, p)
        decreases NumberOfRemainingNodes(c, p), 1
    {
        var inp := DP.PathEnd(p);
        var onp := INPtoONP(c, inp);
        INPtoONPConnected(c, inp);
        assert HPNPConnected(c, inp, onp);
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
        requires HPNPValidOutput(c, DP.PathEnd(p))
        requires PathValid(c, p)
        requires HPNPtoNK(c, DP.PathEnd(p)).CInput?
        decreases NumberOfRemainingNodes(c, p), 1
    {
        var onp := DP.PathEnd(p);
        if HPLength(onp.hpn.hp) == 0 then
            // This is an input to the top level.
            isigs(onp)
        else
            var (hier_n, parent_hp) := HPHeadTail(onp.hpn.hp);
            HPNPValidHPValid(c, onp);
            HPTailValid(c, onp.hpn.hp);
            assert HierarchyPathValid(c, parent_hp);
            // If it's an input inside a hier node, then it connects to
            // the input port on the hier node on the next level up.
            var inp := CInputONPtoINP(c, onp);
            CInputONPtoINPConnected(c, onp);
            assert HPNPConnected(c, onp, inp);
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
        requires HPNPValidOutput(c, DP.PathEnd(p))
        requires PathValid(c, p)
        requires HPNPtoNK(c, DP.PathEnd(p)).CHier?
        decreases NumberOfRemainingNodes(c, p), 1
    {
        var onp := DP.PathEnd(p);
        var inp := CHierONPtoINP(c, onp);
        CHierONPtoINPConnected(c, onp);
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
        requires HPNPValidOutput(c, DP.PathEnd(p))
        requires HPNPtoNK(c, DP.PathEnd(p)).CComb?
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
        requires HPNPValidOutput(c, DP.PathEnd(p))
        decreases NumberOfRemainingNodes(c, p), 2
    {
        var onp := DP.PathEnd(p);
        HPNPValidHPValid(c, onp);
        var hp_c := HierarchyPathCircuit(c, onp.hpn.hp);
        reveal HPNPValidOutput();
        var nk := NodeKind(hp_c, onp.hpn.n).value;
        match nk
        case CInput() => EvaluateONPCInput(c, isigs, p)
        case CHier(_) => EvaluateONPCHier(c, isigs, p)
        case CComb(_, _, _) => EvaluateONPCComb(c, isigs, p)
        case CSeq() => isigs(onp)
        case CConst(v) => v
    }

    ghost predicate StringInputMapValid(c: Circuit, inputmap: map<string, bool>)
    {
        forall s :: s in inputmap <==> s in c.PortMap.inames
    }

    ghost predicate StringOutputMapValid(c: Circuit, outputmap: map<string, bool>)
    {
        forall s :: s in outputmap <==> s in c.PortMap.onames
    }

    ghost predicate CNodeInputMapValid(c: Circuit, inputmap: map<CNode, bool>)
    {
        forall n :: n in inputmap <==> CNodeIsCInput(c, n)
    }

    ghost predicate CNodeOutputMapValid(c: Circuit, outputmap: map<CNode, bool>)
    {
        forall n :: n in outputmap <==> CNodeIsCOutput(c, n)
    }

    function StringMapToPortMap(c: Circuit, inputmap: map<string, bool>): (r: map<CNode, bool>)
        requires CircuitValid(c)
        requires StringInputMapValid(c, inputmap)
        ensures CNodeInputMapValid(c, r)
    {
        reveal CircuitValid();
        reveal CircuitPortNamesValid();
        INameToPortCovers(c.PortMap);
        assert forall p :: (p in c.PortMap.iports <==> CNodeIsCInput(c, p as CNode));
        var iports := (set k | k in c.PortMap.inames :: INameToPort(c.PortMap, k) as CNode);
        assert forall p :: p in iports <==> p as CPort in c.PortMap.iports;
        assert forall p :: p in iports ==> CNodeIsCInput(c, p);
        var r := (map k | k in c.PortMap.inames :: INameToPort(c.PortMap, k) as CNode := inputmap[k]);
        assert forall k :: k in r.Keys <==> k in iports;
        assert forall k :: k in r.Keys ==> CNodeIsCInput(c, k);
        assert forall k :: CNodeIsCInput(c, k) ==> k in r.Keys;
        r
    }

    function PortMapToHPNPMap(inputmap: map<CNode, bool>): HPNP -> bool
    {
        var outputmap := (hpnp: HPNP) => hpnp.hpn.hp == HP([]) && hpnp.hpn.n in inputmap && hpnp.p == OUTPUT_PORT && inputmap[hpnp.hpn.n];
        outputmap
    }

    function InputLabelToHPNP(c: Circuit, input_label: string): (r: HPNP)
        requires CircuitValid(c)
        requires input_label in c.PortMap.inames
        ensures HPNPValidOutput(c, r)
    {
        reveal CircuitValid();
        reveal CircuitPortNamesValid();
        var n := INameToPort(c.PortMap, input_label) as CNode;
        assert n as CPort in c.PortMap.iports;
        assert CNodeIsCInput(c, n);
        reveal HPNPValidOutput();
        HPNP(HPNode(HP([]), n), OUTPUT_PORT)
    }

    function OutputLabelToHPNP(c: Circuit, output_label: string): (r: HPNP)
        requires CircuitValid(c)
        requires output_label in c.PortMap.onames
        ensures HPNPValidInput(c, r)
    {
        reveal CircuitValid();
        reveal CircuitPortNamesValid();
        var n := ONameToPort(c.PortMap, output_label) as CNode;
        assert n as CPort in c.PortMap.oports;
        assert CNodeIsCOutput(c, n);
        reveal HPNPValidInput();
        var r := HPNP(HPNode(HP([]), n), INPUT_PORT);
        //HierarchyPathValid(c, hpnp.hpn.hp) &&
        //var hp_c := HierarchyPathCircuit(c, hpnp.hpn.hp);
        //var maybe_nk := NodeKind(hp_c, hpnp.hpn.n);
        //maybe_nk.Some? &&
        //IsIPort(maybe_nk.value, hpnp.p)
        assert r.p in PortMap(COutput).iports;
        assert IsIPort(COutput, r.p);
        assert HPNPValidInput(c, r);
        r
    }

    lemma EvaluateByLabelHelper(c: Circuit, output_label: string)
        requires CircuitValid(c)
        requires output_label in c.PortMap.onames
        ensures PathValid(c, DG.Path([OutputLabelToHPNP(c, output_label)]))
    {
        var hpnp := OutputLabelToHPNP(c, output_label);
        assert HPNPValidInput(c, hpnp);
        reveal HPNPValidInput();
        reveal DG.PathValid();
        reveal CtoG();
        var p := DG.Path([hpnp]);
        var g := CtoGV(c);
        assert HPNPValid(c, hpnp);
        ValidHPNPIsNode(c, hpnp);
        assert hpnp in AllValidHPNP(c);
        assert DG.IsNode(g, hpnp);
        assert DG.PathValid(g, p);
        assert PathValid(c, p);
    }

    lemma EvaluateByLabelHelper2(c: Circuit)
        requires CircuitValid(c)
        ensures forall input_label :: input_label in c.PortMap.onames ==> PathValid(c, DG.Path([OutputLabelToHPNP(c, input_label)]))
    {
        forall output_label | output_label in c.PortMap.onames
            ensures PathValid(c, DG.Path([OutputLabelToHPNP(c, output_label)]))
        {
            EvaluateByLabelHelper(c, output_label);
        }
    }

    //function EvaluateByPort(c: Circuit, inputmap: map<CNode, bool>): (r: map<CNode, bool>)
    //    requires CircuitValid(c)
    //    requires CircuitNoLoops(c)
    //    requires CircuitComplete(c)
    //    requires CNodeInputMapValid(c, inputmap)
    //    ensures CNodeOutputMapValid(c, r)
    //{
    //    var m := PortMapToHPNPMap(inputmap);
    //    reveal DG.PathValid();
    //    reveal CtoG();
    //    EvaluateByLabelHelper2(c);
    //    (map k | k in c.PortMap.oports :: k as CNode := EvaluateINP(c, m, DG.Path([HPNP(HPNode(HP([]), k as CNode), INPUT_PORT)])))
    //}

    function EvaluateByLabel(c: Circuit, inputmap: map<string, bool>): (r: map<string, bool>)
        requires CircuitValid(c)
        requires CircuitNoLoops(c)
        requires CircuitComplete(c)
        requires StringInputMapValid(c, inputmap)
        ensures StringOutputMapValid(c, r)
    {
        var m := PortMapToHPNPMap(StringMapToPortMap(c, inputmap));
        reveal DG.PathValid();
        reveal CtoG();
        EvaluateByLabelHelper2(c);
        (map k | k in c.PortMap.onames :: k := EvaluateINP(c, m, DG.Path([OutputLabelToHPNP(c, k)])))
    }

}
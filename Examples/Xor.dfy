module XorExample {

    import opened Std.Wrappers
    import Std.Relations

    import C = CircuitBase
    import CB = CircuitBuild
    import CE = CircuitEvaluate
    import CG = CircuitToGraph
    import CH = CircuitHierarchy
    import P = Primitives
    import CircuitNodeOrdering

    import DG = DigraphBase`Spec
    import DP = DigraphPaths`Spec
    import DS = DigraphStepBack`Body

    function {:vcs_split_on_every_assert} MakeXor(): (r: C.Circuit)
        ensures r.PortMap.inames == ["i0", "i1"]
        ensures r.PortMap.onames == ["o"]
    {
        var g := CB.MakeEmptyCircuit();
        var (g, i_0) := CB.AddIPort(g, "i0");
        var (g, i_1) := CB.AddIPort(g, "i1");
        var (g, node_xor) := CB.AddNodeAndConnect(g, P.nk_xor, [("i0", i_0), ("i1", i_1)]);
        var xor_output := CB.GetOutputPort(g, node_xor, "o");
        var g := CB.AddOPortAndConnect(g, xor_output, "o");
        assert C.CircuitValid(g);
        g
    }

    const Xor := MakeXor()

    function xor(a: bool, b: bool): bool
    {
        (!a && b) || (a && !b)
    }

    function XorApply(i0: bool, i1: bool): bool
        requires CG.CircuitNoLoops(Xor)
        requires CH.CircuitComplete(Xor)
    {
        var input_map: map<string, bool> := map["i0":= i0, "i1" := i1];
        assert CE.StringInputMapValid(Xor, input_map);
        var output_map: map<string, bool> := CE.EvaluateByLabel(Xor, input_map);
        output_map["o"]
    }

    predicate XorCorrect()
        requires CG.CircuitNoLoops(Xor)
        requires CH.CircuitComplete(Xor)
    {
        CE.EvaluateByLabel(Xor, map["i0":=false, "i1":=false]) == map["o":=false] &&
        CE.EvaluateByLabel(Xor, map["i0":=false, "i1":=true]) == map["o":=true] &&
        CE.EvaluateByLabel(Xor, map["i0":=true, "i1":=false]) == map["o":=true] &&
        CE.EvaluateByLabel(Xor, map["i0":=true, "i1":=true]) == map["o":=false]
    }

    lemma XorCheck()
        requires CG.CircuitNoLoops(Xor)
        requires CH.CircuitComplete(Xor)
        requires XorCorrect()
        ensures XorApply(false, false) == false
    {
        var b := XorApply(false, false);
    }

    //lemma MultipleStepSetEmptyGivesNoLoop<Node(!new)>(g: Digraph, count: nat, NodeOrdering: (Node, Node) -> bool)
    //    requires DigraphValid(g)
    //    requires Relations.TotalOrdering(NodeOrdering)
    //    requires MultipleStepSetBack(g, AllNodes(g), count, NodeOrdering) == {}
    //    ensures !DigraphLoop(g)

    method XorHasLoop() returns (has_loop: bool)
        ensures !has_loop ==> !DP.DigraphLoop(CG.CtoG(Xor))
    {
        var g := CG.CtoGV(Xor);
        var all_nodes := DG.AllNodes(g);
        CircuitNodeOrdering.HPNPOrderingIsTotal();
        assert Relations.TotalOrdering(CircuitNodeOrdering.HPNPOrdering);
        var msb := DS.MultipleStepSetBack(
            g, all_nodes, |all_nodes|, CircuitNodeOrdering.HPNPOrdering);
        var has_a_loop := msb != {};
        if !has_a_loop {
            DS.MultipleStepSetEmptyGivesNoLoop(
                g, |all_nodes|, CircuitNodeOrdering.HPNPOrdering);
        }
        return has_a_loop;
    }

}
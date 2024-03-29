module CircuitTest {

    import opened Std.Wrappers
    import opened Primitives
    import Std.Collections.Map
    import opened CircuitBase
    import opened CircuitEvaluate
    import opened CircuitHPNP
    import opened CircuitHierarchy
    import opened CircuitToGraph
    import opened CircuitBuild
    import DG = DigraphBase
    import P = Primitives
    // Make a circuit with a single XOR gate.

    const i0_n: CNode := 0
    const i1_n: CNode := 1
    const o_n: CNode := 2
    const xor_n: CNode := 3

    const i0_p := NP(i0_n, OUTPUT_PORT)
    const i1_p := NP(i1_n, OUTPUT_PORT)
    const o_p := NP(o_n, INPUT_PORT)

    const xor_i0 := NP(xor_n, 0)
    const xor_i1 := NP(xor_n, 1)
    const xor_o := NP(xor_n, 2)

    const circ := Circuit(
        NodeKind := map[
            i0_n := CInput(),
            i1_n := CInput(),
            o_n := COutput(),
            xor_n := nk_xor
            ],
        PortSource := map[
            NP(3, 0) := i0_p,
            NP(3, 1) := i1_p,
            NP(2, 0) := xor_o
        ],
        PortNames := map[],
        HierLevel := 0
    )
    const HierLevel: nat := 0
    const PortBound: CPort := 4

    lemma Stuff()
    {
        CircValid();
        assert NPValid(circ, xor_i0);
        var xor_i0_hpnp := HPNP(HPNode(HP([]), xor_n), 0);
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        assert HPNPValid(circ, xor_i0_hpnp);
    }

    lemma CircValid()
        ensures CircuitValid(circ)
    {
        reveal CircuitValid();
    }

    lemma CircComplete()
        ensures CircuitValid(circ)
        ensures CircuitComplete(circ)
    {
        CircValid();
        reveal CircuitComplete();
    }

    lemma CircNoLoops()
        ensures CircuitValid(circ)
        ensures CircuitComplete(circ)
        ensures CircuitNoLoops(circ)
    {
        CircValid();
        CircComplete();
        var g := CtoGV(circ);
        var all_nodes := DG.AllNodes(g);
        assert |all_nodes| == 6;
    }

    lemma Blah()
    {
        var c := circ;
        var i0 := HPNP(HPNode(HP([]), 0), OUTPUT_PORT);
        var i1 := HPNP(HPNode(HP([]), 1), OUTPUT_PORT);
        var o := HPNP(HPNode(HP([]), 2), INPUT_PORT);
        var isigs: HPNP -> bool := (hpnp: HPNP) =>
            if hpnp == i0 then true
            else if hpnp == i0 then true
            else false;
        CircValid();
        CircComplete();
        CircNoLoops();
        var b := EvaluateONP(c, isigs, DG.Path([]));
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
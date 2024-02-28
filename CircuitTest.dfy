module CircuitTest {

    import opened Std.Wrappers
    import C = Circuit
    import P = Primitives
    import Std.Collections.Map
    import CS = CircuitStuff
    import CP = CircuitPath
    import DG
    // Make a circuit with a single XOR gate.

    const i0_n: C.CNode := 0
    const i1_n: C.CNode := 1
    const o_n: C.CNode := 2
    const xor_n: C.CNode := 3

    const i0_p := C.NP(i0_n, C.OUTPUT_PORT)
    const i1_p := C.NP(i1_n, C.OUTPUT_PORT)
    const o_p := C.NP(o_n, C.INPUT_PORT)

    const xor_i0 := C.NP(xor_n, 0)
    const xor_i1 := C.NP(xor_n, 1)
    const xor_o := C.NP(xor_n, 2)

    const circ := C.Circuit(
        NodeKind := (n: C.CNode) => (match n
            case i0_n => Some(C.CInput())
            case i1_n => Some(C.CInput())
            case o_n => Some(C.COutput())
            case xor_n => Some(P.nk_xor)
            case _ => None
            ),
        PortSource := (np: C.NP) => (match np
            case NP(3, 0) => Some(i0_p)
            case NP(3, 1) => Some(i1_p)
            case NP(2, 0) => Some(xor_o)
            case _ => None),
        PortNames := _ => None,
        NodeBound := 4,
        PortBound := 3,
        HierLevel := 0
    )
    const HierLevel: nat := 0
    const PortBound: C.CPort := 4

    lemma Stuff()
    {
        CircValid();
        assert C.NPValid(circ, xor_i0);
        var xor_i0_hpnp := C.HPNP(C.HPNode(C.HP([]), xor_n), 0);
        reveal C.HPNPValidInput();
        reveal C.HPNPValidOutput();
        assert C.HPNPValid(circ, xor_i0_hpnp);
    }

    lemma CircValid()
        ensures C.CircuitValid(circ)
    {
        reveal C.CircuitValid();
    }

    lemma CircComplete()
        ensures C.CircuitValid(circ)
        ensures C.CircuitComplete(circ)
    {
        CircValid();
        reveal C.CircuitComplete();
    }

    lemma CircNoLoops()
        ensures C.CircuitValid(circ)
        ensures C.CircuitComplete(circ)
        ensures CP.CircuitNoLoops(circ)
    {
        CircValid();
        CircComplete();
        var g := CP.CtoGV(circ);
        var all_nodes := DG.AllNodes(g);
        assert |all_nodes| == 6;
    }

    lemma Blah()
    {
        var c := circ;
        var i0 := C.HPNP(C.HPNode(C.HP([]), 0), C.OUTPUT_PORT);
        var i1 := C.HPNP(C.HPNode(C.HP([]), 1), C.OUTPUT_PORT);
        var o := C.HPNP(C.HPNode(C.HP([]), 2), C.INPUT_PORT);
        var isigs: C.HPNP -> bool := (hpnp: C.HPNP) =>
            if hpnp == i0 then true
            else if hpnp == i0 then true
            else false;
        CircValid();
        CircComplete();
        CircNoLoops();
        var b := CS.EvaluateONP(c, isigs, DG.Path([]));
    }

}
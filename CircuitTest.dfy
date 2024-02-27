module CircuitTest {

    import opened Std.Wrappers
    import C = Circuit
    import P = Primitives
    import Std.Collections.Map
    import CS = CircuitStuff
    import CP = CircuitPath
    import DG
    // Make a circuit with a single XOR gate.

    const circ := C.Circuit(
        NodeKind := (n: C.CNode) => (match n
            case 0 => Some(C.CInput())
            case 1 => Some(C.CInput())
            case 2 => Some(C.COutput())
            case 3 => Some(P.nk_xor)
            case _ => None
            ),
        PortSource := (np: C.NP) => (match np
            case NP(3, 0) => Some(C.NP(0, 1))
            case NP(3, 1) => Some(C.NP(1, 1))
            case NP(2, 0) => Some(C.NP(3, 2))
            case _ => None),
        PortNames := _ => None,
        NodeBound := 4,
        PortBound := 3,
        HierLevel := 0
    )
    const HierLevel: nat := 0
    const PortBound: C.CPort := 4

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
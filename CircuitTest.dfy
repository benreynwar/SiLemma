module CircuitTest {

    import opened Std.Wrappers
    import C = Circuit
    import P = Primitives
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

    lemma nk_xor_valid()
        ensures C.CNodeKindValid(HierLevel, PortBound, P.nk_xor)
    {
        reveal C.CircuitValid();
    }

    lemma CircValid()
        ensures C.CircuitValid(circ)
    {
        reveal C.CircuitValid();
    }

}
module CircuitTest {

    import opened Std.Wrappers
    import C = Circuit
    import P = Primitives
    // Make a circuit with a single XOR gate.

    function behav_xor(inputs: map<C.CPort, bool>): Option<map<C.CPort, bool>>
    {
        if 0 !in inputs then
            None
        else if 1 !in inputs then
            None
        else
            var o := if inputs[0] == inputs[1] then false else true;
            Some(map[2 := o])
    }

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
    const lib := C.CLib([circ])

    const HierLevel: nat := 0
    const PortBound: C.CPort := 4

    lemma nk_xor_valid()
        ensures C.CNodeKindValid(lib, HierLevel, PortBound, nk_xor)
    {
        reveal C.CircuitValid();
    }

    lemma CircValid()
        ensures C.CircuitValid(lib, circ)
    {
        reveal C.CircuitValid();
    }

}
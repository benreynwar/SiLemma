module Primitives {

    import opened Std.Wrappers
    import C = Circuit

    function XorBehav(m: map<C.CPort, bool>): Option<map<C.CPort, bool>>
    {
        if (0 in m) && (1 in m) then
            var o := if m[0] == m[1] then false else true;
            Some(map[2 := o])
        else
            None
    }

    function AndBehav(m: map<C.CPort, bool>): Option<map<C.CPort, bool> >
    {
        if (0 in m) && (1 in m) then
            Some(map[0 := m[0] && m[1]])
        else
            None
    }

    const nk_xor := C.CComb(
        IPorts := {0, 1},
        OPorts := {2},
        PathExists := (a: C.CPort, b: C.CPort) => (
            match (a, b)
            case (2, 0) => true
            case (2, 1) => true
            case _ => false
        ),
        Behav := XorBehav,
        PortNames := PortNames2to1
    )

    const xor_port_bound: C.CPort := 3

    lemma nk_xor_valid()
        ensures C.CNodeKindValid(0, xor_port_bound, nk_xor)
    {
    }

    predicate BinaryPathExists(p: C.CPort, q: C.CPort)
    {
        (p in {0, 1}) && (q == 0)
    }

    function PortNames2to1(name: string): Option<C.CPort>
    {
        match name
        case "i0" => Some(0 as C.CPort)
        case "i1" => Some(1 as C.CPort)
        case "o" => Some(2 as C.CPort)
        case _ => None
    }

    const nk_and: C.CNodeKind := C.CComb(
        IPorts := {0 as C.CPort, 1 as C.CPort},
        OPorts := {2 as C.CPort},
        PathExists := BinaryPathExists,
        Behav := AndBehav,
        PortNames := PortNames2to1
    )

}
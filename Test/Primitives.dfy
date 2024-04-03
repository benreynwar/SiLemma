module Primitives {

    import opened Std.Wrappers
    import C = CircuitBase

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
        PathExists := (a: C.CPort, b: C.CPort) => (
            match (a, b)
            case (2, 0) => true
            case (2, 1) => true
            case (_, _) => false
        ),
        Behav := XorBehav,
        PortMap := C.PortMapping(["i0", "i1"], [0, 1], ["o"], [2])
    )

    lemma NKXorValid()
        ensures C.CNodeKindSomewhatValid(nk_and)
    {
    }

    const xor_port_bound: C.CPort := 3

    lemma nk_xor_valid()
        ensures C.CNodeKindValid(0, nk_xor)
    {
    }

    const nk_and: C.CNodeKind := C.CComb(
        PathExists := (a: C.CPort, b: C.CPort) => (
            match (a, b)
            case (2, 0) => true
            case (2, 1) => true
            case (_, _) => false
        ),
        Behav := AndBehav,
        PortMap := C.PortMapping(["i0", "i1"], [0, 1], ["o"], [2])
    )

}
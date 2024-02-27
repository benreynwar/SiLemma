module Primitives {

    import opened Std.Wrappers
    import C = Circuit

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

    const nk_xor := C.CComb(
        IPorts := {0, 1},
        OPorts := {2},
        PathExists := (a: C.CPort, b: C.CPort) => (
            match (a, b)
            case (2, 0) => true
            case (2, 1) => true
            case _ => false
        ),
        Behav := behav_xor,
        PortNames := C.PortNames2to1
    )

    const xor_port_bound: C.CPort := 3

    lemma nk_xor_valid()
        ensures C.CNodeKindValid(0, xor_port_bound, nk_xor)
    {
    }


    //lemma XorValid()
    //    ensures C.CNodeKindValid(

}
// Working to prove that HPNP are bounded.
module CircuitBounds {

    import opened Std.Wrappers
    import opened Circuit
    import Seq=Std.Collections.Seq

    function GetSubCRef(lib: CLib, c: Circuit, n: CNode): (r: Option<CircuitRef>)
        requires CircuitValid(lib, c)
        ensures r.None? || (CRefCircuitValid(lib, r.value) && CRefHierLevelReduced(lib, c, r.value))
        ensures c.NodeKind(n).Some? && c.NodeKind(n).value.CHier? ==>
            r.Some? && (r.value == c.NodeKind(n).value.CRef)
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, c);
        match c.NodeKind(n)
            case Some(nk) => (
                match nk
                case CHier(cref) =>
                    assert CNodeKindValid(lib, c.HierLevel, c.PortBound, nk);
                    assert CRefValid(lib, cref);
                    Some(cref)
                case _ => None
            )
            case _ => None
    }

    predicate CRefHierLevelReduced(lib: CLib, c: Circuit, cref: CircuitRef)
        requires CircuitValid(lib, c)
        requires CRefCircuitValid(lib, cref)
    {
        var unref_c := lib.Circuits[cref];
        unref_c.HierLevel < c.HierLevel
    }

    function DirectSubCRefsInternal(lib: CLib, c: Circuit, n: CNode, subcircuits: seq<CircuitRef>): (r: seq<CircuitRef>)
        requires CircuitValid(lib, c)
        requires forall i: nat :: i < |subcircuits| ==>
            CRefCircuitValid(lib, subcircuits[i]) && CRefHierLevelReduced(lib, c, subcircuits[i])
        requires forall m: CNode :: m >= n && c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==> c.NodeKind(m).value.CRef in subcircuits
        ensures forall i: nat :: i < |r| ==>
            CRefCircuitValid(lib, r[i]) && CRefHierLevelReduced(lib, c, r[i])
        ensures forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            c.NodeKind(m).value.CRef in r
    {
        if n == 0 then
            subcircuits
        else
            var new_cref := GetSubCRef(lib, c, n-1);
            var updated_subcircuits: seq<CircuitRef> :=
                match new_cref
                    case Some(cref) => subcircuits + [cref]
                    case None => subcircuits;
            DirectSubCRefsInternal(lib, c, n-1, updated_subcircuits)
    }

    function DirectSubCRefs(lib: CLib, c: Circuit): (r: seq<CircuitRef>)
        requires CircuitValid(lib, c)
        ensures forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            c.NodeKind(m).value.CRef in r
        ensures forall cref: CircuitRef :: cref in r ==>
            CRefCircuitValid(lib, cref) && CRefHierLevelReduced(lib, c, cref)
    {
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, c);
        assert forall n: CNode :: n >= c.NodeBound ==> c.NodeKind(n).None?;
        DirectSubCRefsInternal(lib, c, c.NodeBound, [])
    }

    lemma {:vcs_split_on_every_assert} HierBoundEncloses(
            lib: CLib, c: Circuit, bound_f: Circuit -> nat, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        ensures
            var hierc := HierarchyPathCircuit(lib, c, hp);
            CircuitValid(lib, hierc) &&
            HierBound(lib, hierc, bound_f) <= HierBound(lib, c, bound_f)
        decreases |hp.v|
    {
        var hierc := HierarchyPathCircuit(lib, c, hp);
        HierarchyPathCircuitValid(lib, c, hp);
        if |hp.v| == 0 {
            assert HierBound(lib, hierc, bound_f) <= HierBound(lib, c, bound_f);
        } else {
            var (head, tail) := HPHeadTail(hp);
            HierBoundEncloses(lib, c, bound_f, tail);
            var tail_c := HierarchyPathCircuit(lib, c, tail);
            HierarchyPathCircuitValid(lib, c, tail);
            assert HierBound(lib, tail_c, bound_f) <= HierBound(lib, c, bound_f);
            assert HierBound(lib, hierc, bound_f) <= HierBound(lib, c, bound_f);
        }
    }

    function GetSubBounds(lib: CLib, c: Circuit, bound_f: Circuit -> nat): (r: seq<nat>)
        requires CircuitValid(lib, c)
        ensures forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            CRefValid(lib, c.NodeKind(m).value.CRef) &&
            var subc := lib.Circuits[c.NodeKind(m).value.CRef];
            CircuitValid(lib, subc) &&
            subc.HierLevel < c.HierLevel &&
            HierBound(lib, subc, bound_f) in r
        decreases c.HierLevel, 0
    {
        var subcrefs := DirectSubCRefs(lib, c);
        var new_bound := bound_f(c);
        assert forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subcref := c.NodeKind(m).value.CRef;
            subcref in subcrefs;
        var bounds := Seq.Map(
            cref requires CRefCircuitValid(lib, cref) && CRefHierLevelReduced(lib, c, cref)  =>
                HierBound(lib, lib.Circuits[cref], bound_f),
            subcrefs);
        assert forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subcref := c.NodeKind(m).value.CRef;
            var subc := lib.Circuits[subcref];
            var index: nat :| index < |subcrefs| && subcrefs[index] == subcref;
            (bounds[index] == HierBound(lib, subc, bound_f)) &&
            (HierBound(lib, subc, bound_f) in bounds);
        bounds
    }

    function {:vcs_split_on_every_assert} HierBound(lib: CLib, c: Circuit, bound_f: Circuit -> nat): (r: nat)
        requires CircuitValid(lib, c)
        ensures forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            CRefValid(lib, c.NodeKind(m).value.CRef) &&
            var subc := lib.Circuits[c.NodeKind(m).value.CRef];
            CircuitValid(lib, subc) &&
            subc.HierLevel < c.HierLevel &&
            HierBound(lib, subc, bound_f) <= r
        ensures bound_f(c) as nat <= r
        decreases c.HierLevel, 1
    {
        var bounds := GetSubBounds(lib, c, bound_f);
        var new_bound := bound_f(c);
        var combined_bounds := bounds + [new_bound];
        var max_bound := Seq.Max(combined_bounds);
        assert new_bound in combined_bounds;
        assert new_bound <= max_bound;
        var subcrefs := DirectSubCRefs(lib, c);
        assert forall pb: nat :: pb in bounds+[new_bound] ==> pb <= max_bound;
        assert forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subcref := c.NodeKind(m).value.CRef;
            (subcref in subcrefs) && 
            var subc := lib.Circuits[subcref];
            (HierBound(lib, subc, bound_f) in bounds + [bound_f(c)]);
        assert forall m: CNode :: c.NodeKind(m).Some? && c.NodeKind(m).value.CHier? ==>
            var subcref := c.NodeKind(m).value.CRef;
            var subc := lib.Circuits[subcref];
            (HierBound(lib, subc, bound_f) <= max_bound);
        max_bound
    }

    // Get a port bound
    // Show that port bound is bigger or equal to all circuit Port Bounds.

    // Port bound is determined recursively from the top Circuit.

    // Then we get a Subcircuit specified by a HP.
    // Prove that that it satisfies it by building the HP up from the start.

    function getpb(c: Circuit): nat
    {
        c.PortBound as nat
    }

    function getnb(c: Circuit): nat
    {
        c.NodeBound as nat
    }

    function HierPortBound(lib: CLib, c: Circuit): nat
        requires CircuitValid(lib, c)
    {
        HierBound(lib, c, getpb)
    }

    function HierNodeBound(lib: CLib, c: Circuit): nat
        requires CircuitValid(lib, c)
    {
        HierBound(lib, c, getnb)
    }

    lemma SubcircuitInHierPortBound(lib: CLib, c: Circuit, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        ensures
            var hier_c := HierarchyPathCircuit(lib, c, hp);
            hier_c.PortBound as nat <= HierPortBound(lib, c)
    {
        HierBoundEncloses(lib, c, getpb, hp);
    }


    lemma SubcircuitInHierNodeBound(lib: CLib, c: Circuit, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        ensures
            var hier_c := HierarchyPathCircuit(lib, c, hp);
            hier_c.NodeBound as nat <= HierNodeBound(lib, c)
    {
        HierBoundEncloses(lib, c, getnb, hp);
    }

    lemma HPInHierNodeBound(lib: CLib, c: Circuit, hp: HierarchyPath)
        requires CircuitValid(lib, c)
        requires HierarchyPathValid(lib, c, hp)
        ensures
            forall n: CNode :: (n in hp.v) ==> n as nat < HierNodeBound(lib, c)
        decreases |hp.v|
    {
        if |hp.v| == 0 {
        } else {
            var (head, tail) := HPHeadTail(hp);
            var hier_c := HierarchyPathCircuit(lib, c, hp);
            var tail_c := HierarchyPathCircuit(lib, c, tail);
            HierarchyPathCircuitValid(lib, c, tail);
            reveal CircuitValid();
            assert head <= tail_c.NodeBound;
            SubcircuitInHierNodeBound(lib, c, tail);
            assert tail_c.NodeBound as nat <= HierNodeBound(lib, c);
            HPInHierNodeBound(lib, c, tail);
            assert head as nat <= HierNodeBound(lib, c);
            assert forall n: CNode :: (n in tail.v) ==> n as nat < HierNodeBound(lib, c);
            assert forall n: CNode :: (n in tail.v + [head]) ==> n as nat < HierNodeBound(lib, c);
            assert tail.v + [head] == hp.v;
        }
    }

    // Show that the any valid hpnp is smaller than total bound

    function HPNPElementBound(lib: CLib, c: Circuit): nat
        requires CircuitValid(lib, c)
    {
        var max_node_index := HierNodeBound(lib, c);
        var max_port_index := HierPortBound(lib, c);
        var max_index := if max_node_index > max_port_index then max_node_index else max_port_index;
        max_index
    }

    lemma HPNPElementsInBound(lib: CLib, c: Circuit, hpnp: HPNP)
        requires CircuitValid(lib, c)
        requires HPNPValid(lib, c, hpnp)
        ensures
            forall n: CNode :: (n in hpnp.hpn.hp.v) ==> n as nat < HPNPElementBound(lib, c)
        ensures hpnp.hpn.n as nat < HPNPElementBound(lib, c)
        ensures hpnp.p as nat < HPNPElementBound(lib, c)
    {
        var element_bound := HPNPElementBound(lib, c);
        HPNPValidHPValid(lib, c, hpnp);
        HPInHierNodeBound(lib, c, hpnp.hpn.hp);
        var hier_c := HierarchyPathCircuit(lib, c, hpnp.hpn.hp);
        HierarchyPathCircuitValid(lib, c, hpnp.hpn.hp);
        SubcircuitInHierNodeBound(lib, c, hpnp.hpn.hp);
        assert hier_c.NodeBound as nat <= element_bound;
        SubcircuitInHierPortBound(lib, c, hpnp.hpn.hp);
        assert hier_c.PortBound as nat <= element_bound;
        reveal CircuitValid();
        assert CircuitNodeKindValid(lib, hier_c);
        reveal HPNPValidInput();
        reveal HPNPValidOutput();
        assert hpnp.p < hier_c.PortBound;
        assert hpnp.hpn.n < hier_c.NodeBound;
    }

    function HPNPBound(lib: CLib, c: Circuit): nat
        requires CircuitValid(lib, c)
    {
        var max_index := HPNPElementBound(lib, c);
        var ns := Seq.Repeat(max_index, c.HierLevel+2);
        SeqNatToNat.ArbLenNatsToNat(ns)
    }


}
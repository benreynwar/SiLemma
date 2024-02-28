module CircuitPortBounds
{

    import opened Std.Wrappers
    import opened Std.Collections.Seq
    import opened CircuitBase
    import opened CircuitHierarchy

    function PortListBound(pl: seq<CPort>): CPort
    {
        if |pl| == 0 then
            0 as CPort
        else
            var pl_nat := seq(|pl|, (index: nat) requires index < |pl| => pl[index] as nat);
            var m: nat := Seq.Max(pl_nat);
            m as CPort
    }

    lemma NKPortBoundBinds(nk: CNodeKind)
        ensures 
            var bound := NKPortBound(nk);
            forall p: CPort ::
                (IsIPort(nk, p) ==> p < bound) &&
                (IsOPort(nk, p) ==> p < bound)
    {
        var bound := NKPortBound(nk);
        match nk
        case CHier(subc) => {
            assert forall p: CPort ::
                (IsIPort(nk, p) ==> p < bound) &&
                (IsOPort(nk, p) ==> p < bound);
        }
        case CComb(iports, oports, path_exists, behav, name) => {
            assert forall p: CPort ::
                (IsIPort(nk, p) ==> p < bound) &&
                (IsOPort(nk, p) ==> p < bound);
        }
        case CInput() => {
        }
        case CConst(v) =>  {
        }
        case COutput() => {
        } 
        case CSeq() => {
            assert forall p: CPort ::
                (IsIPort(nk, p) ==> p < bound) &&
                (IsOPort(nk, p) ==> p < bound);
        }
    }

    function MaxNodeInternal(c: Circuit, f: CNode -> bool, n: CNode): (r: Option<CNode>)
        ensures r.None? ==> !exists m: CNode :: m <= n && f(m)
        ensures r.Some? ==> !exists m: CNode :: m > r.value && m <= n && f(m)
        decreases n
    {
        if f(n) then
            Some(n)
        else
            if n == 0 then
                None
            else
                MaxNodeInternal(c, f, n-1)
    }

    function CInputNodeBound(c: Circuit): (r: CNode)
        requires CircuitValid(c)
        ensures forall n: CNode ::
            c.NodeKind(n).Some? && c.NodeKind(n).value.CInput? ==>
            n < r
    {
        reveal CircuitValid();
        assert forall n: CNode ::
            c.NodeKind(n).Some? ==> n < c.NodeBound;
        var maybe_n := MaxNodeInternal(c, n => c.NodeKind(n).Some? && c.NodeKind(n).value.CInput?, c.NodeBound-1);
        match maybe_n
        case None => 0
        case Some(n) => n + 1
    }

    function COutputNodeBound(c: Circuit): (r: CNode)
        ensures forall n: CNode ::
            c.NodeKind(n).Some? && c.NodeKind(n).value.COutput? ==>
            n < r
    {
        var maybe_n := MaxNodeInternal(c, n => c.NodeKind(n).Some? && c.NodeKind(n).value.COutput?, c.NodeBound-1);
        match maybe_n
        case None => 0
        case Some(n) => n + 1
    }


    function NKPortBound(nk: CNodeKind): CPort
    {
        var bound := match nk
        case CHier(c) =>
            var max_i := CInputNodeBound(c);
            var max_o := COutputNodeBound(c);
            (if max_i > max_o then max_i else max_o) as CPort
        case CComb(iports, oports, _, _, _) =>
            var max_i := PortListBound(iports);
            var max_o := PortListBound(oports);
            if max_i > max_o then max_i+1 else max_o+1
        case CConst(_) => OUTPUT_PORT +1
        case CInput() => OUTPUT_PORT +1
        case COutput() => INPUT_PORT +1
        case CSeq() => (if INPUT_PORT > OUTPUT_PORT then INPUT_PORT else OUTPUT_PORT)+1;
        bound
    }

    ghost function CircuitMaxPortBound(c: Circuit): nat
        requires CircuitValid(c)
        decreases c.HierLevel, 2
    {
        var subcircuits: seq<Circuit> := HierSubcircuits(c);
        var port_bounds := (set c: Circuit | c in subcircuits :: c.PortBound as nat);
        if |port_bounds| == 0 then
            c.PortBound as nat
        else
            var max_hier_port_bound := MaxInSet(port_bounds);
            if c.PortBound as nat > max_hier_port_bound then c.PortBound as nat else max_hier_port_bound
    }

    ghost function HierSubcircuitsInternal(
        hier_level: nat, new_cs: seq<Circuit>, old_cs: seq<Circuit>): (r: seq<Circuit>)
        requires forall x :: x in new_cs ==> x.HierLevel < hier_level
        requires forall x :: x in new_cs ==> CircuitValid(x)
        decreases hier_level, 0, |new_cs|
     {
        if |new_cs| == 0 then
            old_cs
        else
            var head: Circuit := new_cs[0];
            var tail: seq<Circuit> := new_cs[1..];
            var expanded := HierSubcircuits(head);
            HierSubcircuitsInternal(hier_level, tail, old_cs + expanded)
     }
 
     ghost function HierSubcircuits(c: Circuit): (r: seq<Circuit>)
         requires CircuitValid(c)
         decreases c.HierLevel, 1
     {
         var direct := DirectSubcircuits(c);
         reveal CircuitValid();
         assert CircuitNodeKindValid(c);
         HierSubcircuitsInternal(c.HierLevel, direct, direct)
     }

    ghost function MaxInSetInternal(a: set<nat>, max: nat): nat
    {
        if |a| == 0 then
            max
        else
            var y :| y in a;
            MaxInSetInternal(
                a - {y},
                if y > max then y else max
            )
    }

    ghost function MaxInSet(a: set<nat>): nat
        requires |a| > 0
    {
        var y :| y in a;
        MaxInSetInternal(a - {y}, y)
    }



}
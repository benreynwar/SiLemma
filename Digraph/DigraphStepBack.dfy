module DigraphStepBack {

    import opened Std.Wrappers

    import opened DigraphBase
    import opened DigraphPaths

    lemma NoPathLengthXNoPathsLonger<Node>(g: Digraph, length: nat)
        requires !exists p: Path<Node> :: |p.v| == length && PathValid(g, p)
        ensures forall p: Path<Node> :: PathValid(g, p) ==> |p.v| < length
    {
        if exists p :: PathValid(g, p) && |p.v| >= length {
            var p :| PathValid(g, p) && |p.v| >= length;
            var q := Path(p.v[..length]);
            reveal PathValid();
            assert PathValid(g, q);
        }
    }

    function RepeatLoopUntilLength(g: Digraph, p: Path, loop: Path, length: nat): (r: Path)
        requires DigraphValid(g)
        requires PathValid(g, p)
        requires PathValid(g, loop) && PathLoop(loop)
        requires |p.v| > 0
        requires PathEnd(p) == PathStart(loop)
        ensures |r.v| > length
        ensures PathValid(g, r)
        decreases length - |p.v|
    {
        reveal DigraphValid();
        reveal PathValid();
        if |p.v| > length then
            p
        else
            var q := Path(p.v + loop.v[1..]);
            var r := RepeatLoopUntilLength(g, q, loop, length);
            r
    }

    lemma MultipleStepSetEmptyGivesNoLoop<Node(!new)>(g: Digraph, count: nat)
        requires DigraphValid(g)
        requires MultipleStepSetBack(g, AllNodes(g), count) == {}
        ensures !DigraphLoop(g)
    {
        MultipleStepSetBackGivesMaxPathLength(g, count);
        reveal DigraphLoop();
        reveal PathValid();
        if DigraphLoop(g) {
            var p :| PathValid(g, p) && PathLoop(p);
            var q := RepeatLoopUntilLength(g, p, p, count);
        }
    }

    lemma {:vcs_split_on_every_assert} MultipleStepSetBackGivesMaxPathLength<Node(!new)>(g: Digraph, count: nat)
        requires DigraphValid(g)
        requires MultipleStepSetBack(g, AllNodes(g), count) == {}
        ensures forall p : Path<Node> :: PathValid(g, p) ==> |p.v| <= count
    {
        // We want to show that if the input set is all nodes and the result is an empty set then the maximum path length is <= 'count'.
        reveal PathValid();
        var all_nodes := AllNodes(g);

        assert forall n: Node :: g.IsNode(n) ==> NodeValid(g, n);

        if count == 0 {
            assert MultipleStepSetBack(g, AllNodes(g), count) == all_nodes;
            assert all_nodes == {};
        }

        if exists p: Path<Node> :: |p.v| == count+1 && PathValid(g, p) {
            var p: Path<Node> :| |p.v| == count + 1 && PathValid(g, p);
            assert forall n: Node :: n in p.v ==> NodeValid(g, n);
            if count == 0 {
                assert AllNodes(g) == {};
                if |p.v| > 0 {
                    var n := PathStart(p);
                    assert n !in AllNodes(g);
                    assert NodeValid(g, n);
                    assert false;
                }
            } else {
                PathExistsEndInMultipleStepSet(g, p, all_nodes);
            }
            assert forall p : Path<Node> :: PathValid(g, p) ==> |p.v| <= count;
        } else {
            assert !exists p: Path<Node> :: |p.v| == count+1 && PathValid(g, p);
            NoPathLengthXNoPathsLonger(g, count+1);
            assert forall p : Path<Node> :: PathValid(g, p) ==> |p.v| <= count;
        }
    }

    ghost function MultipleStepSetBack<Node(!new)>(g: Digraph, in_ns: set<Node>, count: nat): (r: set<Node>)
        requires DigraphValid(g)
        requires forall n :: n in in_ns ==> NodeValid(g, n)
        ensures forall n :: n in r ==> NodeValid(g, n)
        decreases count
    {
        if count == 0 then
            in_ns
        else
            var s := StepSetBack(g, in_ns);
            MultipleStepSetBack(g, s, count-1)
    }

    ghost function StepSetBackInternal<Node(!new)>(g: Digraph, in_ns: set<Node>, out_ns: set<Node>): (r: set<Node>)
        requires DigraphValid(g)
        requires forall n :: n in in_ns ==> NodeValid(g, n)
        requires forall n :: n in out_ns ==> NodeValid(g, n)
        ensures forall n :: n in r ==> NodeValid(g, n)
        ensures forall m :: (m in r <==> exists n :: (n in in_ns && g.IsConnected(n, m)) || (m in out_ns))
    {
        if |in_ns| == 0 then
            out_ns
        else
            var n :| n in in_ns;
            var connected := StepBack(g, n);
            assert forall m :: m in connected ==> NodeValid(g, m);
            var new_in_ns := in_ns - {n};
            var new_out_ns := out_ns + connected;
            StepSetBackInternal(g, new_in_ns, new_out_ns)
    }

    ghost function StepSetBack<Node(!new)>(g: Digraph, in_ns: set<Node>): (r: set<Node>)
        requires DigraphValid(g)
        requires forall n :: n in in_ns ==> NodeValid(g, n)
        ensures forall n :: n in r ==> NodeValid(g, n)
        ensures forall m :: m in r <==> exists n :: (n in in_ns && g.IsConnected(n, m))
    {
        StepSetBackInternal(g, in_ns, {})
    }

    lemma {:vcs_split_on_every_assert} PathExistsEndInMultipleStepSet<Node(!new)>(g: Digraph, p: Path<Node>, in_ns: set<Node>)
        requires DigraphValid(g)
        requires PathValid(g, p)
        requires |p.v| > 0
        requires forall n :: n in in_ns ==> NodeValid(g, n)
        requires PathStart(p) in in_ns
        ensures
            var out_s := MultipleStepSetBack(g, in_ns, |p.v|-1);
            PathEnd(p) in out_s
        decreases |p.v|
    {
        var out_ns := MultipleStepSetBack(g, in_ns, |p.v|-1);
        if |p.v| == 1 {
            assert out_ns == in_ns;
            assert PathEnd(p) == PathStart(p);
            assert PathEnd(p) in out_ns;
        } else {
            var head := PathStart(p);
            var tail := Path(p.v[1..]);
            var intermed_ns := StepSetBack(g, in_ns);
            reveal PathValid();
            assert g.IsConnected(head, PathStart(tail));
            assert PathStart(tail) in intermed_ns;
            PathExistsEndInMultipleStepSet(g, tail, intermed_ns);
        }
    }
    
    
    function StepBack<Node(!new)>(g: Digraph, n: Node): (r: set<Node>)
        requires DigraphValid(g)
        requires NodeValid(g, n)
        ensures forall m :: m in r ==> NodeValid(g, m)
        ensures forall m :: m in r <==> g.IsConnected(n, m)
    {
        reveal DigraphValid();
        var mapped := set m: nat | m < g.NodeBound :: m;
        var nodes := Set.Map(g.InvNodeMap, mapped);
        var filter := (n: Option<Node>) => n.Some?;
        var filtered_nodes := Set.Filter(filter, nodes);
        var extracted_nodes := set n | n in nodes && n.Some? :: n.value;
        var connected_nodes := set m | m in extracted_nodes && g.IsConnected(n, m) :: m;
        connected_nodes 
    }

}
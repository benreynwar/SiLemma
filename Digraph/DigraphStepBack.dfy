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

        if count == 0 {
            assert MultipleStepSetBack(g, AllNodes(g), count) == all_nodes;
            assert all_nodes == {};
        }

        if exists p: Path<Node> :: |p.v| == count+1 && PathValid(g, p) {
            var p: Path<Node> :| |p.v| == count + 1 && PathValid(g, p);
            if count == 0 {
                assert AllNodes(g) == {};
                if |p.v| > 0 {
                    var n := PathStart(p);
                    assert n !in AllNodes(g);
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
        ensures forall m :: (m in r <==> exists n :: (n in in_ns && IsConnected(g, n, m)) || (m in out_ns))
    {
        if |in_ns| == 0 then
            out_ns
        else
            var n :| n in in_ns;
            var connected := StepBack(g, n);
            var new_in_ns := in_ns - {n};
            var new_out_ns := out_ns + connected;
            StepSetBackInternal(g, new_in_ns, new_out_ns)
    }

    ghost function StepSetBack<Node(!new)>(g: Digraph, in_ns: set<Node>): (r: set<Node>)
        requires DigraphValid(g)
        ensures forall m :: m in r <==> exists n :: (n in in_ns && IsConnected(g, n, m))
    {
        StepSetBackInternal(g, in_ns, {})
    }

    lemma {:vcs_split_on_every_assert} PathExistsEndInMultipleStepSet<Node(!new)>(g: Digraph, p: Path<Node>, in_ns: set<Node>)
        requires DigraphValid(g)
        requires PathValid(g, p)
        requires |p.v| > 0
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
            assert IsConnected(g, head, PathStart(tail));
            assert PathStart(tail) in intermed_ns;
            PathExistsEndInMultipleStepSet(g, tail, intermed_ns);
        }
    }
    
    
    function StepBack<Node(!new)>(g: Digraph, n: Node): (r: set<Node>)
        requires DigraphValid(g)
        ensures forall m :: m in r <==> IsConnected(g, n, m)
    {
        (set m | m in g.Nodes && IsConnected(g, n, m))
    }

}
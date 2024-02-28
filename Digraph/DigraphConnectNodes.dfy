module DigraphConnectNodes {

    import opened DigraphBase
    import opened DigraphPaths

    function ConnectNodes<Node(==)>(g: Digraph, n: Node, m: Node): (r: Digraph)
        requires g.IsNode(n)
        requires g.IsNode(m)
        requires n != m
        requires !g.IsConnected(n, m)
    {
        Digraph(
            g.IsNode,
            (a, b) => ((a==n) && (b==m)) || g.IsConnected(a, b),
            g.NodeMap,
            g.InvNodeMap,
            g.NodeBound
        )
    }

    lemma ConnectNodesDigraphValid<Node>(g: Digraph, n: Node, m: Node)
        requires g.IsNode(n)
        requires g.IsNode(m)
        requires n != m
        requires !g.IsConnected(n, m)
        requires DigraphValid(g)
        ensures
            var r := ConnectNodes(g, n, m);
            DigraphValid(r)
    {
        reveal DigraphValid();
    }

    function ConnectNodesV<Node(==)>(g: Digraph, n: Node, m: Node): (r: Digraph)
        requires g.IsNode(n)
        requires g.IsNode(m)
        requires n != m
        requires !g.IsConnected(n, m)
        requires DigraphValid(g)
        ensures DigraphValid(r)
    {
        ConnectNodesDigraphValid(g, n, m);
        ConnectNodes(g, n, m)
    }

    lemma ConnectNodesPathStillValid<Node>(g: Digraph, n: Node, m: Node, p: Path<Node>)
        requires g.IsNode(n) && g.IsNode(m) && n != m && !g.IsConnected(n, m)
        requires PathValid(g, p)
        ensures
            var r := ConnectNodes(g, n, m);
            PathValid(r, p)
    {
        reveal PathValid(); 
    }

    lemma ConnectNodesPathStillExists<Node(!new)>(
            g: Digraph, n: Node, m: Node, a: Node, b: Node)
        requires g.IsNode(n) && g.IsNode(m) && n != m && !g.IsConnected(n, m)
        requires PathExists(g, a, b)
        ensures
            var r := ConnectNodes(g, n, m);
            PathExists(r, a, b)
    {
        var r := ConnectNodes(g, n, m);
        var p :| PathFromTo(g, p, a, b);
        ConnectNodesPathStillValid(g, n, m, p);
        PathExistsByExample(r, p, a, b);
    }

    lemma ConnectNodesPathExists<Node(!new)>(g: Digraph, n: Node, m: Node)
        requires g.IsNode(n) && g.IsNode(m) && n != m && !g.IsConnected(n, m)
        ensures
            var r := ConnectNodes(g, n, m);
            PathExists(r, n, m)
    {
        var p := Path([n, m]);
        var r := ConnectNodes(g, n, m);
        assert r.IsConnected(n, m);
        reveal PathValid();
        assert PathFromTo(r, p, n, m);
        PathExistsByExample(r, p, n, m);
        assert PathExists(r, n, m);
    }

    // If there was already a path from b to a then adding a connection from a to b will
    // create a loop.
    lemma ConnectNodesDigraphLoop<Node(!new)>(g: Digraph, n: Node, m: Node)
        requires g.IsNode(n) && g.IsNode(m) && n != m && !g.IsConnected(n, m)
        ensures
            var r := ConnectNodes(g, n, m);
            DigraphLoop(r) == DigraphLoop(g) || PathExists(g, m, n)
    {
        var r := ConnectNodes(g, n, m);
        if DigraphLoop(g) {
            reveal DigraphLoop();
            var p: Path<Node> :| PathValid(g, p) && PathLoop(p);
            ConnectNodesPathStillValid(g, n, m, p);
            assert PathValid(r, p);
            assert DigraphLoop(r);
        }
        ConnectNodesPathExists(g, n, m);
        assert PathExists(r, n, m);
        if PathExists(g, m, n) {
            var p :| PathFromTo(g, p, m, n);
            reveal PathValid();
            assert PathFromTo(r, p, m, n);
            ConnectNodesPathStillValid(g, n, m, p);
            assert PathExists(r, m, n);
            PathExistsAdd(r, n, m, n);
            assert PathExists(r, n, n);
            var q :| PathFromTo(r, q, n, n);
            assert PathLoop(q);
            reveal DigraphLoop();
            assert DigraphLoop(r);
        }
        if DigraphLoop(r) {
            reveal DigraphLoop();
            if !DigraphLoop(g) {
                var p :| PathValid(r, p) && PathLoop(p);
                assert !PathValid(g, p);
                reveal PathValid();
                // First assume that n to m is not in the path.
                // Then prove that this is not possible.
                if !exists index: nat :: index < |p.v|-1 && (p.v[index] == n) && (p.v[index+1] == m) {
                    forall index: nat | index < |p.v|-1
                        ensures g.IsConnected(p.v[index], p.v[index+1])
                    {
                        assert r.IsConnected(p.v[index], p.v[index+1]);
                        assert g.IsConnected(p.v[index], p.v[index+1]);
                    }
                    assert false;
                }
                assert exists index: nat :: index < |p.v|-1 && (p.v[index] == n) && (p.v[index+1] == m);
                var index: nat :| index < |p.v|-1 && (p.v[index] == n) && (p.v[index+1] == m);
                assert PathStart(p) == PathEnd(p);
                var q_1 := PathSegment(p, index+1, |p.v|);
                assert |q_1.v| > 0;
                assert PathEnd(q_1) == p.v[|p.v|-1];
                assert PathEnd(q_1) == PathEnd(p);
                PathSegmentValid(r, p, index+1, |p.v|);
                assert PathValid(r, q_1);
                var q_2 := PathSegment(p, 0, index+1);
                assert PathStart(q_2) == PathStart(p);
                assert PathStart(q_2) == PathEnd(q_1);
                PathSegmentValid(r, p, 0, index+1);
                var q := AddPaths(q_1, q_2);
                AddPathsValid(r, q_1, q_2);
                assert PathValid(r, q);
                AddPathsFromTo(r, q_1, q_2);
                assert p.v[index+1] == m;
                assert q_1.v[0] == m;
                assert PathFromTo(r, q, m, n);
                // We want to now show that [n, m] does not appear in q.
                // We actually need to find another path that removes any repeats and then
                // show that that does not include [n, m]
                // Then we can show that that is valid in g.
                var s := PathRemoveLoops(q);
                RemoveLoopsFromToSame(r, q);
                assert PathFromTo(r, s, m, n);
                assert PathValid(r, s);
                assert PathNoRepeats(s);
                assert PathValid(g, s);
                assert PathFromTo(g, s, m, n);
            }
            assert DigraphLoop(g) || PathExists(g, m, n);
        }
    }

}
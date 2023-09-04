module Digraph {

    newtype Node = nat

    datatype Path = Path(v: seq<Node>)

    datatype Digraph = Digraph(
        IsNode: Node -> bool,
        IsConnected: (Node, Node) -> bool,
        // This is larger or equal to all nodes for which IsNode(node) is true.
        // We use this help dafny prove that things are finite and terminate.
        NodeBound: Node
    )

    ghost predicate {:opaque} DigraphValid(g: Digraph)
    {
        (forall n: Node :: n > g.NodeBound ==> !g.IsNode(n)) &&
        (forall n: Node :: !g.IsConnected(n, n)) && // No self-connections
        (forall n: Node, m: Node :: g.IsConnected(n, m) ==> g.IsNode(n) && g.IsNode(m))
    }
    
    lemma NotNodeNotConnected(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires !g.IsNode(n)
        ensures
            (forall m: Node :: !g.IsConnected(m, n)) &&
            (forall m: Node :: !g.IsConnected(n, m))
    {
        reveal DigraphValid();
    }

    predicate {:opaque} PathValid(g: Digraph, p: Path)
    {
        (forall i: nat :: i < |p.v| ==> g.IsNode(p.v[i])) &&
        (forall i: nat :: i < |p.v|-1 ==> g.IsConnected(p.v[i], p.v[i+1]))
    }

    predicate PathLoop(p: Path)
    {
        |p.v| > 1 && p.v[0] == p.v[|p.v|-1]
    }

    predicate PathNoRepeats(p: Path)
    {
        forall i: nat, j: nat :: i < |p.v| && j < |p.v| && i != j ==> p.v[i] != p.v[j]
    }

    predicate PathSimpleLoop(p: Path)
    {
        PathLoop(p) && PathNoRepeats(Path(p.v[1..|p.v|]))
    }

    function PathStart(p: Path): Node
        requires |p.v| > 0
    {
        p.v[0]
    }

    function PathEnd(p: Path): Node
        requires |p.v| > 0
    {
        p.v[|p.v|-1]
    }

    function PathRemoveLoops(p: Path): (r: Path)
        requires |p.v| > 0
    {
        PathRemoveLoopsInternal(p, |p.v|-1)
    }

    function PathFindIndex(p: Path, n: Node): (r: nat)
        requires n in p.v
        ensures r < |p.v|
        ensures p.v[r] == n
    {
        PathFindIndexInternal(p, n, 0)
    }

    function PathFindIndexInternal(p: Path, n: Node, index: nat): (r: nat)
        requires index < |p.v|
        requires n in p.v[index..|p.v|]
        ensures r < |p.v|
        ensures p.v[r] == n
        decreases |p.v| - index
    {
        if p.v[index] == n then
            index
        else
            PathFindIndexInternal(p, n, index+1)
    }

    function PathSegment(p: Path, start: nat, stop: nat): (r: Path)
        requires start < |p.v|
        requires stop <= |p.v|
        requires start < stop
        ensures |r.v| > 0
    {
        Path(p.v[start..stop])
    }

    lemma PathSegmentValid(g: Digraph, p: Path, start: nat, stop: nat)
        requires start < |p.v|
        requires stop <= |p.v|
        requires start < stop
        requires PathValid(g, p)
        ensures 
            var r := PathSegment(p, start, stop);
            PathValid(g, r)
    {
        reveal PathValid();
    }

    function PathRemoveLoopsInternal(p: Path, index: nat): (r: Path)
        requires index < |p.v|
        decreases index
    {
        if index == 0 then
            Path([p.v[0]])
        else 
            var earlier_path := PathRemoveLoopsInternal(p, index-1);
            var n := p.v[index];
            if n in earlier_path.v then
                var loc := PathFindIndex(earlier_path, n);
                Path(earlier_path.v[0..loc+1])
            else
                Path(earlier_path.v + [n])
    }

    lemma RemoveLoopsFromToSame(g: Digraph, p: Path)
        requires |p.v| > 1
        requires p.v[0] != p.v[|p.v|-1]
        requires PathValid(g, p)
        ensures
            var a := p.v[0];
            var b := p.v[|p.v|-1];
            var q := PathRemoveLoops(p);
            ShortPathFromTo(g, q, a, b)
    {
        RemoveLoopsFromToSameInternal(g, p, |p.v|-1);
    }

    lemma RemoveLoopsFromToSameInternal(g: Digraph, p: Path, index: nat)
        requires index < |p.v|
        requires |p.v| > 1
        requires p.v[0] != p.v[|p.v|-1]
        requires PathValid(g, p)
        ensures
            var a := p.v[0];
            var b := p.v[index];
            var q := PathRemoveLoopsInternal(p, index);
            ShortPathFromTo(g, q, a, b)
    {
        var a := p.v[0];
        var b := p.v[index];
        var q := PathRemoveLoopsInternal(p, index);
        if index == 0 {
            assert q == Path([a]);
            reveal PathValid();
            assert ShortPathFromTo(g, q, a, b);
        } else {
            var earlier_path := PathRemoveLoopsInternal(p, index-1);
            RemoveLoopsFromToSameInternal(g, p, index-1);
            var n := p.v[index];
            if n in earlier_path.v {
                var loc := PathFindIndex(earlier_path, n);
                assert q == Path(earlier_path.v[0..loc+1]);
            } else {
                assert q == Path(earlier_path.v + [n]);
            }
            reveal PathValid();
            assert PathValid(g, earlier_path);
            assert PathValid(g, q);
            assert ShortPathFromTo(g, q, a, b);
        }
    }

    lemma RemoveLoopsNoRepeats(p: Path)
        ensures
            var q := PathRemoveLoopsInternal(p, index);
            PathNoRepeats(q)
    {
        RemoveLoopsNoRepeatsInternal(p, 0);
    }

    lemma RemoveLoopsNoRepeatsInternal(p: Path, index: nat)
        requires index < |p.v|
        ensures
            var q := PathRemoveLoopsInternal(p, index);
            PathNoRepeats(q)
    {
        var q := PathRemoveLoopsInternal(p, index);
        if index == 0 {
            var q := Path([p.v[0]]);
            assert |q.v| == 1;
            assert PathNoRepeats(q);
        } else { 
            var earlier_path := PathRemoveLoopsInternal(p, index-1);
            var n := p.v[index];
            if n in earlier_path.v {
                var loc := PathFindIndex(earlier_path, n);
                var q := Path(earlier_path.v[0..loc+1]);
                assert PathNoRepeats(q);
            } else {
                var q := Path(earlier_path.v + [n]);
                assert PathNoRepeats(q);
            }
        }
    }

    ghost predicate PathExists(g: Digraph, a: Node, b: Node)
    {
        exists p: Path :: PathFromTo(g, p, a, b)
    }

    predicate PathFromTo(g: Digraph, p: Path, a: Node, b: Node)
    {
        PathValid(g, p) && |p.v| > 1 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }

    predicate SimplePathFromTo(g: Digraph, p: Path, a: Node, b: Node)
    {
        PathValid(g, p) && |p.v| > 1 && (p.v[0] == a) && (p.v[|p.v|-1] == b) &&
        PathNoRepeats(Path(p.v[0..|p.v|-2]))
    }

    predicate ShortPathFromTo(g: Digraph, p: Path, a: Node, b: Node)
    {
        PathValid(g, p) && |p.v| > 0 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }

    function PathIndex(p: Path, n: Node): (r: nat)
        requires n in p.v
        ensures
            r < |p.v| &&
            p.v[r] == n
        decreases |p.v|
    {
        if p.v[0] == n then
            0
        else
            PathIndex(Path(p.v[1..|p.v|]), n) + 1
    }

    ghost predicate {:opaque} DigraphLoop(g: Digraph)
    {
        exists p: Path :: PathValid(g, p) && PathLoop(p)
    }

    ghost predicate {:opaque} DigraphLoop2(g: Digraph)
    {
        exists n: Node :: PathExists(g, n, n)
    }

    lemma DigraphLoopEquiv(g: Digraph)
        ensures DigraphLoop(g) == DigraphLoop2(g)
    {
        reveal DigraphLoop();
        reveal DigraphLoop2();
        if DigraphLoop(g) {
            var p :| PathValid(g, p) && PathLoop(p);
            assert PathFromTo(g, p, p.v[0], p.v[0]);
            assert PathExists(g, p.v[0], p.v[0]);
        }
    }

    ghost function GetLoopPath(g: Digraph): (r: Path)
        requires DigraphLoop(g)
    {
        reveal DigraphLoop();
        DigraphLoopEquiv(g);
        assert DigraphLoop2(g);
        reveal DigraphLoop2();
        var n :| PathExists(g, n, n);
        var p :| PathValid(g, p) && |p.v| > 1 && p.v[0] == n && p.v[|p.v|-1] == n;
        p
    }

    
    // Adding nodes

    function AddNode(g: Digraph, n: Node): (r: Digraph)
        requires !g.IsNode(n)
    {
        Digraph(
            m=>(m==n) || g.IsNode(m),
            g.IsConnected,
            if n >= g.NodeBound then n else g.NodeBound
        )
    }

    lemma AddNodeDigraphValid(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires !g.IsNode(n)
        ensures
            var r := AddNode(g, n);
            DigraphValid(r)
    {
        reveal DigraphValid();
    }
    
    // There is only one path that becomes valid when we add a node.
    // It is the path containing just that node.
    lemma AddNodePathValid(g: Digraph, n: Node, p: Path)
        requires DigraphValid(g);
        requires !g.IsNode(n)
        ensures
            var r := AddNode(g, n);
            (PathValid(g, p) ==> PathValid(r, p)) &&
            (PathValid(r, p) ==> PathValid(g, p) || p == Path([n])) &&
            true
    {
        var r := AddNode(g, n);
        reveal PathValid();
        reveal DigraphValid();
        assert forall m: Node :: !g.IsConnected(m, n);
        if n in p.v {
            assert !PathValid(g, p);
            if |p.v| == 1 {
                assert PathValid(r, p);
            } else {
                if p.v[0] == n {
                    assert !r.IsConnected(p.v[0], p.v[1]);
                    assert !PathValid(r, p);
                } else {
                    var index := PathIndex(p, n);
                    assert !r.IsConnected(p.v[index-1], p.v[index]);
                    assert !PathValid(r, p);
                }
                assert !PathValid(r, p);
            }
        } else {
        }
    }

    /*
    When we add a node to a graph, that cannot introduce any loops.
    */
    lemma AddNodeLoopConserved(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires !g.IsNode(n)
        ensures
            var r := AddNode(g, n);
            DigraphLoop(g) == DigraphLoop(r)
    {
        var r := AddNode(g, n);
        reveal PathValid();
        reveal DigraphLoop();
        if DigraphLoop(g) {
            var p := GetLoopPath(g);
            assert PathValid(r, p);
            assert DigraphLoop(r);
        }
        if DigraphLoop(r) {
            var p :| PathValid(r, p) && PathLoop(p);
            AddNodePathValid(g, n, p);
            assert PathValid(g, p) || p == Path([n]);
            if p == Path([n]) {
                assert !PathLoop(p);
            }
            assert PathValid(g, p);
            assert DigraphLoop(g);
        }
    }
    

    lemma NotNodePathInvalid(g: Digraph, n: Node, p: Path)
        requires !g.IsNode(n)
        requires n in p.v
        ensures !PathValid(g, p)
    {
        reveal PathValid();
    }

    // Connecting two nodes

    function ConnectNodes(g: Digraph, n: Node, m: Node): (r: Digraph)
        requires g.IsNode(n)
        requires g.IsNode(m)
        requires n != m
        requires !g.IsConnected(n, m)
    {
        Digraph(
            g.IsNode,
            (a, b) => ((a==n) && (b==m)) || g.IsConnected(a, b),
            g.NodeBound
        )
    }

    lemma ConnectNodesDigraphValid(g: Digraph, n: Node, m: Node)
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

    lemma ConnectNodesPathStillValid(g: Digraph, n: Node, m: Node, p: Path)
        requires g.IsNode(n) && g.IsNode(m) && n != m && !g.IsConnected(n, m)
        requires PathValid(g, p)
        ensures
            var r := ConnectNodes(g, n, m);
            PathValid(r, p)
    {
        reveal PathValid(); 
    }

    lemma ConnectNodesPathExists(g: Digraph, n: Node, m: Node)
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
    }

    lemma PathExistsAdd(g: Digraph, a: Node, b: Node, c: Node)
        requires PathExists(g, a, b)
        requires PathExists(g, b, c)
        ensures PathExists(g, a, c)
    {
        var p :| PathFromTo(g, p, a, b);
        var q :| PathFromTo(g, q, b, c);
        assert |q.v| > 1;
        var pq := Path(p.v[0..|p.v|] + q.v[1..|q.v|]);
        reveal PathValid();
        assert PathValid(g, pq);
        assert PathFromTo(g, pq, a, c);
    }

    function AddPaths(p1: Path, p2: Path): (r: Path)
        requires |p1.v| > 0
        requires |p2.v| > 0
        requires p1.v[|p1.v|-1] == p2.v[0]
    {
        var p2t := if |p2.v| > 1 then p2.v[1..|p2.v|] else [];
        Path(p1.v + p2t)
    }

    lemma AddPathsValid(g: Digraph, p1: Path, p2: Path)
        requires PathValid(g, p1)
        requires PathValid(g, p2)
        requires |p1.v| > 0
        requires |p2.v| > 0
        requires p1.v[|p1.v|-1] == p2.v[0]
        ensures
            var r := AddPaths(p1, p2);
            PathValid(g, r)
    {
        reveal PathValid();
    }
    
    lemma AddPathsFromTo(g: Digraph, p1: Path, p2: Path)
        requires PathValid(g, p1)
        requires PathValid(g, p2)
        requires |p1.v| > 0
        requires |p2.v| > 0
        requires PathEnd(p1) == PathStart(p2)
        ensures
            var r := AddPaths(p1, p2);
            var a := PathStart(p1);
            var c := PathEnd(p2);
            ShortPathFromTo(g, r, a, c) &&
            |r.v| == |p1.v| + |p2.v| - 1
    {
        AddPathsValid(g, p1, p2);
    }

    // If there was already a path from b to a then adding a connection from a to b will
    // create a loop.
    lemma ConnectNodesDigraphLoop(g: Digraph, n: Node, m: Node)
        requires g.IsNode(n) && g.IsNode(m) && n != m && !g.IsConnected(n, m)
        //ensures
        //    var r := ConnectNodes(g, n, m);
        //    DigraphLoop(r) == DigraphLoop(g) || PathExists(g, m, n)
    {
        var r := ConnectNodes(g, n, m);
        if DigraphLoop(g) {
            reveal DigraphLoop();
            var p: Path :| PathValid(g, p) && PathLoop(p);
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
                        ensures g.IsConnected(p.v[index], p.v[index+1]);
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
                forall index: nat | index < |s.v|-1 {
                    var n1 := s.v[index];
                    var n2 := s.v[index+1];
                    //assert if index == 0 then n1 == m else n1 != m;
                    assert r.IsConnected(s.v[index], s.v[index+1]);
                    assert !((n1 == n) && (n2 == m));
                    assert g.IsConnected(s.v[index], s.v[index+1]);
                }
                assert PathValid(g, s);
                assert PathFromTo(g, s, m, n);
            }
            //assert DigraphLoop(g) || PathExists(g, m, n);
        }
    }
}
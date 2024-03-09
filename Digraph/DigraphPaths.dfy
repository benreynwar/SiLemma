module DigraphPaths {

    import Std.Collections.Seq
    import Std.Collections.Set
    import Utils
    import opened DigraphBase`Body
    import opened DBS = DigraphBase`Spec

    export Spec
        provides DBS
        provides DigraphLoop
        provides PathFindIndex
        provides PathLoop
        provides GetLoopPath
        provides PathExists, PathFromTo
        reveals PathStart, PathEnd

    export Body
        provides DBS
        reveals DigraphLoop
        reveals PathLoop
        reveals PathExists
        reveals PathFromTo, ShortPathFromTo
        reveals PathStart, PathEnd
        reveals PathSegment
        reveals AddPaths
        reveals PathNoRepeats
        // Shouldn't need to know what's happening inside
        provides GetLoopPath
        provides PathFindIndex
        // Kind reveal without revealing too much other stuff
        provides NumberOfRemainingNodesPath
        // functions shouldn't be used elsewhere
        provides DigraphLoop2
        // Do we even need this
        provides PathRemoveLoops
        // lemmas 
        provides PathExistsByExample, PathExistsAdd
        provides PathSegmentValid
        provides NoLoopsMeansNoRepeats
        provides RemoveLoopsFromToSame
        provides AddPathsValid, AddPathsFromTo
        provides DigraphLoopEquiv

    ghost predicate {:opaque} DigraphLoop<Node(!new)>(g: DBS.Digraph)
        // There's a loop in the digraph.
        // (there exists a path that is a loop).
    {
        exists p: Path<Node> :: PathValid(g, p) && PathLoop(p)
    }

    ghost predicate {:opaque} DigraphLoop2<Node(!new)>(g: Digraph)
        // There's a loop in the digraph.
        // (there exists a node which has a path goes to itself)
    {
        exists n: Node :: PathExists(g, n, n)
    }

    lemma PathExistsToDigraphLoop2<Node>(g: Digraph, n: Node)
        requires PathExists(g, n, n)
        ensures DigraphLoop2(g)
    {
        reveal DigraphLoop2();
    }

    lemma DigraphLoopEquiv<Node(!new)>(g: Digraph)
        // The two definitions for whether the digraph has a loop
        // are equivalent.
        ensures DigraphLoop(g) == DigraphLoop2(g)
    {
        reveal DigraphLoop();
        reveal DigraphLoop2();
        if DigraphLoop(g) {
            var p :| PathValid(g, p) && PathLoop(p);
            assert PathFromTo(g, p, p.v[0], p.v[0]);
            assert PathExists(g, p.v[0], p.v[0]);
            PathExistsToDigraphLoop2(g, p.v[0]);
            assert DigraphLoop2(g);
        } else {
        }
    }

    ghost function GetLoopPath<Node(!new)>(g: Digraph): (r: Path<Node>)
        // Returns a loop from a digraph that has a loop.
        requires DigraphLoop(g)
        ensures PathValid(g, r)
        ensures PathLoop(r)
    {
        reveal DigraphLoop();
        DigraphLoopEquiv(g);
        assert DigraphLoop2(g);
        reveal DigraphLoop2();
        var n :| PathExists(g, n, n);
        var p :| PathValid(g, p) && |p.v| > 1 && p.v[0] == n && p.v[|p.v|-1] == n;
        p
    }

    predicate PathLoop<Node(==)>(p: Path<Node>)
        // The path starts and stop at the same place.
    {
        |p.v| > 1 && p.v[0] == p.v[|p.v|-1]
    }

    predicate PathNoRepeats<Node(==)>(p: Path<Node>)
        // This path does not contain any repeated nodes.
    {
        forall i: nat, j: nat :: i < |p.v| && j < |p.v| && i != j ==> p.v[i] != p.v[j]
    }

    lemma NoLoopsMeansNoRepeats<Node(!new)>(g: Digraph<Node>)
        requires !DigraphLoop(g)
        ensures !exists p: Path<Node> :: PathValid(g, p) && !PathNoRepeats(p)
    {
        if exists p: Path<Node> :: PathValid(g, p) && !PathNoRepeats(p) {
            var p : Path<Node> :| PathValid(g, p) && !PathNoRepeats(p);
            assert PathValid(g, p);
            var i: nat, j: nat :| (i < |p.v|) && (j < |p.v|) && (j > i) && (p.v[i] == p.v[j]);
            var p_loop := PathSegment(p, i, j+1);
            PathSegmentValid(g, p, i, j+1);
            assert PathValid(g, p_loop);
            assert PathLoop(p_loop);
            reveal DigraphLoop();
            assert DigraphLoop(g);
            assert false;
        }
    }

    lemma NoRepeatsIsHasNoDuplicates<Node>(p: Path<Node>)
        requires PathNoRepeats(p)
        ensures Seq.HasNoDuplicates(p.v)
    {
        reveal Seq.HasNoDuplicates();
    }

    predicate PathSimpleLoop<Node(==)>(p: Path<Node>)
        // A simple loop is a loop which doesn't have any repeats
        // (apart from the start and stop)
    {
        PathLoop(p) && PathNoRepeats(Path(p.v[1..|p.v|]))
    }

    ghost predicate PathExists<Node(!new)>(g: Digraph, a: Node, b: Node)
    {
        exists p: Path<Node> :: PathFromTo(g, p, a, b)
    }

    predicate PathFromTo<Node(==)>(g: Digraph, p: Path<Node>, a: Node, b: Node)
        // The path is valid and goes between these parts.
    {
        PathValid(g, p) && |p.v| > 1 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }

    function PathSegment<Node>(p: Path<Node>, start: nat, stop: nat): (r: Path<Node>)
        // Create a new path by taking a segment of an existing one.
        requires start < |p.v|
        requires stop <= |p.v|
        requires start < stop
        ensures |r.v| > 0
    {
        Path(p.v[start..stop])
    }

    lemma PathSegmentValid<Node>(g: Digraph, p: Path<Node>, start: nat, stop: nat)
        // A segment of a valid path is a valid path.
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

    lemma PathExistsByExample<Node>(g: Digraph, p: Path<Node>, a: Node, b: Node)
        requires PathFromTo(g, p, a, b)
        ensures PathExists(g, a, b)
    {
    }

    function PathFindIndexInternal<Node(==)>(p: Path<Node>, n: Node, index: nat): (r: nat)
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

    function PathFindIndex<Node(==)>(p: Path<Node>, n: Node): (r: nat)
        // Find the position of a node in a path. 
        requires n in p.v
        ensures r < |p.v|
        ensures p.v[r] == n
    {
        PathFindIndexInternal(p, n, 0)
    }

    lemma PathExistsAdd<Node(!new)>(g: Digraph, a: Node, b: Node, c: Node)
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

    function NumberOfRemainingNodes<Node>(g: Digraph, visited_nodes: set<Node>): nat
        // This is useful when we want to show that something that walks the
        // graph will terminate.
        requires DigraphValid(g)
        requires forall n :: n in visited_nodes ==> IsNode(g, n)
    {
        reveal IsNode();
        Set.LemmaSubsetSize(visited_nodes, g.Nodes);
        |g.Nodes| - |visited_nodes|
    }

    function NumberOfRemainingNodesPath<Node(==)>(g: Digraph, p: Path<Node>): nat
        // This is useful when we want to show that something that walks the
        // graph will terminate.
        requires DigraphValid(g)
        requires PathValid(g, p)
        requires PathNoRepeats(p)
    {
        NoRepeatsPathSetSize(p);
        var s := PathSet(p);
        assert forall x :: x in s ==> x in p.v;
        reveal PathValid();
        assert forall x :: x in p.v ==> IsNode(g, x);
        NodeSetSize(g, s);
        |g.Nodes| - |p.v|
    }

    lemma NumberOfRemainingNodesDecreases<Node>(
        g: Digraph, visited_nodes: set<Node>, n: Node, new_visited_nodes: set<Node>)
        requires DigraphValid(g)
        requires forall m :: m in visited_nodes ==> IsNode(g, m)
        requires IsNode(g, n)
        requires n !in visited_nodes
        requires new_visited_nodes == visited_nodes + {n}
        ensures
            NumberOfRemainingNodes(g, new_visited_nodes) <
            NumberOfRemainingNodes(g, visited_nodes)
    {
    }

    lemma NodeSetSize<Node>(g: Digraph, nodes: set<Node>)
        // Lets us set an upper bound on the number of nodes in a graph.
        requires DigraphValid(g)
        requires forall n: Node :: n in nodes ==> IsNode(g, n)
        ensures |nodes| <= |g.Nodes|
    {
        reveal IsNode();
        Set.LemmaSubsetSize(nodes, g.Nodes);
    }

    lemma NoRepeatsPathSetSize<Node>(p: Path<Node>)
        requires PathNoRepeats(p)
        ensures |PathSet(p)| == |p.v|
    {
        NoRepeatsIsHasNoDuplicates(p);
        Seq.LemmaCardinalityOfSetNoDuplicates(p.v);
    }

    function PathSet<Node>(p: Path<Node>): (r: set<Node>)
        ensures forall x :: x in r ==> x in p.v
    {
        reveal Seq.ToSet();
        Seq.ToSet(p.v)
    }

    function PathEnd<Node>(p: Path<Node>): Node
        requires |p.v| > 0
    {
        p.v[|p.v|-1]
    }

    function PathStart<Node>(p: Path<Node>): Node
        requires |p.v| > 0
    {
        p.v[0]
    }

    function AddPaths<Node>(p1: Path<Node>, p2: Path<Node>): (r: Path<Node>)
        requires |p1.v| > 0
        requires |p2.v| > 0
        requires p1.v[|p1.v|-1] == p2.v[0]
    {
        var p2t := if |p2.v| > 1 then p2.v[1..|p2.v|] else [];
        Path(p1.v + p2t)
    }

    lemma AddPathsValid<Node>(g: Digraph, p1: Path<Node>, p2: Path<Node>)
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
        var p := AddPaths(p1, p2);
        assert (forall i: nat :: i < |p.v| ==> IsNode(g, p.v[i]));
        assert (forall i: nat :: i < |p.v|-1 ==> IsConnected(g, p.v[i], p.v[i+1]));
    }

    function PathAppend<Node>(g: Digraph, p: Path<Node>, n: Node): (r: Path<Node>)
        // Add a node onto a path.
        requires IsNode(g, n)
        requires |p.v| > 0 ==> IsConnected(g, p.v[|p.v|-1], n)
        requires PathValid(g, p)
        ensures PathValid(g, r)
    {
        reveal PathValid();
        Path(p.v + [n])
    }

    lemma AddPathsFromTo<Node>(g: Digraph, p1: Path<Node>, p2: Path<Node>)
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

    predicate ShortPathFromTo<Node(==)>(g: Digraph, p: Path<Node>, a: Node, b: Node)
        // A valid path between two ports.  But a path of length 1 is allowed.
    {
        PathValid(g, p) && |p.v| > 0 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }
    
    function PathRemoveLoops<Node(==)>(p: Path<Node>): (r: Path<Node>)
        // Creates a new path by snipping off any loops that
        // exist in the path.
        requires |p.v| > 0
    {
        PathRemoveLoopsInternal(p, |p.v|-1)
    }

    function PathRemoveLoopsInternal<Node(==)>(p: Path<Node>, index: nat): (r: Path<Node>)
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

    lemma RemoveLoopsFromToSame<Node>(g: Digraph, p: Path<Node>)
        // When we remove loops we get a path with the same
        // start and end.  Possibly of length 1 node.
        // It won't have repeats.
        requires |p.v| > 1
        requires p.v[0] != p.v[|p.v|-1]
        requires PathValid(g, p)
        ensures
            var a := p.v[0];
            var b := p.v[|p.v|-1];
            var q := PathRemoveLoops(p);
            ShortPathFromTo(g, q, a, b) &&
            PathNoRepeats(q)
    {
        RemoveLoopsFromToSameInternal(g, p, |p.v|-1);
    }

    lemma RemoveLoopsFromToSameInternal<Node>(g: Digraph, p: Path<Node>, index: nat)
        requires index < |p.v|
        requires |p.v| > 1
        requires p.v[0] != p.v[|p.v|-1]
        requires PathValid(g, p)
        ensures
            var a := p.v[0];
            var b := p.v[index];
            var q := PathRemoveLoopsInternal(p, index);
            ShortPathFromTo(g, q, a, b) &&
            PathNoRepeats(q)
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

}
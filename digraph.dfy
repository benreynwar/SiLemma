module DG {

    import opened Std.Wrappers
    import Utils
    import SeqExt
    import Std.Collections.Seq
    import Std.Collections.Set
    import Std.Functions

    datatype Path<Node> = Path(v: seq<Node>)

    datatype Digraph<!Node> = Digraph(
        IsNode: Node -> bool,
        IsConnected: (Node, Node) -> bool,
        NodeMap: Node -> nat,
        InvNodeMap: nat -> Option<Node>,
        NodeBound: nat
    )

    ghost predicate {:opaque} DigraphValid<Node(!new)>(g: Digraph)
    {
        (forall n: Node :: g.NodeMap(n) >= g.NodeBound ==> !g.IsNode(n)) &&
        (forall n: Node :: !g.IsConnected(n, n)) && // No self-connections
        (forall n: Node, m: Node :: g.IsConnected(n, m) ==> g.IsNode(n) && g.IsNode(m)) &&
        (forall n: Node, m: Node :: n != m ==> g.NodeMap(n) != g.NodeMap(m)) &&
        (forall n: Node :: g.InvNodeMap(g.NodeMap(n)) == Some(n)) &&
        Functions.Injective(g.NodeMap) && Functions.Injective(g.InvNodeMap)
    }

    lemma ValidNodeBound<Node>(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires g.IsNode(n)
        ensures g.NodeMap(n) < g.NodeBound
    {
        reveal DigraphValid();
    }

    predicate NodeValid<Node>(g: Digraph, n: Node)
    {
        g.NodeMap(n) < g.NodeBound
    }
    
    lemma NotNodeNotConnected<Node>(g: Digraph, n: Node)
        // If a node is not in the graph
        // then it's not connected to any nodes
        requires DigraphValid(g)
        requires !g.IsNode(n)
        ensures
            (forall m: Node :: !g.IsConnected(m, n)) &&
            (forall m: Node :: !g.IsConnected(n, m))
    {
        reveal DigraphValid();
    }

    predicate {:opaque} PathValid<Node>(g: Digraph, p: Path<Node>)
    {
        (forall i: nat :: i < |p.v| ==> g.IsNode(p.v[i])) &&
        (forall i: nat :: i < |p.v|-1 ==> g.IsConnected(p.v[i], p.v[i+1]))
    }

    predicate {:opaque} PathExcludes<Node>(p: Path<Node>, exclusion: set<Node>)
    {
        forall i: nat :: i < |p.v| ==> p.v[i] !in exclusion
    }

    lemma NodeInExclusionNotInPath<Node>(p: Path<Node>, exclusion: set<Node>, n: Node)
        requires PathExcludes(p, exclusion)
        requires n in exclusion
        ensures n !in p.v
    {
        reveal PathExcludes();
    }

    predicate NextNode<Node>(g: Digraph, n: Node, m: Node)
        requires DigraphValid(g)
        requires g.IsNode(n)
    {
        g.IsNode(m) && g.IsConnected(n, m)
    }

    function PathAppend<Node>(g: Digraph, p: Path<Node>, n: Node): (r: Path<Node>)
        // Add a node onto a path.
        requires g.IsNode(n)
        requires |p.v| > 0 ==> g.IsConnected(p.v[|p.v|-1], n)
        requires PathValid(g, p)
        ensures PathValid(g, r)
    {
        reveal PathValid();
        Path(p.v + [n])
    }

    function PathPrepend<Node>(g: Digraph, p: Path<Node>, n: Node): (r: Path<Node>)
        // Add a node onto a path.
        requires g.IsNode(n)
        requires |p.v| > 0
        requires g.IsConnected(n, p.v[0])
        requires PathValid(g, p)
        ensures PathValid(g, r)
    {
        reveal PathValid();
        Path([n] + p.v)
    }

    lemma PathPrependNoRepeats<Node>(g: Digraph, p: Path<Node>, n: Node)
        requires g.IsNode(n)
        requires |p.v| > 0
        requires g.IsConnected(n, p.v[0])
        requires PathValid(g, p)
        requires PathNoRepeats(p)
        requires n !in p.v
        ensures
            var r := PathPrepend(g, p, n);
            PathNoRepeats(r)
    {
    }

    lemma PathPrependExcludes<Node>(
            g: Digraph, p: Path<Node>, n: Node, exclusion: set<Node>)
        requires g.IsNode(n)
        requires |p.v| > 0
        requires g.IsConnected(n, p.v[0])
        requires PathValid(g, p)
        requires PathExcludes(p, exclusion)
        requires n !in exclusion
        ensures
            var r := PathPrepend(g, p, n);
            PathExcludes(r, exclusion)
    {
        reveal PathExcludes();
    }

    lemma PathAppendOneBigger<Node>(g: Digraph, p: Path<Node>, n: Node)
        // If we add a node to a path that wasn't already in it
        // then that path contains one more node.
        requires g.IsNode(n)
        requires |p.v| > 0
        requires g.IsConnected(PathEnd(p), n)
        requires PathValid(g, p)
        requires n !in p.v
        ensures
            var q := PathAppend(g, p, n);
            |PathSet(p)| + 1 == |PathSet(q)|
    {
        reveal Seq.ToSet();
        var q := PathAppend(g, p, n);
        assert q.v == p.v + [n];
        SeqExt.LemmaToSetAdds(p.v, [n]);
        assert Seq.ToSet(p.v) + Seq.ToSet([n]) == Seq.ToSet(q.v);
        assert PathSet(p) + {n} == PathSet(q);
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

    function PathStart<Node>(p: Path<Node>): Node
        requires |p.v| > 0
    {
        p.v[0]
    }

    function PathEnd<Node>(p: Path<Node>): Node
        requires |p.v| > 0
    {
        p.v[|p.v|-1]
    }

    function RemovePathEnd<Node>(p: Path<Node>): Path<Node>
        requires |p.v| > 0
    {
        Path(p.v[..|p.v|-1])
    }

    lemma IfNoRepeatsEndNotinRemovePathEnd<Node>(p: Path<Node>)
        requires PathNoRepeats(p)
        requires |p.v| > 0
        ensures PathEnd(p) !in RemovePathEnd(p).v
    {
    }

    function PathRemoveLoops<Node(==)>(p: Path<Node>): (r: Path<Node>)
        // Creates a new path by snipping off any loops that
        // exist in the path.
        requires |p.v| > 0
    {
        PathRemoveLoopsInternal(p, |p.v|-1)
    }

    function PathFindIndex<Node(==)>(p: Path<Node>, n: Node): (r: nat)
        // Find the position of a node in a path. 
        requires n in p.v
        ensures r < |p.v|
        ensures p.v[r] == n
    {
        PathFindIndexInternal(p, n, 0)
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

    lemma RemoveLoopsNoRepeats<Node>(p: Path<Node>)
        requires |p.v| > 1
        ensures
            var q := PathRemoveLoopsInternal(p, |p.v|-1);
            PathNoRepeats(q)
    {
        RemoveLoopsNoRepeatsInternal(p, |p.v|-1);
    }

    lemma RemoveLoopsNoRepeatsInternal<Node>(p: Path<Node>, index: nat)
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

    ghost predicate PathExists<Node(!new)>(g: Digraph, a: Node, b: Node)
    {
        exists p: Path<Node> :: PathFromTo(g, p, a, b)
    }

    ghost predicate SimplePathExists<Node(!new)>(g: Digraph, a: Node, b: Node)
    {
        exists p: Path<Node> :: SimplePathFromTo(g, p, a, b)
    }

    ghost predicate SimpleShortExcludedPathExists<Node(!new)>(
        g: Digraph, a: Node, b: Node, exclusion: set<Node>)
    {
        exists p: Path<Node> :: SimpleShortExcludedPathFromTo(g, p, a, b, exclusion)
    }

    lemma SimpleShortExcludedPathExistsByExample<Node>(
        g: Digraph, p: Path<Node>, a: Node, b: Node, exclusion: set<Node>)
        requires SimpleShortExcludedPathFromTo(g, p, a, b, exclusion)
        ensures SimpleShortExcludedPathExists(g, a, b, exclusion)
    {
    }

    lemma PathExistsByExample<Node>(g: Digraph, p: Path<Node>, a: Node, b: Node)
        requires PathFromTo(g, p, a, b)
        ensures PathExists(g, a, b)
    {
    }

    lemma NodeSetSize<Node>(g: Digraph, nodes: set<Node>)
        // Lets us set an upper bound on the number of nodes in a graph.
        requires DigraphValid(g)
        requires forall n: Node :: n in nodes ==> g.IsNode(n)
        ensures |nodes| <= g.NodeBound
    {
        reveal DigraphValid();
        assert forall n: Node :: n in nodes ==> g.NodeMap(n) < g.NodeBound;
        var f := (n: Node) => g.NodeMap(n);
        var nodes_as_nats := set n | n in nodes :: f(n);
        Utils.MappedSetSize(nodes, f, nodes_as_nats);
        assert |nodes_as_nats| == |nodes|;
        Utils.BoundedSetSize(g.NodeBound as nat, nodes_as_nats);
    }

    lemma MaxPathLength<Node>(g: Digraph, p: Path<Node>)
        requires PathNoRepeats(p)
    {
    }

    function NumberOfRemainingNodes<Node>(g: Digraph, visited_nodes: set<Node>): nat
        // This is useful when we want to show that something that walks the
        // graph will terminate.
        requires DigraphValid(g)
        requires forall n :: n in visited_nodes ==> g.IsNode(n)
    {
        NodeSetSize(g, visited_nodes);
        g.NodeBound - |visited_nodes|
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
        assert forall x :: x in p.v ==> g.IsNode(x);
        NodeSetSize(g, s);
        assert |p.v| <= g.NodeBound;
        g.NodeBound - |p.v|
    }

    lemma NumberOfRemainingNodesDecreases<Node>(
        g: Digraph, visited_nodes: set<Node>, n: Node, new_visited_nodes: set<Node>)
        requires DigraphValid(g)
        requires forall m :: m in visited_nodes ==> g.IsNode(m)
        requires g.IsNode(n)
        requires n !in visited_nodes
        requires new_visited_nodes == visited_nodes + {n}
        ensures
            NumberOfRemainingNodes(g, new_visited_nodes) <
            NumberOfRemainingNodes(g, visited_nodes)
    {
    }

    function OneNodePath<Node>(g: Digraph, n: Node): (r: Path<Node>)
        requires DigraphValid(g)
        requires g.IsNode(n)
        ensures PathValid(g, r)
    {
        reveal PathValid();
        Path([n])
    }

    lemma NumberOfRemainingNodesDecreasesPath<Node>(g: Digraph, p: Path<Node>, n: Node)
        requires DigraphValid(g)
        requires PathValid(g, p)
        requires PathNoRepeats(p)
        requires NodeValid(g, n)
        requires g.IsNode(n)
        requires |p.v| > 0 ==> g.IsConnected(PathEnd(p), n)
        requires n !in p.v
        ensures
            var new_p := PathAppend(g, p, n);
            NumberOfRemainingNodesPath(g, new_p) <
            NumberOfRemainingNodesPath(g, p)
    {
    }

    function PathSet<Node>(p: Path<Node>): (r: set<Node>)
        ensures forall x :: x in r ==> x in p.v
    {
        reveal Seq.ToSet();
        Seq.ToSet(p.v)
    }

    lemma NoRepeatsPathSetSize<Node>(p: Path<Node>)
        requires PathNoRepeats(p)
        ensures |PathSet(p)| == |p.v|
    {
        NoRepeatsIsHasNoDuplicates(p);
        Seq.LemmaCardinalityOfSetNoDuplicates(p.v);
    }

    lemma PathSetValid<Node>(g: Digraph, p: Path<Node>)
        // If a path is valid, the nodes in it are valid.
        requires DigraphValid(g)
        requires PathValid(g, p)
        ensures
            var r := PathSet(p);
            (forall n: Node :: n in r ==> NodeValid(g, n)) &&
            (forall n: Node :: n in r ==> g.IsNode(n))
    {
        reveal Seq.ToSet();
        reveal PathValid();
        reveal DigraphValid();
    }

    function PathSetV<Node>(g: Digraph, p: Path<Node>): (r: set<Node>)
        // A helper that combines the PathSet function and PathSetValid lemma.
        // (I'm not sure if this is a sensible way of doing things, but it
        //  feels like it helps us choose how many constraints we're instroducing).
        requires DigraphValid(g)
        requires PathValid(g, p)
        ensures forall n: Node :: n in r ==> NodeValid(g, n)
        ensures forall n: Node :: n in r ==> g.IsNode(n)
    {
        PathSetValid(g, p);
        PathSet(p)
    }

    ghost predicate PathExistsR<Node(!new)>(g: Digraph, a: Node, b: Node)
        // A Path Exists from a to b.
        // A non-ghost version of SimplePathExists.
        requires DigraphValid(g)
        requires g.IsNode(a)
        requires g.IsNode(b)
    {
        !PathDoesNotExistRecursiveInternal(g, a, b, {})
    }

    ghost predicate PathDoesNotExistRecursiveInternal<Node(!new)>(
            g: Digraph, a: Node, b: Node, visited_nodes: set<Node>)
        requires DigraphValid(g)
        requires a !in visited_nodes
        requires b !in visited_nodes
        requires forall n :: n in visited_nodes ==> g.IsNode(n)
        requires g.IsNode(a)
        requires g.IsNode(b)
        decreases NumberOfRemainingNodes(g, visited_nodes)
    {
        var new_visited_nodes := visited_nodes + {a};
        assert |new_visited_nodes| == |visited_nodes| + 1;
        if (a == b) then
            false
        else
            forall n: Node :: (NextNode(g, a, n) && g.NodeMap(n) < g.NodeBound &&
                n !in new_visited_nodes) ==>
                    PathDoesNotExistRecursiveInternal(g, n, b, new_visited_nodes)
    }

    lemma {:vcs_split_on_every_assert} NotPathExistsIsPathDoesNotExistRecursive<Node(!new)>(
            g: Digraph, b: Node, p: Path<Node>)
        requires DigraphValid(g)
        requires |p.v| > 0
        requires b !in PathSet(RemovePathEnd(p))
        requires PathValid(g, p)
        requires PathNoRepeats(p)
        requires g.IsNode(b)
        decreases
            reveal Seq.ToSet();
            reveal PathValid();
            NumberOfRemainingNodes(g, PathSet(p))
        ensures
            var visited_nodes := PathSet(RemovePathEnd(p));
            var end := PathEnd(p);
            reveal Seq.ToSet();
            !SimpleShortExcludedPathExists(g, end, b, visited_nodes) ==
                PathDoesNotExistRecursiveInternal(g, PathEnd(p), b, visited_nodes)
    {
        var visited_nodes := PathSet(RemovePathEnd(p));
        var new_visited_nodes := PathSet(p);
        var end := PathEnd(p);
        reveal PathValid();
        assert g.IsNode(end);
        reveal Seq.ToSet();
        assert new_visited_nodes == visited_nodes + {end};
        assert |new_visited_nodes| == |visited_nodes| + 1;
        assert |PathSet(p)| > |PathSet(RemovePathEnd(p))|;
        assert end !in visited_nodes;
        if (end == b) {
            reveal PathValid();
            assert !PathDoesNotExistRecursiveInternal(
                g, end, b, visited_nodes);
            var esp := Path([end]);
            reveal PathExcludes();
            SimpleShortExcludedPathExistsByExample(
                g, esp, end, b, visited_nodes);
            assert SimpleShortExcludedPathExists(g, end, b, visited_nodes);
            assert !SimpleShortExcludedPathExists(g, end, b, visited_nodes) ==
                PathDoesNotExistRecursiveInternal(g, PathEnd(p), b, visited_nodes);
        } else {
            // Show that if of the children has a path
            // then this has a path.
            // Show that otherwise then this does not have a path.
            if exists n: Node :: NextNode(g, end, n) && g.NodeMap(n) < g.NodeBound &&
                    n !in new_visited_nodes &&
                    SimpleShortExcludedPathExists(g, n, b, new_visited_nodes) {
                var n: Node :| NextNode(g, end, n) && g.NodeMap(n) < g.NodeBound &&
                    n !in new_visited_nodes &&
                    SimpleShortExcludedPathExists(g, n, b, new_visited_nodes);
                assert SimpleShortExcludedPathExists(g, n, b, new_visited_nodes);  
                var shorter: Path<Node> :| SimpleShortExcludedPathFromTo(
                    g, shorter, n, b, new_visited_nodes);
                reveal PathExcludes();
                PathPrependNoRepeats(g, shorter, end);
                PathPrependExcludes(g, shorter, end, visited_nodes);
                var longer: Path<Node> := PathPrepend(g, shorter, end);
                SimpleShortExcludedPathExistsByExample(
                    g, longer, end, b, visited_nodes);
                assert SimpleShortExcludedPathExists(g, end, b, visited_nodes);
                var new_path := PathAppend(g, p, n);
                NumberOfRemainingNodesDecreases(g, PathSet(p), n, PathSet(new_path));
                NotPathExistsIsPathDoesNotExistRecursive(g, b, new_path);
                assert !PathDoesNotExistRecursiveInternal(
                    g, PathEnd(new_path), b, new_visited_nodes);
                assert !PathDoesNotExistRecursiveInternal(g, PathEnd(p), b, visited_nodes);
            } else {
                if SimpleShortExcludedPathExists(g, end, b, visited_nodes) {
                    var sse: Path<Node> :| SimpleShortExcludedPathFromTo(
                        g, sse, end, b, visited_nodes);
                    var n := sse.v[1];
                    assert NextNode(g, end, n);
                    reveal PathValid();
                    ValidNodeBound(g, n);
                    assert g.NodeMap(n) < g.NodeBound;
                    reveal PathExcludes();
                    assert n !in new_visited_nodes;
                    var shorter := Path(sse.v[1..]);
                    SimpleShortExcludedPathExistsByExample(
                        g, shorter, n, b, new_visited_nodes);
                    assert SimpleShortExcludedPathExists(g, n, b, new_visited_nodes);
                    // This constradicts that such as 'n' does not exist.
                    assert false;
                }
                forall n: Node | NextNode(g, end, n) && g.NodeMap(n) < g.NodeBound &&
                        n !in new_visited_nodes
                    ensures
                        var new_path := PathAppend(g, p, n);
                        PathDoesNotExistRecursiveInternal(g, n, b, new_visited_nodes)
                {
                    assert !SimpleShortExcludedPathExists(g, n, b, new_visited_nodes);
                    var new_path := PathAppend(g, p, n);
                    NumberOfRemainingNodesDecreases(g, PathSet(p), n, PathSet(new_path));
                    NotPathExistsIsPathDoesNotExistRecursive(g, b, new_path);
                    assert PathDoesNotExistRecursiveInternal(g, n, b, new_visited_nodes);
                }
                assert !SimpleShortExcludedPathExists(g, end, b, visited_nodes);
                assert PathDoesNotExistRecursiveInternal(g, end, b, visited_nodes);
            }
        }
    }

    predicate PathFromTo<Node(==)>(g: Digraph, p: Path<Node>, a: Node, b: Node)
        // The path is valid and goes between these parts.
    {
        PathValid(g, p) && |p.v| > 1 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }

    predicate SimplePathFromTo<Node(==)>(g: Digraph, p: Path<Node>, a: Node, b: Node)
        // That path is valid and has no repeats (except possibly the end points).
    {
        PathValid(g, p) && |p.v| > 1 && (p.v[0] == a) && (p.v[|p.v|-1] == b) &&
        PathNoRepeats(Path(p.v[0..|p.v|-2]))
    }

    predicate SimpleShortExcludedPathFromTo<Node>(
        g: Digraph, p: Path<Node>, a: Node, b: Node, exclusion: set<Node>)
        // That path is valid and has no repeats
        // and doesn't go through any nodes in exclusion
    {
        PathValid(g, p) && |p.v| > 0 && (p.v[0] == a) && (p.v[|p.v|-1] == b) &&
        PathNoRepeats(p) &&
        PathExcludes(p, exclusion)
    }

    predicate ShortPathFromTo<Node(==)>(g: Digraph, p: Path<Node>, a: Node, b: Node)
        // A valid path between two ports.  But a path of length 1 is allowed.
    {
        PathValid(g, p) && |p.v| > 0 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }

    ghost predicate {:opaque} DigraphLoop<Node(!new)>(g: Digraph)
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

    function AddNode<Node(==)>(g: Digraph, n: Node): (r: Digraph)
        requires !g.IsNode(n)
    {
        Digraph(
            m=>(m==n) || g.IsNode(m),
            g.IsConnected,
            g.NodeMap,
            g.InvNodeMap,
            if g.NodeMap(n) >= g.NodeBound then g.NodeMap(n)+1 else g.NodeBound
        )
    }

    lemma AddNodeDigraphValid<Node>(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires !g.IsNode(n)
        ensures
            var r := AddNode(g, n);
            DigraphValid(r)
    {
        reveal DigraphValid();
    }

    function AddNodeV<Node(==)>(g: Digraph, n: Node): (r: Digraph)
        requires DigraphValid(g)
        requires !g.IsNode(n)
        ensures
            DigraphValid(r)
    {
        AddNodeDigraphValid(g, n);
        AddNode(g, n)
    }

    lemma AddNodePathValidHelper<Node>(r: Digraph, n: Node, x: Node)
        requires (forall m: Node :: !r.IsConnected(n, m))
        requires (forall m: Node :: !r.IsConnected(m, n))
        ensures !r.IsConnected(n, x)
        ensures !r.IsConnected(x, n)
    {
    }
    
    // There is only one path that becomes valid when we add a node.
    // It is the path containing just that node.
    lemma AddNodePathValid<Node>(g: Digraph, n: Node, p: Path<Node>)
        requires DigraphValid(g)
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
        assert forall m: Node :: !g.IsConnected(n, m);
        assert forall m: Node :: !r.IsConnected(m, n);
        assert forall m: Node :: !r.IsConnected(n, m);
        if n in p.v {
            assert !PathValid(g, p);
            if |p.v| == 1 {
                assert PathValid(r, p);
            } else {
                if p.v[0] == n {
                    AddNodePathValidHelper(r, n, p.v[1]);
                    assert !r.IsConnected(p.v[0], p.v[1]);
                    assert !PathValid(r, p);
                } else {
                    var index := PathFindIndex(p, n);
                    AddNodePathValidHelper(r, n, p.v[index-1]);
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
    lemma AddNodeLoopConserved<Node(!new)>(g: Digraph, n: Node)
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
    

    lemma NotNodePathInvalid<Node>(g: Digraph, n: Node, p: Path<Node>)
        requires !g.IsNode(n)
        requires n in p.v
        ensures !PathValid(g, p)
    {
        reveal PathValid();
    }

    // Connecting two nodes

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

    lemma IsNodeImpliesNodeValid<Node>(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires g.IsNode(n)
        ensures NodeValid(g, n)
    {
        reveal DigraphValid();
    }

    function AllNodes<Node(!new)>(g: Digraph): (r: set<Node>)
        requires DigraphValid(g)
        ensures forall n: Node :: g.IsNode(n) ==> n in r
        ensures forall n: Node :: n in r ==> g.IsNode(n)
        ensures forall n: Node :: n in r ==> NodeValid(g, n)
    {
        reveal DigraphValid();
        var mapped := set m: nat | m < g.NodeBound :: m;
        var nodes := Set.Map(g.InvNodeMap, mapped);
        var filter := (n: Option<Node>) => n.Some? && g.IsNode(n.value);
        var filtered_nodes := Set.Filter(filter, nodes);
        assert forall n :: n in filtered_nodes ==> filter(n);
        var extracted_nodes := set n | n in filtered_nodes :: n.value;
        extracted_nodes
    }

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


}
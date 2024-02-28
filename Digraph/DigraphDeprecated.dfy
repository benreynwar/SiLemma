module DigraphDeprecated {

    import opened Std.Wrappers
    import Utils
    import SeqExt
    import Std.Collections.Seq
    import Std.Collections.Set
    import Std.Functions

    import opened DigraphBase
    import opened DigraphPaths

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


    lemma MaxPathLength<Node>(g: Digraph, p: Path<Node>)
        requires PathNoRepeats(p)
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

    lemma NotNodePathInvalid<Node>(g: Digraph, n: Node, p: Path<Node>)
        requires !g.IsNode(n)
        requires n in p.v
        ensures !PathValid(g, p)
    {
        reveal PathValid();
    }


    lemma IsNodeImpliesNodeValid<Node>(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires g.IsNode(n)
        ensures NodeValid(g, n)
    {
        reveal DigraphValid();
    }


}
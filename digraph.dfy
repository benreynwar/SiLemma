include "utils.dfy"
include "SeqExt.dfy"
include "../libraries/src/Collections/Sequences/Seq.dfy"

module DG {

    import Utils
    import SeqExt
    import Seq

    newtype Node = nat

    datatype Path = Path(v: seq<Node>)

    datatype Digraph = Digraph(
        IsNode: Node -> bool,
        IsConnected: (Node, Node) -> bool,
        // This is larger or equal to all nodes for which IsNode(node) is true.
        // We use this help dafny prove that things are finite and terminate.
        NodeBound: Node
    )

    predicate NodeValid(g: Digraph, n: Node)
    {
        n < g.NodeBound
    }

    function NodeValidSetSize(g: Digraph): nat
    {
        g.NodeBound as nat
    }

    function EmptyDigraph(): (r: Digraph)
        ensures DigraphValid(r)
    {
        reveal DigraphValid();
        Digraph(
            _ => false,
            (_, _) => false,
            0
        )
    }

    ghost predicate {:opaque} DigraphValid(g: Digraph)
    {
        (forall n: Node :: n >= g.NodeBound ==> !g.IsNode(n)) &&
        (forall n: Node :: !g.IsConnected(n, n)) && // No self-connections
        (forall n: Node, m: Node :: g.IsConnected(n, m) ==> g.IsNode(n) && g.IsNode(m))
    }

    lemma ValidNodeBound(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires g.IsNode(n)
        ensures n < g.NodeBound
    {
        reveal DigraphValid();
    }

    
    lemma NotNodeNotConnected(g: Digraph, n: Node)
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

    predicate {:opaque} PathValid(g: Digraph, p: Path)
    {
        (forall i: nat :: i < |p.v| ==> g.IsNode(p.v[i])) &&
        (forall i: nat :: i < |p.v|-1 ==> g.IsConnected(p.v[i], p.v[i+1]))
    }

    predicate {:opaque} PathExcludes(p: Path, exclusion: set<Node>)
    {
        forall i: nat :: i < |p.v| ==> p.v[i] !in exclusion
    }

    lemma NodeInExclusionNotInPath(p: Path, exclusion: set<Node>, n: Node)
        requires PathExcludes(p, exclusion)
        requires n in exclusion
        ensures n !in p.v
    {
        reveal PathExcludes();
    }

    predicate NextNode(g: Digraph, n: Node, m: Node)
        requires DigraphValid(g)
        requires g.IsNode(n)
    {
        g.IsNode(m) && g.IsConnected(n, m)
    }

    function PathAppend(g: Digraph, p: Path, n: Node): (r: Path)
        // Add a node onto a path.
        requires g.IsNode(n)
        requires |p.v| > 0
        requires g.IsConnected(p.v[|p.v|-1], n)
        requires PathValid(g, p)
        ensures PathValid(g, r)
    {
        reveal PathValid();
        Path(p.v + [n])
    }

    function PathPrepend(g: Digraph, p: Path, n: Node): (r: Path)
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

    lemma PathPrependNoRepeats(g: Digraph, p: Path, n: Node)
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

    lemma PathPrependExcludes(
            g: Digraph, p: Path, n: Node, exclusion: set<Node>)
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

    lemma PathAppendOneBigger(g: Digraph, p: Path, n: Node)
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

    predicate PathLoop(p: Path)
        // The path starts and stop at the same place.
    {
        |p.v| > 1 && p.v[0] == p.v[|p.v|-1]
    }

    predicate PathNoRepeats(p: Path)
        // This path does not contain any repeated nodes.
    {
        forall i: nat, j: nat :: i < |p.v| && j < |p.v| && i != j ==> p.v[i] != p.v[j]
    }

    predicate PathSimpleLoop(p: Path)
        // A simple loop is a loop which doesn't have any repeats
        // (apart from the start and stop)
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

    function RemovePathEnd(p: Path): Path
        requires |p.v| > 0
    {
        Path(p.v[..|p.v|-1])
    }

    lemma IfNoRepeatsEndNotinRemovePathEnd(p: Path)
        requires PathNoRepeats(p)
        requires |p.v| > 0
        ensures PathEnd(p) !in RemovePathEnd(p).v
    {
    }

    function PathRemoveLoops(p: Path): (r: Path)
        // Creates a new path by snipping off any loops that
        // exist in the path.
        requires |p.v| > 0
    {
        PathRemoveLoopsInternal(p, |p.v|-1)
    }

    function PathFindIndex(p: Path, n: Node): (r: nat)
        // Find the position of a node in a path. 
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
        // Create a new path by taking a segment of an existing one.
        requires start < |p.v|
        requires stop <= |p.v|
        requires start < stop
        ensures |r.v| > 0
    {
        Path(p.v[start..stop])
    }

    lemma PathSegmentValid(g: Digraph, p: Path, start: nat, stop: nat)
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

    lemma RemoveLoopsFromToSameInternal(g: Digraph, p: Path, index: nat)
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

    lemma RemoveLoopsNoRepeats(p: Path)
        requires |p.v| > 1
        ensures
            var q := PathRemoveLoopsInternal(p, |p.v|-1);
            PathNoRepeats(q)
    {
        RemoveLoopsNoRepeatsInternal(p, |p.v|-1);
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

    ghost predicate SimplePathExists(g: Digraph, a: Node, b: Node)
    {
        exists p: Path :: SimplePathFromTo(g, p, a, b)
    }

    ghost predicate SimpleShortExcludedPathExists(
        g: Digraph, a: Node, b: Node, exclusion: set<Node>)
    {
        exists p: Path :: SimpleShortExcludedPathFromTo(g, p, a, b, exclusion)
    }

    lemma SimpleShortExcludedPathExistsByExample(
        g: Digraph, p: Path, a: Node, b: Node, exclusion: set<Node>)
        requires SimpleShortExcludedPathFromTo(g, p, a, b, exclusion)
        ensures SimpleShortExcludedPathExists(g, a, b, exclusion)
    {
    }

    lemma PathExistsByExample(g: Digraph, p: Path, a: Node, b: Node)
        requires PathFromTo(g, p, a, b)
        ensures PathExists(g, a, b)
    {
    }

    lemma NodeSetSize(g: Digraph, nodes: set<Node>)
        // Lets us set an upper bound on the number of nodes in a graph.
        requires DigraphValid(g)
        requires forall n: Node :: n in nodes ==> g.IsNode(n)
        ensures |nodes| <= NodeValidSetSize(g)
    {
        reveal DigraphValid();
        assert forall n: Node :: n in nodes ==> n < g.NodeBound;
        var f := (n: Node) => n as nat;
        var nodes_as_nats := set n | n in nodes :: f(n);
        Utils.MappedSetSize(nodes, f, nodes_as_nats);
        assert |nodes_as_nats| == |nodes|;
        Utils.BoundedSetSize(g.NodeBound as nat, nodes_as_nats);
    }

    function NumberOfRemainingNodes(g: Digraph, visited_nodes: set<Node>): nat
        // This is useful when we want to show that something that walks the
        // graph will terminate.
        requires DigraphValid(g)
        requires forall n :: n in visited_nodes ==> g.IsNode(n)
    {
        NodeSetSize(g, visited_nodes);
        NodeValidSetSize(g) - |visited_nodes|
    }

    lemma NumberOfRemainingNodesDecreases(
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

    function PathSet(p: Path): (r: set<Node>)
    {
        Seq.ToSet(p.v)
    }

    lemma PathSetValid(g: Digraph, p: Path)
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

    function PathSetV(g: Digraph, p: Path): (r: set<Node>)
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

    predicate PathExistsR(g: Digraph, a: Node, b: Node)
        // A Path Exists from a to b.
        // A non-ghost version of SimplePathExists.
        requires DigraphValid(g)
        requires g.IsNode(a)
        requires g.IsNode(b)
    {
        !PathDoesNotExistRecursiveInternal(g, a, b, {})
    }

    predicate PathDoesNotExistRecursiveInternal(
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
            forall n: Node :: NextNode(g, a, n) && n < g.NodeBound &&
                    n !in new_visited_nodes ==>
                PathDoesNotExistRecursiveInternal(g, n, b, new_visited_nodes)
    }

    lemma {:vcs_split_on_every_assert} NotPathExistsIsPathDoesNotExistRecursive(
            g: Digraph, b: Node, p: Path)
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
            if exists n: Node :: NextNode(g, end, n) && n < g.NodeBound &&
                    n !in new_visited_nodes &&
                    SimpleShortExcludedPathExists(g, n, b, new_visited_nodes) {
                var n: Node :| NextNode(g, end, n) && n < g.NodeBound &&
                    n !in new_visited_nodes &&
                    SimpleShortExcludedPathExists(g, n, b, new_visited_nodes);
                assert SimpleShortExcludedPathExists(g, n, b, new_visited_nodes);  
                var shorter: Path :| SimpleShortExcludedPathFromTo(
                    g, shorter, n, b, new_visited_nodes);
                reveal PathExcludes();
                PathPrependNoRepeats(g, shorter, end);
                PathPrependExcludes(g, shorter, end, visited_nodes);
                var longer: Path := PathPrepend(g, shorter, end);
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
                    var sse: Path :| SimpleShortExcludedPathFromTo(
                        g, sse, end, b, visited_nodes);
                    var n := sse.v[1];
                    assert NextNode(g, end, n);
                    reveal PathValid();
                    ValidNodeBound(g, n);
                    assert n < g.NodeBound;
                    reveal PathExcludes();
                    assert n !in new_visited_nodes;
                    var shorter := Path(sse.v[1..]);
                    SimpleShortExcludedPathExistsByExample(
                        g, shorter, n, b, new_visited_nodes);
                    assert SimpleShortExcludedPathExists(g, n, b, new_visited_nodes);
                    // This constradicts that such as 'n' does not exist.
                    assert false;
                }
                forall n: Node | NextNode(g, end, n) && n < g.NodeBound &&
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

    predicate PathFromTo(g: Digraph, p: Path, a: Node, b: Node)
        // The path is valid and goes between these parts.
    {
        PathValid(g, p) && |p.v| > 1 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }

    predicate SimplePathFromTo(g: Digraph, p: Path, a: Node, b: Node)
        // That path is valid and has no repeats (except possibly the end points).
    {
        PathValid(g, p) && |p.v| > 1 && (p.v[0] == a) && (p.v[|p.v|-1] == b) &&
        PathNoRepeats(Path(p.v[0..|p.v|-2]))
    }

    predicate SimpleShortExcludedPathFromTo(
        g: Digraph, p: Path, a: Node, b: Node, exclusion: set<Node>)
        // That path is valid and has no repeats
        // and doesn't go through any nodes in exclusion
    {
        PathValid(g, p) && |p.v| > 0 && (p.v[0] == a) && (p.v[|p.v|-1] == b) &&
        PathNoRepeats(p) &&
        PathExcludes(p, exclusion)
    }

    predicate ShortPathFromTo(g: Digraph, p: Path, a: Node, b: Node)
        // A valid path between two ports.  But a path of length 1 is allowed.
    {
        PathValid(g, p) && |p.v| > 0 && (p.v[0] == a) && (p.v[|p.v|-1] == b)
    }

    ghost predicate {:opaque} DigraphLoop(g: Digraph)
        // There's a loop in the digraph.
        // (there exists a path that is a loop).
    {
        exists p: Path :: PathValid(g, p) && PathLoop(p)
    }

    ghost predicate {:opaque} DigraphLoop2(g: Digraph)
        // There's a loop in the digraph.
        // (there exists a node which has a path goes to itself)
    {
        exists n: Node :: PathExists(g, n, n)
    }

    lemma PathExistsToDigraphLoop2(g: Digraph, n: Node)
        requires PathExists(g, n, n);
        ensures DigraphLoop2(g);
    {
        reveal DigraphLoop2();
    }

    lemma DigraphLoopEquiv(g: Digraph)
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

    ghost function GetLoopPath(g: Digraph): (r: Path)
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

    function AddNode(g: Digraph, n: Node): (r: Digraph)
        requires !g.IsNode(n)
    {
        Digraph(
            m=>(m==n) || g.IsNode(m),
            g.IsConnected,
            if n >= g.NodeBound then n+1 else g.NodeBound
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

    function AddNodeV(g: Digraph, n: Node): (r: Digraph)
        requires DigraphValid(g)
        requires !g.IsNode(n)
        ensures
            DigraphValid(r)
    {
        AddNodeDigraphValid(g, n);
        AddNode(g, n)
    }

    lemma AddNodePathValidHelper(r: Digraph, n: Node, x: Node)
        requires (forall m: Node :: !r.IsConnected(n, m))
        requires (forall m: Node :: !r.IsConnected(m, n))
        ensures !r.IsConnected(n, x);
        ensures !r.IsConnected(x, n);
    {
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

    function ConnectNodesV(g: Digraph, n: Node, m: Node): (r: Digraph)
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

    lemma ConnectNodesPathStillValid(g: Digraph, n: Node, m: Node, p: Path)
        requires g.IsNode(n) && g.IsNode(m) && n != m && !g.IsConnected(n, m)
        requires PathValid(g, p)
        ensures
            var r := ConnectNodes(g, n, m);
            PathValid(r, p)
    {
        reveal PathValid(); 
    }

    lemma ConnectNodesPathStillExists(
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
        PathExistsByExample(r, p, n, m);
        assert PathExists(r, n, m);
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
        ensures
            var r := ConnectNodes(g, n, m);
            DigraphLoop(r) == DigraphLoop(g) || PathExists(g, m, n)
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
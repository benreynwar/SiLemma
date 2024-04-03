module DigraphCombine {

    export Body
        provides DBS
        provides DPS
        provides Combine
        reveals DigraphsCompatible
        provides CombineValid
        provides CombineNoLoops

    import DBS = DigraphBase`Spec
    import DPS = DigraphPaths`Spec
    import opened DigraphBase`Body
    import opened DigraphPaths`Body

    ghost predicate {:opaque} DigraphsCompatible<Node(!new)>(g1: Digraph, g2: Digraph)
    {
        forall n: Node :: !(IsNode(g1, n) && IsNode(g2, n))
    }

    function {:opaque} Combine<Node(!new)>(g1: Digraph, g2: Digraph): (r: Digraph)
        requires DigraphValid(g1)
        requires DigraphValid(g2)
        requires DigraphsCompatible(g1, g2)
        ensures forall n :: IsNode(r, n) == IsNode(g1, n) || IsNode(g2, n)
        ensures forall n: (Node, Node) :: IsConnected(r, n.0, n.1) == IsConnected(g1, n.0, n.1) || IsConnected(g2, n.0, n.1)
    {
        reveal IsNode();
        reveal IsConnected();
        var r := Digraph(
            g1.Nodes + g2.Nodes,
            g1.Connections + g2.Connections
        );
        assert forall n: (Node, Node) :: IsConnected(r, n.0, n.1) == IsConnected(g1, n.0, n.1) || IsConnected(g2, n.0, n.1);
        r
    }

    lemma CombineInputsAreSubgraphs<Node(!new)>(g1: Digraph, g2: Digraph)
        requires DigraphValid(g1)
        requires DigraphValid(g2)
        requires DigraphsCompatible(g1, g2)
        ensures 
            var r := Combine(g1, g2);
            IsSubgraph(r, g1) &&
            IsSubgraph(r, g2)
    {
        reveal IsSubgraph();
        reveal Combine();
        reveal DigraphsCompatible();
        reveal DigraphValid();
        reveal IsNode();
        reveal IsConnected();
    }

    lemma CombineValid<Node(!new)>(g1: Digraph, g2: Digraph)
        requires DigraphValid(g1)
        requires DigraphValid(g2)
        requires DigraphsCompatible(g1, g2)
        ensures DigraphValid(Combine(g1, g2))
    {
        reveal DigraphsCompatible();
        reveal Combine();
        reveal DigraphValid();
        reveal IsConnected();
        var g := Combine(g1, g2);
        reveal IsNode();
        assert forall n: Node :: (IsConnected(g, n, n) == IsConnected(g1, n ,n) || IsConnected(g2, n, n));
        assert forall n: Node :: (IsNode(g, n) == IsNode(g1, n) || IsNode(g2, n));
        assert forall n: Node :: !IsConnected(g, n, n);
        assert forall n: Node, m: Node :: IsConnected(g1, n, m) ==> IsNode(g1, n) && IsNode(g1, m);
        assert forall n: Node, m: Node :: IsConnected(g2, n, m) ==> IsNode(g2, n) && IsNode(g2, m);
        forall n, m: Node | IsConnected(g, n, m)
            ensures IsNode(g, n) && IsNode(g, m)
        {
            if IsConnected(g1, n, m) {
                assert IsNode(g1, n) && IsNode(g1, m);
            } else {
                assert IsConnected(g2, n, m);
                assert IsNode(g2, n) && IsNode(g2, m);
            }
        }
        assert DigraphValid(g);
    }

    ghost predicate {:opaque} IsSubgraph<Node(!new)>(g: Digraph, s: Digraph)
    {
        (forall n :: IsNode(s, n) ==> IsNode(g, n)) &&
        (forall n, m :: IsNode(s, n) && IsNode(s, m) ==> IsConnected(s, n, m) == IsConnected(g, n, m))
    }

    function GetSubgraph<Node>(g: Digraph, is_member: Node -> bool): Digraph
    {
        Digraph(
            (set n: Node | n in g.Nodes && is_member(n) :: n),
            (set n: (Node, Node) | n in g.Connections && is_member(n.0) && is_member(n.1) :: n)
        )
    }

    lemma SubgraphIsSubgraph<Node(!new)>(g: Digraph, is_member: Node -> bool)
        ensures IsSubgraph(g, GetSubgraph(g, is_member))
    {
        reveal IsSubgraph();
        reveal IsNode();
        reveal IsConnected();
    }

    lemma PathValidInSubgraphValidInGraph<Node(!new)>(g: Digraph, s: Digraph, p: Path)
        requires IsSubgraph(g, s)
        ensures PathValid(s, p) ==> PathValid(g, p)
    {
        reveal IsSubgraph();
        reveal PathValid();
    }

    lemma PathInSubgraphValidInGraphValidInSubgraph<Node(!new)>(g: Digraph, s: Digraph, p: Path)
        requires PathValid(g, p)
        requires IsSubgraph(g, s)
        requires forall n :: n in p.v ==> IsNode(s, n)
        ensures PathValid(s, p)
    {
        reveal IsSubgraph();
        reveal PathValid();
    }

    function FindPathCrossingInternal<Node(!new)>(g1: Digraph, g2: Digraph, p: Path): (r: nat)
        // Find where a path crosses from one subgraph to another.
        requires DigraphValid(g1)
        requires DigraphValid(g2)
        requires DigraphsCompatible(g1, g2)
        requires exists n: Node :: n in p.v && IsNode(g1, n)
        requires exists n: Node :: n in p.v && IsNode(g2, n)
        requires IsNode(g1, p.v[0])
        requires
            var g := Combine(g1, g2);
            PathValid(g, p)
        decreases |p.v|
        ensures r < |p.v|-1
        ensures IsNode(g1, p.v[r]) && IsNode(g2, p.v[r+1])
    {
        reveal DigraphsCompatible();
        var g := Combine(g1, g2);
        reveal PathValid();
        reveal Combine();
        reveal IsNode();
        if IsNode(g2, p.v[1]) then
            0
        else
            assert IsNode(g1, p.v[1]);
            FindPathCrossingInternal(g1, g2, Path(p.v[1..])) + 1
    }

    function FindPathCrossing<Node(!new)>(g1: Digraph, g2: Digraph, p: Path): (r: nat)
        // Find where a path crosses from one subgraph to another.
        requires DigraphValid(g1)
        requires DigraphValid(g2)
        requires DigraphsCompatible(g1, g2)
        requires exists n: Node :: n in p.v && IsNode(g1, n)
        requires exists n: Node :: n in p.v && IsNode(g2, n)
        requires
            var g := Combine(g1, g2);
            PathValid(g, p)
        ensures r < |p.v|-1
        ensures (IsNode(g1, p.v[r]) && IsNode(g2, p.v[r+1])) ||
                (IsNode(g2, p.v[r]) && IsNode(g1, p.v[r+1]))
    {
        reveal Combine();
        reveal PathValid();
        reveal IsNode();
        reveal IsConnected();
        if IsNode(g1, p.v[0]) then
            var r := FindPathCrossingInternal(g1, g2, p);
            assert IsNode(g1, p.v[r]) && IsNode(g2, p.v[r+1]);
            r
        else
            reveal DigraphsCompatible();
            assert IsNode(g2, p.v[0]);
            var r := FindPathCrossingInternal(g2, g1, p);
            assert IsNode(g2, p.v[r]) && IsNode(g1, p.v[r+1]);
            r
    }

    lemma CombineNoLoops<Node(!new)>(g1: Digraph, g2: Digraph)
        requires DigraphValid(g1)
        requires DigraphValid(g2)
        requires !DigraphLoop(g1)
        requires !DigraphLoop(g2)
        requires DigraphsCompatible(g1, g2)
        ensures DigraphValid(Combine(g1, g2))
        ensures !DigraphLoop(Combine(g1, g2))
    {
        CombineValid(g1, g2);
        reveal DigraphsCompatible();
        reveal Combine();
        reveal PathValid();
        var r := Combine(g1, g2);
        CombineInputsAreSubgraphs(g1, g2);
        reveal DigraphValid();
        reveal DigraphLoop();
        forall p: Path<Node>
            ensures PathValid(r, p) ==> !PathLoop(p)
        {
            if PathValid(r, p) {
                reveal IsNode();
                assert forall n: Node :: n in p.v ==> IsNode(g1, n) || IsNode(g2, n);
                if forall n: Node :: n in p.v ==> IsNode(g1, n) {
                    PathInSubgraphValidInGraphValidInSubgraph(r, g1, p);
                    assert PathValid(g1, p);
                    assert !PathLoop(p);
                } else if forall n: Node :: n in p.v ==> IsNode(g2, n) {
                    PathInSubgraphValidInGraphValidInSubgraph(r, g2, p);
                    assert PathValid(g2, p);
                    assert !PathLoop(p);
                } else {
                    var index := FindPathCrossing(g1, g2, p);
                    reveal IsConnected();
                    if IsNode(g1, p.v[index]) {
                        assert IsNode(g2, p.v[index+1]);
                        assert !IsConnected(r, p.v[index], p.v[index+1]);
                    } else {
                        assert IsNode(g1, p.v[index+1]);
                        assert !IsConnected(r, p.v[index], p.v[index+1]);
                    }
                }
                assert !PathLoop(p);
            }
        }
        reveal DigraphLoop();
        assert !DigraphLoop(r);
    }
}

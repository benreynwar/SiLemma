module DigraphAddNode {

    import opened DigraphBase
    import opened DigraphPaths
    // Adding nodes

    function AddNode<Node(==)>(g: Digraph, n: Node): (r: Digraph)
        requires !IsNode(g, n)
    {
        Digraph(
            g.Nodes + {n},
            g.Connections
        )
    }

    lemma AddNodeDigraphValid<Node>(g: Digraph, n: Node)
        requires DigraphValid(g)
        requires !IsNode(g, n)
        ensures
            var r := AddNode(g, n);
            DigraphValid(r)
    {
        reveal DigraphValid();
    }

    function AddNodeV<Node(==)>(g: Digraph, n: Node): (r: Digraph)
        requires DigraphValid(g)
        requires !IsNode(g, n)
        ensures
            DigraphValid(r)
    {
        AddNodeDigraphValid(g, n);
        AddNode(g, n)
    }

    lemma AddNodePathValidHelper<Node>(r: Digraph, n: Node, x: Node)
        requires (forall m: Node :: !IsConnected(r, n, m))
        requires (forall m: Node :: !IsConnected(r, m, n))
        ensures !IsConnected(r, n, x)
        ensures !IsConnected(r, x, n)
    {
    }
    
    // There is only one path that becomes valid when we add a node.
    // It is the path containing just that node.
    lemma AddNodePathValid<Node>(g: Digraph, n: Node, p: Path<Node>)
        requires DigraphValid(g)
        requires !IsNode(g, n)
        ensures
            var r := AddNode(g, n);
            (PathValid(g, p) ==> PathValid(r, p)) &&
            (PathValid(r, p) ==> PathValid(g, p) || p == Path([n])) &&
            true
    {
        var r := AddNode(g, n);
        reveal PathValid();
        reveal DigraphValid();
        assert forall m: Node :: !IsConnected(g, m, n);
        assert forall m: Node :: !IsConnected(g, n, m);
        assert forall m: Node :: !IsConnected(r, m, n);
        assert forall m: Node :: !IsConnected(r, n, m);
        if n in p.v {
            assert !PathValid(g, p);
            if |p.v| == 1 {
                assert PathValid(r, p);
            } else {
                if p.v[0] == n {
                    AddNodePathValidHelper(r, n, p.v[1]);
                    assert !IsConnected(r, p.v[0], p.v[1]);
                    assert !PathValid(r, p);
                } else {
                    var index := PathFindIndex(p, n);
                    AddNodePathValidHelper(r, n, p.v[index-1]);
                    assert !IsConnected(r, p.v[index-1], p.v[index]);
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
        requires !IsNode(g, n)
        ensures
            var r := AddNode(g, n);
            DigraphLoop(g) == DigraphLoop(r)
    {
        var r := AddNode(g, n);
        reveal PathValid();
        reveal IsNode();
        reveal IsConnected();
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
    
}
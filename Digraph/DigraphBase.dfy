module DigraphBase {

    import opened Std.Wrappers
    import Std.Functions
    import Std.Collections.Set

    import SetExt

    export Spec
        reveals Path, PathValid
        provides Digraph, DigraphValid, IsNode, IsConnected
        provides AllNodes, NodeCount

    export Body
        provides SetExt
        reveals Path, PathValid
        reveals Digraph, DigraphValid, IsNode, IsConnected
        reveals AllNodes, NodeCount

    datatype Path<Node> = Path(v: seq<Node>)

    datatype Digraph<Node(==)> = Digraph(
        Nodes: set<Node>,
        Connections: set<(Node, Node)>
    )

    predicate {:opaque} IsNode<Node>(g: Digraph, n: Node)
    {
        n in g.Nodes
    }

    predicate {:opaque} IsConnected<Node>(g: Digraph, n: Node, m: Node)
    {
        (n, m) in g.Connections
    }

    ghost predicate {:opaque} DigraphValid<Node(!new)>(g: Digraph)
    {
        (forall n: Node :: !IsConnected(g, n, n)) && // No self-connections
        (forall n: Node, m: Node :: IsConnected(g, n, m) ==> IsNode(g, n) && IsNode(g, m))
    }
    
    lemma NotNodeNotConnected<Node(!new)>(g: Digraph, n: Node)
        // If a node is not in the graph
        // then it's not connected to any nodes
        requires DigraphValid(g)
        requires !IsNode(g, n)
        ensures
            (forall m: Node :: !IsConnected(g, m, n)) &&
            (forall m: Node :: !IsConnected(g, n, m))
    {
        reveal DigraphValid();
    }

    predicate {:opaque} PathValid<Node>(g: Digraph, p: Path<Node>)
    {
        (forall i: nat :: i < |p.v| ==> IsNode(g, p.v[i])) &&
        (forall i: nat :: i < |p.v|-1 ==> IsConnected(g, p.v[i], p.v[i+1]))
    }

    function AllNodes<Node(!new)>(g: Digraph): (r: set<Node>)
        requires DigraphValid(g)
        ensures forall n: Node :: IsNode(g, n) ==> n in r
        ensures forall n: Node :: n in r ==> IsNode(g, n)
    {
        reveal IsNode();
        g.Nodes
    }

    ghost predicate {:opaque} DigraphsEqual<Node(!new)>(g: Digraph, h: Digraph)
    {
        (forall n: Node :: IsNode(g, n) == IsNode(h, n)) &&
        (forall n, m: Node :: IsConnected(g, n, m) == IsConnected(h, n, m))
    }

    lemma DigraphsEqualAreEqual<Node(!new)>(g: Digraph, h: Digraph)
        requires DigraphsEqual(g, h)
        ensures g == h
    {
        reveal DigraphsEqual();
        reveal IsNode();
        reveal IsConnected();
        forall n: Node
            ensures (n in g.Nodes) == (n in h.Nodes)
        {
            assert IsNode(g, n) == IsNode(h, n);
        }
        forall n: (Node, Node)
            ensures (n in g.Connections) == (n in h.Connections)
        {
            assert IsConnected(g, n.0, n.1) == IsConnected(h, n.0, n.1);
        }
    }

    function NodeCount<Node>(g: Digraph): nat
    {
        |g.Nodes|
    }

}
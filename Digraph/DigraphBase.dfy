module DigraphBase {

    import opened Std.Wrappers
    import Std.Functions
    import Std.Collections.Set

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


}
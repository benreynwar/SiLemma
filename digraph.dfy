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

    ghost predicate {:opaque} PathLoop(p: Path)
    {
        (exists i: nat, j: nat :: i < |p.v| && j < |p.v| && i != j ==> p.v[i] == p.v[j])
    }

    ghost predicate {:opaque} DigraphLoop(g: Digraph)
    {
        exists p: Path :: PathValid(g, p) && PathLoop(p)
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

    lemma AddNodePathLoopConserved(g: Digraph, n: Node, p: Path)
        requires !g.IsNode(n)
    {
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
        // All the paths in the two graphs are the same except for one additional one in
        // r which is [n]
        reveal PathValid();
        forall p: Path {
            if p == Path([n]) {
                assert !g.IsNode(n);
                NotNodePathInvalid(g, n, Path([n]));
                assert !PathValid(g, p);
                assert PathValid(r, p);
                reveal PathLoop();
                assert !PathLoop(p);
            } else if PathValid(r, p) {
                AddNodePathValid(g, n, p);
                assert PathValid(g, p) || p == Path([n]);
                assert PathValid(g, p);
            } else {
                assert !PathValid(g, p);
            }
        }
    }

    lemma LengthOneNoLoop(p: Path)
        requires |p| == 1
        ensures NoLoop(p)
    {
        reveal NoLoop();
    }
    

    lemma NotNodePathInvalid(g: Digraph, n: Node, p: Path)
        requires !g.IsNode(n)
        requires n in p.v
        ensures !PathValid(g, p)
    {
        reveal PathValid();
    }
}
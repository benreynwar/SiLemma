include "digraph.dfy"

module TestDigraph {

    import DG

    function BuildDigraph(): (r: DG.Digraph)
        ensures DG.DigraphValid(r)
    {
        var g := DG.EmptyDigraph();
        var node_0 := 0;
        var node_1 := 1;
        var node_2 := 2;
        var node_3 := 3;
        var node_4 := 4;
        var g := DG.AddNodeV(g, node_0);
        var g := DG.AddNodeV(g, node_1);
        //DG.ConnectNodesPathExists(g, node_0, node_1);
        var g := DG.ConnectNodesV(g, node_0, node_1);
        reveal DG.PathValid();
        assert DG.PathExistsR(g, node_0, node_1);
        var g := DG.AddNodeV(g, node_2);
        DG.ConnectNodesPathExists(g, node_1, node_2);
        var g := DG.ConnectNodesV(g, node_1, node_2);
        assert DG.PathExistsR(g, node_0, node_1);
        assert DG.PathExistsR(g, node_1, node_2);
        assert !DG.PathExistsR(g, node_2, node_1);
        assert !DG.PathExistsR(g, node_2, node_0);
        assert DG.PathExistsR(g, node_0, node_2);
        // 0->1->2
        // Check that there is a path from 0 to 2.
        g
    }

}
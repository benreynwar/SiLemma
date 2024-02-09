// Nodes in a graph contain input ports and output ports.
// Within a node there can be paths from arbitrary
//    input ports to arbitrary output ports
// Between nodes each input port can be connected to at most
//    one output port.
// Each output port can go to arbitrary number of input ports.
// The graph keeps track of unconnected input ports and output ports.

include "../libraries/src/Wrappers.dfy"
include "digraph.dfy"
include "utils.dfy"
include "SeqNatToNat.dfy"
include "SeqNatToNatOrder.dfy"

module HG {

    import opened Wrappers
    import DG
    import SeqNatToNat
    import SeqNatToNatOrder
    import Utils

    newtype HNode = nat
    newtype HPort = nat

    predicate GEHPort(a: HPort, b: HPort)
    {
        a >= b
    }

    datatype HNodeKind = HNodeKind(
        IPorts: set<HPort>,
        OPorts: set<HPort>,
        PathExists: (HPort, HPort) -> bool
    )

    const InputNodeKind := HNodeKind(
        IPorts := {},
        OPorts := {0 as HPort},
        PathExists := (_, _) => false
    )

    const OutputNodeKind := HNodeKind(
        IPorts := {0 as HPort},
        OPorts := {},
        PathExists := (_, _) => false
    )

    const RegisterNodeKind := HNodeKind(
        IPorts := {0 as HPort},
        OPorts := {0 as HPort},
        PathExists := (_, _) => false
    )

    ghost predicate HNodeKindValid(nk: HNodeKind)
    {
        (forall a: HPort, b: HPort ::
            (a !in nk.IPorts ==> !nk.PathExists(a, b)) &&
            (b !in nk.OPorts ==> !nk.PathExists(a, b)))
        &&
        (forall a: HPort ::
            !(a in nk.IPorts && a in nk.OPorts))
    }

    lemma NoSelfPathExists(nk: HNodeKind)
        requires HNodeKindValid(nk)
        ensures forall p: HPort :: !nk.PathExists(p, p)
    {
    }

    ghost function HNodeKindPortBound(nk: HNodeKind): HPort
    {
        var maxi := if |nk.IPorts| == 0 then 0 else Utils.MaxInSet(GEHPort, nk.IPorts)+1;
        var maxo := if |nk.OPorts| == 0 then 0 else Utils.MaxInSet(GEHPort, nk.OPorts)+1;
        Utils.Max(GEHPort, maxi, maxo)
    }
    lemma NKPortsWithinBound(nk: HNodeKind, p: HPort)
        requires p in nk.IPorts || p in nk.OPorts
        ensures p <= HNodeKindPortBound(nk)
    {
    }

    predicate HNodeKindContainsPort(n: HNodeKind, p: HPort)
    {
        p in n.IPorts || p in n.OPorts
    }

    datatype INP = INP(n: HNode, p: HPort)
    predicate INPValid(g: HGraph, p: INP)
    {
        g.NodeKind(p.n).Some? && p.p in g.NodeKind(p.n).Extract().IPorts
    }
    function INPToDGNode(inp: INP): DG.Node
    {
        SeqNatToNat.NatsToNat([inp.n as nat, inp.p as nat]) as DG.Node
    }

    datatype ONP = ONP(n: HNode, p: HPort)
    predicate ONPValid(g: HGraph, p: ONP)
    {
        g.NodeKind(p.n).Some? && p.p in g.NodeKind(p.n).Extract().OPorts
    }
    function ONPToNat(onp: ONP): DG.Node
    {
        SeqNatToNat.NatsToNat([onp.n as nat, onp.p as nat]) as DG.Node
    }

    function DGNodeToNodePort(n: DG.Node): (HNode, HPort)
    {
        var nats := SeqNatToNat.NatToNats(n as nat, 2);
        (nats[0] as HNode, nats[1] as HPort)
    }

    datatype HGraph = HGraph(
        NodeKind: HNode -> Option<HNodeKind>,
        PortSource: INP -> Option<ONP>,
        // This is larger or equal to all nodes for which IsNode(node) is true.
        // We use this help dafny prove that things are finite and terminate.
        NodeBound: HNode,
        PortBound: HPort
    )

    ghost predicate HGraphValid(g: HGraph)
    {
        (forall n: HNode :: n >= g.NodeBound ==> g.NodeKind(n).None?)
        &&
        (forall inp: INP :: !INPValid(g, inp) ==> g.PortSource(inp).None?)
        &&
        (forall inp: INP :: g.PortSource(inp).Some? ==>
            ONPValid(g, g.PortSource(inp).Extract()))
        &&
        (forall n: HNode :: g.NodeKind(n).Some? ==>
            HNodeKindPortBound(g.NodeKind(n).Extract()) <= g.PortBound)
        &&
        (forall n: HNode :: g.NodeKind(n).Some? ==>
            HNodeKindValid(g.NodeKind(n).Extract()))
    }

    predicate NodePortInGraph(g: HGraph, n: HNode, p: HPort)
    {
        g.NodeKind(n).Some? && HNodeKindContainsPort(g.NodeKind(n).Extract(), p)
    }
    lemma NodePortNotInGraphWhenOutOfBound(g: HGraph, n: HNode, p: HPort)
        requires (n >= g.NodeBound) || (p >= g.PortBound)
        requires HGraphValid(g)
        ensures !NodePortInGraph(g, n, p)
    {
    }

    predicate DGNodeInGraph(g: HGraph, n: DG.Node)
    {
        var (n, p) := DGNodeToNodePort(n);
        NodePortInGraph(g, n, p)
    }
    predicate DGNodesConnected(g: HGraph, a: DG.Node, b: DG.Node)
    {
        if !DGNodeInGraph(g, a) then
            false
        else if !DGNodeInGraph(g, b) then
            false
        else
            var (na, pa) := DGNodeToNodePort(a);
            var (nb, pb) := DGNodeToNodePort(b);
            if (na == nb) then
                var nka := g.NodeKind(na).Extract();
                nka.PathExists(pa, pb)
            else
                g.PortSource(INP(na, pa)) == Some(ONP(nb, pb))
    }

    function HGraphToDigraph(g: HGraph): DG.Digraph
    {
      DG.Digraph(
        n => DGNodeInGraph(g, n),
        (a, b) => DGNodesConnected(g, a, b),
        SeqNatToNat.NatsToNat([g.NodeBound as nat, g.PortBound as nat]) as DG.Node
        )
    }

    lemma BadPortINPInvalid(g: HGraph, n: HNode, p: HPort)
        requires HGraphValid(g)
        requires p > g.PortBound
        ensures !INPValid(g, INP(n, p))
    {
    }

    lemma HGraphToDigraphValidBound(g: HGraph)
        requires HGraphValid(g)
        ensures
            var dg := HGraphToDigraph(g);
            forall n: DG.Node :: n >= dg.NodeBound ==> !dg.IsNode(n)
    {
        var dg := HGraphToDigraph(g);
        forall n: DG.Node | n >= dg.NodeBound
            ensures !dg.IsNode(n)
        {
            var bounds := SeqNatToNat.NatToNats(n as nat, 2);
            var hn := bounds[0] as HNode;
            var hp := bounds[1] as HPort;
            {SeqNatToNat.NatToNatsToNat(n as nat, 2);}
            assert bounds == [hn as nat, hp as nat];
            assert SeqNatToNat.NatsToNat([hn as nat, hp as nat]) == n as nat;

            SeqNatToNatOrder.NatsToNatOrder2(hn as nat, hp as nat, g.NodeBound as nat, g.PortBound as nat);
            assert hn >= g.NodeBound || hp >= g.PortBound;
            assert dg.IsNode(n) == NodePortInGraph(g, hn, hp);
            NodePortNotInGraphWhenOutOfBound(g, hn, hp);
            assert !dg.IsNode(n);
        }
        assert forall n: DG.Node :: n >= dg.NodeBound ==> !dg.IsNode(n);
    }

    lemma HGraphToDigraphValidNoSelfConnections(g: HGraph)
        requires HGraphValid(g)
        ensures
            var dg := HGraphToDigraph(g);
            forall n: DG.Node :: !dg.IsConnected(n, n)
    {
    }

    lemma HGraphToDigraphValidConnections(g: HGraph)
        requires HGraphValid(g)
        ensures
            var dg := HGraphToDigraph(g);
            forall n: DG.Node, m: DG.Node :: dg.IsConnected(n, m) ==> dg.IsNode(n) && dg.IsNode(m)
    {
    }

    lemma HGraphToDigraphValid(g: HGraph)
        requires HGraphValid(g)
        ensures
            var dg := HGraphToDigraph(g);
            DG.DigraphValid(dg)
    {
        var dg := HGraphToDigraph(g);
        HGraphToDigraphValidBound(g);
        HGraphToDigraphValidNoSelfConnections(g);
        HGraphToDigraphValidConnections(g);
        reveal DG.DigraphValid();
        assert DG.DigraphValid(dg);
    }

}
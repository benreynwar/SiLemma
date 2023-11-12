// Nodes in a graph contain input ports and output ports.
// Within a node there can be paths from arbitrary
//    input ports to arbitrary output ports
// Between nodes each input port can be connected to at most
//    one output port.
// Each output port can go to arbitrary number of input ports.
// The graph keeps track of unconnected input ports and output ports.

include "../libraries/src/Wrappers.dfy"

module HG {

    import opened Wrappers

    newtype HNode = nat
    newtype HPort = nat

    datatype HNodeKind = HNodeKind(
        IPorts: set<HPort>,
        OPorts: set<HPort>,
        PathExists: (HPort, HPort) -> bool
    )

    ghost predicate HNodeKindValid(nk: HNodeKind)
    {
        (forall a: HPort, b: HPort ::
            (a !in nk.IPorts ==> !nk.PathExists(a, b)) &&
            (b !in nk.IPorts ==> !nk.PathExists(a, b)))
        &&
        (forall a: HPort ::
            !(a in nk.IPorts && a in nk.OPorts))
    }

    datatype HGraph = HGraph(
        NodeKind: HNode -> Option<HNodeKind>,
        PortSource: INP -> Option<ONP>,
        // This is larger or equal to all nodes for which IsNode(node) is true.
        // We use this help dafny prove that things are finite and terminate.
        NodeBound: HNode
    )

    datatype INP = INP(n: HNode, p: HPort)
    datatype ONP = ONP(n: HNode, p: HPort)

    predicate INPValid(g: HGraph, p: INP)
    {
        g.NodeKind(p.n).Some? && p.p in g.NodeKind(p.n).Extract().IPorts
    }

    predicate ONPValid(g: HGraph, p: ONP)
    {
        g.NodeKind(p.n).Some? && p.p in g.NodeKind(p.n).Extract().OPorts
    }

    ghost predicate HGraphValid(g: HGraph)
    {
        (forall n: HNode :: n >= g.NodeBound ==> g.NodeKind(n).None?)
        &&
        (forall inp: INP :: !INPValid(g, inp) ==> g.PortSource(inp).None?)
        &&
        (forall inp: INP :: g.PortSource(inp).Some? ==>
            ONPValid(g, g.PortSource(inp).Extract()))
    }

}
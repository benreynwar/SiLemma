include "../libraries/src/Wrappers.dfy"
include "SeqNatToNat.dfy"
include "circuit.dfy"

module CircuitPath {

    import opened Wrappers
    import opened Circuit

    datatype Path = PathNil | PathCons(head: HPNP, tail: Path)

    function PathLength(p: Path): nat
    {
        match p
        case PathNil => 0
        case PathCons(head, tail) => 1 + PathLength(tail)
    }

    function PathStart(p: Path): HPNP
        requires p.PathCons?
    {
        match p
        case PathCons(head, Nil) => head
        case PathCons(head, tail) => PathStart(tail)
    }

    predicate {:opaque} HPNPOtoIConnected(c: Circuit, a: HPNP, b: HPNP)
        requires CircuitValid(c)
        requires HPNPValidOutput(c, a)
        requires HPNPValidInput(c, b)
    {
        var a_c := HierarchyPathCircuit(c, a.hpn.hp);
        var maybe_a_nk := a_c.NodeKind(a.hpn.n);
        match maybe_a_nk
        case None => false
        case Some(a_nk) =>
            match a_nk
            case CInput => (
                match a.hpn.hp
                // This is a top level input. It's not connected to anything.
                case Top => false
                case Level(hier_n, parent_hp) =>
                    // If it's an input inside a hier node, then it connects to
                    // the input port on the hier node on the next level up.
                    if parent_hp == b.hpn.hp then
                        var hier_inp := HPNP(HPNode(parent_hp, hier_n), a.hpn.n as CPort);
                        hier_inp == b
                    else
                        false
            )
            case CHier(lower_c) => (
                // It's an output port from a hier node.
                // It only connects to the input into the corresponding Output node in that circuit.
                var maybe_level_nk := lower_c.NodeKind(a.p as CNode);
                match maybe_level_nk
                case Some(Output) =>
                    var new_hp := ExtendHierarchyPath(c, a.hpn.hp, a.hpn.n);
                    var hier_inp := HPNP(HPNode(new_hp, a.p as CNode), 0);
                    hier_inp == b 
                case _ => false
            )
            case CComb(_, _, path_exists, _) =>
                (a.hpn.hp == b.hpn.hp) &&
                (a.hpn.n == b.hpn.n) &&
                path_exists(a.p, b.p)
            case CReg => false
    }

    predicate {:opaque} HPNPItoOConnected(c: Circuit, a: HPNP, b: HPNP)
    {
        false
    }

    predicate {:opaque} HPNPConnected(c: Circuit,  a: HPNP, b: HPNP)
        requires CircuitValid(c)
    {
        (HPNPValidInput(c, a) && HPNPValidOutput(c, b) &&
            HPNPItoOConnected(c, a, b)) ||
        (HPNPValidOutput(c, a) && HPNPValidInput(c, b) &&
            HPNPOtoIConnected(c, a, b))
    }

    predicate PathValid(c: Circuit, p: Path)
        requires CircuitValid(c)
        decreases p
    {
        match p
        case PathNil => true
        case PathCons(head, PathCons(head2, tail)) =>
            HPNPValid(c, head) && HPNPConnected(c, head2, head) &&
            PathValid(c, PathCons(head2, tail))
        case PathCons(head, tail) =>
            HPNPValid(c, head) && PathValid(c, tail)
    }

    predicate ReversePathValid(c: Circuit, p: Path)
        requires CircuitValid(c)
        decreases p
    {
        match p
        case PathNil => true
        case PathCons(head, PathCons(head2, tail)) =>
            HPNPValid(c, head) && HPNPConnected(c, head, head2) &&
            ReversePathValid(c, PathCons(head2, tail))
        case PathCons(head, tail) =>
            HPNPValid(c, head) && ReversePathValid(c, tail)
    }

    predicate {:opaque} PathExcludes(p: Path, exclusion: set<HPNP>)
    {
        match p
        case Nil => true
        case PathCons(head, tail) => head !in exclusion && PathExcludes(tail, exclusion)
    }

    predicate {:opaque} PathContainsNP(p: Path, np: HPNP)
    {
        match p
        case Nil => false
        case PathCons(head, tail) => head == np || PathContainsNP(tail, np)
    }

    lemma NPInExclusionNotInPath(p: Path, exclusion: set<HPNP>, np: HPNP)
        requires PathExcludes(p, exclusion)
        requires np in exclusion
        ensures !PathContainsNP(p, np)
    {
        reveal PathExcludes();
        reveal PathContainsNP();
    }

    predicate NextNode(c: Circuit, n: HPNP, m: HPNP)
        requires CircuitValid(c)
        requires HPNPValid(c, n)
    {
        HPNPConnected(c, n, m)
    }

    function PathAppend(p: Path, n: HPNP): (r: Path)
    {
        PathCons(n, p)
    }

    lemma PathAppendValid(c: Circuit, p: Path, n: HPNP)
        // Add a node onto a path.
        requires CircuitValid(c)
        requires HPNPValid(c, n)
        requires p.PathCons?
        requires HPNPConnected(c, p.head, n)
        requires PathValid(c, p)
        ensures
            var r := PathAppend(p, n);
            PathValid(c, r)
    {
    }

    lemma ReversePathAppendValid(c: Circuit, p: Path, n: HPNP)
        // Add a node onto a path.
        requires CircuitValid(c)
        requires HPNPValid(c, n)
        requires p.PathCons?
        requires HPNPConnected(c, n, p.head)
        requires ReversePathValid(c, p)
        ensures
            var r := PathAppend(p, n);
            ReversePathValid(c, r)
    {
    }

    function ReversePathInternal(p: Path, partial_reversed: Path): (r: Path)
        ensures PathLength(r) == PathLength(p) + PathLength(partial_reversed)
    {
        match p
        case PathNil => partial_reversed
        case PathCons(head, tail) => ReversePathInternal(tail, PathCons(head, partial_reversed))
    }

    lemma ReversedLengthOnePathIsUnchanged(p: Path)
        requires p.PathCons?
        requires p.tail == PathNil
        ensures ReversePath(p) == p
    {
        var head := p.head;
        assert p == PathCons(head, PathNil);
        assert ReversePath(p) == ReversePathInternal(p, PathNil);
    }

    lemma ReversePathInternalForwardValid(c: Circuit, p: Path, partial_reversed: Path)
        requires CircuitValid(c)
        requires PathValid(c, p)
        requires ReversePathValid(c, partial_reversed)
        requires (p.PathCons? && partial_reversed.PathCons?) ==> HPNPConnected(c, p.head, partial_reversed.head)
        ensures
            var r := ReversePathInternal(p, partial_reversed);
            ReversePathValid(c, r)
    {
        match p
        case PathNil => {}
        case PathCons(head, tail) =>
            ReversePathInternalForwardValid(c, tail, PathCons(head, partial_reversed));
    }

    lemma ReversePathForwardValid(c: Circuit, p: Path)
        requires CircuitValid(c)
        requires PathValid(c, p)
        ensures
            var r := ReversePath(p);
            ReversePathValid(c, r)
    {
        ReversePathInternalForwardValid(c, p, PathNil);
    }

    lemma ReversePathInternalBackwardValid(c: Circuit, p: Path, partial_reversed: Path)
        requires CircuitValid(c)
        requires ReversePathValid(c, p)
        requires PathValid(c, partial_reversed)
        requires (p.PathCons? && partial_reversed.PathCons?) ==> HPNPConnected(c, partial_reversed.head, p.head)
        ensures
            var r := ReversePathInternal(p, partial_reversed);
            PathValid(c, r)
    {
        match p
        case PathNil => {}
        case PathCons(head, tail) =>
            ReversePathInternalBackwardValid(c, tail, PathCons(head, partial_reversed));
    }

    lemma ReversePathBackwardValid(c: Circuit, p: Path)
        requires CircuitValid(c)
        requires ReversePathValid(c, p)
        ensures
            var r := ReversePath(p);
            PathValid(c, r)
    {
        ReversePathInternalBackwardValid(c, p, PathNil);
    }

    function ReversePath(p: Path): (r: Path)
        ensures PathLength(p) == PathLength(r)
    {
        ReversePathInternal(p, PathNil)
    }
    
    function PathPrepend(p: Path, n: HPNP): (r: Path)
    {
        var reversed := ReversePath(p);
        var appended := PathAppend(reversed, n);
        var prepended := ReversePath(appended);
        prepended
    }

    lemma PathStartIsReversedHead(p: Path)
        requires p.PathCons?
        ensures ReversePath(p).head == PathStart(p)
    {
        match p
        case PathCons(head, PathNil) => {
            assert head == PathStart(p);
            assert ReversePath(p) == ReversePathInternal(p, PathNil);
            assert ReversePath(p).head == head;
        }
        case PathCons(head, tail) => {
            PathStartIsReversedHead(tail);
            assert ReversePath(tail).head == PathStart(tail);
        }
    }

    lemma PathPrependValid(c: Circuit, p: Path, n: HPNP)
        // Add a node onto a path.
        requires CircuitValid(c)
        requires HPNPValid(c, n)
        requires p.PathCons?
        requires HPNPConnected(c, PathStart(p), n)
        requires PathValid(c, p)
        ensures
            var r := PathPrepend(p, n);
            PathValid(c, r);
    {
        var reversed := ReversePath(p);
        assert reversed.head == PathStart(p);
        ReversePathForwardValid(c, p);
        assert ReversePathValid(c, reversed);
        var appended := PathAppend(reversed, n);
        ReversePathAppendValid(c, reversed, n);
        assert ReversePathValid(c, appended);
        var prepended := ReversePath(appended);
    }

}
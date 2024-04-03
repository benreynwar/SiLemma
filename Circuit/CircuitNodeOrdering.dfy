module CircuitNodeOrdering {

    import Std.Relations

    import C = CircuitBase

    predicate HPOrdering(a: C.HierarchyPath, b: C.HierarchyPath)
        decreases |a.v|
    {
        if a == C.HP([]) then
            true
        else if b == C.HP([]) then
            false
        else if a.v[0] == b.v[0] then
            HPOrdering(C.HP(a.v[1..]), C.HP(b.v[1..]))
        else
            a.v[0] <= b.v[0]
    }
    predicate HPNodeOrdering(a: C.HPNode, b: C.HPNode)
    {
        if a.hp == b.hp then
            a.n <= b.n
        else
            HPOrdering(a.hp, b.hp)
    }

    predicate HPNPOrdering(a: C.HPNP, b: C.HPNP)
    {
        if a.hpn == b.hpn then
            a.p <= b.p
        else
            HPNodeOrdering(a.hpn, b.hpn)
    }

    lemma HPOrderingReflexiveInternal(a: C.HierarchyPath)
        ensures HPOrdering(a, a)
        decreases a.v
    {
        if a == C.HP([]) {
        } else {
            HPOrderingReflexiveInternal(C.HP(a.v[1..]));
        }
    }

    lemma HPOrderingReflexive()
        ensures Relations.Reflexive(HPOrdering)
    {
        forall a: C.HierarchyPath
            ensures HPOrdering(a, a)
        {
            HPOrderingReflexiveInternal(a);
        }
    }

    lemma HPOrderingAntiSymmetricInternal(a: C.HierarchyPath, b: C.HierarchyPath)
        ensures HPOrdering(a, b) && HPOrdering(b, a) ==> a == b
        decreases |a.v|
    {
        if a == C.HP([]) {
        } else {
            if b == C.HP([]) {
            } else {
                if a.v[0] == b.v[0] {
                } else {
                    HPOrderingAntiSymmetricInternal(C.HP(a.v[1..]), C.HP(b.v[1..]));
                    assert HPOrdering(a, b) && HPOrdering(b, a) ==> a == b;
                }
            }
        }
    }

    lemma HPOrderingAntiSymmetric()
        ensures Relations.AntiSymmetric(HPOrdering)
    {
        forall a: C.HierarchyPath, b: C.HierarchyPath
            ensures HPOrdering(a, b) && HPOrdering(b, a) ==> a == b
        {
            HPOrderingAntiSymmetricInternal(a, b);
        }
    }

    lemma HPOrderingTransitiveInternal(a: C.HierarchyPath, b: C.HierarchyPath, c: C.HierarchyPath)
        ensures HPOrdering(a, b) && HPOrdering(b, c) ==> HPOrdering(a, c)
        decreases |a.v|
    {
    }

    lemma HPOrderingTransitive()
        ensures Relations.Transitive(HPOrdering)
    {
        forall a: C.HierarchyPath, b: C.HierarchyPath, c: C.HierarchyPath
            ensures HPOrdering(a, b) && HPOrdering(b, c) ==> HPOrdering(a, c)
        {
            HPOrderingTransitiveInternal(a, b, c);
        }
    }

    lemma HPOrderingStronglyConnectedInternal(a: C.HierarchyPath, b: C.HierarchyPath)
        ensures HPOrdering(a, b) || HPOrdering(b, a)
        decreases a.v
    {
        if a == C.HP([]) {
        } else {
            if b == C.HP([]) {
            } else {
                if a.v[0] == b.v[0] {
                } else {
                    HPOrderingStronglyConnectedInternal(C.HP(a.v[1..]), C.HP(b.v[1..]));
                }
            }
        }
    }

    lemma HPOrderingStronglyConnected()
        ensures Relations.StronglyConnected(HPOrdering)
    {
        forall a: C.HierarchyPath, b: C.HierarchyPath
            ensures HPOrdering(a, b) || HPOrdering(b, a)
        {
            HPOrderingStronglyConnectedInternal(a, b);
        }
    }

    lemma {:vcs_split_on_every_assert} HPOrderingIsTotal()
        ensures Relations.TotalOrdering(HPOrdering)
    {
        HPOrderingReflexive();
        HPOrderingAntiSymmetric();
        HPOrderingTransitive();
        HPOrderingStronglyConnected();
        assert Relations.Reflexive(HPOrdering);
        assert Relations.Transitive(HPOrdering);
        assert Relations.StronglyConnected(HPOrdering);
        assert Relations.AntiSymmetric(HPOrdering);
    }

    lemma HPNodeOrderingIsTotal()
        ensures Relations.TotalOrdering(HPNodeOrdering)
    {
        HPOrderingIsTotal();
        assert Relations.Reflexive(HPNodeOrdering);
        assert Relations.AntiSymmetric(HPNodeOrdering);
        assert Relations.Transitive(HPNodeOrdering);
        assert Relations.StronglyConnected(HPNodeOrdering);
    }
        
    lemma HPNPOrderingIsTotal()
        ensures Relations.TotalOrdering(HPNPOrdering)
    {
        HPNodeOrderingIsTotal();
    }


}
module MapExt {

    lemma ExtendedMapValues<T, U>(m: map<T, U>, x: T, y: U)
        requires x !in m
        ensures
            m[x := y].Values == m.Values + {y}
    {
        var n := m[x := y];
        assert n.Keys == m.Keys + {x};
    }

}
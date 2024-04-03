module SeqExt {
    import Seq = Std.Collections.Seq
    import Functions = Std.Functions
    import Std.Math

    lemma LemmaToSetAdds<X>(xs: seq<X>, ys: seq<X>)
        ensures Seq.ToSet(xs) + Seq.ToSet(ys) == Seq.ToSet(xs + ys)
    {
        reveal Seq.ToSet();
        assert forall x :: x in (xs + ys) <==> (x in xs) || (x in ys);
    }

    lemma MapConservesNoDuplicates<X(!new), Y>(f: X -> Y, xs: seq<X>)
        requires Seq.HasNoDuplicates(xs)
        requires Functions.Injective(f)
        ensures Seq.HasNoDuplicates(Seq.Map(f, xs))
    {
        reveal Seq.HasNoDuplicates();
    }

    lemma FilterStillContains<X>(f: X -> bool, xs: seq<X>, x: X)
        requires f(x)
        requires x in xs
        ensures x in Seq.Filter(f, xs)
    {
        reveal Seq.Filter();
    }

    lemma MapStillContains<X, Y>(f: X --> Y, xs: seq<X>, x: X)
        requires x in xs
        requires f.requires(x)
        requires forall xx :: xx in xs ==> f.requires(xx)
        ensures f(x) in Seq.Map(f, xs)
    {
        reveal Seq.Map();
    }

    function SetConcat<X(==)>(a: seq<X>, b: seq<X>): (r: seq<X>)
        requires Seq.HasNoDuplicates(a)
        requires Seq.HasNoDuplicates(b)
        ensures Seq.HasNoDuplicates(r)
        decreases |b|
    {
        if |b| == 0 then
            a
        else
            var x := b[0];
            var new_b := b[1..];
            var new_a := if x !in a then a + [x] else a;
            reveal Seq.HasNoDuplicates();
            assert Seq.HasNoDuplicates(new_a);
            assert Seq.HasNoDuplicates(new_b);
            SetConcat(new_a, new_b)
    }

}

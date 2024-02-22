module SeqExt {
    import Seq = Std.Collections.Seq
    import Functions = Std.Functions

    lemma LemmaToSetAdds<X>(xs: seq<X>, ys: seq<X>)
        ensures Seq.ToSet(xs) + Seq.ToSet(ys) == Seq.ToSet(xs + ys)
    {
        reveal Seq.ToSet();
        assert forall x :: x in (xs + ys) <==> (x in xs) || (x in ys);
    }

    lemma MapConservesNoDuplicates<X, Y>(f: X -> Y, xs: seq<X>)
        requires Seq.HasNoDuplicates(xs)
        requires Functions.Injective(f)
        ensures Seq.HasNoDuplicates(Seq.Map(f, xs))
    {
        reveal Seq.HasNoDuplicates();
    }
}

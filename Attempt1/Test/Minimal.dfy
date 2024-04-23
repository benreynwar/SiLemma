module Minimal {
    import opened Std.Wrappers
    import Std.Collections.Set
    import Std.Functions

    //function MapAndExtract<X(!new), Y(!new)>(f: X -> Option<Y>, xs: set<X>): (ys: set<Y>)
    //    // Like the Set.Map function, except it takes a function argument that resturns an
    //    // Option<Y>, and the None results are discarded.
    //    requires Functions.Injective(f)
    //{
    //    var mapped: set<Option<Y>> := Set.Map(f, xs);
    //    var filtered: set<Option<Y>> := Set.Filter((x: Option<Y>) => x.Some?, mapped);
    //    var extract := (x: Option<Y>) requires x.Some? => x.value;
    //    assert Functions.Injective(extract);
    //    var extracted: set<Y> := Set.Map(extract, filtered);
    //    extracted
    //}

    //ghost predicate MyInjective<X(!new), Y>(f: X --> Y)
    //    reads f.reads
    //    //requires forall x :: f.requires(x)
    //{
    //    forall x1, x2 :: f.requires(x1) && f.requires(x2) && f(x1) == f(x2) ==> x1 == x2
    //}
}

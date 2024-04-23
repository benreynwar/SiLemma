module SetExt {

    import Std.Relations

  ///* Returns the maximum integer value in a non-empty set of integers. */
  //function {:opaque} Max(xs: set<int>): int
  //  requires 0 < |xs|
  //  ensures forall k :: k in xs ==> Max(xs) >= k
  //  ensures Max(xs) in xs
  //{
  //  var y :| 
  //  assert xs == [xs[0]] + xs[1..];
  //  if |xs| == 1 then xs[0] else Math.Max(xs[0], Max(xs[1..]))
  //}

    ghost function ToSeq<T>(s: set<T>): (r: seq<T>)
        ensures |s| == |r|
    {
        if |s| == 0 then
            []
        else
            var y :| y in s;
            var r := s - {y};
            [y] + ToSeq(r)
    }

    lemma SetRemoval<T>(s: set<T>, x: T)
        requires x in s
        ensures
            var new_s := s - {x};
            s == new_s + {x}
    {
    }

    lemma {:vcs_split_on_every_assert} ThereIsAMinimum<T(!new)>(s: set<T>, R: (T, T)->bool)
        requires Relations.TotalOrdering(R)
        requires s != {}
        ensures exists x :: x in s && forall y :: y in s ==> R(x, y)
        decreases |s|
    {
        var x :| x in s;
        var goal := exists x :: x in s && forall y :: y in s ==> R(x, y);
        if s == {x} {
            assert forall y:: y in s ==> y == x;
            assert goal;
        } else {
            assert x in s;
            var new_s := s - {x};
            SetRemoval(s, x);
            assert s == new_s + {x};
            assert |new_s| < |s|;
            assert new_s != {};
            ThereIsAMinimum(new_s, R);
            var z :| z in new_s && forall y :: y in new_s ==> R(z, y);
            assert forall y :: y in s ==> y in new_s || y == x;
            if R(z, x) {
                assert goal;
            } else {
                assert goal;
            }
        }
        assert goal;
    }

    function GetMin<T(!new)>(s: set<T>, R: (T, T) -> bool): (r: T)
        requires Relations.TotalOrdering(R)
        requires s != {}
        ensures r in s
    {
        ThereIsAMinimum(s, R);
        var x :| x in s && forall y :: y in s ==> R(x, y);
        assert x in s;
        x
    }

    lemma ToSeqStillContains<T>(s: set<T>, x: T)
        requires x in s
        ensures x in ToSeq(s)
    {
    }

    function SetProduct<T, U>(t: set<T>, u: set<U>): (r: set<(T, U)>)
    {
        (set x: T, y: U | x in t && y in u :: (x, y))
    }


}
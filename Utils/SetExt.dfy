module SetExt {

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
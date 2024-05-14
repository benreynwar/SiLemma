module Utils {

  import Std.Collections.Seq
  import Std.Collections.Map

  predicate SetsNoIntersection<T>(a: set<T>, b: set<T>)
  {
    |a * b| == 0
  }

  lemma SetsNoIntersectionDuh<T>(a: set<T>, b: set<T>)
    requires SetsNoIntersection(a, b)
    ensures !exists x :: x in a && x in b
  {
    if exists x :: x in a && x in b {
      var x :| x in a && x in b;
      assert x in a * b;
    }
  }

  lemma SetsNoIntersectionAdds<T>(a: set<T>, b: set<T>, c: set<T>)
    requires SetsNoIntersection(a, b)
    requires SetsNoIntersection(a, c)
    ensures SetsNoIntersection(a, b + c)
  {
    if exists x :: x in a && x in b + c {
      var x :| x in a && x in b + c;
      assert x in b || x in c;
      if x in b {
        assert x in a && x in b;
        assert x in (a * b);
      } else {
        assert x in a && x in c;
        assert x in (a * c);
      }
      assert false;
    }
  }

  lemma SetsNoIntersectionSymm<T>(a: set<T>, b: set<T>)
    ensures SetsNoIntersection(a, b) == SetsNoIntersection(b, a)
  {
    assert a * b == b * a;
  }

  lemma NotInBoth<T>(x: T, a: set<T>, b: set<T>)
    requires SetsNoIntersection(a, b)
    ensures !((x in a) && (x in b))
  {
    if (x in a) && (x in b) {
      assert x in (a * b);
      assert false;
    }
  }

  lemma InThisNotInThat<T>(x: T, a: set<T>, b: set<T>)
    requires x in a
    requires SetsNoIntersection(a, b)
    ensures x !in b
  {
    if x in b {
      assert x in (a * b);
      assert false;
    }
  }

  lemma ManyInThisNotInThat<T>(xs: set<T>, a: set<T>, b: set<T>)
    requires forall x :: x in xs ==> x in a
    requires SetsNoIntersection(a, b)
    ensures forall x :: x in xs ==> x !in b
  {
    forall x | x in xs
      ensures x !in b
    {
      InThisNotInThat(x, a, b);
    }
  }
    
  function ExtractMap<T, U>(a: map<T, U>, k: set<T>): (r: map<T, U>)
    requires forall x :: x in k ==> x in a
    ensures r.Keys == k
    ensures forall x :: x in k ==> r[x] == a[x]
  {
    (map x | x in k :: a[x])
  }

  function CombineSets<T>(sc1: set<T>, sc2: set<T>): (r: set<T>)
    requires SetsNoIntersection(sc1, sc2)
  {
    sc1 + sc2
  }

  lemma AddMapsCorrect<T, U>(a: map<T, U>, b: map<T, U>)
    requires SetsNoIntersection(a.Keys, b.Keys)
    ensures
      var r := AddMapsImpl(a, b);
      && r.Keys == a.Keys + b.Keys
      && Map.IsSubset(a, r)
      && Map.IsSubset(b, r)
  {
    forall x: T
      ensures !((x in a) && (x in b))
    {
      NotInBoth(x, a.Keys, b.Keys);
    }
  }

  function AddMapsImpl<T, U>(a: map<T, U>, b: map<T, U>): (r: map<T, U>)
    requires SetsNoIntersection(a.Keys, b.Keys)
    ensures r.Keys == a.Keys + b.Keys
  {
    a + b
  }

  function AddMaps<T, U>(a: map<T, U>, b: map<T, U>): (r: map<T, U>)
    requires SetsNoIntersection(a.Keys, b.Keys)
    ensures r.Keys == a.Keys + b.Keys
    ensures Map.IsSubset(a, r)
    ensures Map.IsSubset(b, r)
  {
    AddMapsCorrect(a, b);
    AddMapsImpl(a, b)
  }

  lemma StillHasNoDuplicates<X>(s: seq<X>, x: X)
    requires Seq.HasNoDuplicates(s)
    requires x !in s
    ensures Seq.HasNoDuplicates(s + [x])
  {
    reveal Seq.HasNoDuplicates();
  }

  function Xor(a: bool, b: bool): bool
  {
    (a && !b) || (!a && b)
  }


}
module Utils {

  import Std.Collections.Seq
  import Std.Collections.Map

  predicate SetsNoIntersection<T>(a: set<T>, b: set<T>)
  {
    a !! b
  }

  lemma SubsetsNoIntersection<T>(a: set<T>, b: set<T>, aa: set<T>, bb: set<T>)
    requires SetsNoIntersection(a, b)
    requires aa <= a
    requires bb <= b
    ensures SetsNoIntersection(aa, bb)
  {
    var cc := aa * bb;
    assert cc <= aa;
    assert cc <= bb;
    assert cc <= a;
    assert cc <= b;
    assert cc <= a * b;
    assert |cc| == 0;
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

  lemma HasNoDuplicatesNotInBoth<T>(a: seq<T>, b: seq<T>, x: T)
    requires Seq.HasNoDuplicates(a + b)
    ensures !(x in a && x in b)
  {
    if x in a && x in b {
      assert |a| > 0;
      var index1 := Seq.IndexOf(a, x);
      var index2 := Seq.IndexOf(b, x);
      assert (a + b)[index1] == (a + b)[|a| + index2];
      reveal Seq.HasNoDuplicates();
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

  predicate UniqueElements<T(==)>(els: seq<T>)
  {
    forall i: nat, j: nat :: i < |els| && j < |els| && i != j ==> els[i] != els[j]
  }

  lemma NotEqualFromUniqueElements<T>(els: seq<T>, index1: nat, index2: nat)
    requires UniqueElements(els)
    requires index1 < |els|
    requires index2 < |els|
    requires index1 != index2
    ensures els[index1] != els[index2]
  {
  }

  opaque predicate MapMatchesSeqs<T(==), U(==)>(m: map<T, U>, a: seq<T>, b: seq<U>)
    requires |a| == |b|
  {
    forall index: nat :: index < |a| ==> a[index] in m && m[a[index]] == b[index]
  }

  opaque function SeqsToMap<T(==), U(==)>(a: seq<T>, b: seq<U>): (r: map<T, U>)
    requires Seq.HasNoDuplicates(a)
    requires |a| == |b|
    ensures r.Keys == Seq.ToSet(a)
    ensures MapMatchesSeqs(r, a, b)
  {
    reveal Seq.ToSet();
    reveal MapMatchesSeqs();
    if |a| == 0 then
      map[]
    else
      var x := a[0];
      var new_a := a[1..];
      var y := b[0];
      var new_b := b[1..];
      assert Seq.HasNoDuplicates(new_a) && x !in new_a by {
        reveal Seq.HasNoDuplicates();
      }
      var new_map := SeqsToMap(new_a, new_b);
      var r := new_map[x := y];
      r
  }

  lemma NoIntersectionEquiv<T>(a: set<T>, b: set<T>)
    ensures (a !! b) == (|a * b| == 0)
  {
    if !(a !! b) {
      var x :| x in a && x in b;
      assert x in a * b;
    }
  }


  lemma SubSeqsNoDuplicates<T>(a: seq<T>, b: seq<T>)
    requires Seq.HasNoDuplicates(a + b)
    ensures Seq.HasNoDuplicates(a)
    ensures Seq.HasNoDuplicates(b)
    ensures Seq.ToSet(a) !! Seq.ToSet(b)
  {
    reveal Seq.HasNoDuplicates();
    if !Seq.HasNoDuplicates(a) {
      var index1: nat, index2: nat :| index1 < |a| && index2 < |a| && index1 != index2 && a[index1] == a[index2];
      assert (a+b)[index1] == (a+b)[index2];
      assert !Seq.HasNoDuplicates(a+b);
    }
    if !Seq.HasNoDuplicates(b) {
      var index1: nat, index2: nat :| index1 < |b| && index2 < |b| && index1 != index2 && b[index1] == b[index2];
      assert (a+b)[|a| + index1] == (a+b)[|a| + index2];
      assert !Seq.HasNoDuplicates(a+b);
    }
    if !(Seq.ToSet(a) !! Seq.ToSet(b)) {
      NoIntersectionEquiv(Seq.ToSet(a), Seq.ToSet(b));
      assert |Seq.ToSet(a) * Seq.ToSet(b)| > 0;
      assert !(Seq.ToSet(a) !! Seq.ToSet(b));
      var v :| v in Seq.ToSet(a) * Seq.ToSet(b);
      reveal Seq.ToSet();
      var index1 := Seq.IndexOf(a, v);
      var index2 := Seq.IndexOf(b, v);
      assert (a+b)[index1] == (a+b)[|a| + index2];
      assert !Seq.HasNoDuplicates(a+b);
    }
  }

  lemma NoDuplicatesInConcat<T>(xs: seq<T>, ys: seq<T>)
    // Like the one in the std library but using Seq.ToSet rather than
    // multiset.
    requires Seq.HasNoDuplicates(xs)
    requires Seq.HasNoDuplicates(ys)
    requires Seq.ToSet(xs) !! Seq.ToSet(ys)
    ensures Seq.HasNoDuplicates(xs+ys)
  {
    reveal Seq.HasNoDuplicates();
    reveal Seq.ToSet();
    var zs := xs + ys;
    if |zs| > 1 {
      assert forall i :: 0 <= i < |xs| ==> zs[i] in Seq.ToSet(xs);
      assert forall j :: |xs| <= j < |zs| ==> zs[j] in Seq.ToSet(ys);
      assert forall i, j :: 0 <= i < |xs| <= j < |zs| ==> zs[i] != zs[j];
    }
  }

  lemma ConcatSeqToSet<T>(a: seq<T>, b: seq<T>)
    ensures Seq.ToSet(a + b) == Seq.ToSet(a) + Seq.ToSet(b)
  {
    reveal Seq.ToSet();
  }

}
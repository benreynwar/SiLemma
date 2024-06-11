module Utils {

  import Std.Collections.Seq
  import Std.Collections.Map

  predicate SetsNoIntersection<T>(a: set<T>, b: set<T>)
  {
    a !! b
  }

  predicate SeqsNoIntersection<T(==)>(a: seq<T>, b: seq<T>)
  {
    Seq.ToSet(a) !! Seq.ToSet(b)
  }

  predicate SeqsNoIntersectionByIndex<T(==)>(a: seq<T>, b: seq<T>)
  {
    !exists index1: nat, index2: nat :: index1 < |a| && index2 < |b| && a[index1] == b[index2]
  }

  lemma SeqsNoIntersectionEquiv<T>(a: seq<T>, b: seq<T>)
    ensures SeqsNoIntersection(a, b) == SeqsNoIntersectionByIndex(a, b)
  {
    if !SeqsNoIntersectionByIndex(a, b) {
        var index1: nat, index2: nat :| index1 < |a| && index2 < |b| && a[index1] == b[index2];
        assert a[index1] in a;
        assert a[index1] in b;
        reveal Seq.ToSet();
        assert a[index1] in Seq.ToSet(a);
        assert a[index1] in Seq.ToSet(b);
        assert a[index1] in Seq.ToSet(a) * Seq.ToSet(b);
        assert !SeqsNoIntersection(a, b);
    }
    if !SeqsNoIntersection(a, b) {
      var value :| value in Seq.ToSet(a) * Seq.ToSet(b);
      reveal Seq.ToSet();
      assert value in a;
      assert value in b;
    }
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

  function ChunkSeq<T>(a: seq<T>, n_chunks: nat, chunk_size: nat): (r: seq<seq<T>>)
    requires |a| == n_chunks * chunk_size
    ensures chunk_size * |r| == |a|
    ensures forall c :: c in r ==> |c| == chunk_size
  {
    if n_chunks == 0 then
      []
    else
      ChunkSeq(a[..|a|-chunk_size], n_chunks-1, chunk_size) + [a[(|a|-chunk_size)..]]
  }

  lemma ChunkSeqSingle<T>(a: seq<T>)
    ensures ChunkSeq(a, 1, |a|) == [a]
  {
  }

  function DivMod(a: nat, b: nat): (r: (nat, nat))
    requires b > 0
    ensures r.0 * b + r.1 == a
    ensures r.1 < b
  {
    if a < b then
      (0, a)
    else
      var (p, q) := DivMod(a - b, b);
      (p + 1, q)
  }

  lemma DivModHelper(a: nat, n_chunks: nat, chunk_size: nat)
    requires a < n_chunks * chunk_size
    ensures
      var (p, q) := DivMod(a, chunk_size);
      p < n_chunks
  {
  }

  function JoinSets<T(!new)>(a: seq<set<T>>): (r: set<T>)
    ensures forall x: T :: (exists b :: b in a && x in b) == (x in r)
  {
    if |a| == 0 then
      {}
    else
      a[0] + JoinSets(a[1..])
  }

  function UnchunkSeq<T>(a: seq<seq<T>>, n_chunks: nat, chunk_size: nat): (r: seq<T>)
    requires |a| == n_chunks
    requires forall c :: c in a ==> |c| == chunk_size
    ensures |r| == n_chunks * chunk_size
  {
    var r := seq(n_chunks*chunk_size, (index: nat) requires index < n_chunks*chunk_size =>
      var (chunk_index, index_in_chunk) := DivMod(index, chunk_size);
      a[chunk_index][index_in_chunk]);
    r
  }

  ghost predicate NoDuplicatesNoIntersections<T>(a: seq<seq<T>>)
  {
    && (forall index: nat :: index < |a| ==> Seq.HasNoDuplicates(a[index]))
    && (forall index1: nat, index2: nat :: index1 < |a| && index2 < |a| && (index1 != index2) ==>
      SeqsNoIntersection(a[index1], a[index2]))
  }

  ghost predicate SeqSeqsNoIntersection<T>(a: seq<seq<T>>, b: seq<seq<T>>)
  {
    forall index1: nat, index2: nat :: index1 < |a| && index2 < |b| ==> SeqsNoIntersection(a[index1], b[index2])
  }

  lemma UnchunkSeqNoDuplicates<T>(a: seq<seq<T>>, n_chunks: nat, chunk_size: nat)
    requires |a| == n_chunks
    requires forall c :: c in a ==> |c| == chunk_size
    requires NoDuplicatesNoIntersections(a)
    ensures Seq.HasNoDuplicates(UnchunkSeq(a, n_chunks, chunk_size))
  {
    var r := UnchunkSeq(a, n_chunks, chunk_size);
    forall index1: nat, index2: nat | index1 < |r| && index2 < |r| && index1 != index2
      ensures r[index1] != r[index2]
    {
      var (p1, q1) := DivMod(index1, chunk_size);
      DivModHelper(index1, n_chunks, chunk_size);
      var (p2, q2) := DivMod(index2, chunk_size);
      DivModHelper(index2, n_chunks, chunk_size);
      assert r[index1] == a[p1][q1];
      assert r[index2] == a[p2][q2];
      if p1 == p2 {
        assert q1 != q2;
        assert a[p1][q1] != a[p2][q2] by {
          reveal Seq.HasNoDuplicates();
        }
      } else {
        assert Seq.ToSet(a[p1]) !! Seq.ToSet(a[p2]);
        reveal Seq.ToSet();
        assert a[p1][q1] in Seq.ToSet(a[p1]);
        assert a[p1][q1] !in Seq.ToSet(a[p2]);
        assert a[p2][q2] in Seq.ToSet(a[p2]);
        assert a[p1][q1] != a[p2][q2];
      }
    }
    reveal Seq.HasNoDuplicates();
  }

  lemma UnchunkSeqsNoIntersection<T>(a: seq<seq<T>>, b: seq<seq<T>>, n_chunks_a: nat, chunk_size_a: nat, n_chunks_b: nat, chunk_size_b: nat)
    requires |a| == n_chunks_a
    requires forall c :: c in a ==> |c| == chunk_size_a
    requires |b| == n_chunks_b
    requires forall c :: c in b ==> |c| == chunk_size_b
    requires NoDuplicatesNoIntersections(a)
    requires NoDuplicatesNoIntersections(b)
    requires SeqSeqsNoIntersection(a, b)
    ensures SeqsNoIntersection(UnchunkSeq(a, n_chunks_a, chunk_size_a), UnchunkSeq(b, n_chunks_b, chunk_size_b))
  {
    var uca := UnchunkSeq(a, n_chunks_a, chunk_size_a);
    var ucb := UnchunkSeq(b, n_chunks_b, chunk_size_b);
    forall index1: nat, index2: nat | index1 < n_chunks_a*chunk_size_a && index2 < n_chunks_b*chunk_size_b
      ensures uca[index1] != ucb[index2]
    {
      var (p1, q1) := DivMod(index1, chunk_size_a);
      DivModHelper(index1, n_chunks_a, chunk_size_a);
      var (p2, q2) := DivMod(index2, chunk_size_b);
      DivModHelper(index2, n_chunks_b, chunk_size_b);
      assert uca[index1] == a[p1][q1];
      assert ucb[index2] == b[p2][q2];
      assert SeqsNoIntersection(a[p1], b[p2]);
      SeqsNoIntersectionEquiv(a[p1], b[p2]);
      assert a[p1][q1] != b[p2][q2];
    }
    SeqsNoIntersectionEquiv(uca, ucb);
  }

}
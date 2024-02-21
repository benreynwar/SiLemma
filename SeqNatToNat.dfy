module SeqNatToNat {

  import opened Std.Wrappers

  // Define functions that take a Seq<nat> and convert it
  // reversibly to a single nat.

  // The approach take is to:
  // 1) Split each nat into bits (Seq<bool).
  // 2) Interleave those bits.
  // 3) Convert the bits back into a new nat.

  // Pop a bit off a nat (lsb).
  function PopBit(n: nat): (r: (bool, nat))
  {
    var b := n % 2 == 1;
    (b, if b then (n-1)/2 else n/2)
  }

  // Push a bit onto a nat (lsb).
  function PushBit(b: bool, n: nat): (r: nat)
  {
    (if b then 1 else 0) + 2 * n
  }

  function divmod(n: nat, d: nat): (r: (nat, nat))
    requires d > 0
    decreases n
    ensures n == r.0 + r.1*d
    ensures r.0 < d
  {
    if n < d then
      (n, 0)
    else
      var (r1, r2) := divmod(n-d, d);
      (r1, r2+1)
  }

  function divmodinv(rem: nat, quot: nat, d: nat): nat
    requires rem < d
    requires d > 0
  {
    rem + quot * d
  }

  lemma RemoveLTFactor(a: nat, b: nat, f: nat)
    requires a*f < b*f
    ensures a < b
  {
  }

  lemma divmodUnique(rem1: nat, quot1: nat, rem2: nat, quot2: nat, d: nat)
    requires d > 0
    requires rem1 < d
    requires rem2 < d
    requires divmodinv(rem1, quot1, d) == divmodinv(rem2, quot2, d)
    ensures rem1 == rem2
    ensures quot1 == quot2
  {
    var n := divmodinv(rem1, quot1, d);
    assert n == divmodinv(rem2, quot2, d);
    assert n < d+quot2*d;
    assert n < d+quot1*d;
    assert n >= quot2*d;
    assert n >= quot1*d;
    assert quot1*d < d+quot2*d;
    RemoveLTFactor(quot1, 1+quot2, d);
    assert quot1 < 1+quot2;
    assert quot2*d < d+quot1*d;
    RemoveLTFactor(quot2, 1+quot1, d);
    assert quot2 < 1+quot1;
    assert quot1 == quot2;
    assert rem1+quot1*d == rem2+quot2*d;
    assert rem1 == rem2;
  }

  lemma divmodinvdivmod(rem: nat, quot: nat, d: nat)
    requires rem < d
    requires d > 0
    ensures
      var n := divmodinv(rem, quot, d);
      divmod(n, d) == (rem, quot)
    decreases quot
  {
      var n := divmodinv(rem, quot, d);
      assert n == rem + quot*d;
      if n < d {
        assert divmod(n, d) == (rem, quot);
      } else {
        var (rem2, quot2) := divmod(n-d, d);
        divmodinvdivmod(rem2, quot2, d);
        assert divmod(n-d, d) == (rem2, quot2);
        assert divmod(n, d) == (rem2, quot2+1);
        assert n-d == rem2 + quot2*d;
        assert n == rem2 + (quot2+1)*d;
        divmodUnique(rem, quot, rem2, quot2+1, d);
        assert rem == rem2;
        assert quot == quot2+1;
        assert divmod(n, d) == (rem, quot);
      }

  }

  lemma divmodDecreases(n: nat, d: nat)
    requires d > 1
    requires n > 0
    ensures
      var (r, q) := divmod(n, d);
      q < n
    decreases n
  {
  }

  lemma PushPop(b: bool, n: nat)
    ensures
      var r := PushBit(b, n);
      PopBit(r) == (b, n)
  {
  }

  function BitsToNat(ns: seq<bool>): (r: nat)
    decreases |ns|
    ensures r < pow2(|ns|)
  {
    if |ns| == 0 then
      0
    else
      var h := ns[0];
      var t: nat := BitsToNat(ns[1..]);
      PushBit(h, t)
  }

  function BitsToNatRev(ns: seq<bool>): (r: nat)
    decreases |ns|
    ensures r < pow2(|ns|)
  {
    if |ns| == 0 then
      0
    else
      var h := ns[|ns|-1];
      var t := BitsToNatRev(ns[..|ns|-1]);
      t + if h then pow2(|ns|-1) else 0
  }

  //lemma BitsToNatEquiv(ns: seq<bool>)
  //  ensures BitsToNat(ns) == BitsToNatRev(ns)
  //{
  //}

  lemma BitsToNatNotZero(ns: seq<bool>)
    requires exists index: nat :: index < |ns| && ns[index]
    ensures BitsToNat(ns) > 0
  {
  }

  function NatToBits(n: nat, l: nat): (r: seq<bool>)
    requires n < pow2(l)
    ensures |r| == l
  {
    if l == 0 then
      []
    else
      var (h, t) := PopBit(n);
      [h] + NatToBits(t, l-1)
  }

  lemma BitsToNatToBits(ns: seq<bool>)
    ensures NatToBits(BitsToNat(ns), |ns|) == ns
    decreases |ns|
  {
    if |ns| == 0 {
      var n: nat := BitsToNat(ns);
      var r: seq<bool> := NatToBits(n, |ns|);
      assert r == ns;
    } else {
      var new_ns := NatToBits(BitsToNat(ns), |ns|);
      assert new_ns == NatToBits(PushBit(ns[0], BitsToNat(ns[1..])), |ns|);
      var (h, t) := PopBit(PushBit(ns[0], BitsToNat(ns[1..])));
      PushPop(ns[0], BitsToNat(ns[1..]));
      assert h == ns[0];
      assert t == BitsToNat(ns[1..]);
      assert new_ns == [h] + NatToBits(BitsToNat(ns[1..]), |ns|-1);
      BitsToNatToBits(ns[1..]);
      assert new_ns == [h] + ns[1..];
      assert new_ns == ns;
    }
  }

  lemma {:vcs_split_on_every_assert} NatToBitsToNat(n: nat, l: nat)
    requires n < pow2(l)
    ensures BitsToNat(NatToBits(n, l)) == n
    decreases l
  {
    if l == 0 {
      assert n == 0;
      assert BitsToNat(NatToBits(n, l)) == n;
    } else {
      var b := n % 2 == 1;
      var new_n := if b then (n-1)/2 else n/2;
      calc {
        BitsToNat(NatToBits(n, l));
        BitsToNat([b] + NatToBits(new_n, l-1));
        n % 2 + 2*BitsToNat(NatToBits(new_n, l-1));
        {NatToBitsToNat(new_n, l-1);}
        n % 2 + 2*new_n;
        n;
      }
    }
  }

  function ShiftLeftOne(n: nat): (r: nat)
  {
    if n % 2 == 0 then
      n/2
    else
      (n-1)/2
  }

  lemma SplitLowestBit(n: nat)
    ensures n == n % 2 + 2*ShiftLeftOne(n)
  {
  }

  lemma IsLowestBit(n: nat, a: nat, b: nat)
    requires a < 2
    requires n == a + 2 * b
    ensures a == n % 2
  {
  }

  function Max(ns: seq<nat>): (r: nat)
    requires |ns| > 0
    ensures r in ns
    ensures forall index: nat | index < |ns| :: ns[index] <= r
  {
    if |ns| == 1 then
      ns[0]
    else
      var max_later := Max(ns[1..]);
      if ns[0] > max_later then
        ns[0]
      else
        max_later
  }

  function pow2(n: nat): (r: nat)
    ensures r > 0
    decreases n
  {
    if n == 0 then
      1
    else
      2 * pow2(n-1)
  }

  function {:opaque} PopLowBits(ns: seq<nat>): (r: seq<bool>)
    requires |ns| > 0
    ensures |r| == |ns|
  {
    seq(|ns|, i requires 0<= i < |ns| => ns[i] % 2 == 1)
  }

  predicate HasTrueElement(b: seq<bool>)
  {
    exists index: nat :: index < |b| && b[index]
  }

  lemma PopLowBitsMaxOne(ns: seq<nat>)
    requires |ns| > 0
    requires Max(ns) == 1
    ensures
      var r := PopLowBits(ns);
      HasTrueElement(r)
  {
    var r := PopLowBits(ns);
    var index: nat :| index < |ns| && ns[index] == Max(ns);
    reveal PopLowBits();
    assert r[index];
    assert HasTrueElement(r);
  }

  function {:opaque} PopUpperBits(ns: seq<nat>): (r: seq<nat>)
    requires |ns| > 0
    ensures |r| == |ns|
    ensures Max(ns) > 0 ==> Max(r) < Max(ns)
  {
    seq(|ns|, i requires 0 <= i < |ns| => ShiftLeftOne(ns[i]))
  }

  lemma PopUpperBitsNonZero(ns: seq<nat>)
    requires |ns| > 0
    requires Max(ns) > 1
    ensures Max(PopUpperBits(ns)) > 0
  {
    var r := PopUpperBits(ns);
    var max_index: nat :| max_index < |ns| && ns[max_index] == Max(ns);
    reveal PopUpperBits();
    assert r[max_index] == ShiftLeftOne(ns[max_index]);
  }

  function NatsToNat(ns: seq<nat>): (r: nat)
    requires |ns| > 0
    decreases Max(ns)
  {
    var max := Max(ns);
    if max == 0 then
      0
    else
      var line := PopLowBits(ns);
      var reduced_ns := PopUpperBits(ns);
      divmodinv(BitsToNat(line), NatsToNat(reduced_ns), pow2(|ns|))
  }

  function {:opaque} PushBits(head: seq<bool>, tail: seq<nat>): (r: seq<nat>)
    requires |head| == |tail|
    ensures |r| == |head|
  {
      var l := |head|;
      seq(l, i requires 0 <= i < l => (if head[i] then 1 else 0) + 2*tail[i])
  }

  function NatToNats(n: nat, l: nat): (r: seq<nat>)
    requires l > 0
    decreases n
  {
    if n == 0 then
      seq(l, i requires 0 <= i < l => 0)
    else
      assert pow2(l) > 1;
      var (rem, quot) := divmod(n, pow2(l));
      var head: seq<bool> := NatToBits(rem, l);
      assert |head| == l;
      var tail: seq<nat> := NatToNats(quot, l);
      assert |tail| == l;
      PushBits(head, tail)
  }

  lemma NatsToNatToNatsPartial(ns: seq<nat>)
    requires |ns| > 0
    ensures PushBits(PopLowBits(ns), PopUpperBits(ns)) == ns
  {
      var line := PopLowBits(ns);
      var reduced_ns := PopUpperBits(ns);
      reveal PopLowBits();
      reveal PopUpperBits();
      reveal PushBits();
      var merged := PushBits(line, reduced_ns);
      assert merged == ns;
  }

  lemma MultBothGreaterZero(a: nat, b: nat)
    requires a > 0
    requires b > 0
    ensures a * b > 0
  {
  }

  predicate AllZeros(ns: seq<nat>)
  {
    forall i: nat :: i < |ns| ==> ns[i] == 0
  }

  lemma TrueGivesNonZero(n: nat, l: nat)
    requires n < pow2(l)
    requires true in NatToBits(n, l)
    ensures n > 0
  {
  }

  lemma AllFalseGivesZero(n: nat, l: nat)
    requires n < pow2(l)
    requires !(true in NatToBits(n, l))
    ensures n == 0
  {
  }

  lemma {:vcs_split_on_every_assert} NatToNatsNonZero(n: nat, l: nat)
    requires n > 0
    requires l > 0
    ensures Max(NatToNats(n, l)) > 0
  {
    assert pow2(l) > 1;
    var exn := NatToNats(n, l);
    var (rem, quot) := divmod(n, pow2(l));
    assert rem < pow2(l);
    var head: seq<bool> := NatToBits(rem, l);
    assert |head| == l;
    var tail: seq<nat> := NatToNats(quot, l);
    assert |tail| == l;
    var expanded := PushBits(head, tail);
    assert expanded == NatToNats(n, l);
    reveal PushBits();
    if true in head {
      TrueGivesNonZero(rem, l);
      assert rem > 0;
      var index: nat :| index < l && head[index];
      assert expanded[index] > 0;
      assert Max(NatToNats(n, l)) > 0;
    } else {
      AllFalseGivesZero(rem, l);
      assert rem == 0;
      assert quot > 0;
      NatToNatsNonZero(quot, l);
      assert Max(tail) > 0;
      var index: nat :| index < l && tail[index] > 0;
      assert expanded[index] > 0;
      assert Max(NatToNats(n, l)) > 0;
    }
  }

  lemma {:vcs_split_on_every_assert} NatsToNatNonZero(ns: seq<nat>)
    requires |ns| > 0
    requires Max(ns) > 0
    ensures NatsToNat(ns) > 0
    decreases Max(ns)
  {
      var max := Max(ns);
      var max_index: nat :| max_index < |ns| && ns[max_index] == max;
      var line := PopLowBits(ns);
      var reduced_ns := PopUpperBits(ns);
      if max == 1 {
        PopLowBitsMaxOne(ns);
        BitsToNatNotZero(line);
        assert BitsToNat(line) > 0;
      } else {
        PopUpperBitsNonZero(ns);
        NatsToNatNonZero(reduced_ns);
        assert NatsToNat(reduced_ns) > 0;
      }
      assert NatsToNat(ns) == divmodinv(BitsToNat(line), NatsToNat(reduced_ns), pow2(|ns|));
      if max == 1 {
        assert BitsToNat(line) > 0;
        assert NatsToNat(ns) > 0;
      } else {
        assert NatsToNat(reduced_ns) > 0;
        assert pow2(|ns|) > 0;
        MultBothGreaterZero(pow2(|ns|), NatsToNat(reduced_ns));
        assert pow2(|ns|)*NatsToNat(reduced_ns) > 0;
        assert NatsToNat(ns) > 0;
      }

  }

  lemma {:vcs_split_on_every_assert} NatsToNatToNats(ns: seq<nat>)
    requires |ns| > 0
    ensures NatToNats(NatsToNat(ns), |ns|) == ns
    decreases Max(ns)
  {
    if Max(ns) == 0 {
      assert NatsToNat(ns) == 0;
      assert NatToNats(NatsToNat(ns), |ns|) == ns;
    } else {
      var n := NatsToNat(ns);
      NatsToNatNonZero(ns);
      assert n > 0;
      var l := |ns|;
      var line := PopLowBits(ns);
      var reduced_ns := PopUpperBits(ns);
      assert n == divmodinv(BitsToNat(line), NatsToNat(reduced_ns), pow2(l));
      var (rem, quot) := divmod(n, pow2(l));
      divmodUnique(rem, quot, BitsToNat(line), NatsToNat(reduced_ns), pow2(l));
      var new_ns := NatToNats(NatsToNat(ns), |ns|);
      assert new_ns == NatToNats(divmodinv(BitsToNat(line), NatsToNat(reduced_ns), pow2(l)), l);
      assert new_ns == NatToNats(divmodinv(rem, quot, pow2(l)), l);
      var head: seq<bool> := NatToBits(rem, l);
      assert |head| == l;
      var tail: seq<nat> := NatToNats(quot, l);
      assert new_ns == PushBits(head, tail);
      assert head == NatToBits(BitsToNat(line), l);
      BitsToNatToBits(line);
      assert head == line;
      NatsToNatToNats(reduced_ns);
      assert tail == NatToNats(NatsToNat(reduced_ns), l);
      assert tail == reduced_ns;
      assert new_ns == PushBits(line, reduced_ns);
      assert new_ns == PushBits(PopLowBits(ns), PopUpperBits(ns));
      NatsToNatToNatsPartial(ns);
      assert new_ns == ns;
    }
  }

  lemma NatToNatsToNatPartial(head: seq<bool>, tail: seq<nat>)
    requires |head| > 0
    requires |head| == |tail|
    ensures PopLowBits(PushBits(head, tail)) == head
    ensures PopUpperBits(PushBits(head, tail)) == tail
  {
      reveal PushBits();
      reveal PopLowBits();
      reveal PopUpperBits();
  }

  lemma {:vcs_split_on_every_assert} NatToNatsToNat(n: nat, l: nat)
    requires l > 0
    ensures NatsToNat(NatToNats(n, l)) == n
    decreases n
  {
    if n == 0 {
        assert NatsToNat(NatToNats(n, l)) == n;
    } else {
        var ns := NatToNats(n, l);
        NatToNatsNonZero(n, l);
        assert Max(ns) > 0;
        var new_n := NatsToNat(NatToNats(n, l));
        var (rem, quot) := divmod(n, pow2(l));
        var head: seq<bool> := NatToBits(rem, l);
        var tail: seq<nat> := NatToNats(quot, l);
        assert new_n == NatsToNat(PushBits(head, NatToNats(quot, l)));
        assert ns == PushBits(head, NatToNats(quot, l));
        NatToNatsToNatPartial(head, tail);
        assert PopLowBits(ns) == head;
        assert PopUpperBits(ns) == tail;
        assert new_n == divmodinv(BitsToNat(head), NatsToNat(tail), pow2(l));
        NatToNatsToNat(quot, l);
        assert NatsToNat(NatToNats(quot, l)) == quot;
        assert new_n == divmodinv(BitsToNat(head), quot, pow2(l));
        NatToBitsToNat(rem, l);
        assert new_n == divmodinv(rem, quot, pow2(l));
        assert NatsToNat(NatToNats(n, l)) == n;
    }
  }

  function ArbLenNatsToNat(ns: seq<nat>): nat
  {
    if |ns| == 0 then
      0
    else
      var n_body := NatsToNat(ns);
      NatsToNat([|ns|, n_body])
  }

  function NatToArbLenNats(n: nat): seq<nat>
  {
    if n == 0 then
      []
    else
      var l_and_v := NatToNats(n, 2);
      var l := l_and_v[0];
      var v := l_and_v[1];
      if l == 0 then
        []
      else
        NatToNats(v, l)
  }

  lemma ArbLenNatsLengthCorrect(a: seq<nat>)
    ensures 
      var n := ArbLenNatsToNat(a);
      var l := NatToNats(n, 2)[0];
      l == |a|
  {
    var n := ArbLenNatsToNat(a);
    var l := NatToNats(n, 2)[0];
    if a == [] {
    } else {
      var n_body := NatsToNat(a);
      assert n == NatsToNat([|a|, n_body]);
      NatsToNatToNats([|a|, n_body]);
      assert NatToNats(n, 2) == [|a|, n_body];
    }
  }
      
  lemma {:vcs_split_on_every_assert} ArbLenNatsToNatUnique(a: seq<nat>, b: seq<nat>)
    ensures a != b ==> ArbLenNatsToNat(a) != ArbLenNatsToNat(b)
  {
    var a_n := ArbLenNatsToNat(a);
    var b_n := ArbLenNatsToNat(b);
    var a_l_and_v := NatToNats(a_n, 2);
    var b_l_and_v := NatToNats(b_n, 2);
    var a_l := a_l_and_v[0];
    var b_l := b_l_and_v[0];
    ArbLenNatsLengthCorrect(a);
    ArbLenNatsLengthCorrect(b);
    assert a_l == |a|;
    assert b_l == |b|;
    if (|a| != |b|) {
    } else {
      if |a| == 0 {
      } else {
        var a_body := NatsToNat(a);
        var b_body := NatsToNat(b);
        var a_n := NatsToNat([|a|, a_body]);
        var b_n := NatsToNat([|b|, b_body]);
        NatsToNatToNats(a);
        NatsToNatToNats(b);
        NatsToNatToNats([|a|, a_body]);
        NatsToNatToNats([|b|, b_body]);
        if a != b {
          assert a_body != b_body;
          assert a_n != b_n;
        }
      }
    }
  }

  function {:vcs_split_on_every_assert} NatsToNatBound(l: nat, bound: nat): nat
    requires l > 0
  {
    var bound_ns := seq(l, i requires 0 <= i < l => bound);
    NatsToNat(bound_ns)
  }

  function {:vcs_split_on_every_assert} ArbLenNatsToNatBound(max_length: nat, bound: nat): nat
    requires max_length > 0
  {
    var bound_ns := seq(max_length, i requires 0 <= i < max_length => bound);
    ArbLenNatsToNat(bound_ns)
  }

  lemma {:vcs_split_on_every_assert} BoundIncreasesWithLength(la: nat, lb: nat, bound: nat)
    requires la > 0
    requires lb > la
    ensures NatsToNatBound(la, bound) < NatsToNatBound(lb, bound)
  {
  }

  lemma {:vcs_split_on_every_assert} ArbLenBoundIncreasesWithLength(la: nat, lb: nat, bound: nat)
    requires la > 0
    requires lb > la
    ensures ArbLenNatsToNatBound(la, bound) < ArbLenNatsToNatBound(lb, bound)
  {
  }

  lemma {:vcs_split_on_every_assert} ArbLenNatsToNatBounded(a: seq<nat>, max_length: nat, bound: nat)
    requires |a| > 0
    requires |a| <= max_length
    requires forall i : nat :: i < |a| ==> a[i] < bound
    ensures ArbLenNatsToNat(a) < ArbLenNatsToNatBound(max_length, bound)
  {
  }

  lemma ArbLenNatsToNatOutOfBoundElementOutOfBound(a: seq<nat>, max_length: nat, bound: nat)
    requires |a| > 0
    requires |a| <= max_length
    requires ArbLenNatsToNat(a) >= ArbLenNatsToNatBound(max_length, bound)
    ensures exists i: nat :: i < |a| && a[i] >= bound
  {
    if !exists i: nat :: i < |a| && a[i] >= bound {
      assert forall i: nat :: i< |a| ==> a[i] < bound;
      ArbLenNatsToNatBounded(a, max_length, bound);
    } else {
    }
  }
}

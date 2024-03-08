
module Utils {

    import Std.Collections.Seq

    lemma SeqSize(ns: seq<nat>, bound: nat)
        requires Seq.HasNoDuplicates(ns)
        requires forall x :: x in ns ==> x < bound
        ensures |ns| <= bound
    {
        var s := Seq.ToSet(ns);
        reveal Seq.ToSet();
        Seq.LemmaCardinalityOfSetNoDuplicates(ns);
        assert |s| == |ns|;
        BoundedSetSize(bound, s);
    }

    lemma SeqIncrease(ns: seq<nat>, n: nat, bound: nat)
        requires Seq.HasNoDuplicates(ns)
        requires forall x :: x in ns ==> x < bound
        requires n < bound
        requires n !in ns
        ensures |ns| <= bound
        ensures forall x :: x in ns+[n] ==> x < bound
        ensures |ns+[n]| <= bound
        ensures |ns+[n]| == |ns| + 1
    {
        var nsn := ns + [n];
        reveal Seq.HasNoDuplicates();
        SeqSize(nsn, bound);
    }

    lemma AllBelowBoundSize(bound: nat)
        ensures
            var below := set n : nat | n < bound :: n;
            |below| ==  bound
        decreases bound
    {
        if bound == 0 {
        } else {
            AllBelowBoundSize(bound-1);
            var belowminus := (set n : nat | n < bound-1 :: n);
            var below := (set n : nat | n < bound :: n);
            assert below == belowminus + {bound-1};
        }
    }

    lemma SizeOfContainedSet(a: set<nat>, b: set<nat>)
        requires forall n: nat :: n in a ==> n in b
        ensures |a| <= |b|
        decreases |a|
    {
        if |a| == 0 {
        } else {
            var y :| y in a;
            var new_a := a - {y};
            var new_b := b - {y};
            SizeOfContainedSet(new_a, new_b);
        }
    }

    lemma BoundedSetSize(bound: nat, values: set<nat>)
        requires forall n :: n in values ==> n < bound
        ensures |values| <= bound
    {
        var all_below_bound := set n : nat | n < bound :: n;
        AllBelowBoundSize(bound);
        assert |all_below_bound| == bound;
        assert forall n :: n in values ==> n in all_below_bound;
        SizeOfContainedSet(values, all_below_bound);
    }

    lemma MappedSetSize<T, U>(s: set<T>, f: T->U, t: set<U>)
        requires forall n: T, m: T :: m != n ==> f(n) != f(m)
        requires t == set n | n in s :: f(n)
        ensures |s| == |t|
        decreases |s|
    {
        var t := set n | n in s :: f(n);
        if |s| == 0 {
        } else {
            var y :| y in s;
            var new_s := s - {y};
            var new_t := t - {f(y)};
            assert new_t == set n | n in new_s :: f(n);
            MappedSetSize(new_s, f, new_t);
        }
    }

    lemma SetSizes<T>(a: set<T>, b: set<T>, c: set<T>)
        requires c == a + b
        requires forall t: T :: t in a ==> t !in b
        requires forall t: T :: t in b ==> t !in a
        ensures |c| == |a| + |b|
    {
    }

    lemma SetSizeOne<T>(s: set<T>, x: T)
        requires x in s
        requires |s| == 1
        ensures s == {x}
    {
        var y :| y in s;
        var new_s := s - {y};
        assert s == new_s + {y};
    }

    ghost predicate GEValid<T(!new)>(ge: (T, T)->bool)
    {
        (forall a: T, b: T, c: T :: ge(a, b) && ge(b, c) ==> ge(a, c)) &&
        (forall a: T :: ge(a, a)) &&
        (forall a: T, b: T :: ge(a, b) || ge(b, a))
    }

    function Max<T>(ge: (T, T)->bool, a: T, b: T): (r: T)
        requires GEValid(ge)
        ensures ge(r, a)
        ensures ge(r, b)
    {
        if ge(a, b) then a else b
    }

    ghost function MaxInSet<T>(ge: (T, T)->bool, s: set<T>): (r: T)
        requires GEValid(ge)
        requires |s| > 0
        decreases |s|
        ensures
            forall x :: x in s ==> ge(r, x)
    {
        var x :| x in s;
        if |s| == 1 then
            SetSizeOne(s, x);
            x
        else
            var new_s := s - {x};
            var new_max := MaxInSet(ge, new_s);
            var max := Max(ge, x, new_max);
            max
    }

    predicate IsOrder(l: nat, order: seq<nat>)
    {
        (|order| == l) &&
        (forall index: nat :: index < l ==> index in order)
    }

    ghost predicate Commutative<T(!new)>(op: (T, T)->T)
    {
        forall a: T, b: T :: op(a, b) == op(b, a)
    }
    ghost predicate Associative<T(!new)>(op: (T, T)->T)
    {
        forall a: T, b: T, c: T :: op(a, op(b, c)) == op(op(a, b), c)
    }
    predicate IsReordering<T(==)>(a: seq<T>, b: seq<T>)
    {
        multiset(a) == multiset(b)
    }

    function LeftFold<T>(op: (T, T)->T, start:T, s: seq<T>): T
    {
        if |s| == 0 then
            start
        else
            op(s[0], LeftFold(op, start, s[1..]))
    }

    function Switch<T>(a: seq<T>, index: nat): (r: seq<T>)
        requires index > 0
        requires index < |a|
        //ensures multiset(a) == multiset(r)
    {
        var r := a[..index-1] + [a[index]] + [a[index-1]] + a[index+1..];
        r
    }

    lemma LeftFoldMoveLeftInsensitive<T>(op: (T, T)->T, start: T, a: seq<T>, index: nat)
        requires index > 0
        requires index < |a|
        //ensures
        //    var b := MoveLeft(a, index);
        //    LeftFold(op, start, a) == LeftFold(op, start, b)
    {
        if index > 1 {
            LeftFoldMoveLeftInsensitive(op, start, a[1..], index-1);
        } else {
        }
    }

    //lemma LeftFoldOrderInsensitive<T>(op: (T, T)->T, start: T, a: seq<T>, b: seq<T>)
    //    requires Commutative(op)
    //    requires Associative(op)
    //    requires IsReordering(a, b)
    //    ensures LeftFold(op, start, a) == LeftFold(op, start, b)
    //{

    //}


            //assert x < |hpnps|;
            //assert x + y*|hpnps| == n;
            //assert x + y*|hpnps| < |hpnps|*|hpnps|;
            //assert |hpnps| + y*|hpnps| <= |hpnps|*|hpnps|;
            //assert (1+y)*|hpnps| <= |hpnps|*|hpnps|;
            //assert (1+y) <= |hpnps|;
            //assert y < |hpnps|;


}
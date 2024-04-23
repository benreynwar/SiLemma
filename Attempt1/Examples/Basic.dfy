module Basic {

    function xor(a: bool, b: bool): bool
    {
        (a && !b) || (!a && b)
    }

    function BitAdder(a1a: bool, a1b: bool, a1c: bool): (r: (bool, bool))
    {
        var b1a := xor(a1a, a1b);
        var b1b := a1c;
        var b2a := a1a && a1b;

        var c1a := xor(b1a, b1b);
        var c2a := b1a && b1b;
        var c2b := b2a;

        var d1a := c1a;
        var d2a := xor(c2a, c2b);
        var d3a := c2a && c2b;

        assert !d3a;

        assert ((a1a, a1b, a1c) == (false, true, false)) ==> d1a && !d2a;

        (d1a, d2a)
    }

    predicate IsBitAdderCorrect(a1a: bool, a1b: bool, a1c: bool)
    {
        var r := BitAdder(a1a, a1b, a1c);
        BoolToNat(a1a) + BoolToNat(a1b) + BoolToNat(a1c) == SeqBoolToNat([r.0, r.1])
    }

    lemma BitAdderCorrect(a1a: bool, a1b: bool, a1c: bool)
        ensures IsBitAdderCorrect(a1a, a1b, a1c)
    {
        assert IsBitAdderCorrect(false, false, false);
        assert IsBitAdderCorrect(false, false, true);
        assert IsBitAdderCorrect(false, true, false);
        assert IsBitAdderCorrect(false, true, true);
        assert IsBitAdderCorrect(true, false, false);
        assert IsBitAdderCorrect(true, false, true);
        assert IsBitAdderCorrect(true, true, false);
        assert IsBitAdderCorrect(true, true, true);
    }


    function Adder(a: seq<bool>, b: seq<bool>, c: bool): (r: seq<bool>)
        requires |a| == |b|
        ensures |r| == |a| + 1
    {
        if |a| == 0 then
            [c]
        else
            var a_tail := a[..|a|-1];
            var b_tail := b[..|b|-1];
            var r_tail := Adder(a_tail, b_tail, c);
            var head_c := r_tail[|r_tail|-1];
            var (head1, head2) := BitAdder(a[|a|-1], b[|b|-1], head_c);
            r_tail[..|r_tail|-1] + [head1, head2]
    }

    predicate IsAdderCorrect(a: seq<bool>, b: seq<bool>, c: bool)
        requires |a| == |b|
    {
        var r := Adder(a, b, c);
        SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == SeqBoolToNat(r)
    }

    lemma AdderCorrectSanityHelper(a: nat, b: seq<bool>, c: bool, d: bool)
        requires a == SeqBoolToNat(b + [c] + [d])
        ensures a == SeqBoolToNat(b + [c, d])
    {
        assert b + [c] + [d] == b + [c, d];
    }

    lemma AdderCorrect(a: seq<bool>, b: seq<bool>, c: bool)
        requires |a| == |b|
        ensures IsAdderCorrect(a, b, c)
    {
        if |a| == 0 {
        } else {
            var a_tail := a[..|a|-1];
            var b_tail := b[..|b|-1];
            var r_tail := Adder(a_tail, b_tail, c);
            AdderCorrect(a_tail, b_tail, c);
            var MSBValue := pow2(|a|-1);
            assert SeqBoolToNat(a) == SeqBoolToNat(a_tail) + BoolToNat(a[|a|-1])*MSBValue;
            assert SeqBoolToNat(b) == SeqBoolToNat(b_tail) + BoolToNat(b[|a|-1])*MSBValue;
            assert SeqBoolToNat(a_tail) + SeqBoolToNat(b_tail) + BoolToNat(c) == SeqBoolToNat(r_tail);
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == 
                SeqBoolToNat(a_tail) + SeqBoolToNat(b_tail) + BoolToNat(c) + (BoolToNat(a[|a|-1])+BoolToNat(b[|a|-1]))*MSBValue;
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == 
                SeqBoolToNat(r_tail) + (BoolToNat(a[|a|-1])+BoolToNat(b[|a|-1]))*MSBValue;
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == 
                SeqBoolToNat(r_tail[..|r_tail|-1]) + (BoolToNat(r_tail[|a|-1]) + BoolToNat(a[|a|-1])+BoolToNat(b[|a|-1]))*MSBValue;
            BitAdderCorrect(r_tail[|a|-1], a[|a|-1], b[|a|-1]);
            var o := BitAdder(r_tail[|a|-1], a[|a|-1], b[|a|-1]);
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == 
                SeqBoolToNat(r_tail[..|r_tail|-1]) + SeqBoolToNat([o.0, o.1])*MSBValue;
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == 
                SeqBoolToNat(r_tail[..|r_tail|-1]) + BoolToNat(o.0)*MSBValue + BoolToNat(o.1)*2*MSBValue;
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == 
                SeqBoolToNat(r_tail[..|r_tail|-1] + [o.0]) + BoolToNat(o.1)*2*MSBValue;
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == 
                SeqBoolToNat(r_tail[..|r_tail|-1] + [o.0] + [o.1]);
            assert [o.0] + [o.1] == [o.0, o.1];
            AdderCorrectSanityHelper(SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c), r_tail[..|r_tail|-1], o.0, o.1);
            assert SeqBoolToNat(a) + SeqBoolToNat(b) + BoolToNat(c) == SeqBoolToNat(r_tail[..|r_tail|-1] + [o.0, o.1]);
        }
    }


    function BoolToNat(b: bool): nat
    {
        if b then 1 else 0
    }

    function SeqBoolToNat(bs: seq<bool>): (r: nat)
    {
        if |bs| == 0 then
            0
        else
            SeqBoolToNat(bs[0..|bs|-1]) + (if bs[|bs|-1] then pow2(|bs|-1) else 0)
    }

    function pow2(a: nat): nat
    {
        if a == 0 then
            1
        else
            2 * pow2(a-1)
    }

    lemma SeqBoolToNatMSB(bs: seq<bool>)
        requires |bs| > 0
        ensures SeqBoolToNat(bs) == SeqBoolToNat(bs[..|bs|-1]) + (if bs[|bs|-1] then pow2(|bs|-1) else 0)
    {
    }

    function NatToSeqBool(n: nat): seq<bool>
    {
        if n == 0 then
            []
        else
            if n % 2 == 0 then
                [false] + NatToSeqBool(n/2)
            else
                [true] + NatToSeqBool((n-1)/2)
    }

    // Write a function to build a circuit.
    // Write a function to confirm that it has no loops.

}
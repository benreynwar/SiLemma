module Model_Mux2 {

  import opened Model_Expr
  import opened MapFunction
  
  function BaseMux2Expr(sel: Expr, a: Expr, b: Expr): (e: Expr)
  {
    var notsel := MInv(sel);
    var mux2 := MOr(MAnd(notsel, a), MAnd(sel, b));
    mux2
  }

  function BaseMux2(sel: bool, a: bool, b: bool): bool
  {
    if sel then b else a
  }

  lemma BaseMux2Equiv(sel: Expr, a: Expr, b: Expr, si: SI)
    requires sel.SIValid(si)
    requires a.SIValid(si)
    requires b.SIValid(si)
    ensures
      var mux := BaseMux2Expr(sel, a, b);
      var sel_val := sel.Evaluate(si);
      var a_val := a.Evaluate(si);
      var b_val := b.Evaluate(si);
      && mux.SIValid(si)
      && (mux.Evaluate(si) == BaseMux2(sel_val, a_val, b_val))
  {
    var sel_val := sel.Evaluate(si);
    var a_val := a.Evaluate(si);
    var b_val := b.Evaluate(si);
    var notsel := MInv(sel);
    var mux2 := MOr(MAnd(notsel, a), MAnd(sel, b));
    assert sel.Evaluate(si) == sel_val;
    assert a.Evaluate(si) == a_val;
    assert b.Evaluate(si) == b_val;
    assert notsel.Evaluate(si) == !sel_val;
    assert mux2.Evaluate(si) == (!sel_val && a_val) || (sel_val && b_val);
  }

  opaque function Mux2Expr(sel: Expr, a: G<Expr>, b: G<Expr>): (r: G<Expr>)
    requires ToBase(a) == ToBase(b)
    ensures ToBase(a) == ToBase(r)
  {
    match a
    case GSingle(e) => GSingle(BaseMux2Expr(sel, a.v, b.v))
    case GSeq(s) => GSeq(seq(|s|, (i: nat) requires i < |s| =>
      ToBaseEqual(a, b);
      assert |ToBase(a).s| == |ToBase(b).s|;
      Mux2Expr(sel, a.s[i], b.s[i])))
  }

  function Mux2(sel: bool, a: G<bool>, b: G<bool>): (r: G<bool>)
    requires ToBase(a) == ToBase(b)
    ensures ToBase(a) == ToBase(r)
  {
    if sel then b else a
  }

  lemma Mux2Equiv(sel: Expr, a: G<Expr>, b: G<Expr>, si: SI)
    requires sel.SIValid(si)
    requires ToBase(a) == ToBase(b)
    requires GExprSIValid(a, si)
    requires GExprSIValid(b, si)
    ensures
      var mux := Mux2Expr(sel, a, b);
      var sel_val := sel.Evaluate(si);
      var a_val := GExprEvaluate(a, si);
      var b_val := GExprEvaluate(b, si);
      && ToBase(a) == ToBase(a_val)
      && ToBase(a) == ToBase(b_val)
      && GExprSIValid(mux, si)
      && (GExprEvaluate(mux, si) == Mux2(sel_val, a_val, b_val))
  {
    var mux := Mux2Expr(sel, a, b);
    var sel_val := sel.Evaluate(si);
    var a_val := GExprEvaluate(a, si);
    var b_val := GExprEvaluate(b, si);
    var t := ToBase(a);
    assert ToBase(a_val) == t;
    assert ToBase(mux) == t;
    assert ToBase(b_val) == t;
    match a
    case GSingle(v) => {
      assert a.v.SIValid(si) && b.v.SIValid(si) by {
        reveal GExprSIValid();
      }
      BaseMux2Equiv(sel, a.v, b.v, si);
      assert GExprSIValid(mux, si) by {
        reveal Mux2Expr();
        assert mux.v.SIValid(si);
        reveal GExprSIValid();
      }
      assert (GExprEvaluate(mux, si) == Mux2(sel_val, a_val, b_val)) by {
        reveal Mux2Expr();
        reveal GExprEvaluate();
      }
    }
    case GSeq(s) => {
      ToBaseEqualSeqLength(a_val, b_val);
      ToBaseEqualSeqLength(a, mux);
      assert |a_val.s| == |b_val.s|;
      forall i: nat | i < |s|
        ensures |mux.s| == |a.s|
        ensures GExprSIValid(mux.s[i], si)
        ensures |a_val.s| == |a.s|
        ensures |b_val.s| == |a.s|
        ensures ToBase(a_val.s[i]) == ToBase(b_val.s[i])
        ensures GExprEvaluate(mux.s[i], si) == Mux2(sel_val, a_val.s[i], b_val.s[i])
      {
        ToBaseEqualSeq(a, b, i);
        ToBaseEqualSeq(a, a_val, i);
        ToBaseEqualSeq(a, b_val, i);
        assert GExprSIValid(a.s[i], si) && GExprSIValid(b.s[i], si) by {
          reveal GExprSIValid();
        }
        Mux2Equiv(sel, a.s[i], b.s[i], si);
        assert mux.s[i] == Mux2Expr(sel, a.s[i], b.s[i]) by {
          reveal Mux2Expr();
        }
        assert GExprSIValid(mux.s[i], si);
        assert && a_val.s[i] == GExprEvaluate(a.s[i], si)
               && b_val.s[i] == GExprEvaluate(b.s[i], si) by {
          reveal GExprEvaluate();
        }
        assert (GExprEvaluate(mux.s[i], si) == Mux2(sel_val, a_val.s[i], b_val.s[i]));
      }
      assert GExprSIValid(mux, si) by {
        reveal GExprSIValid();
      }
      assert (GExprEvaluate(mux, si) == Mux2(sel_val, a_val, b_val)) by {
        reveal GExprEvaluate();
      }
    }
  }

}
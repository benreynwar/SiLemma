module Model_Expr {

  import opened Utils
  import opened MapFunction

  datatype Expr = 
    | MXor(e1: Expr, e2: Expr)
    | MAnd(e1: Expr, e2: Expr)
    | MOr(e1: Expr, e2: Expr)
    | MInv(e: Expr)
    | MIden(e: Expr)
    | MConst(value: bool)
    | MInput(ref: nat)
    | MState(ref: nat)
  {
    predicate RefValid(il: nat, sl: nat)
    {
      match this
      case MXor(e1, e2) => e1.RefValid(il, sl) && e2.RefValid(il, sl)
      case MAnd(e1, e2) => e1.RefValid(il, sl) && e2.RefValid(il, sl)
      case MOr(e1, e2) => e1.RefValid(il, sl) && e2.RefValid(il, sl)
      case MInv(e) => e.RefValid(il, sl)
      case MIden(e) => e.RefValid(il, sl)
      case MConst(v) => true
      case MInput(ref) => ref < il
      case MState(ref) => ref < sl
    }

    predicate SIValid(si: SI)
    {
      RefValid(|si.inputs|, |si.state|)
    }

    function Evaluate(si: SI): (result: bool)
      requires SIValid(si)
    {
      match this
      case MXor(e1, e2) => Xor(e1.Evaluate(si), e2.Evaluate(si))
      case MAnd(e1, e2) => e1.Evaluate(si) && e2.Evaluate(si)
      case MOr(e1, e2) => e1.Evaluate(si) || e2.Evaluate(si)
      case MInv(e) => !e.Evaluate(si)
      case MIden(e) => e.Evaluate(si)
      case MConst(v) => v
      case MInput(r) => si.inputs[r]
      case MState(r) => si.state[r]
    }

  }

  datatype G<T> =
    | GSingle(v: T)
    | GSeq(s: seq<G>)

  datatype Unary = Zero

  function ToBase<T>(ge: G<T>): G<Unary>
  {
    match ge
    case GSingle(v) => G<Unary>.GSingle(Zero)
    case GSeq(s) => G<Unary>.GSeq(seq(|s|, (i: nat) requires i < |s| => ToBase(s[i])))
  }

  opaque predicate GExprSIValid(ge: G<Expr>, si: SI)
  {
    match ge
    case GSingle(e) => e.SIValid(si)
    case GSeq(s) => forall i: nat :: i < |s| ==> GExprSIValid(s[i], si)
  }

  opaque function GExprEvaluate(ge: G<Expr>, si: SI): (gb: G<bool>)
    requires GExprSIValid(ge, si)
    ensures ToBase(gb) == ToBase(ge)
  {
    reveal GExprSIValid();
    var gb := match ge
      case GSingle(e) => G<bool>.GSingle(e.Evaluate(si))
      case GSeq(s) => G<bool>.GSeq(seq(|s|, (i: nat) requires i < |s| => GExprEvaluate(s[i], si)));
    assert ToBase(gb) == ToBase(ge);
    gb
  }

  predicate ToBaseComponentsEqual<T, U>(ge1: G<T>, ge2: G<U>)
    requires ToBase(ge1) == ToBase(ge2)
  {
    match ge1
    case GSingle(v) => (
      assert ge2.GSingle?;
      true
    )
    case GSeq(s) => (
      assert |ToBase(ge1).s| == |ge1.s|;
      forall i: nat :: i < |s| ==> ToBase(ge1.s[i]) == ToBase(ge2.s[i])
    )
  }

  lemma ToBaseEqualSeqLength<T, U>(ge1: G<T>, ge2: G<U>)
    requires ToBase(ge1) == ToBase(ge2)
    requires ge1.GSeq?
    ensures |ge1.s| == |ge2.s|
  {
    assert |ToBase(ge1).s| == |ToBase(ge2).s|;
  }

  lemma ToBaseEqualSeq<T, U>(ge1: G<T>, ge2: G<U>, index: nat)
    requires ge1.GSeq?
    requires index < |ge1.s|
    requires ToBase(ge1) == ToBase(ge2)
    ensures ge2.GSeq?
    ensures |ge1.s| == |ge2.s|
    ensures ToBase(ge1.s[index]) == ToBase(ge2.s[index])
  {
    assert |ToBase(ge1).s| == |ge1.s|;
    assert |ToBase(ge2).s| == |ge2.s|;
    assert ToBase(ge1.s[index]) == ToBase(ge1).s[index];
  }

  lemma ToBaseEqual<T, U>(ge1: G<T>, ge2: G<U>)
    requires ToBase(ge1) == ToBase(ge2)
    ensures ToBaseComponentsEqual(ge1, ge2)
  {
    match ge1
    case GSingle(v) => {
      assert ge2.GSingle?;
      //true
    }
    case GSeq(s) => {
      assert |ToBase(ge1).s| == |ge1.s|;
      assert |ToBase(ge2).s| == |ge2.s|;
      forall i: nat | i < |s|
        ensures ToBase(ge1.s[i]) == ToBase(ge2.s[i])
      {
        assert ToBase(ge1).s[i] == ToBase(ge1.s[i]);
      }
    }
  }

  //datatype ExprType =
  //  | ETBase(e: Expr)
  //  | ETSeq(ets: seq<ExprType>)
  //{
  //  predicate SIValid(si: SI)
  //  {
  //    match this
  //    case ETBase(e) => e.SIValid(si)
  //    case ETSeq(ets) => forall i: nat :: i < |ets| ==> ets[i].SIValid(si)
  //  }
  //  function Evaluate(si: SI): ValType
  //  {
  //    match this
  //    case ETBase(e) => VTBase(e.Evaluate(si))
  //    case ETSeq(ets) => VTSeq(seq(|ets|, (i: nat) requires i < |ets| => ets[i].Evaluate(si)))
  //  }
  //}

  //opaque predicate ExprsSIValid(es: seq<Expr>, si: SI)
  //{
  //  forall i: nat :: i < |es| ==> es[i].SIValid(si)
  //}

  //opaque function ExprsEvaluate(es: seq<Expr>, si: SI): (r: seq<bool>)
  //  requires ExprsSIValid(es, si)
  //  ensures |r| == |es|
  //{
  //  reveal ExprsSIValid();
  //  seq(|es|, (i: nat) requires i < |es| => es[i].Evaluate(si))
  //}


  //datatype Soe = Soe(
  //  input_width: nat,
  //  outputs: seq<Expr>,
  //  state: seq<Expr>
  //)
  //{

  //  opaque predicate Valid()
  //  {
  //    && (forall o_index: nat :: o_index < |outputs| ==> outputs[o_index].RefValid(input_width, |state|))
  //    && (forall s_index: nat :: s_index < |state| ==> state[s_index].RefValid(input_width, |state|))
  //  }

  //  opaque function Evaluate(si: SI): (so: SO)
  //    requires Valid()
  //    requires |si.inputs| == input_width
  //    requires |si.state| == |state|
  //    ensures |so.outputs| == |outputs|
  //    ensures |so.state| == |state|
  //  {
  //    reveal Valid();
  //    var outputs := seq(|outputs|, (o_index: nat) requires o_index < |outputs| => outputs[o_index].Evaluate(si));
  //    var new_state := seq(|state|, (s_index: nat) requires s_index < |state| => state[s_index].Evaluate(si));
  //    SO(outputs, new_state)
  //  }

  //}

  //ghost opaque predicate SoeUFEquiv(soe: Soe, uf: UpdateFunction)
  //  requires soe.Valid()
  //  requires uf.Valid()
  //{
  //  && (soe.input_width == uf.input_width)
  //  && (|soe.outputs| == uf.output_width)
  //  && (|soe.state| == uf.state_width)
  //  && (forall si: SI :: |si.inputs| == uf.input_width && |si.state| == uf.state_width ==>
  //    && uf.sf.requires(si)
  //    && (soe.Evaluate(si) == uf.sf(si)))
  //}

}
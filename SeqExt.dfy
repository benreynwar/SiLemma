include "../libraries/src/Collections/Sequences/Seq.dfy"

module SeqExt {
  import opened Seq

  lemma LemmaToSetAdds<X>(xs: seq<X>, ys: seq<X>)
    ensures ToSet(xs) + ToSet(ys) == ToSet(xs + ys)
  {
    reveal ToSet();
    assert forall x :: x in (xs + ys) <==> (x in xs) || (x in ys);
  }
        
}

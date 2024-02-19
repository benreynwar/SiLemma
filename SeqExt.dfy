module SeqExt {
  import Seq = Std.Collections.Seq

  lemma LemmaToSetAdds<X>(xs: seq<X>, ys: seq<X>)
    ensures Seq.ToSet(xs) + Seq.ToSet(ys) == Seq.ToSet(xs + ys)
  {
    reveal Seq.ToSet();
    assert forall x :: x in (xs + ys) <==> (x in xs) || (x in ys);
  }
        
}

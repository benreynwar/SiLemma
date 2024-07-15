module InsertersReg {

  import opened MapFunction
  import opened Circ
  import opened Scuf
  import opened ConservedSubcircuit
  import opened Modifiers_ManyParallel
  import opened Inserters.Seq
  import opened Modifiers.SwitchUF

  function RegSF(n: nat, si: SI): (so: SO)
    requires |si.inputs| == n
    requires |si.state| == n
  {
    SO(si.state, si.inputs)
  }

  function RegUpdateFunction(n: nat): (uf: UpdateFunction)
    ensures uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      n, n, n,
      (si: SI) requires |si.inputs| == n && |si.state| == n
        => SO(si.state, si.inputs)
    )
  }

  lemma RegSFIsManyParallelSeqSF(n: nat, si: SI)
    requires |si.inputs| == n
    requires |si.state| == n
    ensures
      RegSF(n, si) == ManyParallelSF(SeqUpdateFunction(), n, si)
  {
  }

  function RegInserter(n: nat): (z: ScufInserter)
    ensures z.Valid()
  {
    var z_seq := SeqInserter();
    var z_parseq := ManyParallelModifier(z_seq, n);
    var new_uf := RegUpdateFunction(n);
    assert UpdateFunctionsEquiv(new_uf, z_parseq.uf) by {
      reveal ManyParallelUpdateFunction();
      forall si: SI | |si.inputs| == n && |si.state| == n
        ensures z_parseq.uf.sf(si) == new_uf.sf(si)
      {
        RegSFIsManyParallelSeqSF(n, si);
      }
      reveal UpdateFunctionsEquiv();
    }
    var z_final := SwitchUFModifier(z_parseq, new_uf);
    z_final
  }

}
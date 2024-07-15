module Inserters_ManyIdent {

  import opened Circ
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened Inserters_Unary
  import opened Modifiers.SwitchUF
  import opened Modifiers_ManyParallel
  import opened Inserters.Ident

  opaque function ManyIdentUF(n: nat): (r: UpdateFunction)
    ensures r.Valid()
    ensures r.input_width == n
    ensures r.output_width == n
    ensures r.state_width == 0
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      n, n, 0,
      (si: SI) requires |si.inputs| == n && |si.state| == 0 =>
        SO(si.inputs, [])
      )
  }

  function ManyIdentInserterImpl(n: nat): (z: ScufInserter)
    ensures z.Valid()
  {
    var z_ident := IdentInserter();
    var z := ManyParallelModifier(z_ident, n);
    z
  }

  lemma ManyIdentUFEquivInternal(n: nat, si: SI)
    requires |si.inputs| == n
    requires |si.state| == 0
    ensures
      && ManyParallelSF(IdentUF(), n, si) == SO(si.inputs, [])
  {
    reveal UpdateFunction.Valid();
    reveal IdentUF();
  }

  lemma ManyIdentUFEquiv(n: nat)
    ensures
      var uf_base := ManyParallelUpdateFunction(IdentUF(), n);
      var new_uf := ManyIdentUF(n);
      UpdateFunctionsEquiv(new_uf, uf_base)
  {
    reveal IdentUF();
    var uf_base := ManyParallelUpdateFunction(IdentUF(), n);
    var new_uf := ManyIdentUF(n);
    reveal UpdateFunction.Valid();
    forall si | new_uf.SIVal(si)
      ensures new_uf.sf(si) == uf_base.sf(si)
    {
      reveal ManyIdentUF();
      reveal IdentUF();
      reveal ManyParallelUpdateFunction();
      ManyIdentUFEquivInternal(n, si);
    }
    reveal UpdateFunctionsEquiv();
  }

  opaque function ManyIdentInserter(n: nat): (z: ScufInserter)
    ensures z.Valid()
    ensures z.uf == ManyIdentUF(n)
  {
    var z_base := ManyIdentInserterImpl(n);
    var new_uf := ManyIdentUF(n);
    ManyIdentUFEquiv(n);
    var z := SwitchUFModifier(z_base, new_uf);
    z
  }

}

module Inserters.Ident {

  import opened Circ
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened Inserters_Unary
  import opened Modifiers.SwitchUF

  opaque function IdentUF(): (r: UpdateFunction)
    ensures r.Valid()
    ensures r.input_width == 1
    ensures r.output_width == 1
    ensures r.state_width == 0
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      1, 1, 0,
      (si: SI) requires |si.inputs| == 1 && |si.state| == 0 =>
        SO([si.inputs[0]], [])
      )
  }

  opaque function IdentInserter(): (z: ScufInserter)
    ensures z.Valid()
    ensures z.uf == IdentUF()
  {
    var z_binary := UnaryInserter(CIden);
    reveal UpdateFunctionsEquiv();
    reveal IdentUF();
    var z := SwitchUFModifier(z_binary, IdentUF());
    z
  }

}

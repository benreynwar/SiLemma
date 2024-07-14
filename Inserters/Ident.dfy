module Inserters.Ident {

  import opened Circ
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened Inserters_Unary
  import opened Modifiers.SwitchUF

  function IdentUF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      1, 1, 0,
      (si: SI) requires |si.inputs| == 1 && |si.state| == 0 =>
        SO([si.inputs[0]], [])
      )
  }

  function IdentInserter(): (z: ScufInserter)
    ensures z.Valid()
  {
    var z_binary := UnaryInserter(CIden);
    reveal UpdateFunctionsEquiv();
    var z := SwitchUFModifier(z_binary, IdentUF());
    z
  }

}

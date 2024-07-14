module Inserters.Inv{

  import opened Circ
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened Inserters_Unary
  import opened Modifiers.SwitchUF

  function InvUF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      1, 1, 0,
      (si: SI) requires |si.inputs| == 1 && |si.state| == 0 =>
        SO([!si.inputs[0]], [])
      )
  }

  function InvInserter(): (z: ScufInserter)
    ensures z.Valid()
  {
    var z_binary := UnaryInserter(CInv);
    reveal UpdateFunctionsEquiv();
    var z := SwitchUFModifier(z_binary, InvUF());
    z
  }

}

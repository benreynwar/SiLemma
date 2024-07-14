module Inserters.Or{

  import opened Circ
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened Inserters_Binary
  import opened Modifiers.SwitchUF

  const OrUFConst := UpdateFunction(
    2, 1, 0,
    (si: SI) requires |si.inputs| == 2 && |si.state| == 0 =>
      SO([si.inputs[0] || si.inputs[1]], []))

  function OrUF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    OrUFConst
  }

  function OrInserter(): (z: ScufInserter)
    ensures z.Valid()
  {
    var z_binary := BinaryInserter(COr);
    reveal UpdateFunctionsEquiv();
    var z := SwitchUFModifier(z_binary, OrUF());
    z
  }

}

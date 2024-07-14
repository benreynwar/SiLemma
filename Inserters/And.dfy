module Inserters.And{

  import opened Circ
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened Inserters_Binary
  import opened Modifiers.SwitchUF

  const AndUFConst := UpdateFunction(
    2, 1, 0,
    (si: SI) requires |si.inputs| == 2 && |si.state| == 0 =>
      SO([si.inputs[0] && si.inputs[1]], []))

  opaque function AndUF(): (r: UpdateFunction)
    ensures r.Valid()
    ensures r.input_width == 2
    ensures r.output_width == 1
    ensures r.state_width == 0
  {
    reveal UpdateFunction.Valid();
    AndUFConst
  }

  opaque function AndInserter(): (z: ScufInserter)
    ensures z.Valid()
    ensures z.uf == AndUF()
  {
    var z_binary := BinaryInserter(CAnd);
    reveal UpdateFunctionsEquiv();
    reveal AndUF();
    var z := SwitchUFModifier(z_binary, AndUF());
    z
  }

}

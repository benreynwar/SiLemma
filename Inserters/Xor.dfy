module Inserters.XOr{

  import opened Circ
  import opened Utils
  import opened ConservedSubcircuit
  import opened MapFunction
  import opened Inserters_Binary
  import opened Modifiers.SwitchUF

  const XorUFConst := UpdateFunction(
    2, 1, 0,
    (si: SI) requires |si.inputs| == 2 && |si.state| == 0 =>
      SO([Xor(si.inputs[0], si.inputs[1])], []))

  opaque function XorUF(): (r: UpdateFunction)
    ensures r.Valid()
    ensures r.input_width == 2
    ensures r.output_width == 1
    ensures r.state_width == 0
  {
    reveal UpdateFunction.Valid();
    XorUFConst
  }

  opaque function XorInserter(): (z: ScufInserter)
    ensures z.Valid()
    ensures z.uf == XorUF()
  {
    var z_binary := BinaryInserter(CXor);
    reveal UpdateFunctionsEquiv();
    reveal XorUF();
    var z := SwitchUFModifier(z_binary, XorUF());
    z
  }

}

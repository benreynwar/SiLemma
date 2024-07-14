module ModifiersAppendReg {
    
  import opened Circ
  import opened Scuf
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened InsertersReg
  import opened MapFunction
  import opened Modifiers_Series
  import opened Modifiers.SwitchUF

  function AppendRegSF(rf_base: UpdateFunction, si: SI): (so: SO)
    requires rf_base.Valid()
    requires |si.inputs| == rf_base.input_width && |si.state| == rf_base.state_width + rf_base.output_width
  {
    var si_base := SI(si.inputs, si.state[..rf_base.state_width]);
    reveal UpdateFunction.Valid();
    var so_base := rf_base.sf(si_base);
    var old_reg_state := si.state[|si_base.state|..];
    var so := SO(old_reg_state, so_base.state + so_base.outputs);
    so
  }

  opaque function AppendRegUpdateFunction(uf: UpdateFunction): (new_uf: UpdateFunction)
    requires uf.Valid()
    ensures new_uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      uf.input_width,
      uf.output_width,
      uf.state_width + uf.output_width,
      (si: SI) requires |si.inputs| == uf.input_width && |si.state| == uf.state_width + uf.output_width =>
        AppendRegSF(uf, si)
    )
  }

  lemma UFEquiv(uf: UpdateFunction)
    requires uf.Valid()
    ensures
      var reg_width := uf.output_width;
      var uf_reg := RegUpdateFunction(reg_width);
      var uf_combined := SeriesUpdateFunction(uf, uf_reg);
      var uf_appendreg := AppendRegUpdateFunction(uf);
      UpdateFunctionsEquiv(uf_appendreg, uf_combined)
  {
    reveal UpdateFunction.Valid();
    reveal UpdateFunctionsEquiv();
    reveal SeriesUpdateFunction();
    reveal AppendRegUpdateFunction();
  }

  opaque function AppendRegModifier(z: ScufInserter): (new_z: ScufInserter)
    requires z.Valid()
    ensures new_z.Valid()
  {
    reveal ScufInserter.Valid();
    var z_reg := RegInserter(z.uf.output_width);
    var z_series := SeriesModifier(z, z_reg);
    var new_uf := AppendRegUpdateFunction(z.uf);
    assert UpdateFunctionsEquiv(new_uf, z_series.uf) by {
      UFEquiv(z.uf);
    }
    var new_z := SwitchUFModifier(z_series, new_uf);
    new_z
  }

}
module AppendReg {
    
  import opened Circ
  import opened Entity
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened IslandBundle
  import opened Inserters.Reg
  import opened CombineSeries
  import opened MapFunction

  function AppendRegSF(rf_base: RFunction, si: SI): (so: SO)
    requires rf_base.Valid()
    requires |si.inputs| == rf_base.input_width && |si.state| == rf_base.state_width + rf_base.output_width
  {
    var si_base := SI(si.inputs, si.state[..rf_base.state_width]);
    reveal RFunction.Valid();
    var so_base := rf_base.sf(si_base);
    var old_reg_state := si.state[|si_base.state|..];
    var so := SO(old_reg_state, so_base.state + so_base.outputs);
    so
  }

  function AppendRegRF(rf_base: RFunction): (rf: RFunction)
    requires rf_base.Valid()
    ensures rf.Valid()
  {
    reveal RFunction.Valid();
    RFunction(
      rf_base.input_width,
      rf_base.output_width,
      rf_base.state_width + rf_base.output_width,
      (si: SI) requires |si.inputs| == rf_base.input_width && |si.state| == rf_base.state_width + rf_base.output_width =>
        AppendRegSF(rf_base, si)
    )
  }

  lemma RFEquiv(rf_base: RFunction)
    requires rf_base.Valid()
    ensures
      var reg_width := rf_base.output_width;
      var rf_reg := RegRF(reg_width);
      var rf_combined := CombineSeriesRF(rf_base, rf_reg);
      var rf_appendreg := AppendRegRF(rf_base);
      RFunctionEquiv(rf_appendreg, rf_combined)
  {
    reveal RFunction.Valid();
    reveal RFunctionEquiv();
  }

  function AppendReg(c: Circuit, ei: EntityInserter): (r: (Circuit, Entity))
    requires CircuitValid(c)
    requires ei.Valid()
    ensures SimpleInsertion(c, r.0, r.1)
  {
    var reg_width := ei.rf.output_width;
    var ei_reg := RegInserter(reg_width);
    var (c_a, e_a) := InsertTwoInSeries(c, ei, ei_reg);
    reveal EntityInserter.Valid();
    var new_rf := AppendRegRF(ei.rf);
    RFEquiv(ei.rf);
    var rf_combined := CombineSeriesRF(ei.rf, ei_reg.rf);
    assert RFunctionEquiv(new_rf, rf_combined);
    assert rf_combined.MFConsistent(e_a.mf);
    MFConsistentEquiv(rf_combined, new_rf, e_a.mf);
    assert new_rf.MFConsistent(e_a.mf);
    var e_b := EntitySwapRF(c_a, e_a, new_rf);
    (c_a, e_a)
  }

}
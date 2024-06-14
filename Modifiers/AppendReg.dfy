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
    requires c.Valid()
    requires ei.Valid()
    ensures SimpleInsertion(c, r.0, r.1)
    ensures
      reveal EntityInserter.Valid();
      AppendRegRF(ei.rf).MFConsistent(r.1.mf)
  {
    var reg_width := ei.rf.output_width;
    var ei_reg := RegInserter(reg_width);
    var (c_a, e_a) := InsertTwoInSeries(c, ei, ei_reg);
    assert ei.rf.Valid() by {
      reveal EntityInserter.Valid();
    }
    var new_rf := AppendRegRF(ei.rf);
    RFEquiv(ei.rf);
    var rf_combined := CombineSeriesRF(ei.rf, ei_reg.rf);
    assert c_a.Valid() && EntityValid(c_a, e_a) && e_a.mf.Valid() by {
      reveal SimpleInsertion();
    }
    MFConsistentEquiv(rf_combined, new_rf, e_a.mf);
    var e_b := EntitySwapRF(c_a, e_a, new_rf);
    assert SimpleInsertion(c, c_a, e_b) by {
      reveal SimpleInsertion();
    }
    (c_a, e_b)
  }

  function AppendRegInserter(ei_base: EntityInserter): (ei: EntityInserter)
    requires ei_base.Valid()
    ensures ei.Valid()
  {
    reveal EntityInserter.Valid();
    EntityInserter(
      AppendRegRF(ei_base.rf),
      (c: Circuit) requires c.Valid() => AppendReg(c, ei_base)
    )
  }

}
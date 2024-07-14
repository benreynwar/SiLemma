module Inserters_Mux2 {

  import Std.Collections.Seq

  import opened ConservedSubcircuit
  import opened Inserters.Ident
  import opened Inserters_ManyIdent
  import opened Inserters.Inv
  import opened Inserters.And
  import opened Inserters.Or
  import opened SelfConnect
  import opened MapFunction
  import opened Modifiers.Merge
  import opened Modifiers_Series
  import opened Modifiers_ForwardConnect
  import opened Modifiers.NewOutputs
  import opened Modifiers.SwitchUF

  opaque function Mux2UF(): (uf: UpdateFunction)
    ensures uf.Valid()
    ensures uf.input_width == 3
    ensures uf.output_width == 1
    ensures uf.state_width == 0
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      3, 1, 0,
      (si: SI) requires |si.inputs| == 3 && |si.state| == 0 =>
        SO([if si.inputs[0] then si.inputs[2] else si.inputs[1]], []))
  }

  function GetNewOutputs(): (new_outputs: seq<nat>)
    ensures NewOutputsValid(4, new_outputs)
  {
    var new_outputs := [0, 3, 1, 2];
    assert NewOutputsValid(4, new_outputs) by {
      reveal NewOutputsValid();
      reveal Seq.HasNoDuplicates();
    }
    new_outputs
  }

  opaque function Mux2UFBase(): (uf: UpdateFunction)
    ensures uf.Valid()
    ensures uf.input_width == 3
    ensures uf.output_width == 1
    ensures uf.state_width == 0
  {
    var uf_sel := IdentUF();
    var uf_notsel := InvUF();
    var conn := Mux2IdentInvForwardConn();
    var uf_sel_notsel := ForwardConnectUF(uf_sel, uf_notsel, conn);
    assert uf_sel_notsel.input_width == 1;
    assert uf_sel_notsel.output_width == 2;
    assert uf_sel_notsel.state_width == 0;

    // Create a module that just bundles the 'A' and 'B' input signals together
    var uf_a_b := ManyIdentUF(2);
    assert uf_a_b.input_width == 2;
    assert uf_a_b.output_width == 2;
    assert uf_a_b.state_width == 0;

    // Now join those two modules.
    var uf_sel_notsel_a_b := MergeUpdateFunctions(uf_sel_notsel, uf_a_b);
    assert uf_sel_notsel_a_b.input_width == 3;
    assert uf_sel_notsel_a_b.output_width == 4;
    assert uf_sel_notsel_a_b.state_width == 0;

    // Rearrange the output wires so that we can feed them easily into the and gates.
    var new_outputs := GetNewOutputs();

    var uf_sel_a_notsel_b := NewOutputsUpdateFunction(uf_sel_notsel_a_b, new_outputs);
    assert uf_sel_a_notsel_b.input_width == 3;
    assert uf_sel_a_notsel_b.output_width == 4;
    assert uf_sel_a_notsel_b.state_width == 0;

    // Now build a module with two and gates in parallel
    var uf_ands := MergeUpdateFunctions(AndUF(), AndUF());
    assert uf_ands.input_width == 4;
    assert uf_ands.output_width == 2;
    assert uf_ands.state_width == 0;
    
    // And feed the other module into the and gates.
    var uf_upto_ands := SeriesUpdateFunction(uf_sel_a_notsel_b, uf_ands);
    assert uf_upto_ands.input_width == 3;
    assert uf_upto_ands.output_width == 2;
    assert uf_upto_ands.state_width == 0;

    // And finally feed the outputs of the ands into an or.
    var uf_mux := SeriesUpdateFunction(uf_upto_ands, OrUF());
    assert uf_mux.input_width == 3;
    assert uf_mux.output_width == 1;
    assert uf_mux.state_width == 0;
    uf_mux
  }

  lemma {:vcs_split_on_every_assert} Mux2UFEquiv()
    // FixMe: Using 29M
    ensures UpdateFunctionsEquiv(Mux2UF(), Mux2UFBase())
  {
    var uf := Mux2UF();
    var uf_base := Mux2UFBase();
    assert uf.input_width == uf_base.input_width;
    assert uf.output_width == uf_base.output_width;
    assert uf.state_width == uf_base.state_width;
    forall si: SI | uf.SIVal(si)
      ensures
        && uf.sf.requires(si)
        && uf_base.sf.requires(si)
        && (uf.sf(si) == uf_base.sf(si))
    {
      // Proving behavior for (ident inv)
      var uf_sel := IdentUF();
      var uf_notsel := InvUF();
      var conn := Mux2IdentInvForwardConn();
      var uf_sel_notsel := ForwardConnectUF(uf_sel, uf_notsel, conn);
      var si_sel_notsel := SI([si.inputs[0]], []);
      assert uf_sel_notsel.input_width == 1;
      reveal UpdateFunction.Valid();
      var so_sel_notsel := uf_sel_notsel.sf(si_sel_notsel);
      assert so_sel_notsel.outputs == [si.inputs[0], !si.inputs[0]] by {
        var si_sel := SI([si.inputs[0]], []);
        var so_sel := uf_sel.sf(si_sel);
        assert so_sel == SO([si.inputs[0]], []) by {
          reveal IdentUF();
        }
        var si_inv_input := conn.NIO2I([], so_sel.outputs);
        assert si_inv_input == [so_sel.outputs[0]] by {
          reveal Mux2IdentInvForwardConn();
        }
        var si_inv := SI(si_inv_input, []);
        var so_inv := uf_notsel.sf(si_inv);
        assert so_inv == SO([!si.inputs[0]], []) by {
          reveal InvUF();
        }
        reveal ForwardConnectUF();
        assert so_sel_notsel == ForwardConnectSF(uf_sel, uf_notsel, conn, si_sel_notsel);
        assert so_sel_notsel == SO(so_sel.outputs + so_inv.outputs, so_sel.state + so_inv.state) by {
          var uf1 := uf_sel;
          var uf2 := uf_notsel;
          var si1: SI := SI(si_sel_notsel.inputs[..uf1.input_width], si_sel_notsel.state[..uf1.state_width]);
          assert si1 == si_sel;
          var so1 := uf1.sf(si1);
          var si2_true_input := si_sel_notsel.inputs[uf1.input_width..];
          var si2_input := conn.NIO2I(si2_true_input, so1.outputs);
          var si2 := SI(si2_input, si_sel_notsel.state[uf1.state_width..]);
          assert si2 == si_inv;
          var so2 := uf2.sf(si2);
          var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
        }
      }
      // Proving behavior for after we add the idents in and rearrange.
      // Create a module that just bundles the 'A' and 'B' input signals together
      var uf_a_b := ManyIdentUF(2);
      var si_a_b := SI(si.inputs[1..], []);

      // Now join those two modules.
      var uf_sel_notsel_a_b := MergeUpdateFunctions(uf_sel_notsel, uf_a_b);
      var so_sel_notsel_a_b := uf_sel_notsel_a_b.sf(si);
      assert so_sel_notsel_a_b == SO([si.inputs[0], !si.inputs[0], si.inputs[1], si.inputs[2]], []) by {
        MergeUpdateFunctionBehav(uf_sel_notsel, uf_a_b, si);
        assert uf_sel_notsel.sf(SI([si.inputs[0]], [])) == SO([si.inputs[0], !si.inputs[0]], []);
        reveal ManyIdentUF();
        assert uf_a_b.sf(SI(si.inputs[1..], [])) == SO(si.inputs[1..], []);
        assert MergeSF(uf_sel_notsel, uf_a_b, si) == SO([si.inputs[0], !si.inputs[0], si.inputs[1], si.inputs[2]], []) by {
          var uf1 := uf_sel_notsel;
          var uf2 := uf_a_b;
          var si1 := SI(si.inputs[..uf1.input_width], si.state[..uf1.state_width]);
          var si2 := SI(si.inputs[uf1.input_width..], si.state[uf1.state_width..]);
          assert si1 == si_sel_notsel;
          assert si2 == si_a_b;
          reveal UpdateFunction.Valid();
          var so1 := uf1.sf(si1);
          var so2 := uf2.sf(si2);
          var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
        }
      }
      // Rearrange the output wires so that we can feed them easily into the and gates.
      var new_outputs := GetNewOutputs();
      var uf_sel_a_notsel_b := NewOutputsUpdateFunction(uf_sel_notsel_a_b, new_outputs);

      var so_sel_a_notsel_b := uf_sel_a_notsel_b.sf(si);
      assert so_sel_a_notsel_b == SO([si.inputs[0], si.inputs[2], !si.inputs[0], si.inputs[1]], []) by {
        reveal NewOutputsUpdateFunction();
      }

      // Now build a module with two and gates in parallel
      var uf_ands := MergeUpdateFunctions(AndUF(), AndUF());
      
      // And feed the other module into the and gates.
      var uf_upto_ands := SeriesUpdateFunction(uf_sel_a_notsel_b, uf_ands);
      var so_upto_ands := uf_upto_ands.sf(si);
      assert so_upto_ands == SO([si.inputs[0] && si.inputs[2], (!si.inputs[0]) && si.inputs[1]], []) by {
        reveal AndUF();
        var si_ands := SI(so_sel_a_notsel_b.outputs, []);
        MergeUpdateFunctionBehav(AndUF(), AndUF(), si_ands);
        var uf1 := AndUF();
        var uf2 := AndUF();
        var si1 := SI(si_ands.inputs[..uf1.input_width], si_ands.state[..uf1.state_width]);
        var si2 := SI(si_ands.inputs[uf1.input_width..], si_ands.state[uf1.state_width..]);
        assert si1 == SI([si.inputs[0], si.inputs[2]], []);
        assert si2 == SI([!si.inputs[0], si.inputs[1]], []);
        reveal UpdateFunction.Valid();
        var so1 := uf1.sf(si1);
        var so2 := uf2.sf(si2);
        var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
        reveal SeriesUpdateFunction();
      }

      // And finally feed the outputs of the ands into an or.
      var uf_mux := SeriesUpdateFunction(uf_upto_ands, OrUF());

      assert uf.sf(si) == uf_mux.sf(si) by {
        reveal OrUF();
        reveal SeriesUpdateFunction();
        var si_or := SI(so_upto_ands.outputs, []);
        var so_or := OrUF().sf(si_or);
        assert so_or == SO([(si.inputs[0] && si.inputs[2]) || ((!si.inputs[0]) && si.inputs[1])], []);
        var so_mux := uf_mux.sf(si);
        assert so_mux == SO([(si.inputs[0] && si.inputs[2]) || ((!si.inputs[0]) && si.inputs[1])], []);
        reveal Mux2UF();
      }
      assert uf_base == uf_mux by {
        reveal Mux2UFBase();
      }
    }
    reveal UpdateFunctionsEquiv();
  }

  // A mux consists of
  // Three inputs (sel, A, B)
  // inv_sel = ! sel
  // A_sel   = A && inv_sel
  // B_sel   = B && sel
  // result  = A_sel || B_sel
  
  opaque function Mux2IdentInvForwardConn(): (r: InternalConnection)
    // Takes the output from ident and feeds it into a inv
    ensures r.Valid()
    ensures r.i_width == 1
    ensures r.ni_width == 0
    ensures r.o_width == 1
  {
    var ni_width := 0;
    var i_width := 1;
    var o_width := 1;
    var connections := map[0 := 0];
    var i2ni := [];
    var nio2i := [(true, 0)];
    var conn := InternalConnection(ni_width, i_width, o_width, connections, i2ni, nio2i);
    assert conn.Valid() by {
      reveal InternalConnection.ConnectionsValid();
      reveal InternalConnection.ToNIMapValid();
      reveal InternalConnection.ToIMapValid();
      reveal Seq.HasNoDuplicates();
    }
    conn
  }

  function Mux2InserterImpl(): (z: ScufInserter)
    ensures z.Valid()
    ensures z.uf == Mux2UFBase()
  {
    // Create a module that takes in the 'sel' signal and outputs the 'sel' and !'sel'.
    var z_sel := IdentInserter();
    var z_notsel := InvInserter();
    var conn := Mux2IdentInvForwardConn();
    var z_sel_notsel := ForwardConnectionModifier(z_sel, z_notsel, conn);

    // Create a module that just bundles the 'A' and 'B' input signals together
    var z_a_b := ManyIdentInserter(2);

    // Now join those two modules.
    var z_sel_notsel_a_b := MergeModifier(z_sel_notsel, z_a_b);

    // Rearrange the output wires so that we can feed them easily into the and gates.
    var new_outputs := GetNewOutputs();
    var z_sel_a_notsel_b := NewOutputsModifier(z_sel_notsel_a_b, new_outputs);

    // Now build a module with two and gates in parallel
    var z_ands := MergeModifier(AndInserter(), AndInserter());
    
    // And feed the other module into the and gates.
    var z_upto_ands := SeriesModifier(z_sel_a_notsel_b, z_ands);

    // And finally feed the outputs of the ands into an or.
    var z_mux := SeriesModifier(z_upto_ands, OrInserter());
    assert z_mux.uf == Mux2UFBase() by {
      reveal Mux2UFBase();
    }
    z_mux
  }

  function Mux2Inserter(): (z: ScufInserter)
    ensures z.Valid()
    ensures z.uf == Mux2UF()
  {
    var z_base := Mux2InserterImpl();
    var new_uf := Mux2UF();
    Mux2UFEquiv();
    assert UpdateFunctionsEquiv(new_uf, Mux2UFBase());
    var z := SwitchUFModifier(z_base, new_uf);
    z
  }
}
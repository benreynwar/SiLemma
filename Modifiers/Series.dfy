module ModifiersSeries {

  import opened Circ
  import opened Scuf
  import opened MapFunction
  import opened ConservedSubcircuit
  import opened SelfConnect
  import opened Modifiers.Merge
  import opened Modifiers.Connect
  import opened Modifiers.NewOutputs
  import opened Modifiers.SwitchUF
  import opened Utils
  import opened Path
  import opened Subcircuit

  function {:vcs_split_on_every_assert} SeriesInternalConnection(input_width_1: nat, input_width_2: nat, output_width_2: nat): (r: InternalConnection)
    ensures r.Valid()
    ensures r.connections.Values == Seq.ToSet(Range(0, input_width_2))
    ensures r.connections.Keys == Seq.ToSet(Range(input_width_1, input_width_1 + input_width_2))
  {
    reveal  Seq.ToSet();
    var ni_width := input_width_1;
    var i_width := input_width_1 + input_width_2;
    var o_width := input_width_2 + output_width_2;
    var connection_values: seq<nat> := Range(0, input_width_2);
    var connection_keys: seq<nat> := Range(input_width_1, input_width_1 + input_width_2);
    assert Seq.HasNoDuplicates(connection_keys) by {
      reveal Seq.HasNoDuplicates();
    }
    var connections: map<nat, nat> := SeqsToMap(connection_keys, connection_values);
    assert connections.Values == Seq.ToSet(connection_values) by {
      reveal SeqsToMap();
      reveal Seq.ToSet();
      reveal MapMatchesSeqs();
    }
    var i2ni := seq(input_width_1, (i: nat) requires i < input_width_1 => i);
    var nio2i := seq(input_width_1 + input_width_2, (i: nat) requires i < input_width_1 + input_width_2 =>
      if i < input_width_1 then (false, i) else (true, i - input_width_1));
    var conn := InternalConnection(ni_width, i_width, o_width, connections, i2ni, nio2i);
    assert conn.Valid() by {
      reveal InternalConnection.Valid();
      reveal Seq.HasNoDuplicates();
      assert (ni_width <= i_width);
      assert (i_width <= ni_width + o_width);
      assert (|i2ni| == ni_width);
      assert (|nio2i| == i_width);
      assert Seq.HasNoDuplicates(i2ni);
      assert Seq.HasNoDuplicates(nio2i);
      assert (forall index: nat :: index in connections.Values ==> index < o_width);
      assert (forall index: nat :: index in connections.Keys ==> index < i_width);
      assert (forall ni_index: nat :: ni_index < ni_width ==> (
        var i_index: nat := i2ni[ni_index];
        && (i_index < i_width)
        && var (from_output, index) := nio2i[i_index];
        && (!from_output)
        && (index == ni_index)
      ));
      forall i_index: nat | i_index < i_width
        ensures
          var (from_output, index) := nio2i[i_index];
          && ((!from_output) ==> index < ni_width && i2ni[index] == i_index && (i_index !in connections))
          && ((from_output) ==> index < o_width && (i_index in connections) && (index == connections[i_index]))
      {
        var (from_output, index) := nio2i[i_index];
        if from_output {
          reveal MapMatchesSeqs();
          assert i_index >= input_width_1;
          assert index < o_width;
          assert index == i_index - input_width_1;
          InRange(input_width_1, input_width_1 + input_width_2, i_index);
          assert connection_keys[index] == i_index;
          assert connection_values[index] == index;
          assert i_index in connection_keys;
          assert index == connections[i_index];
        } else {
          assert i_index < input_width_1;
          assert index < ni_width && i2ni[index] == i_index && (i_index !in connections);
        }
      }
    }
    conn
  }

  lemma InputsAndOutputsConnected(s: Scuf, input_width_1: nat, input_width_2: nat, output_width_2: nat)
    requires |s.mp.inputs| == input_width_1 + input_width_2
    requires |s.mp.outputs| == input_width_2 + output_width_2
    ensures
      var conn := SeriesInternalConnection(input_width_1, input_width_2, output_width_2);
      && (conn.GetConnectedOutputs(s.mp) == Seq.ToSet(s.mp.outputs[..input_width_2]))
      && (conn.GetConnectedInputs(s.mp) == Seq.ToSet(s.mp.inputs[input_width_1..]))
  {
    var connection_values: seq<nat> := Range(0, input_width_2);
    var connection_keys: seq<nat> := Range(input_width_1, input_width_1 + input_width_2);
    var conn := SeriesInternalConnection(input_width_1, input_width_2, output_width_2);
    assert conn.connections.Values == Seq.ToSet(connection_values);
    reveal Seq.ToSet();
    assert forall np :: np in conn.GetConnectedOutputs(s.mp) ==> np in Seq.ToSet(s.mp.outputs[..input_width_2]);
    forall np | np in Seq.ToSet(s.mp.outputs[..input_width_2])
      ensures np in conn.GetConnectedOutputs(s.mp)
    {
      assert np in s.mp.outputs[..input_width_2];
      var index: nat :| index < input_width_2 && s.mp.outputs[index] == np;
      InRange(0, input_width_2, index);
      assert index in connection_values;
      assert np in conn.GetConnectedOutputs(s.mp);
    }
    assert forall np :: np in conn.GetConnectedInputs(s.mp) ==> np in Seq.ToSet(s.mp.inputs[input_width_1..]);
    forall np | np in Seq.ToSet(s.mp.inputs[input_width_1..])
      ensures np in conn.GetConnectedInputs(s.mp)
    {
      assert np in s.mp.inputs[input_width_1..];
      var index: nat :| index >= input_width_1 && index < input_width_1 + input_width_2 && s.mp.inputs[index] == np;
      InRange(input_width_1, input_width_1 + input_width_2, index);
      assert index in connection_keys;
      assert np in conn.GetConnectedInputs(s.mp);
    }
  }

  function SeriesSF(uf1: UpdateFunction, uf2: UpdateFunction, si: SI): (so: SO)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf2.input_width == uf1.output_width
    requires |si.inputs| == uf1.input_width
    requires |si.state| == uf1.state_width + uf2.state_width
    ensures |so.outputs| == uf2.output_width
    ensures |so.state| == uf1.state_width + uf2.state_width
  {
    reveal UpdateFunction.Valid();
    var si1_state := si.state[..uf1.state_width];
    var si2_state := si.state[uf1.state_width..];
    var si1 := SI(si.inputs, si1_state);
    assert |si1.inputs| == uf1.input_width;
    assert |si1.state| == uf1.state_width;
    var so1 := uf1.sf(si1);
    var si2 := SI(so1.outputs, si2_state);
    assert |si2.inputs| == uf2.input_width;
    assert |si2.state| == uf2.state_width;
    var so2 := uf2.sf(si2);
    var so := SO(so2.outputs, so1.state + so2.state);
    so
  }

  function SeriesStep2UpdateFunction(uf1: UpdateFunction, uf2: UpdateFunction): (step2_uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf1.output_width == uf2.input_width
    ensures step2_uf.Valid()
    ensures step2_uf.input_width == uf1.input_width
    ensures step2_uf.output_width == uf1.output_width + uf2.output_width
    ensures step2_uf.state_width == uf1.state_width + uf2.state_width
    ensures step2_uf.Valid()
  {
    var step1_uf := MergeUpdateFunctions(uf1, uf2);
    reveal MergeUpdateFunctions();
    var conn := SeriesInternalConnection(uf1.input_width, uf2.input_width, uf2.output_width);
    assert conn.o_width == uf2.input_width + uf2.output_width;
    var step2_uf := ConnectUpdateFunction(step1_uf, conn);
    step2_uf
  }

  function SeriesStep2ModelSF(uf1: UpdateFunction, uf2: UpdateFunction, si: SI): (so: SO)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf1.output_width == uf2.input_width
    requires |si.inputs| == uf1.input_width
    requires |si.state| == uf1.state_width + uf2.state_width
    ensures |so.outputs| == uf1.output_width + uf2.output_width
    ensures |so.state| == uf1.state_width + uf2.state_width
  {
    reveal UpdateFunction.Valid();
    var si1 := SI(si.inputs, si.state[..uf1.state_width]);
    var so1 := uf1.sf(si1);
    var si2 := SI(so1.outputs, si.state[uf1.state_width..]);
    var so2 := uf2.sf(si2);
    var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
    so
  }

  function SeriesStep2ModelUpdateFunction(uf1: UpdateFunction, uf2: UpdateFunction): (step2m_uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf1.output_width == uf2.input_width
    ensures step2m_uf.Valid()
  {
    reveal UpdateFunction.Valid();
    var new_uf := UpdateFunction(
      uf1.input_width,
      uf1.output_width + uf2.output_width,
      uf1.state_width + uf2.state_width,
      (si: SI) requires |si.inputs| == uf1.input_width && |si.state| == uf1.state_width + uf2.state_width
        => SeriesStep2ModelSF(uf1, uf2, si)
    );
    new_uf
  }

  lemma SeriesStep2UpdateFunctionEquiv(uf1: UpdateFunction, uf2: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf2.input_width == uf1.output_width
    ensures UpdateFunctionsEquiv(SeriesStep2UpdateFunction(uf1, uf2), SeriesStep2ModelUpdateFunction(uf1, uf2))
  {
    reveal UpdateFunctionsEquiv();
    var step2_uf := SeriesStep2UpdateFunction(uf1, uf2);
    var step2m_uf := SeriesStep2ModelUpdateFunction(uf1, uf2);
    reveal UpdateFunction.Valid();
    var conn := SeriesInternalConnection(uf1.input_width, uf2.input_width, uf2.output_width);
    forall si | step2_uf.SIVal(si)
      ensures step2_uf.sf(si) == step2m_uf.sf(si)
    {
      var si1 := SI(si.inputs, si.state[..uf1.state_width]);
      var so1 := uf1.sf(si1);
      var si2 := SI(so1.outputs, si.state[uf1.state_width..]);
      var so2 := uf2.sf(si2);
      var uf_merged := MergeUpdateFunctions(uf1, uf2);
      var si_merged := SI(si.inputs + so1.outputs, si.state);
      var so_merged := uf_merged.sf(si_merged);
      assert so_merged == SO(so1.outputs + so2.outputs, so1.state + so2.state) by {
        reveal MergeUpdateFunctions();
      }
      assert so_merged == step2m_uf.sf(si);
      assert conn.SNI2SOSecondPass(uf_merged, si) == step2_uf.sf(si);
      // For the first pass we feed all zeros into uf2.
      var fake_input := seq(uf2.input_width, (index: nat) requires index < uf2.input_width => false);
      var si2_fake := SI(fake_input, si2.state);
      var so2_fake := uf2.sf(si2_fake);
      var so_first_pass := SO(so1.outputs + so2_fake.outputs, so1.state + so2_fake.state);
      var si_merged_fake := SI(si.inputs + fake_input, si.state);
      var so_merged_first_pass := uf_merged.sf(si_merged_fake);
      assert so_first_pass == so_merged_first_pass by {
        reveal MergeUpdateFunctions();
      }
      assert conn.SNI2SOFirstPass(uf_merged, si) == so_first_pass by {
        var fake_outputs := seq(uf1.output_width + uf2.output_width, (index: nat) requires index < uf1.output_width + uf2.output_width => false);
        assert conn.SNI2SIFromOutputs(si, fake_outputs) == SI(si.inputs + fake_input, si.state);
        reveal MergeUpdateFunctions();
      }
      assert conn.SNI2SOSecondPass(uf_merged, si) == so_merged by {
        var si_second_pass := conn.SNI2SIFromOutputs(si, so_first_pass.outputs);
        assert si_second_pass == si_merged;
      }
      assert so_merged == step2_uf.sf(si);
      assert step2_uf.sf(si) == step2m_uf.sf(si);
    }
  }

  function SeriesStep3UpdateFunction(uf1: UpdateFunction, uf2: UpdateFunction): (step3_uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf1.output_width == uf2.input_width
    ensures step3_uf.Valid()
    ensures step3_uf.output_width == uf2.output_width
    ensures step3_uf.input_width == uf1.input_width
    ensures step3_uf.state_width == uf1.state_width + uf2.state_width
  {
    var step2_uf := SeriesStep2UpdateFunction(uf1, uf2);
    var new_outputs := SeriesNewOutputs(uf1.output_width, uf2.output_width);
    var step3_uf := NewOutputsUpdateFunction(step2_uf, new_outputs);
    step3_uf
  }

  function SeriesUpdateFunction(uf1: UpdateFunction, uf2: UpdateFunction): (new_uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf2.input_width == uf1.output_width
    ensures new_uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      uf1.input_width,
      uf2.output_width,
      uf1.state_width + uf2.state_width,
      (si: SI) requires |si.inputs| == uf1.input_width && |si.state| == uf1.state_width + uf2.state_width
        => SeriesSF(uf1, uf2, si)
    )
  }

  lemma SeriesUpdateFunctionEquiv(uf1: UpdateFunction, uf2: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires uf2.input_width == uf1.output_width
    ensures UpdateFunctionsEquiv(SeriesUpdateFunction(uf1, uf2), SeriesStep3UpdateFunction(uf1, uf2))
  {
    SeriesStep2UpdateFunctionEquiv(uf1, uf2);
    reveal UpdateFunctionsEquiv();
  }

  function SeriesNewOutputs(output_width_1: nat, output_width_2: nat): (new_outputs: seq<nat>)
    ensures forall i: nat :: i < |new_outputs| ==> new_outputs[i] < output_width_1 + output_width_2
    ensures Seq.HasNoDuplicates(new_outputs)
  {
    reveal Seq.HasNoDuplicates();
    seq(output_width_2, (i: nat) requires i < output_width_2 => output_width_1 + i)
  }

  function SeriesModifier(z1: ScufInserter, z2: ScufInserter): (new_z: ScufInserter)
    requires z1.Valid()
    requires z2.Valid()
    requires z1.uf.output_width == z2.uf.input_width
    ensures new_z.Valid()
  {

    reveal UpdateFunctionsEquiv();
    reveal ScufInserter.Valid();
    reveal SimpleInsertion();
    var z_merged := MergeModifier(z1, z2);
    var conn := SeriesInternalConnection(z1.uf.input_width, z2.uf.input_width, z2.uf.output_width);
    assert InserterConnectionConsistent(z_merged, conn) by {
      assert UFConnectionConsistent(z_merged.uf, conn) by {
        reveal MergeUpdateFunctions();
      }
      forall c: Circuit | c.Valid()
        ensures
          var (new_c, s) := z_merged.fn(c);
          ScufConnectionConsistent(new_c, s, conn)
      {
        z_merged.ValidForCircuit(c);
        var (new_c, s) := z_merged.fn(c);
        //var conn_outputs := conn.GetConnectedOutputs(s.mp);
        //var conn_inputs := conn.GetConnectedInputs(s.mp);
        assert new_c.Valid() && s.Valid(new_c) by {
          reveal SimpleInsertion();
        }
        assert ScufConnectionConsistent(new_c, s, conn) by {
          assert (conn.i_width == s.uf.input_width);
          assert (conn.o_width == s.uf.output_width);
          MergeModifierPathConstraints(z1, z2, c);
          InputsAndOutputsConnected(s, z1.uf.input_width, z2.uf.input_width, z2.uf.output_width);
          reveal Seq.ToSet();
          assert conn.GetConnectedOutputs(s.mp) == Seq.ToSet(s.mp.outputs[..z1.uf.output_width]);
          assert !PathExistsBetweenNPSets(new_c, conn.GetConnectedOutputs(s.mp), conn.GetConnectedInputs(s.mp));
          assert forall x :: (x in s.mp.inputs) ==> (x !in new_c.PortSource) by {
            FInputsInSc(new_c, s);
            reveal NPsInSc();
            IsIslandNoInputs(new_c, s.sc);
            assert forall x: NP :: (x in s.mp.inputs) ==> (x.n in s.sc);
            reveal ConnInputs();
            reveal UnconnInputs();
            reveal Scuf.SomewhatValid();
            reveal Seq.ToSet();
            assert forall x: NP :: (x in s.mp.inputs) ==> x in AllInputs(new_c, s.sc);
          }
          assert (forall i_index :: i_index in conn.connections ==> s.mp.inputs[i_index] !in new_c.PortSource);
          reveal ScufConnectionConsistent();
        }
      }
      reveal InserterConnectionConsistent();
    }
    var z_connected := ConnectModifier(z_merged, conn);
    var new_outputs := SeriesNewOutputs(z1.uf.output_width, z2.uf.output_width);
    assert z_connected.uf.output_width == z1.uf.output_width + z2.uf.output_width by {
      reveal MergeUpdateFunctions();
    }
    var z_new_outputs := NewOutputsModifier(z_connected, new_outputs);
    var new_uf := SeriesUpdateFunction(z1.uf, z2.uf);
    SeriesUpdateFunctionEquiv(z1.uf, z2.uf);
    var z_final := SwitchUFModifier(z_new_outputs, new_uf);
    z_final
  }

}
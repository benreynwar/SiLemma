module Inserters.And3{

  import opened Std.Wrappers

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Utils
  import opened Scuf
  import opened MapFunction
  import opened ConnectionEval
  import opened Connection
  import opened Subcircuit
  import opened MapConnection
  import opened Modifiers.Merge
  import opened SelfConnect
  import opened Modifiers.Connect
  import opened Path
  import opened Modifiers.SwitchUF
  import opened Modifiers.NewOutputs

  import opened And

  const And3UFConst := UpdateFunction(
    3, 1, 0,
    (si: SI) requires |si.inputs| == 3 && |si.state| == 0 =>
      SO([si.inputs[0] && si.inputs[1] && si.inputs[2]], []))

  function And3UF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    And3UFConst
  }

  function And3Step1UF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
    4, 2, 0,
    (si: SI) requires |si.inputs| == 4 && |si.state| == 0 =>
      SO([si.inputs[0] && si.inputs[1], si.inputs[2] && si.inputs[3]], []))
  }
  
  function And3Step1UFx(): (r: UpdateFunction)
  ensures r.input_width == 4
  ensures r.output_width == 2
  ensures r.state_width == 0
  {
    reveal MergeUpdateFunctions();
    MergeUpdateFunctions(AndUF(), AndUF())
  }

  function And3Step1SF(si: SI): (so: SO)
    requires |si.inputs| == 4
    requires |si.state| == 0
  {
    MergeSF(AndUF(), AndUF(), si)
  }

  lemma {:vcs_split_on_every_assert} LemmaAnd3Step1UF()
    // Seems to need 'vcs_split_on_every_assert'.
    // I suspect this is due to whatever curse MergeUpdateFunctions has.
    ensures UpdateFunctionsEquiv(And3Step1UF(), And3Step1UFx())
  {
    var uf1 := And3Step1UF();
    var ufa := AndUF();
    var uf2 := MergeUpdateFunctions(ufa, ufa);
    assert uf2.input_width == 4 by {reveal MergeUpdateFunctions();}
    assert uf2.output_width == 2 by {reveal MergeUpdateFunctions();}
    assert uf2.state_width == 0 by {reveal MergeUpdateFunctions();}

    reveal AndUF();
    forall si: SI | uf1.SIVal(si)
      ensures uf2.sf.requires(si)
      ensures uf1.sf(si) == uf2.sf(si)
    {
      assert uf2.sf.requires(si) && uf2.sf(si) == MergeSF(ufa, ufa, si) by {
        reveal MergeUpdateFunctions();
      }
      reveal UpdateFunction.Valid();
      assert uf1.sf(si) == uf2.sf(si);
    }
    reveal UpdateFunctionsEquiv();
  }

  function And3Step2UF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
    3, 2, 0,
    (si: SI) requires |si.inputs| == 3 && |si.state| == 0 =>
      SO([si.inputs[0] && si.inputs[1], si.inputs[0] && si.inputs[1] && si.inputs[2]], []))
  }

  function And3Step2UFx(): (r: UpdateFunction)
  {
    var conn := And3InternalConnection();
    reveal And3InternalConnection();
    ConnectUpdateFunction(And3Step1UFx(), conn)
  }

  lemma LemmaAnd3Step2UF()
    ensures
      var conn := And3InternalConnection();
      UpdateFunctionsEquiv(And3Step2UF(), And3Step2UFx())
  {
    LemmaAnd3Step1UF();
    reveal And3InternalConnection();
    reveal ConnectUpdateFunction();
    reveal UpdateFunctionsEquiv();
  }

  function And3Step3UF(): (r: UpdateFunction)
    ensures r.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
    3, 1, 0,
    (si: SI) requires |si.inputs| == 3 && |si.state| == 0 =>
      SO([si.inputs[0] && si.inputs[1] && si.inputs[2]], []))
  }

  function And3Step3UFx(): (r: UpdateFunction)
  {
    var new_outputs := And3NewOutputs();
    NewOutputsUpdateFunction(And3Step2UFx(), new_outputs)
  }

  lemma LemmaAnd3Step3UF()
    ensures
      UpdateFunctionsEquiv(And3Step3UF(), And3Step3UFx())
  {
    LemmaAnd3Step2UF();
    reveal NewOutputsUpdateFunction();
    reveal UpdateFunctionsEquiv();
  }

  lemma And3UpdateFunctionsEquiv()
    ensures 
      reveal MergeUpdateFunctions();
      var merged_uf := MergeUpdateFunctions(AndUF(), AndUF());
      var conn := And3InternalConnection();
      reveal And3InternalConnection();
      var connected_uf := ConnectUpdateFunction(merged_uf, conn);
      var new_outputs := And3NewOutputs();
      var new_outputs_uf := NewOutputsUpdateFunction(connected_uf, new_outputs);
      UpdateFunctionsEquiv(And3UF(), new_outputs_uf)
  {
      LemmaAnd3Step3UF();
      reveal UpdateFunctionsEquiv();
  }

  opaque function And3InternalConnection(): (r: InternalConnection)
    ensures r.Valid()
    ensures r.connections.Keys == {3}
    ensures r.connections.Values == {0}
  {
    var ni_width := 3;
    var i_width := 4;
    var o_width := 2;
    var connections := map[3 := 0];
    var i2ni := [0, 1, 2];
    var nio2i := [(false, 0), (false, 1), (false, 2), (true, 0)];
    var conn := InternalConnection(ni_width, i_width, o_width, connections, i2ni, nio2i);
    assert conn.Valid() by {
      reveal InternalConnection.ConnectionsValid();
      reveal InternalConnection.ToNIMapValid();
      reveal InternalConnection.ToIMapValid();
      reveal Seq.HasNoDuplicates();
    }
    conn
  }

  function And3NewOutputs(): (r: seq<nat>)
    ensures Seq.HasNoDuplicates(r)
    ensures NewOutputsValid(2, r)
  {
    reveal NewOutputsValid();
    reveal Seq.HasNoDuplicates();
    [1]
  }

  lemma And3ScufConnectionConsistent(c: Circuit)
    requires c.Valid()
    ensures
      var z_and1 := AndInserter();
      var z_and2 := AndInserter();
      var z := MergeModifier(z_and1, z_and2);
      && z.fn.requires(c)
      && var (new_c, s) := z.fn(c);
      && var conn := And3InternalConnection();
      && new_c.Valid()
      && s.Valid(new_c)
      && ScufConnectionConsistent(new_c, s, conn)
  {
    reveal Seq.ToSet();

    var z_and1 := AndInserter();
    var z_and2 := AndInserter();
    assert z_and1.uf.input_width == 2;
    var z := MergeModifier(z_and1, z_and2);
    MergeModifierPathConstraints(z_and1, z_and2, c);
    z.ValidForCircuit(c);
    var (new_c, s) := z.fn(c);

    var conn := And3InternalConnection();
    reveal And3InternalConnection();
    assert conn.connections == map[3 := 0];
    assert conn.connections.Keys == {3};
    assert conn.connections.Values == {0};

    assert forall index :: index in conn.connections.Values ==> index < 1;

    assert new_c.Valid() && s.Valid(new_c) by {
      reveal ScufInserter.Valid();
      reveal SimpleInsertion();
      z.ValidForCircuit(c);
      assert SimpleInsertion(c, new_c, s);
    }
  
    reveal InternalConnection.ConnectionsValid();
    reveal ONPsValid();
    s.SomewhatValidToRelaxInputs(new_c);
    ScufFOutputsAreValid(new_c, s);
    assert s.uf.input_width == 4 && s.uf.output_width == 2 by {
      reveal MergeInserter();
    }
    var conn_outputs := conn.GetConnectedOutputs(s.mp);
    assert conn_outputs == {s.mp.outputs[0]};
    var conn_inputs := conn.GetConnectedInputs(s.mp);
    assert conn_inputs == {s.mp.inputs[3]};

    assert ScufConnectionConsistent(new_c, s, conn) by {
      reveal InternalConnection.ConnectionsValid();
      reveal ONPsValid();
      s.SomewhatValidToRelaxInputs(new_c);
      ScufFOutputsAreValid(new_c, s);
      assert s.uf.input_width == 4 && s.uf.output_width == 2 by {
        reveal MergeInserter();
      }
      assert (conn.i_width == s.uf.input_width);
      assert (conn.o_width == s.uf.output_width);
      var s1_inputs := Seq.ToSet(s.mp.inputs[..z_and1.uf.input_width]);
      assert s1_inputs == {s.mp.inputs[0], s.mp.inputs[1]};
      var s2_inputs := Seq.ToSet(s.mp.inputs[z_and1.uf.input_width..]);
      assert s2_inputs == {s.mp.inputs[2], s.mp.inputs[3]};
      var s1_outputs := Seq.ToSet(s.mp.outputs[..z_and1.uf.output_width]);
      assert s1_outputs == {s.mp.outputs[0]};
      var s2_outputs := Seq.ToSet(s.mp.outputs[z_and1.uf.output_width..]);
      assert s2_outputs == {s.mp.outputs[1]};
      assert !PathExistsBetweenNPSets(new_c, s1_outputs, s2_inputs);
      assert conn.GetConnectedOutputs(s.mp) <= s1_outputs;
      assert conn.GetConnectedInputs(s.mp) <= s2_inputs;
      NoPathExistsBetweenNPSubSets(new_c, s1_outputs, s2_inputs, conn.GetConnectedOutputs(s.mp), conn.GetConnectedInputs(s.mp));
      assert !PathExistsBetweenNPSets(new_c, conn.GetConnectedOutputs(s.mp), conn.GetConnectedInputs(s.mp));
      assert Seq.ToSet(s.mp.inputs) !! new_c.PortSource.Keys by {
        reveal ScufInserter.Valid();
        assert z.SpecificValid(c);
        reveal SimpleInsertion();
        assert IsIsland(new_c, s.sc);
        InputsOfIslandNotInPortSource(new_c, s);
      }
      assert (forall i_index :: i_index in conn.connections ==> s.mp.inputs[i_index] !in new_c.PortSource);
      reveal ScufConnectionConsistent();
    }
  }

  lemma And3InserterHelper()
    ensures
      var z_and1 := AndInserter();
      var z_and2 := AndInserter();
      var z_par_ands := MergeModifier(z_and1, z_and2);
      var conn := And3InternalConnection();
      InserterConnectionConsistent(z_par_ands, conn)
  {
    var z_and1 := AndInserter();
    var z_and2 := AndInserter();
    assert z_and1.uf.input_width == 2;

    var z_par_ands := MergeModifier(z_and1, z_and2);
    assert z_par_ands.uf.input_width == 4;

    var conn := And3InternalConnection();
    reveal And3InternalConnection();

    assert InserterConnectionConsistent(z_par_ands, conn) by {
      assert UFConnectionConsistent(z_par_ands.uf, conn) by {
        assert (conn.i_width == z_par_ands.uf.input_width);
        assert (conn.o_width == z_par_ands.uf.output_width);
      }
      forall c: Circuit | c.Valid()
        ensures
          reveal ScufInserter.Valid();
          var (new_c, s) := z_par_ands.fn(c);
          && new_c.Valid() && s.Valid(new_c)
          && ScufConnectionConsistent(new_c, s, conn)
      {
        reveal ScufInserter.Valid();
        var (new_c, s) := z_par_ands.fn(c);
        And3ScufConnectionConsistent(c);
        assert ScufConnectionConsistent(new_c, s, conn);
      }
      reveal InserterConnectionConsistent();
    }
  }

  opaque function And3Inserter(): (z: ScufInserter)
    ensures z.Valid()
  {

    var z_and1 := AndInserter();
    var z_and2 := AndInserter();
    assert z_and1.uf.input_width == 2;

    var z_par_ands := MergeModifier(z_and1, z_and2);
    assert z_par_ands.uf.input_width == 4;
    assert z_par_ands.uf.output_width == 2;

    var conn := And3InternalConnection();

    assert InserterConnectionConsistent(z_par_ands, conn) by {
      And3InserterHelper();
    }

    var z_connected := ConnectModifier(z_par_ands, conn);
    assert z_connected.uf.output_width == 2;

    var new_outputs := And3NewOutputs();
    assert forall i: nat :: i < |new_outputs| ==> new_outputs[i] < z_connected.uf.output_width;
    var z_remove_outputs := NewOutputsModifier(z_connected, new_outputs);

    var merged_uf := MergeUpdateFunctions(AndUF(), AndUF());
    var connected_uf := ConnectUpdateFunction(merged_uf, conn);
    var final_uf := NewOutputsUpdateFunction(connected_uf, new_outputs);
    assert connected_uf == z_connected.uf by {
      assert z_and1.uf == AndUF();
      assert merged_uf == z_par_ands.uf;
    }
    assert final_uf == z_remove_outputs.uf;

    assert UpdateFunctionsEquiv(And3UF(), final_uf) by {
      And3UpdateFunctionsEquiv();
    }
    var z_switched := SwitchUFModifier(z_remove_outputs, And3UF());
    z_switched
  }

}
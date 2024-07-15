module Modifiers_ForwardConnect{

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
  import opened SelfConnectEval
  import opened Modifiers.Connect
  import opened Path
  import opened Modifiers.SwitchUF
  import opened Modifiers.NewOutputs


  function ForwardConnectSF(uf1: UpdateFunction, uf2: UpdateFunction, conn: InternalConnection, si: SI): (so: SO)
    // Here the connection is mapping the uf1.outputs and the left over inputs to the uf2 inputs.
    requires uf1.Valid()
    requires uf2.Valid()
    requires conn.Valid()
    requires conn.i_width == uf2.input_width
    requires conn.o_width == uf1.output_width
    requires |si.inputs| == uf1.input_width + conn.ni_width
    requires |si.state| == uf1.state_width + uf2.state_width
  {
    reveal UpdateFunction.Valid();
    var si1: SI := SI(si.inputs[..uf1.input_width], si.state[..uf1.state_width]);
    var so1 := uf1.sf(si1);
    var si2_true_input := si.inputs[uf1.input_width..];
    var si2_input := conn.NIO2I(si2_true_input, so1.outputs);
    var si2 := SI(si2_input, si.state[uf1.state_width..]);
    var so2 := uf2.sf(si2);
    var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
    so
  }

  opaque function ForwardConnectUF(uf1: UpdateFunction, uf2: UpdateFunction, conn: InternalConnection): (new_uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires conn.Valid()
    requires conn.i_width == uf2.input_width
    requires conn.o_width == uf1.output_width
    ensures new_uf.Valid()
    ensures new_uf.input_width == uf1.input_width + conn.ni_width
    ensures new_uf.output_width == uf1.output_width + uf2.output_width
    ensures new_uf.state_width == uf1.state_width + uf2.state_width
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      uf1.input_width + conn.ni_width, uf1.output_width + uf2.output_width, uf1.state_width + uf2.state_width,
      (si: SI) requires |si.inputs| == uf1.input_width + conn.ni_width && |si.state| == uf1.state_width + uf2.state_width =>
        ForwardConnectSF(uf1, uf2, conn, si)
        )
  }

  function hack(b: bool, n: nat): (bool, nat)
    // Just to get around dafny's struggles width seq<(bool, int)> vs seq<(bool, nat)>.
  {
    (b, n)
  }

  opaque function NewI2NI(input_width_1: nat, ni_width: nat, i2ni: seq<nat>): (new_i2ni: seq<nat>)
    requires Seq.HasNoDuplicates(i2ni)
    requires |i2ni| == ni_width - input_width_1
    ensures Seq.HasNoDuplicates(new_i2ni)
    ensures |new_i2ni| == ni_width
  {
    reveal Seq.HasNoDuplicates();
    var i2ni := seq(ni_width, (i: nat) requires i < ni_width =>
                if i < input_width_1 then i else i2ni[i-input_width_1] + input_width_1);
    i2ni
  }

  lemma NewNIO2IProperties(input_width_1:  nat, input_width_2: nat, nio2i: seq<(bool, nat)>, index: nat)
    requires Seq.HasNoDuplicates(nio2i)
    requires |nio2i| == input_width_2
    requires index < input_width_1 + input_width_2
    ensures
      var new_nio2i := NewNIO2I(input_width_1, input_width_2, nio2i);
      && (index < input_width_1 ==> new_nio2i[index] == (false, index))
      && (index >= input_width_1 ==> (
        var (from_output, other_index) := nio2i[index-input_width_1];
        && (from_output ==> (
          && new_nio2i[index] == (true, other_index))
          )
        && (!from_output ==> new_nio2i[index] == (false, other_index + input_width_1))
        && (from_output == new_nio2i[index].0)
      ))
  {
    reveal NewNIO2I();
    if index >= input_width_1 {
      var (from_output, other_index) := nio2i[index-input_width_1];
    }
  }

  opaque function NewNIO2I(input_width_1: nat, input_width_2: nat, nio2i: seq<(bool, nat)>): (new_nio2i: seq<(bool, nat)>)
    requires Seq.HasNoDuplicates(nio2i)
    requires |nio2i| == input_width_2
    ensures Seq.HasNoDuplicates(new_nio2i)
    ensures |new_nio2i| == input_width_1 + input_width_2
  {
    reveal Seq.HasNoDuplicates();
    var i_width := input_width_1 + input_width_2;
    var new_nio2i: seq<(bool, nat)> := seq(i_width, (i: nat) requires i < i_width =>
                if i < input_width_1 then hack(false, i) else
                  var (from_output, index) := nio2i[i-input_width_1];
                  if from_output then hack(true, index) else hack(false, index +input_width_1));
    assert Seq.HasNoDuplicates(new_nio2i) by {
      forall i1: nat, i2: nat | i1 != i2 && i1 < i_width && i2 < i_width
        ensures new_nio2i[i1] != new_nio2i[i2]
      {
        if i1 < input_width_1 {
          if i2 < input_width_1 {
            assert new_nio2i[i1] != new_nio2i[i2];
          } else {
            var (from_output, index) := nio2i[i2-input_width_1];
            assert new_nio2i[i1] != new_nio2i[i2];
          }
        } else {
          var (from_output1, index1) := nio2i[i1-input_width_1];
          if i2 < input_width_1 {
            assert new_nio2i[i1] != new_nio2i[i2];
          } else {
            var (from_output2, index2) := nio2i[i2-input_width_1];
            assert new_nio2i[i1] != new_nio2i[i2];
          }
        }
      }
    }
    new_nio2i
  }

  opaque function NewConnections(input_width_1: nat, connections: map<nat, nat>): (new_connections: map<nat, nat>)
    ensures new_connections.Values == connections.Values
  {
    var new_connections := (map k | k in connections ::
      (k + input_width_1) := connections[k]);
    assert new_connections.Values == connections.Values by {
      forall v | v in new_connections.Values
        ensures v in connections.Values
      {
      }
      forall v | v in connections.Values
        ensures v in new_connections.Values
      {
        var k: nat :| k in connections && connections[k] == v;
        var new_k := k + input_width_1;
        assert new_connections[new_k] == v;
      }
    }
    new_connections
  }

  lemma NewConnectionsHelper2(input_width_1: nat, connections: map<nat, nat>, forward_index: nat)
    requires forward_index !in connections
    ensures
      var new_connections := NewConnections(input_width_1, connections);
      && forward_index + input_width_1 !in new_connections
  {
    reveal NewConnections();
  }

  lemma NewConnectionsHelper(input_width_1: nat, output_width_1: nat, connections: map<nat, nat>,
                             forward_index: nat)
    requires forall o_index :: o_index in connections.Values ==> o_index < output_width_1
    requires forward_index in connections
    ensures
      var new_connections := NewConnections(input_width_1, connections);
      && forward_index + input_width_1 in new_connections
      && new_connections[forward_index + input_width_1] == connections[forward_index]
  {
    reveal NewConnections();
  }

  lemma NewConnectionsProperties(input_width_1: nat, output_width_1: nat, connections: map<nat, nat>)
    requires forall o_index :: o_index in connections.Values ==> o_index < output_width_1
    ensures
      var new_connections := NewConnections(input_width_1, connections);
      && (forall o_index :: o_index in new_connections.Values ==> o_index < output_width_1)
      && (forall i_index :: i_index in new_connections.Keys ==> i_index >= input_width_1)
      && forall forward_index :: forward_index in connections ==> forward_index + input_width_1 in new_connections
  {
    reveal NewConnections();
    reveal InternalConnection.ConnectionsValid();
    var new_connections := NewConnections(input_width_1, connections);
    assert forall o_index :: o_index in new_connections.Values ==> o_index < output_width_1;
    assert new_connections.Values == connections.Values;
  }

  lemma InternalConnectionToIMapValid(uf1: UpdateFunction, uf2: UpdateFunction, forward_conn: InternalConnection)
    requires uf1.Valid()
    requires uf2.Valid()
    requires forward_conn.Valid()
    requires forward_conn.i_width == uf2.input_width
    requires forward_conn.o_width == uf1.output_width
    ensures
      var internal_conn := ForwardConnectionToInternalConnectionImpl(uf1, uf2, forward_conn);
      internal_conn.ToIMapValid()
  {
    var internal_conn := ForwardConnectionToInternalConnectionImpl(uf1, uf2, forward_conn);
    var i_width := internal_conn.i_width;
    var ni_width := internal_conn.ni_width;
    var o_width := internal_conn.o_width;
    var nio2i := internal_conn.nio2i;
    var connections := internal_conn.connections;
    var i2ni := internal_conn.i2ni;

    assert connections == NewConnections(uf1.input_width, forward_conn.connections);

    forall i_index: nat | i_index < i_width
      ensures
        var (from_output, index) := nio2i[i_index];
        && ((!from_output) ==> index < ni_width && i2ni[index] == i_index && (i_index !in connections))
        && ((from_output) ==> index < o_width && (i_index in connections) && (index == connections[i_index]))
    {
      var (from_output, index) := nio2i[i_index];
      assert forall o_index :: o_index in forward_conn.connections.Values
               ==> o_index < uf1.output_width by {
        reveal InternalConnection.ConnectionsValid();
      }
      NewConnectionsProperties(uf1.input_width, uf1.output_width, forward_conn.connections);
      NewNIO2IProperties(uf1.input_width, uf2.input_width, forward_conn.nio2i, i_index);
      if i_index < uf1.input_width {
        //NIO2IHelper1(uf1.input_width, uf2.input_width, forward_conn.nio2i, i_index);
        assert !from_output;
        assert index == i_index;
        assert i2ni[index] == i_index by {
          reveal NewI2NI();
        }
        assert i_index !in connections;
      } else {
        var i_index_in_2 := i_index - uf1.input_width;
        var (forward_from_output, forward_index) := forward_conn.nio2i[i_index_in_2];
        assert from_output == forward_from_output;
        if from_output {
          reveal InternalConnection.ToIMapValid();
          assert forward_index < uf1.output_width by {
            assert forward_from_output;
          }
          assert index < o_width;
          assert index == forward_index;
          assert i_index_in_2 in forward_conn.connections by {
            reveal InternalConnection.ConnectionsValid();
          }
          NewConnectionsHelper(uf1.input_width, uf1.output_width, forward_conn.connections, i_index_in_2);
          assert (i_index in connections);
          assert (forward_index == forward_conn.connections[i_index_in_2]);
          assert (index == connections[i_index]) by {
            reveal InternalConnection.ConnectionsValid();
            NewConnectionsHelper(uf1.input_width, uf1.output_width, forward_conn.connections, i_index_in_2);
            assert i_index_in_2 + uf1.input_width in connections;
          }
        } else {
          // We know that:
          // var (from_output, index) := nio2i[i_index];
          // var (forward_from_output, forward_index) := forward_conn.nio2i[i_index - uf1.input_width];
          assert forward_index == index - uf1.input_width by {
            reveal NewNIO2I();
          } 
          assert forward_index < ni_width - uf1.input_width by {
            reveal InternalConnection.ToIMapValid();
          }
          assert index < ni_width;
          assert i2ni[index] == i_index &&
                 forward_conn.i2ni[index - uf1.input_width] == i_index - uf1.input_width by {
            reveal InternalConnection.ToNIMapValid();
            reveal InternalConnection.ToIMapValid();
            reveal NewI2NI();
            assert i2ni[index] == i_index;
          }
          assert (i_index !in connections) by {
            reveal InternalConnection.ToIMapValid();
            reveal InternalConnection.ToNIMapValid();
            assert i_index_in_2 !in forward_conn.connections;
            reveal NewConnections();
            NewConnectionsHelper2(uf1.input_width, forward_conn.connections, i_index_in_2);
            assert connections == NewConnections(uf1.input_width, forward_conn.connections);
            assert i_index_in_2 + uf1.input_width !in connections;
          }
        }
      }
    }
    reveal InternalConnection.ToIMapValid();
  }

  function ForwardConnectionToInternalConnectionImpl(
    uf1: UpdateFunction, uf2: UpdateFunction, forward_conn: InternalConnection): (internal_conn: InternalConnection)
    requires uf1.Valid()
    requires uf2.Valid()
    requires forward_conn.Valid()
    requires forward_conn.i_width == uf2.input_width
    requires forward_conn.o_width == uf1.output_width
    ensures internal_conn.BasicValid()
  {
    var ni_width := uf1.input_width + forward_conn.ni_width;
    var i_width := uf1.input_width + uf2.input_width;
    var o_width := uf1.output_width + uf2.output_width;
    // For the connections the keys are now pointing at the combined inputs and must be increases by uf1.input_width
    // The values are pointing at combined outputs but are unchanged.
    var connections := NewConnections(uf1.input_width, forward_conn.connections);
    var i2ni := NewI2NI(uf1.input_width, ni_width, forward_conn.i2ni);
    var nio2i := NewNIO2I(uf1.input_width, uf2.input_width, forward_conn.nio2i);
    var internal_conn := InternalConnection(ni_width, i_width, o_width, connections, i2ni, nio2i);
    reveal Seq.HasNoDuplicates();
    assert (ni_width <= i_width);
    assert (i_width <= ni_width + o_width);
    assert (|i2ni| == ni_width);
    assert (|nio2i| == i_width);
    assert Seq.HasNoDuplicates(i2ni);
    assert Seq.HasNoDuplicates(nio2i);
    internal_conn
  }

  function ForwardConnectionToInternalConnection(
      uf1: UpdateFunction, uf2: UpdateFunction, forward_conn: InternalConnection): (internal_conn: InternalConnection)
    // Transform a connection that is connection uf1 outputs to uf2 inputs to a connection that is connecting
    // the merged outputs to the merged inputs.
    requires uf1.Valid()
    requires uf2.Valid()
    requires forward_conn.Valid()
    requires forward_conn.i_width == uf2.input_width
    requires forward_conn.o_width == uf1.output_width
    ensures internal_conn.connections.Values == forward_conn.connections.Values
    ensures forall i_index :: i_index in internal_conn.connections.Keys ==> i_index >= uf1.input_width
    ensures forall o_index :: o_index in internal_conn.connections.Values ==> o_index < uf1.output_width
    ensures internal_conn.Valid()
  {
    var internal_conn := ForwardConnectionToInternalConnectionImpl(uf1, uf2, forward_conn);
    var i_width := internal_conn.i_width;
    var ni_width := internal_conn.ni_width;
    var o_width := internal_conn.o_width;
    var nio2i := internal_conn.nio2i;
    var connections := internal_conn.connections;
    var i2ni := internal_conn.i2ni;

    assert internal_conn.BasicValid();
    assert internal_conn.ToNIMapValid() by {
      reveal InternalConnection.ToNIMapValid();
      reveal NewI2NI();
      reveal NewNIO2I();
    }
    InternalConnectionToIMapValid(uf1, uf2, forward_conn);
    assert internal_conn.ConnectionsValid() by {
      reveal InternalConnection.ConnectionsValid();
      reveal NewConnections();
      assert (forall index: nat :: index in connections.Values ==> index < o_width);
      assert (forall index: nat :: index in connections.Keys ==> index < i_width);
    }
    reveal InternalConnection.ConnectionsValid();
    NewConnectionsProperties(uf1.input_width, uf1.output_width, forward_conn.connections);
    internal_conn
  }

  lemma ForwardScufConnectionConsistent(c: Circuit, s1: Scuf, s2: Scuf, forward_conn: InternalConnection)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires MergeRequirements(c, s1, s2)
    requires forward_conn.Valid()
    requires forward_conn.i_width == s2.uf.input_width
    requires forward_conn.o_width == s1.uf.output_width
    ensures
      var internal_conn := ForwardConnectionToInternalConnection(s1.uf, s2.uf, forward_conn);
      var s_merged := MergeScufs(c, s1, s2);
      ScufConnectionConsistent(c, s_merged, internal_conn)
  {
    reveal Seq.ToSet();
    var internal_conn := ForwardConnectionToInternalConnection(s1.uf, s2.uf, forward_conn);
    var s := MergeScufs(c, s1, s2);
    assert ScufConnectionConsistent(c, s, internal_conn) by {
      reveal ScufConnectionConsistent();
      assert (internal_conn.i_width == s.uf.input_width);
      assert (internal_conn.o_width == s.uf.output_width);
      MergeScufsPathConstraints(c, s1, s2);
      var outputs_from_s1 := Seq.ToSet(s.mp.outputs[..s1.uf.output_width]);
      var inputs_to_s2 := Seq.ToSet(s.mp.inputs[s1.uf.input_width..]);
      assert !PathExistsBetweenNPSets(c, outputs_from_s1, inputs_to_s2);
      var conn_outputs := internal_conn.GetConnectedOutputs(s.mp);
      var conn_inputs := internal_conn.GetConnectedInputs(s.mp);
      assert forall o_index :: o_index in internal_conn.connections.Values
                ==> o_index < s1.uf.output_width by {
        reveal InternalConnection.ConnectionsValid();
      }
      assert conn_outputs <= outputs_from_s1;
      assert forall i_index :: i_index in internal_conn.connections.Keys
                ==> s1.uf.input_width <= i_index < s1.uf.input_width + s2.uf.input_width by {
        reveal InternalConnection.ConnectionsValid();
      }
      assert conn_inputs <= inputs_to_s2;
      NoPathExistsBetweenNPSubSets(c, outputs_from_s1, inputs_to_s2, conn_outputs, conn_inputs);
      assert !PathExistsBetweenNPSets(c, conn_outputs, conn_inputs);
      forall i_index | i_index in internal_conn.connections
        ensures s.mp.inputs[i_index] !in c.PortSource
      {
        reveal IsIsland();
        InputsOfIslandNotInPortSource(c, s); 
        assert s.mp.inputs[i_index] !in c.PortSource;
      }
    }
  }

  opaque function ForwardConnectionModifierImpl(
      z1: ScufInserter, z2: ScufInserter, conn: InternalConnection): (z: ScufInserter)
    requires z1.Valid()
    requires z2.Valid()
    requires conn.Valid()
    requires conn.i_width == z2.uf.input_width
    requires conn.o_width == z1.uf.output_width
    ensures z.Valid()
  {
    reveal Seq.ToSet();
    reveal ScufInserter.Valid();

    var z_par := MergeModifier(z1, z2);

    var internal_conn := ForwardConnectionToInternalConnection(z1.uf, z2.uf, conn);

    assert InserterConnectionConsistent(z_par, internal_conn) by {
      assert UFConnectionConsistent(z_par.uf, internal_conn) by {
        assert (internal_conn.i_width == z_par.uf.input_width);
        assert (internal_conn.o_width == z_par.uf.output_width);
      }
      forall c: Circuit | c.Valid()
        ensures
          var (new_c, s) := z_par.fn(c);
          && new_c.Valid() && s.Valid(new_c)
          && ScufConnectionConsistent(new_c, s, internal_conn)
      {
        var (new_c, s) := z_par.fn(c);
        assert z_par.Valid();
        z_par.ValidForCircuit(c);
        reveal SimpleInsertion();
        assert new_c.Valid();
        var (intermed_c, s1, s2) := InsertTwo(c, z1, z2);
        assert MergeRequirements(intermed_c, s1, s2) by {
          reveal DualInsertion();
        }
        assert intermed_c == new_c && s == MergeScufs(new_c, s1, s2) by {
          reveal MergeInserter();
          reveal MergeModifier();
        }
        ForwardScufConnectionConsistent(new_c, s1, s2, conn);
      }
      reveal InserterConnectionConsistent();
    }

    var z_connected := ConnectModifier(z_par, internal_conn);
    assert z_connected.Valid();
    z_connected
  }

  lemma ForwardConnectBaseUFIsImplUF(z1: ScufInserter, z2: ScufInserter, conn: InternalConnection)
    requires z1.Valid()
    requires z2.Valid()
    requires conn.Valid()
    requires conn.i_width == z2.uf.input_width
    requires conn.o_width == z1.uf.output_width
    ensures
      reveal ScufInserter.Valid();
      ForwardConnectionModifierImpl(z1, z2, conn).uf == ForwardConnectBaseUF(z1.uf, z2.uf, conn)
  {
    reveal ScufInserter.Valid();
    reveal ForwardConnectionModifierImpl();
  }

  lemma ForwardConnectBaseUFIsScufUF(c: Circuit, s1: Scuf, s2: Scuf, conn: InternalConnection)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires MergeRequirements(c, s1, s2)
    requires conn.Valid()
    requires conn.i_width == s2.uf.input_width
    requires conn.o_width == s1.uf.output_width
    ensures
      ForwardConnectImpl(c, s1, s2, conn).1.uf == ForwardConnectBaseUF(s1.uf, s2.uf, conn)
  {
  }

  function ForwardConnectBaseUF(uf1: UpdateFunction, uf2: UpdateFunction, conn: InternalConnection): (uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    requires conn.Valid()
    requires conn.i_width == uf2.input_width
    requires conn.o_width == uf1.output_width
    ensures uf.Valid()
  {
    var uf_par := MergeUpdateFunctions(uf1, uf2);
    var internal_connection := ForwardConnectionToInternalConnection(uf1, uf2, conn);
    var uf_connect := ConnectUpdateFunction(uf_par, internal_connection);
    uf_connect
  }

  lemma ForwardConnectionUFEquivInternal(uf1: UpdateFunction, uf2: UpdateFunction, forward_conn: InternalConnection, si: SI)
    requires uf1.Valid()
    requires uf2.Valid()
    requires forward_conn.Valid()
    requires forward_conn.i_width == uf2.input_width
    requires forward_conn.o_width == uf1.output_width
    requires 
      var new_uf := ForwardConnectUF(uf1, uf2, forward_conn);
      new_uf.SIVal(si)
    ensures 
      var uf_base := ForwardConnectBaseUF(uf1, uf2, forward_conn);
      var new_uf := ForwardConnectUF(uf1, uf2, forward_conn);
      && uf_base.sf.requires(si)
      && new_uf.sf.requires(si)
      && (new_uf.sf(si) == uf_base.sf(si))
    {
      var new_uf := ForwardConnectUF(uf1, uf2, forward_conn);
      var si1 := SI(si.inputs[..uf1.input_width], si.state[..uf1.state_width]);
      reveal UpdateFunction.Valid();
      var so1 := uf1.sf(si1);
      var sni2_inputs := si.inputs[uf1.input_width..];
      var si2_inputs := forward_conn.NIO2I(sni2_inputs, so1.outputs);
      var si2 := SI(si2_inputs, si.state[uf1.state_width..]);
      var so2 := uf2.sf(si2);
      var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
      assert so == new_uf.sf(si) by {
        reveal ForwardConnectUF();
      }

      var si_expanded := SI(si1.inputs + si2.inputs, si.state);

      var uf_par := MergeUpdateFunctions(uf1, uf2);
      assert so == uf_par.sf(si_expanded) by {
        reveal MergeUpdateFunctions();
      }
      var internal_connection := ForwardConnectionToInternalConnection(uf1, uf2, forward_conn);
      var uf_connect := ConnectUpdateFunction(uf_par, internal_connection);

      assert uf_connect.sf(si) == internal_connection.SNI2SOSecondPass(uf_par, si) by {
        reveal ConnectUpdateFunction();
      }

      // Following the logic inside SNI2SOSecondPass
      var so_first_pass := internal_connection.SNI2SOFirstPass(uf_par, si);
      var fake_output := seq(uf_par.output_width, (index: nat) requires index < uf_par.output_width => false);
      assert so_first_pass == internal_connection.SNI2SOFromOutputs(uf_par, si, fake_output);
      assert so_first_pass.outputs[..uf1.output_width] == so1.outputs by {
        var si_with_fake := internal_connection.SNI2SIFromOutputs(si, fake_output);
        assert si_with_fake.inputs == internal_connection.NIO2I(si.inputs, fake_output);
        forall index: nat | index < uf1.input_width
          ensures si_with_fake.inputs[index] == si1.inputs[index]
        {
          NewNIO2IProperties(uf1.input_width, uf2.input_width, forward_conn.nio2i, index);
          assert si_with_fake.inputs[index] == si1.inputs[index];
        }
        assert si_with_fake.inputs[..uf1.input_width] == si1.inputs;
        reveal UpdateFunction.Valid();
        reveal MergeUpdateFunctions();
        var so := uf_par.sf(si_with_fake);
      }

      var si_second_pass := internal_connection.SNI2SIFromOutputs(si, so_first_pass.outputs);
      assert si_second_pass == si_expanded by {
        forall index: nat | index < uf1.input_width + uf2.input_width
          ensures si_second_pass.inputs[index] == si_expanded.inputs[index]
        {
          NewNIO2IProperties(uf1.input_width, uf2.input_width, forward_conn.nio2i, index);
          if index < uf1.input_width {
            assert si_second_pass.inputs[index] == si_expanded.inputs[index];
          } else {
            assert si_expanded.inputs[index] == forward_conn.NIO2I(sni2_inputs, so1.outputs)[index- uf1.input_width];
            assert si_second_pass.inputs[index] == internal_connection.NIO2I(si.inputs, so_first_pass.outputs)[index];
            var (forward_from_output, forward_index) := forward_conn.nio2i[index-uf1.input_width];
            reveal InternalConnection.ToIMapValid();
            if forward_from_output {
              assert forward_index < |so_first_pass.outputs|;
            } else {
              assert forward_index < forward_conn.ni_width;
            }
            assert internal_connection.nio2i[index] ==
              (if forward_from_output then hack(true, forward_index) else hack(false, forward_index + uf1.input_width));
            assert si_second_pass.inputs[index] ==
              (if forward_from_output then so_first_pass.outputs[forward_index] else si.inputs[forward_index + uf1.input_width]);
            reveal NewNIO2I();
            assert si_second_pass.inputs[index] == si_expanded.inputs[index];
          }
        }
      }
      reveal UpdateFunction.Valid();
      assert uf_connect.sf(si) == uf_par.sf(si_second_pass);

      assert so == uf_connect.sf(si);
    }

  lemma ForwardConnectionUFEquiv(uf1: UpdateFunction, uf2: UpdateFunction, conn: InternalConnection)
    requires uf1.Valid()
    requires uf2.Valid()
    requires conn.Valid()
    requires conn.i_width == uf2.input_width
    requires conn.o_width == uf1.output_width
    ensures 
      var uf_base := ForwardConnectBaseUF(uf1, uf2, conn);
      var new_uf := ForwardConnectUF(uf1, uf2, conn);
      UpdateFunctionsEquiv(new_uf, uf_base)
  {
    var uf_base := ForwardConnectBaseUF(uf1, uf2, conn);
    var new_uf := ForwardConnectUF(uf1, uf2, conn);
    assert UpdateFunctionsEquiv(new_uf, uf_base) by {
      forall si: SI | new_uf.SIVal(si)
        ensures
          && uf_base.sf.requires(si)
          && new_uf.sf.requires(si)
          && (new_uf.sf(si) == uf_base.sf(si))
      {
        ForwardConnectionUFEquivInternal(uf1, uf2, conn, si);
        assert new_uf.sf(si) == uf_base.sf(si);
      }
      reveal UpdateFunctionsEquiv();
    }
  }

  function ForwardConnectImpl(c: Circuit, s1: Scuf, s2: Scuf, conn: InternalConnection): (new_c_s: (Circuit, Scuf))
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires MergeRequirements(c, s1, s2)
    requires conn.Valid()
    requires conn.i_width == s2.uf.input_width
    requires conn.o_width == s1.uf.output_width
    ensures
      var (new_c, new_s) := new_c_s;
      && new_c.Valid()
      && new_s.Valid(new_c)
      && s1.uf.Valid()
      && s2.uf.Valid()
  {
    var s_par := MergeScufs(c, s1, s2);
    var internal_conn := ForwardConnectionToInternalConnection(s1.uf, s2.uf, conn);
    ForwardScufConnectionConsistent(c, s1, s2, conn);
    assert ScufConnectionConsistent(c, s_par, internal_conn);
    var (new_c, new_s) := ConnectCircuitScuf(c, s_par, internal_conn);
    (new_c, new_s)
  }

  opaque function ForwardConnect(c: Circuit, s1: Scuf, s2: Scuf, conn: InternalConnection): (new_c_s: (Circuit, Scuf))
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires MergeRequirements(c, s1, s2)
    requires conn.Valid()
    requires conn.i_width == s2.uf.input_width
    requires conn.o_width == s1.uf.output_width
    ensures
      var (new_c, new_s) := new_c_s;
      && new_c.Valid()
      && new_s.Valid(new_c)
      && s1.uf.Valid()
      && s2.uf.Valid()
      && (new_s.uf == ForwardConnectUF(s1.uf, s2.uf, conn))
  {
    var (new_c, intermed_s) := ForwardConnectImpl(c, s1, s2, conn);
    var new_uf := ForwardConnectUF(s1.uf, s2.uf, conn);
    assert UpdateFunctionsEquiv(intermed_s.uf, new_uf) by {
      ForwardConnectionUFEquiv(s1.uf, s2.uf, conn);
      ForwardConnectBaseUFIsScufUF(c, s1, s2, conn);
      reveal UpdateFunctionsEquiv();
    }
    var new_s := ScufSwapUF(new_c, intermed_s, new_uf);
    (new_c, new_s)
  }

  opaque function ForwardConnectionModifier(
      z1: ScufInserter, z2: ScufInserter, conn: InternalConnection): (z: ScufInserter)
    requires z1.Valid()
    requires z2.Valid()
    requires conn.Valid()
    requires conn.i_width == z2.uf.input_width
    requires conn.o_width == z1.uf.output_width
    ensures z.Valid()
    ensures
      && z1.uf.Valid()
      && z2.uf.Valid()
      && (z.uf == ForwardConnectUF(z1.uf, z2.uf, conn))
  {
    reveal Seq.ToSet();
    reveal ScufInserter.Valid();

    var z_conn := ForwardConnectionModifierImpl(z1, z2, conn);
    var new_uf := ForwardConnectUF(z1.uf, z2.uf, conn);
    assert UpdateFunctionsEquiv(new_uf, z_conn.uf) by {
      ForwardConnectionUFEquiv(z1.uf, z2.uf, conn);
      ForwardConnectBaseUFIsImplUF(z1, z2, conn);
    }
    var z := SwitchUFModifier(z_conn, new_uf);
    z
  }
}
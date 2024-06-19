module SelfConnect {

  import opened Circ
  import opened ConservedSubcircuit
  import opened Scuf
  import opened MapConnection
  import opened MapFunction
  import opened Eval
  import opened Connection
  import opened Utils
  import opened Subcircuit

  // A scuf is modified such that some of its outputs are connected to the inputs.
  // The outputs remain unchanged, but the new input width is reduced.
  // `InternalConnection` defines a mapping from the (new_inputs, outputs) to the original inputs.
  datatype InternalConnection = InternalConnection(
    ni_width: nat,  // Width of the new inputs
    i_width: nat,   // Width of the original inputs
    o_width: nat,   // Width of the outputs.
    connections: map<nat, nat>, // Maps input indices to output indices
    i2ni: seq<nat>, // A map that can be used to generate new_inputs from inputs.
    nio2i: seq<(bool, nat)> // A map to generate inputs from new_inputs and outputs.
  ) {
    ghost opaque predicate Valid() {
      && (ni_width <= i_width)
      && (i_width <= ni_width + o_width)
      && (|i2ni| == ni_width)
      && (|nio2i| == i_width)
      && Seq.HasNoDuplicates(i2ni)
      && Seq.HasNoDuplicates(nio2i)
      && (forall index: nat :: index in connections.Values ==> index < o_width)
      && (forall index: nat :: index in connections.Keys ==> index < i_width)
      && (forall ni_index: nat :: ni_index < ni_width ==> (
        var i_index: nat := i2ni[ni_index];
        && (i_index < i_width)
        && var (from_output, index) := nio2i[i_index];
        && (!from_output)
        && (index == ni_index)
      ))
      && (forall i_index: nat :: i_index < i_width ==> (
        var (from_output, index) := nio2i[i_index];
        && ((!from_output) ==> index < ni_width && i2ni[index] == i_index && (i_index !in connections))
        && ((from_output) ==> index < o_width && (i_index in connections) && (index == connections[i_index]))
      ))
    }
    function NIO2I<T>(bni: seq<T>, bo: seq<T>): (bi: seq<T>)
      requires Valid()
      requires |bni| == ni_width
      requires |bo| == o_width
      ensures |bi| == i_width
    {
      reveal Valid();
      seq(i_width, (i_index: int) requires 0 <= i_index < i_width =>
        var (from_output, index) := nio2i[i_index];
        if !from_output then
          bni[index]
        else
          bo[index]
      )
    }

    function I2NI<T>(bi: seq<T>): (bni: seq<T>)
      requires Valid()
      requires |bi| == i_width
      ensures |bni| == ni_width
    {
      reveal Valid();
      seq(ni_width, (ni_index: int) requires 0 <= ni_index < ni_width =>
        var i_index := i2ni[ni_index];
        assert i_index < i_width;
        bi[i_index])
    }

    function MapConnectedInputs<T(==)>(bi: seq<T>): (r: set<T>)
      requires Valid()
      requires |bi| == i_width
    {
      reveal Valid();
      (set index | index in connections :: bi[index])
    }

    lemma I2NIProperties<T>(bi: seq<T>)
      requires Valid()
      requires |bi| == i_width
      requires Seq.HasNoDuplicates(bi)
      ensures
        var bni := I2NI(bi);
        reveal Valid();
        && Seq.HasNoDuplicates(bni)
        && Seq.ToSet(bni) == Seq.ToSet(bi) - MapConnectedInputs(bi)
    {
      reveal Valid();
      reveal Seq.ToSet();
      reveal Seq.HasNoDuplicates();
      var bni := I2NI(bi);
      forall i_index: nat | i_index < i_width
        ensures bi[i_index] in Seq.ToSet(bni) || bi[i_index] in MapConnectedInputs(bi)
      {
        var (from_output, index) := nio2i[i_index];
        if from_output {
          assert bi[i_index] in MapConnectedInputs(bi);
        } else {
          reveal Seq.ToSet();
          assert bi[i_index] == bni[index];
          assert bi[i_index] in Seq.ToSet(bni);
        }
      }
    }

    lemma NIO2I2NI<T>(bni: seq<T>, bo: seq<T>)
      requires Valid()
      requires |bni| == ni_width
      requires |bo| == o_width
      ensures I2NI(NIO2I(bni, bo)) == bni
    {
      reveal Valid();
    }

    function GetConnectedInputs(mp: ScufMap): (r: set<NP>)
      requires Valid()
      requires MPConnectionConsistent(mp, this)
      ensures r <= Seq.ToSet(mp.inputs)
    {
      reveal Valid();
      reveal Seq.ToSet();
      (set i_index | i_index in connections :: mp.inputs[i_index])
    }

    function GetConnectedOutputs(mp: ScufMap): (r: set<NP>)
      requires Valid()
      requires MPConnectionConsistent(mp, this)
      ensures r <= Seq.ToSet(mp.outputs)
    {
      reveal Valid();
      reveal Seq.ToSet();
      (set o_index | o_index in connections.Values :: mp.outputs[o_index])
    }

    lemma GetConnectionProperties(c: Circuit, s: Scuf)
      requires Valid()
      requires c.Valid()
      requires s.Valid(c)
      requires ScufConnectionConsistent(c, s, this)
      ensures
        reveal ScufConnectionConsistent();
        var r := GetConnection(s.mp);
        && (forall onp :: onp in r.Values ==> ONPValid(c, onp))
        && (forall inp :: inp in r ==> INPValid(c, inp))
        && (forall inp :: inp in r ==> NoPathInScuf(c, s, r[inp], inp))
        && MPConnectionConsistent(s.mp, this)
        && (r.Keys == GetConnectedInputs(s.mp))
        && (r.Values == GetConnectedOutputs(s.mp))
        && ConnectCircuitRequirements(c, r)
    {
      reveal ScufConnectionConsistent();
      var np_connections := GetConnection(s.mp);
      reveal Seq.ToSet();
      s.SomewhatValidToRelaxInputs(c);
      ScufFInputsAreValid(c, s);
      ScufFOutputsAreValid(c, s);
      assert ConnectCircuitRequirements(c, np_connections) by {
        reveal ConnectCircuitRequirements();
      }
    }

    function GetConnection(mp: ScufMap): (r: map<NP, NP>)
      requires Valid()
      requires mp.Valid()
      requires MPConnectionConsistent(mp, this)
      ensures MPConnectionConsistent(mp, this)
      ensures r.Keys == GetConnectedInputs(mp)
      ensures r.Values == GetConnectedOutputs(mp)
    {
      reveal Valid();
      assert |mp.inputs| == i_width;
      assert (forall index: nat :: index in connections.Keys ==> index < i_width);
      assert Seq.HasNoDuplicates(mp.inputs);
      reveal Seq.HasNoDuplicates();
      var np_connections := (map i_index | i_index in connections :: mp.inputs[i_index] := mp.outputs[connections[i_index]]);
      assert np_connections.Values == GetConnectedOutputs(mp) by {
        forall onp | onp in np_connections.Values
          ensures onp in GetConnectedOutputs(mp)
        {
          var o_index: nat :| o_index < |mp.outputs| && mp.outputs[o_index] == onp;
          assert o_index in connections.Values;
        }
        forall onp | onp in GetConnectedOutputs(mp)
          ensures onp in np_connections.Values
        {
          var o_index: nat :| o_index < |mp.outputs| && mp.outputs[o_index] == onp;
          assert o_index in connections.Values;
          var i_index :| i_index in connections && connections[i_index] == o_index;
          assert onp == mp.outputs[connections[i_index]];
          assert np_connections[mp.inputs[i_index]] == onp;
        }
      }
      np_connections
    }

    function FIFirstPass(mp: ScufMap, fi: FI): (fi_first_pass: FI)
      requires Valid()
      requires mp.Valid()
      requires MPConnectionConsistent(mp, this)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures fi_first_pass.state == fi.state
      ensures FIValid(fi_first_pass, mp.inputs, mp.state)
    {
      var output_width := |mp.outputs|;
      var fake_output := seq(output_width, (index: nat) requires index < output_width => false);
      var new_mp := ConnectScufMap(mp, this);
      var sni_first_pass := new_mp.fi2si(fi);
      var si_first_pass := SI(NIO2I(sni_first_pass.inputs, fake_output), sni_first_pass.state);
      var fi_first_pass := mp.si2fi(si_first_pass);
      assert fi_first_pass.state == fi.state by {
        MapToSeqToMap(mp.state, fi.state);
      }
      fi_first_pass
    }

    function FISecondPass(mp: ScufMap, uf: UpdateFunction, fi: FI): (fi_second_pass: FI)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires UFConnectionConsistent(uf, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures FIValid(fi_second_pass, mp.inputs, mp.state)
    {
      var new_mp := ConnectScufMap(mp, this);
      var sni_first_pass := new_mp.fi2si(fi);
      var fake_outputs := seq(uf.output_width, (index: nat) requires index < uf.output_width => false);
      var si_first_pass := SI(NIO2I(sni_first_pass.inputs, fake_outputs), sni_first_pass.state);
      reveal UpdateFunction.Valid();
      var so_first_pass := uf.sf(si_first_pass);
      var si_second_pass := SI(NIO2I(sni_first_pass.inputs, so_first_pass.outputs), sni_first_pass.state);
      var fi_second_pass := mp.si2fi(si_second_pass);
      fi_second_pass
    }

  }

  ghost predicate NoPathInScuf(c: Circuit, s: Scuf, onp: NP, inp: NP)
    requires c.Valid()
    requires s.Valid(c)
    requires NPValid(c, onp)
  {
    forall fi: FI :: FIValid(fi, s.mp.inputs, s.mp.state) ==> (
      assert FICircuitValid(c, fi) by {
        s.SomewhatValidToRelaxInputs(c);
        ScufValidFiValidToFICircuitValid(c, s, fi);
      }
      var new_fi := FI(fi.inputs - {inp}, fi.state);
      assert FICircuitValid(c, new_fi) by {
        reveal FICircuitValid();
      }
      Evaluate(c, onp, fi) == Evaluate(c, onp, new_fi)
    )
  }

  opaque ghost predicate ScufConnectionConsistent(c: Circuit, s: Scuf, conn: InternalConnection)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
  {
    reveal InternalConnection.Valid();
    && (conn.i_width == s.uf.input_width)
    && (conn.o_width == s.uf.output_width)
    && (forall i_index, o_index :: i_index in conn.connections && o_index in conn.connections.Values ==>
        var inp := s.mp.inputs[i_index];
        var onp := s.mp.outputs[o_index];
        s.SomewhatValidToRelaxInputs(c);
        ScufFOutputsAreValid(c, s);
        ScufFInputsAreValid(c, s);
        NoPathInScuf(c, s, onp, inp))
    && (forall i_index :: i_index in conn.connections ==> s.mp.inputs[i_index] !in c.PortSource)
  }

  predicate UFConnectionConsistent(uf: UpdateFunction, conn: InternalConnection)
  {
    && (conn.i_width == uf.input_width)
    && (conn.o_width == uf.output_width)
  }

  predicate MPConnectionConsistent(mp: ScufMap, conn: InternalConnection)
  {
    && (conn.i_width == |mp.inputs|)
    && (conn.o_width == |mp.outputs|)
  }

  lemma ScufConsistentUFMPConsistent(c: Circuit, s: Scuf, conn: InternalConnection)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    ensures UFConnectionConsistent(s.uf, conn)
    ensures MPConnectionConsistent(s.mp, conn)
  {
    reveal ScufConnectionConsistent();
  }

  opaque ghost predicate InserterConnectionConsistent(z: ScufInserter, conn: InternalConnection)
    requires z.Valid()
    requires conn.Valid()
  {
    reveal ScufInserter.Valid();
    && UFConnectionConsistent(z.uf, conn)
    && forall c: Circuit :: c.Valid() ==> (
      z.ValidForCircuit(c);
      var (new_c, s) := z.fn(c);
      assert new_c.Valid() && s.Valid(new_c) by {
        reveal SimpleInsertion();
      }
      ScufConnectionConsistent(new_c, s, conn)
    )
  }

  function ConnectUpdateFunction(uf: UpdateFunction, conn: InternalConnection): (new_uf: UpdateFunction)
    requires uf.Valid()
    requires conn.Valid()
    requires UFConnectionConsistent(uf, conn)
    ensures new_uf.Valid()
  {
    reveal UpdateFunction.Valid();
    UpdateFunction(
      conn.ni_width,
      uf.output_width,
      uf.state_width,
      (sni: SI) requires |sni.inputs| == conn.ni_width && |sni.state| == uf.state_width =>
        var fake_bo := seq(uf.output_width, index requires 0 <= index < uf.output_width => false);
        var fake_bi := conn.NIO2I(sni.inputs, fake_bo);
        var fake_si := SI(fake_bi, sni.state);
        var fake_so := uf.sf(fake_si);
        var bi := conn.NIO2I(sni.inputs, fake_so.outputs);
        var si := SI(bi, sni.state);
        var so := uf.sf(si);
        so
    )
  }


  lemma SelfConnectFirstPassMFLookup(s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    requires s.MapValid()
    requires conn.Valid()
    requires MPConnectionConsistent(s.mp, conn)
    requires UFConnectionConsistent(s.uf, conn)
    requires np in conn.GetConnectedOutputs(s.mp)
    requires
      var new_s := ConnectScuf(s, conn);
      FIValid(fi, new_s.mp.inputs, new_s.mp.state)
    ensures
      var new_s := ConnectScuf(s, conn);
      var fi_first_pass := conn.FIFirstPass(s.mp, fi);
      assert FIValid(fi_first_pass, s.mp.inputs, s.mp.state);
      reveal Seq.ToSet();
      MFLookup(s, fi_first_pass, np) == MFLookup(new_s, fi, np)
  {
  }

  lemma SelfConnectSecondPassMFLookup(s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    requires s.MapValid()
    requires conn.Valid()
    requires MPConnectionConsistent(s.mp, conn)
    requires UFConnectionConsistent(s.uf, conn)
    requires np in s.mp.outputs || np in StateINPs(s.mp.state)
    requires
      var new_s := ConnectScuf(s, conn);
      FIValid(fi, new_s.mp.inputs, new_s.mp.state)
    ensures
      var new_s := ConnectScuf(s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      assert FIValid(fi_second_pass, s.mp.inputs, s.mp.state);
      reveal Seq.ToSet();
      MFLookup(s, fi_second_pass, np) == MFLookup(new_s, fi, np)
  {
  }

  function ConnectScufMap(mp: ScufMap, conn: InternalConnection): (new_mp: ScufMap)
    requires mp.Valid()
    requires conn.Valid()
    requires MPConnectionConsistent(mp, conn)
    ensures new_mp.Valid()
    ensures
      var connection := conn.GetConnection(mp);
      && Seq.ToSet(new_mp.inputs) + connection.Keys == Seq.ToSet(mp.inputs)
      && Seq.ToSet(new_mp.inputs) == Seq.ToSet(mp.inputs) - connection.Keys
  {
    var new_mp := ScufMap(
      conn.I2NI(mp.inputs),
      mp.outputs,
      mp.state);
    conn.I2NIProperties(mp.inputs);
    new_mp
  }

  function ConnectScuf(s: Scuf, conn: InternalConnection): (new_scuf: Scuf)
    requires s.MapValid()
    requires conn.Valid()
    requires UFConnectionConsistent(s.uf, conn)
    ensures new_scuf.MapValid()
  {
    var new_s := Scuf(s.sc, ConnectScufMap(s.mp, conn), ConnectUpdateFunction(s.uf, conn));
    assert new_s.MapValid() by {
      assert new_s.mp.Valid();
      assert new_s.mp.InSc(new_s.sc) by {
        reveal NPsInSc();
      }
      assert new_s.uf.Valid();
      assert ScufMapUpdateFunctionConsistent(new_s.mp, new_s.uf);
    }
    new_s
  }

  lemma ConnectCircuitConnOutputsConstant(c: Circuit, s: Scuf, conn: InternalConnection)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    ensures
      var connection := conn.GetConnection(s.mp);
      var new_c := ConnectCircuit(c, connection);
      ConnOutputs(c, s.sc) == ConnOutputs(new_c, s.sc)
  {
  }

  lemma ConnectCircuitAllInputsDecreases(c: Circuit, s: Scuf, conn: InternalConnection)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    ensures
      var connection := conn.GetConnection(s.mp);
      var new_c := ConnectCircuit(c, connection);
      && AllInputs(c, s.sc) == AllInputs(new_c, s.sc) + connection.Keys
      && AllInputs(c, s.sc) - connection.Keys == AllInputs(new_c, s.sc)
  {
  }

  function ConnectCircuitScufImpl(c: Circuit, s: Scuf, conn: InternalConnection): (r: (Circuit, Scuf))
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    ensures
      var (new_c, new_s) := r;
      && new_c.Valid()
      && s.MapValid()
      && ScValid(c, s.sc)
      && s.SomewhatValidRelaxInputs(c)
      && new_s.MapValid()
      && new_s.SomewhatValid(new_c)
  {
    reveal ScufConnectionConsistent();
    var connection := conn.GetConnection(s.mp);
    conn.GetConnectionProperties(c, s);
    var new_c := ConnectCircuit(c, connection);
    var new_s := ConnectScuf(s, conn);
    assert new_s.SomewhatValid(new_c) by {
      assert s.Valid(c);
      reveal Scuf.SomewhatValid();
      assert ScValid(new_c, new_s.sc) by {
        reveal ScValid();
      }
      assert (AllONPs(new_c, new_s.sc) >= Seq.ToSet(new_s.mp.outputs) >= ConnOutputs(new_c, new_s.sc)) by {
        reveal AllONPs();
        reveal Seq.ToSet();
        reveal ConnOutputs();
        ConnectCircuitConnOutputsConstant(c, s, conn);
        assert ConnOutputs(new_c, new_s.sc) == ConnOutputs(c, s.sc);
      }
      assert (Seq.ToSet(new_s.mp.inputs) == AllInputs(new_c, new_s.sc)) by {
        assert Seq.ToSet(s.mp.inputs) == AllInputs(c, new_s.sc);
        ConnectCircuitAllInputsDecreases(c, s, conn);
        assert Seq.ToSet(new_s.mp.inputs) == Seq.ToSet(s.mp.inputs) - connection.Keys;
        assert AllInputs(new_c, new_s.sc) == AllInputs(c, s.sc) - connection.Keys;
      }
      assert (Seq.ToSet(new_s.mp.state) == AllSeq(new_c, new_s.sc)) by {
        reveal AllSeq();
      }
    }
    assert s.ValidRelaxInputs(new_c) by {
      assert ScValid(new_c, s.sc) by {
        assert ScValid(c, s.sc);
        reveal ScValid();
        assert new_c.NodeKind == c.NodeKind;
      }
      assert s.SomewhatValidRelaxInputs(new_c) by {
      }
      assert s.EvaluatesCorrectly(new_c) by {
      }
    }
    (new_c, new_s)
  }

  function ConnectCircuitScuf(c: Circuit, s: Scuf, conn: InternalConnection): (r: (Circuit, Scuf))
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    ensures
      var (new_c, new_s) := r;
      && new_c.Valid()
      && new_s.Valid(new_c)
      && s.ValidRelaxInputs(new_c)
  {
    reveal ScufConnectionConsistent();
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s,conn);
    assert new_s.Valid(new_c) by {
      assert ScValid(new_c, s.sc) by {
        assert ScValid(c, s.sc);
        reveal ScValid();
        assert new_c.NodeKind == c.NodeKind;
      }
      assert s.SomewhatValid(new_c) by {
      }
      assert s.EvaluatesCorrectly(new_c) by {
      }
    }
    (new_c, new_s)
  }

}
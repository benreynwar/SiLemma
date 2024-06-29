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
  import opened Path

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

    opaque function I2NIInternal<T>(bi: seq<T>, ni_index: nat): (bni: seq<T>)
      requires Valid()
      requires |bi| == i_width
      requires ni_index <= ni_width
      ensures |bni| == ni_index
      ensures forall index: nat :: index < ni_index ==>
        reveal Valid();
        bni[index] == bi[i2ni[index]]
      decreases ni_index
    {
      if ni_index == 0 then
        []
      else
        reveal Valid();
        var i_index := i2ni[ni_index-1];
        I2NIInternal(bi, ni_index-1) + [bi[i_index]]
    }

    function I2NI<T>(bi: seq<T>): (bni: seq<T>)
      requires Valid()
      requires |bi| == i_width
      ensures |bni| == ni_width
    {
      reveal I2NIInternal();
      I2NIInternal(bi, ni_width)
    }

    lemma I2NICorrect<T>(bi: seq<T>)
      requires Valid()
      requires |bi| == i_width
      ensures 
        reveal Valid();
        var bni := I2NI(bi);
        forall ni_index: nat :: ni_index < ni_width ==>
          bni[ni_index] == bi[i2ni[ni_index]]
    {
      reveal Valid();
      reveal I2NIInternal();
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

    lemma NI2NIO2I<T>(bi: seq<T>, bo: seq<T>)
      requires Valid()
      requires |bi| == i_width
      requires |bo| == o_width
      requires forall i_index: nat :: i_index < i_width ==> (
        reveal Valid();
        var (from_output, index) := nio2i[i_index];
        from_output ==> bi[i_index] == bo[index]
      )
      ensures NIO2I(I2NI(bi), bo) == bi
    {
      reveal Valid();
      I2NICorrect(bi);
      var bni := I2NI(bi);
      assert forall ni_index: nat :: ni_index < ni_width ==>
        bni[ni_index] == bi[i2ni[ni_index]];
      var bi_new := NIO2I(bni, bo);
      forall i_index: nat | i_index < i_width
        ensures bi_new[i_index] == bi[i_index]
      {
        var (from_output, index) := nio2i[i_index];
        if !from_output {
          assert bi_new[i_index] == bni[index];
          assert bi_new[i_index] == bi[i_index];
        } else {
          assert bi_new[i_index] == bo[index];
          assert bi_new[i_index] == bi[i_index];
        }
      }
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
        && MPConnectionConsistent(s.mp, this)
        && (r.Keys == GetConnectedInputs(s.mp))
        && (r.Values == GetConnectedOutputs(s.mp))
        && reveal ONPsValid();
        && !PathExistsBetweenNPSets(c, r.Values, r.Keys)
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
      reveal ONPsValid();
      assert !PathExistsBetweenNPSets(c, np_connections.Values, np_connections.Keys) by {
        assert (np_connections.Keys == GetConnectedInputs(s.mp));
        assert (np_connections.Values == GetConnectedOutputs(s.mp));
        assert !PathExistsBetweenNPSets(c, GetConnectedOutputs(s.mp), GetConnectedInputs(s.mp));
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

    function SIFromOutputs(mp: ScufMap, fi: FI, outputs: seq<bool>): (si_from_outputs: SI)
      requires Valid()
      requires mp.Valid()
      requires MPConnectionConsistent(mp, this)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      requires |outputs| == |mp.outputs|
      ensures |si_from_outputs.state| == |mp.state|
      ensures |si_from_outputs.inputs| == |mp.inputs|
    {
      var output_width := |mp.outputs|;
      var new_mp := ConnectScufMap(mp, this);
      var sni_pass := new_mp.fi2si(fi);
      SI(NIO2I(sni_pass.inputs, outputs), sni_pass.state)
    }

    function SOFromOutputs(mp: ScufMap, uf: UpdateFunction, fi: FI, outputs: seq<bool>): (so_from_outputs: SO)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      requires |outputs| == |mp.outputs|
      ensures |so_from_outputs.state| == |mp.state|
      ensures |so_from_outputs.outputs| == |mp.outputs|
    {
      var si := SIFromOutputs(mp, fi, outputs);
      reveal UpdateFunction.Valid();
      var so := uf.sf(si);
      so
    }

    function FIFromOutputs(mp: ScufMap, fi: FI, outputs: seq<bool>): (fi_from_outputs: FI)
      requires Valid()
      requires mp.Valid()
      requires MPConnectionConsistent(mp, this)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      requires |outputs| == |mp.outputs|
      ensures fi_from_outputs.state == fi.state
      ensures FIValid(fi_from_outputs, mp.inputs, mp.state)
    {
      var si_pass := SIFromOutputs(mp, fi, outputs);
      var fi_pass := mp.si2fi(si_pass);
      assert fi_pass.state == fi.state by {
        MapToSeqToMap(mp.state, fi.state);
      }
      fi_pass
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
      FIFromOutputs(mp, fi, fake_output)
    }

    function FOFirstPass(mp: ScufMap, uf: UpdateFunction, fi: FI): (fo_first_pass: FO)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires UFConnectionConsistent(uf, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures fo_first_pass.outputs.Keys == Seq.ToSet(mp.outputs)
      ensures fo_first_pass.state.Keys == Seq.ToSet(mp.state)
    {
      var so_first_pass := SOFirstPass(mp, uf, fi);
      mp.so2fo(so_first_pass)
    }

    lemma FOFirstPassTOFISecondPass(mp: ScufMap, uf: UpdateFunction, fi: FI, inp: NP)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires UFConnectionConsistent(uf, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var conn_inputs := GetConnectedInputs(mp);
        inp in conn_inputs
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures
        var fo_first_pass := FOFirstPass(mp, uf, fi);
        var fi_second_pass := FISecondPass(mp, uf, fi);
        var npconnections := GetConnection(mp);
        var onp := npconnections[inp];
        fi_second_pass.inputs[inp] == fo_first_pass.outputs[onp]
    {
      assert inp in mp.inputs by {
        reveal Seq.ToSet();
      }
      var new_mp := ConnectScufMap(mp, this);
      var inp_index := Seq.IndexOf(mp.inputs, inp);
      var si := new_mp.fi2si(fi);
      var so_first_pass := SOFirstPass(mp, uf, fi);
      var fi_second_pass := FISecondPass(mp, uf, fi);
      var si_second_pass := SI(NIO2I(si.inputs, so_first_pass.outputs), si.state);
      assert mp.inputs[inp_index] == inp;
      assert fi_second_pass == mp.si2fi(si_second_pass);
      assert fi_second_pass.inputs == SeqsToMap(mp.inputs, si_second_pass.inputs);
      assert si_second_pass.inputs[inp_index] == fi_second_pass.inputs[inp] by {
        reveal MapMatchesSeqs();
      }

      assert inp_index < |nio2i| by {
        reveal Valid();
      }

      var conn_inputs := GetConnectedInputs(mp);
      assert inp_index in connections by {
        assert inp in conn_inputs;
        reveal Valid();
        reveal Seq.ToSet();
        reveal Seq.HasNoDuplicates();
        assert conn_inputs == (set i | i in connections :: mp.inputs[i]);
      }
      var (from_output, onp_index) := nio2i[inp_index];
      assert from_output by {
        reveal Valid();
        assert ((!from_output) ==> onp_index < ni_width && i2ni[onp_index] == inp_index && (inp_index !in connections));
        assert ((from_output) ==> onp_index < o_width && (inp_index in connections) && (onp_index == connections[inp_index]));
      }
      var npconnections := GetConnection(mp);
      var onp := npconnections[inp];
      assert onp_index < |mp.outputs| by {
        reveal Valid();
      }
      assert mp.outputs[onp_index] == onp by {
        reveal Valid();
        reveal Seq.HasNoDuplicates();
      }
      var fo_first_pass := FOFirstPass(mp, uf, fi);
      assert so_first_pass.outputs[onp_index] == fo_first_pass.outputs[onp] by {
        reveal MapMatchesSeqs();
      }
    }

    function SOFirstPass(mp: ScufMap, uf: UpdateFunction, fi: FI): (so_first_pass: SO)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires UFConnectionConsistent(uf, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures |so_first_pass.outputs| == |mp.outputs|
      ensures |so_first_pass.outputs| == uf.output_width
    {
      var output_width := |mp.outputs|;
      var fake_output := seq(output_width, (index: nat) requires index < output_width => false);
      SOFromOutputs(mp, uf, fi, fake_output)
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
      ensures fi.state == fi_second_pass.state
    {
      var so := SOFirstPass(mp, uf, fi);
      FIFromOutputs(mp, fi, so.outputs)
    }

    lemma FIFromOutputsMatchingKeyMatchingValue(mp: ScufMap, uf: UpdateFunction, fi: FI, outputs: seq<bool>)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires UFConnectionConsistent(uf, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures
        var fi_pass := FIFromOutputs(mp, fi, outputs);
        forall x :: (x in fi.inputs && x in fi_pass.inputs) ==>
          (fi.inputs[x] == fi_pass.inputs[x])
    {
      reveal Seq.ToSet();
      var new_mp := ConnectScufMap(mp, this);
      var fi_pass := FIFromOutputs(mp, fi, outputs);
      forall x: NP | (x in fi.inputs && x in fi_pass.inputs)
        ensures fi.inputs[x] == fi_pass.inputs[x]
      {
        assert FIValid(fi, new_mp.inputs, new_mp.state);
        assert FIValid(fi_pass, mp.inputs, mp.state);
        assert x in mp.inputs;
        assert x in new_mp.inputs;

        var output_width := |mp.outputs|;
        var sni_pass := new_mp.fi2si(fi);
        var si_pass := SI(NIO2I(sni_pass.inputs, outputs), sni_pass.state);
        var fi_pass := mp.si2fi(si_pass);

        var ni_index := Seq.IndexOf(new_mp.inputs, x);
        assert new_mp.inputs[ni_index] == x;
        var i_index := Seq.IndexOf(mp.inputs, x);
        assert mp.inputs[i_index] == x;
        assert new_mp.inputs == I2NI(mp.inputs);
        assert |i2ni| == ni_width && i2ni[ni_index] < i_width by {
          reveal Valid();
        }
        assert new_mp.inputs[ni_index] == mp.inputs[i2ni[ni_index]] by {
          I2NICorrect(mp.inputs);
        }
        assert i2ni[ni_index] == i_index by {
          assert mp.inputs[i2ni[ni_index]] == x;
          assert mp.inputs[i_index] == x;
          assert Seq.HasNoDuplicates(mp.inputs);
          reveal Seq.HasNoDuplicates();
        }

        var value := fi.inputs[x];
        new_mp.fi2siInputs(fi, x);
        assert sni_pass.inputs[ni_index] == value;
        NIO2I2NI(sni_pass.inputs, outputs);
        assert si_pass.inputs[i2ni[ni_index]] == value;
        assert si_pass.inputs[i_index] == value;
        assert mp.inputs[i_index] == x;
        mp.si2fi2si(si_pass);
        mp.fi2siInputs(fi_pass, x);
        assert fi_pass.inputs[x] == value;
      }
    }
    lemma FIFirstPassMatchingKeyMatchingValue(mp: ScufMap, uf: UpdateFunction, fi: FI)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires UFConnectionConsistent(uf, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures
        var fi_pass := FIFirstPass(mp, fi);
        forall x :: (x in fi.inputs && x in fi_pass.inputs) ==>
          (fi.inputs[x] == fi_pass.inputs[x])
    {
      var output_width := |mp.outputs|;
      var fake_output := seq(output_width, (index: nat) requires index < output_width => false);
      FIFromOutputsMatchingKeyMatchingValue(mp, uf, fi, fake_output);
    }

    lemma FISecondPassMatchingKeyMatchingValue(mp: ScufMap, uf: UpdateFunction, fi: FI)
      requires Valid()
      requires mp.Valid()
      requires uf.Valid()
      requires MPConnectionConsistent(mp, this)
      requires UFConnectionConsistent(uf, this)
      requires ScufMapUpdateFunctionConsistent(mp, uf)
      requires
        var new_mp := ConnectScufMap(mp, this);
        FIValid(fi, new_mp.inputs, new_mp.state)
      ensures
        var fi_second_pass := FISecondPass(mp, uf, fi);
        forall x :: (x in fi.inputs && x in fi_second_pass.inputs) ==>
          (fi.inputs[x] == fi_second_pass.inputs[x])
    {
      var so := SOFirstPass(mp, uf, fi);
      FIFromOutputsMatchingKeyMatchingValue(mp, uf, fi, so.outputs);
    }
  }

  //opaque ghost predicate NoPathsInScuf(c: Circuit, s: Scuf, onps: set<NP>, inps: set<NP>)
  //  requires c.Valid()
  //  requires s.SomewhatValidRelaxInputs(c)
  //  requires ONPsValid(c, onps)
  //{
  //  forall fi: FI :: FIValid(fi, s.mp.inputs, s.mp.state) ==> (
  //    assert FICircuitValid(c, fi) by {
  //      ScufValidFiValidToFICircuitValid(c, s, fi);
  //    }
  //    var new_fi := FI(fi.inputs - inps, fi.state);
  //    assert FICircuitValid(c, new_fi) by {
  //      reveal FICircuitValid();
  //    }
  //    reveal ONPsValid();
  //    forall path: seq<NP> :: EvaluatePathRequirements(c, path) &&  Seq.Last(path) in onps ==>
  //      EvaluateONPInner(c, path, fi) == EvaluateONPInner(c, path, new_fi)
  //  )
  //}

  function GetSubPathInOldInternal(c: Circuit, new_c: Circuit, inps: set<NP>, p: seq<NP>, index: nat): (subp: seq<NP>)
    requires c.Valid()
    requires new_c.Valid()
    requires new_c.NodeKind == c.NodeKind
    requires forall np :: np in c.PortSource ==> np in new_c.PortSource && c.PortSource[np] == new_c.PortSource[np]
    requires forall np :: np in new_c.PortSource && np !in c.PortSource ==> np in inps
    requires index < |p|
    requires Seq.Last(p) in inps
    requires index > 0 ==> p[index-1] !in inps
    requires PathValid(new_c, p)
    requires PathValid(c, p[..index])
    ensures PathValid(c, subp)
    ensures |subp| > 0
    ensures Seq.Last(subp) in inps
    ensures Seq.First(subp) == Seq.First(p)
    decreases |p| - index
  {
    reveal PathValid();
    if p[index] in inps then
      p[..index+1]
    else
      assert PathValid(c, p[..(index+1)]) by {
        assert PathValid(c, p[..index]);
        assert NPValid(c, p[index]);
        assert PathValid(new_c, p);
        assert NPValid(new_c, p[index]);
        if index > 0 {
          assert NPValid(new_c, p[index-1]);
          assert NPsConnected(new_c, p[index-1], p[index]);
          assert p[index-1] !in inps;
          assert NPsConnected(c, p[index-1], p[index]);
        }
      }
      GetSubPathInOldInternal(c, new_c, inps, p, index+1)
  }

  function GetSubPathInOld(c: Circuit, new_c: Circuit, inps: set<NP>, p: seq<NP>): (subp: seq<NP>)
    requires c.Valid()
    requires new_c.Valid()
    requires new_c.NodeKind == c.NodeKind
    requires forall np :: np in c.PortSource ==> np in new_c.PortSource && c.PortSource[np] == new_c.PortSource[np]
    requires forall np :: np in new_c.PortSource && np !in c.PortSource ==> np in inps
    requires |p| > 0
    requires Seq.Last(p) in inps
    requires PathValid(new_c, p)
    ensures PathValid(c, subp)
    ensures |subp| > 0
    ensures Seq.Last(subp) in inps
    ensures Seq.First(subp) == Seq.First(p)
  {
    reveal PathValid();
    GetSubPathInOldInternal(c, new_c, inps, p, 0)
  }

  lemma StillNoPathExistsBetweenNPSets(c: Circuit, new_c: Circuit, onps: set<NP>, inps: set<NP>)
    requires c.Valid()
    requires new_c.Valid()
    requires ONPsValid(c, onps)
    requires ONPsValid(new_c, onps)
    requires new_c.NodeKind == c.NodeKind
    requires forall np :: np in c.PortSource ==> np in new_c.PortSource && c.PortSource[np] == new_c.PortSource[np]
    requires forall np :: np in new_c.PortSource && np !in c.PortSource ==> np in inps
    requires !PathExistsBetweenNPSets(c, onps, inps)
    ensures !PathExistsBetweenNPSets(new_c, onps, inps)
  {
    //exists p: seq<NP> :: (|p| > 0) && PathValid(c, p) && (Seq.First(p) in nps_a) && (Seq.Last(p) in nps_b)
    reveal PathExistsBetweenNPSets();
    if PathExistsBetweenNPSets(new_c, onps, inps) {
      var p :| (|p| > 0) && PathValid(new_c, p) && (Seq.First(p) in onps) && (Seq.Last(p) in inps);
      var psub := GetSubPathInOld(c, new_c, inps, p);
      assert PathBetweenNPSets(c, psub, onps, inps);
    }
  }

  //lemma ApplyNoPathsInScuf(c: Circuit, s: Scuf, onps: set<NP>, inps: set<NP>, path: seq<NP>,
  //                         subinps: set<NP>, fi: FI)
  //  requires c.Valid()
  //  requires s.SomewhatValidRelaxInputs(c)
  //  requires ONPsValid(c, onps)
  //  //requires INPsValid(c, inps)
  //  //requires subinps <= inps
  //  requires subinps == inps
  //  requires FIValid(fi, s.mp.inputs, s.mp.state)
  //  requires EvaluateONPInnerRequirements(c, path, fi)
  //  requires
  //    var new_fi := FI(fi.inputs - subinps, fi.state);
  //    EvaluateONPInnerRequirements(c, path, new_fi)
  //  requires Seq.Last(path) in onps
  //  requires NoPathsInScuf(c, s, onps, inps)
  //  ensures
  //    var new_fi := FI(fi.inputs - subinps, fi.state);
  //    && reveal ONPsValid();
  //    && (EvaluateONPInner(c, path, fi) == EvaluateONPInner(c, path, new_fi))
  //{
  //  reveal NoPathsInScuf();
  //}


  opaque ghost predicate ScufConnectionConsistent(c: Circuit, s: Scuf, conn: InternalConnection)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
  {
    reveal InternalConnection.Valid();
    reveal ONPsValid();
    s.SomewhatValidToRelaxInputs(c);
    ScufFOutputsAreValid(c, s);
    && (conn.i_width == s.uf.input_width)
    && (conn.o_width == s.uf.output_width)
    && !PathExistsBetweenNPSets(c, conn.GetConnectedOutputs(s.mp), conn.GetConnectedInputs(s.mp))
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
      && s.SomewhatValidRelaxInputs(new_c)
      && new_s.SomewhatValid(new_c)
      && SubcircuitWeaklyConserved(c, new_c, s.sc)
      && NoNewExternalConnections(c, new_c, s.sc)
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
    assert SubcircuitWeaklyConserved(c, new_c, s.sc) by {
      reveal SubcircuitWeaklyConserved();
    }
    assert NoNewExternalConnections(c, new_c, s.sc) by {
      reveal NoNewExternalConnections();
    }
    (new_c, new_s)
  }

  lemma ConnectCircuitScufConserved(c: Circuit, s: Scuf, conn: InternalConnection, fi: FI)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    requires FIValid(fi, s.mp.inputs, s.mp.state)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      ConservedValid(c, new_c, s, fi)
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    assert c.Valid();
    assert new_c.Valid();
    assert s.Valid(c);
    assert c.NodeKind == new_c.NodeKind;
    assert SubcircuitConserved(c, new_c, s.sc) by {
      reveal SubcircuitConserved();
      reveal ScValid();
      var sc := s.sc;
      var ca := c;
      var cb := new_c;
      assert (forall n :: n in sc ==> n in cb.NodeKind);
      assert (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n]);
      assert (forall np: NP :: np.n in sc && np in ca.PortSource ==>
          np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np]);
      assert (forall np: NP :: np.n in sc && np !in ca.PortSource && np in cb.PortSource ==>
          cb.PortSource[np].n !in sc);
    }
    assert (Seq.ToSet(s.mp.inputs) == fi.inputs.Keys);
    assert (Seq.ToSet(s.mp.state) == fi.state.Keys);
    assert OutputsInFOutputs(new_c, s);
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
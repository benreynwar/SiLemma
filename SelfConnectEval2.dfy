module SelfConnectEval2 {

  import opened Circ
  import opened Scuf
  import opened SelfConnect
  import opened MapFunction
  import opened Eval
  import opened Utils
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened Path
  import opened Path2

  // At the toplevel we're trying to prove that when we connect some outputs to some inputs we the resulting
  // circuit is consistent with the updated UpdateFunction.


  // The new update function does:
  // 1) Set all the recycled inputs to 0.
  // 2) Run the old update function to get the outputs. The output values from this are correct for the connected outputs
  //    because there are no connections from the inputs to the outputs internally.
  // 3) Set the recycles inputs to the proper values from the outputs.
  // 4) Run the old update function again.


  // Proof steps.
  // 1) Prove that Evaluation using fi_actual matches Evaluation using fi.
  //    Evaluate(new_c, np, fi) == Evaluate(new_c, np, fi_with_real_outputs)
  // 2) Prove that the result for c and new_c will be the same if all the connections are in fi
  //    Evaluate(new_c, np, fi_with_real_outputs) == Evaluate(c, np, fi_with_real_outputs)
  // 2) Prove that Evaluation using fi_actual matches old_update(fi_actual)
  //    Evaluate(c, np, fi_with_real_outputs) == EvalOk(UFOld(fi_with_real_outputs))
  // 3) Prove that old_update(fi_actual) == new_update(fi)
  //    EvalOk(UFOld(fi_with_real_outputs)) == EvalOk(UFNew(fi))
  //
  // Thus we get Evaluate(new_c, np, fi) == EvalOk(UFNew(fi))

  // (1) is probably going to be the hardest.
  // Having a different FI is only going to have an effect when we're at an INP that is in fi_with_real_inputs
  // but not in fi.
  // At this point we know that EvaluateINP(new, path, fi_with_real_outputs) is just EvalOk(fi_with_real_outputs[inp])
  // however we need to prove this is the same with fi.
  // It will be EvaluateONP(new, path + corresponding_onp, fi).  We need to be able to prove that if onp is in the connected outputs
  // that
  // a) EvaluateONP(new_c, path, fi) == EvaluateONP(new_c, path, fi_with_fake_outputs)
  // b) EvaluateONP(new_c, path, fi_with_fake_outputs) == EvaluateONP(c, path, fi_with_fake_outputs)
  // c) EvaluateONP(c, path, fi_with_fake_outputs) == EvalOk(UFOld(fi_with_fake_outputs))
  // d) EvalOK(UFOld(fi_with_real_outputs)) == EvalOK(UFOld(fi_with_fake_outputs))) if onp is in connected outputs.

  lemma EvaluateSelfConnectOldONP(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    //
    // Here we need to prove that when we take a circuit and connect some of the input points to
    // other nodes it doesn't effect the evaluation.
    // This is because at the input points the evaluation is terminated.
    //
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    requires FIValid(fi, s.mp.inputs, s.mp.state)
    requires NPValid(c, np)
    requires np in s.mp.outputs || np in StateINPs(s.mp.state)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FICircuitValid(new_c, fi)
      && FICircuitValid(c, fi)
      && (Evaluate(new_c, np, fi) == Evaluate(c, np, fi))
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    assert ConservedValid(c, new_c, s, fi) by {
      assert c.Valid();
      assert new_c.Valid();
      assert s.Valid(c);
      assert SubcircuitWeaklyConserved(c, new_c, s.sc);
      assert (Seq.ToSet(s.mp.inputs) == fi.inputs.Keys);
      assert (Seq.ToSet(s.mp.state) == fi.state.Keys);
      assert OutputsInFOutputs(new_c, s) by {
        reveal Scuf.SomewhatValidRelaxInputs();
        assert OutputsInFOutputs(c, s);
        reveal ConnOutputs();
        assert NoNewExternalConnections(c, new_c, s.sc);
        reveal NoNewExternalConnections();
        assert ConnOutputs(c, s.sc) == ConnOutputs(new_c, s.sc);
      }
    }
    assert np.n in s.sc by {
      reveal NPsInSc();
      FOutputsInSc(c, s);
      reveal Seq.ToSet();
      if np in s.mp.outputs {
        assert np.n in s.sc;
      }
      if np in StateINPs(s.mp.state) {
        assert np.n in s.sc;
      }
    }
    EvaluateConserved(c, new_c, s, np, fi);
  }

  lemma EvaluateWithActual(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    requires
      && var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (np in s.mp.outputs || np in StateINPs(s.mp.state))
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (Evaluate(new_c, np, fi_second_pass) == Evaluate(new_c, np, fi))
  {
    if ONPValid(c, np) {
      EvaluateONPInnerSelfConnect(c, s, conn, [np], fi);
    } else {
      EvaluateINPInnerSelfConnect(c, s, conn, [np], fi);
    }
  }


  lemma EvaluateONPInnerConnectedOutputs(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI, outputs: seq<bool>)
    //
    // Here we prove that if when we evaluate one of the outputs that we have connected to an input,
    // the result of the evaluation is not effected is we remove the connected inputs from the
    // termination points.
    // This is true because we enforce that there are not paths from the connected outputs to the connected
    // inputs.
    //
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    requires
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && (|outputs| == |s.mp.outputs|)
      && var fi_pass := conn.FIFromOutputs(s.mp, fi, outputs);
      && EvaluateONPInnerRequirements(new_c, path, fi)
      && EvaluateONPInnerRequirements(new_c, path, fi_pass)
      && PathValid(new_c, path)
      && NPValid(new_c, Seq.Last(path))
      && (|path| > 1 ==> !PathExists(new_c, Seq.Last(path), path[|path|-2]))
      && (Seq.Last(path) in conn.GetConnectedOutputs(s.mp))
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_pass := conn.FIFromOutputs(s.mp, fi, outputs);
      reveal FICircuitValid();
      && (EvaluateONPInner(new_c, path, fi_pass) == EvaluateONPInner(new_c, path, fi))
      && reveal Seq.ToSet();
      && (EvaluateONPInner(new_c, path, fi_pass) == EvalOk(MFLookup(s, fi_pass, Seq.Last(path))))
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var np := Seq.Last(path);
    var fi_pass := conn.FIFromOutputs(s.mp, fi, outputs);
    var onps := conn.GetConnectedOutputs(s.mp);
    var inps := conn.GetConnectedInputs(s.mp);
    assert Seq.ToSet(new_s.mp.inputs) == Seq.ToSet(s.mp.inputs) - inps;
    assert fi == FI(fi_pass.inputs - inps, fi_pass.state) by {
      assert fi.state == fi_pass.state;
      var output_width := |s.mp.outputs|;
      //var fake_output := seq(output_width, (index: nat) requires index < output_width => false);
      var sni := new_s.mp.fi2si(fi);
      conn.NIO2I2NI(sni.inputs, outputs);
      assert fi.inputs.Keys == fi_pass.inputs.Keys - inps;
      assert fi.inputs == fi_pass.inputs -inps by {
        forall np | np in fi.inputs
          ensures fi.inputs[np] == fi_pass.inputs[np]
        {
          conn.FIFromOutputsMatchingKeyMatchingValue(s.mp, s.uf, fi, outputs);
        }
      }
    }
    assert ONPsValid(c, onps) && ONPsValid(new_c, onps) by {
      ScufFOutputsAreValid(c, s);
      reveal Seq.ToSet();
      reveal ONPsValid();
    }
    assert !PathExistsBetweenNPSets(new_c, onps, inps) by {
      reveal ScufConnectionConsistent();
      assert ONPsValid(c, onps);
      StillNoPathExistsBetweenNPSets(c, new_c, onps, inps);
    }
    assert FICircuitValid(new_c, fi_pass) by {
      reveal FICircuitValid();
    }
    NoPathExistsBetweenNPSetsToToNPSet(new_c, onps, inps, Seq.Last(path));
    EvaluateONPInnerReduceFI(new_c, path, fi_pass, inps);
    assert fi == FI(fi_pass.inputs - inps, fi_pass.state);
    assert EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_pass);
    assert Seq.HasNoDuplicates([Seq.Last(path)]) && PathValid(new_c, [Seq.Last(path)]) by {
      reveal Seq.HasNoDuplicates();
      reveal PathValid();
    }
    calc {
      EvaluateONPInner(new_c, path, fi_pass);
      {
        reveal Seq.HasNoDuplicates();
        reveal PathValid();
        var prefix := if |path| > 1 then ValidPathSegment(new_c, path, 0, |path|-1) else [];
        EvaluateONPInnerPrepend(new_c, prefix, [Seq.Last(path)], fi_pass);
        assert path == prefix + [Seq.Last(path)];
      }
      EvaluateONPInner(new_c, [Seq.Last(path)], fi_pass);
      Evaluate(new_c, Seq.Last(path), fi_pass);
      {
        reveal InternalConnection.Valid();
        EvaluateSelfConnectOldONP(c, s, conn, Seq.Last(path), fi_pass);
      }
      Evaluate(c, Seq.Last(path), fi_pass);
      {
        assert s.Valid(c);
        reveal InternalConnection.Valid();
        reveal Scuf.EvaluatesCorrectly();
      }
      EvalOk(MFLookup(s, fi_pass, Seq.Last(path)));
    }
  }

  ghost predicate EvaluateINPInnerSelfConnectRequirements(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
  {
    && c.Valid()
    && s.Valid(c)
    && conn.Valid()
    && ScufConnectionConsistent(c, s, conn)
    && var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
    && var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
    && EvaluateINPInnerRequirements(new_c, path, fi_second_pass)
    && EvaluateINPInnerRequirements(new_c, path, fi)
  }

  lemma EvaluateINPInnerSelfConnectHelperA(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
    requires EvaluateINPInnerSelfConnectRequirements(c, s, conn, path, fi)
    requires (Seq.Last(path) !in fi.inputs)
    requires PathValid(c, path)
    requires 
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (Seq.Last(path) in fi_second_pass.inputs)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var onp: NP := new_c.PortSource[Seq.Last(path)];
      && PathValid(new_c, path + [onp])
      && Seq.HasNoDuplicates(path + [onp])
      && ONPValid(new_c, onp)
      && (onp !in path)
      && !PathExists(new_c, onp, Seq.Last(path))
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var onp: NP := new_c.PortSource[Seq.Last(path)];
    conn.GetConnectionProperties(c, s);
    var conn_outputs := conn.GetConnectedOutputs(s.mp);
    var conn_inputs := conn.GetConnectedInputs(s.mp);
    //assert PathValid(c, path) by {
    //  assert PathValid(new_c, path);
    //  reveal PathValid();
    //}
    assert ONPValid(new_c, onp) by {
      reveal Circuit.Valid();
    }
    assert onp !in path by {
      // We know there are no paths from onp to Seq.Last(path) because onp is one of the connected outputs,
      // and Seq.Last(path) is one of the connected inputs, and we know there are no pathes between.
      if onp in path {
        var index := Seq.IndexOf(path, onp);
        var path_contradict := ValidPathSegment(c, path, index, |path|);
        assert PathFromTo(c, path_contradict, onp, Seq.Last(path));
        assert onp in conn.GetConnectedOutputs(s.mp);
        assert Seq.Last(path) in conn.GetConnectedInputs(s.mp);
        assert PathBetweenNPSets(c, path_contradict, conn_outputs, conn_inputs);
        reveal PathExistsBetweenNPSets();
        assert PathExistsBetweenNPSets(c, conn_outputs, conn_inputs);
      }
    }
    assert !PathExists(new_c, onp, Seq.Last(path)) by {
      reveal PathExists();
      reveal PathExistsBetweenNPSets();
      NoPathExistsBetweenNPSetsToNoPathExists(new_c, conn_outputs, conn_inputs, onp, Seq.Last(path));
    }
    StillHasNoDuplicates(path, onp);
    AppendPathValid(new_c, path, onp);
  }


  lemma EvaluateINPInnerSelfConnectHelperB(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
    requires EvaluateINPInnerSelfConnectRequirements(c, s, conn, path, fi)
    requires PathValid(c, path)
    requires 
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (Seq.Last(path) !in fi.inputs)
      && (Seq.Last(path) in fi_second_pass.inputs)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var onp: NP := new_c.PortSource[Seq.Last(path)];
      var fi_first_pass := conn.FIFirstPass(s.mp, fi);
      var conn_outputs := conn.GetConnectedOutputs(s.mp);
      reveal FICircuitValid();
      && PathValid(new_c, path + [onp])
      && Seq.HasNoDuplicates(path + [onp])
      && ONPValid(new_c, onp)
      && (onp in conn_outputs)
      && (EvaluateONPInner(new_c, path + [onp], fi) == EvaluateONPInner(new_c, path + [onp], fi_first_pass))
  {
    EvaluateINPInnerSelfConnectHelperA(c, s, conn, path, fi);
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var onp: NP := new_c.PortSource[Seq.Last(path)];
    var fi_first_pass := conn.FIFirstPass(s.mp, fi);
    conn.GetConnectionProperties(c, s);
    EvaluateINPInnerSelfConnectHelperA(c, s, conn, path, fi);
    var conn_outputs := conn.GetConnectedOutputs(s.mp);
    var conn_inputs := conn.GetConnectedInputs(s.mp);
    assert !PathExistsBetweenNPSets(new_c, conn_outputs, conn_inputs) by {
      reveal ScufConnectionConsistent();
      reveal ONPsValid();
      StillNoPathExistsBetweenNPSets(c, new_c, conn_outputs, conn_inputs);
    }
    reveal FICircuitValid();
    var output_width := |s.mp.outputs|;
    var fake_output := seq(output_width, (index: nat) requires index < output_width => false);
    assert Seq.Last(path) in conn_inputs;
    assert onp in conn_outputs;
    EvaluateONPInnerConnectedOutputs(c, s, conn, path + [onp], fi, fake_output);
    assert EvaluateONPInner(new_c, path + [onp], fi) == EvaluateONPInner(new_c, path + [onp], fi_first_pass);
  }


  lemma EvaluateINPInnerSelfConnectHelper(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
    requires EvaluateINPInnerSelfConnectRequirements(c, s, conn, path, fi)
    requires PathValid(c, path)
    requires 
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (Seq.Last(path) !in fi.inputs)
      && (Seq.Last(path) in fi_second_pass.inputs)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (EvaluateINPInner(new_c, path, fi_second_pass) == EvaluateINPInner(new_c, path, fi))
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var head := Seq.Last(path);
    var onp: NP := new_c.PortSource[head];
    var output_width := |s.mp.outputs|;
    var fake_output := seq(output_width, (index: nat) requires index < output_width => false);
    var si_first_pass := conn.SIFromOutputs(s.mp, fi, fake_output);
    var fi_first_pass := s.mp.si2fi(si_first_pass);
    s.mp.si2fi2si(si_first_pass);
    assert si_first_pass == conn.SIFromOutputs(s.mp, fi, fake_output);
    assert s.uf.sf.requires(si_first_pass) by {
      reveal UpdateFunction.Valid();
    }
    var so_first_pass := s.uf.sf(si_first_pass);
    assert so_first_pass == conn.SOFirstPass(s.mp, s.uf, fi);
    assert s.mp.so2fo.requires(so_first_pass) by {
      reveal UpdateFunction.Valid();
    }
    var fo_first_pass := s.mp.so2fo(so_first_pass);
    assert fo_first_pass == conn.FOFirstPass(s.mp, s.uf, fi);
    var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
    calc {
      EvaluateINPInner(new_c, path, fi);
      {
        EvaluateINPInnerSelfConnectHelperA(c, s, conn, path, fi);
      }
      EvaluateONPInner(new_c, path + [onp], fi);
      {
        EvaluateINPInnerSelfConnectHelperB(c, s, conn, path, fi);
        reveal FICircuitValid();
      }
      EvaluateONPInner(new_c, path + [onp], fi_first_pass);
      {
        var conn_outputs := conn.GetConnectedOutputs(s.mp);
        assert onp in conn_outputs;
        reveal Seq.ToSet();
        assert onp in s.mp.outputs;
        EvaluateINPInnerSelfConnectHelperA(c, s, conn, path, fi);
        reveal PathValid();
        EvaluateONPInnerConnectedOutputs(c, s, conn, path + [onp], fi, fake_output);
      }
      EvalOk(MFLookup(s, fi_first_pass, onp));
      {
        reveal Seq.ToSet();
        EvaluateINPInnerSelfConnectHelperB(c, s, conn, path, fi);
        assert onp in s.mp.outputs;
      }
      EvalOk(MFLookupOutput(s, fi_first_pass, onp));
      EvalOk(fo_first_pass.outputs[onp]);
      {
        EvaluateINPInnerSelfConnectHelperB(c, s, conn, path, fi);
        conn.FOFirstPassTOFISecondPass(s.mp, s.uf, fi, head);
      }
      EvalOk(fi_second_pass.inputs[head]);
      EvaluateINPInner(new_c, path, fi_second_pass);
    }
    assert (EvaluateINPInner(new_c, path, fi_second_pass) == EvaluateINPInner(new_c, path, fi));
  }

  lemma {:vcs_split_on_every_assert} EvaluateINPInnerSelfConnect(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    //requires
    //  reveal ScufConnectionConsistent();
    //  forall np :: np in path ==> np !in conn.GetConnectedOutputs(s.mp)
    requires
      && var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && EvaluateINPInnerRequirements(new_c, path, fi_second_pass)
      && EvaluateINPInnerRequirements(new_c, path, fi)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (EvaluateINPInner(new_c, path, fi_second_pass) == EvaluateINPInner(new_c, path, fi))
    decreases
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      |NodesNotInPath(new_c, path)|, 3
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var fi_first_pass := conn.FIFirstPass(s.mp, fi);
    var so_first_pass := conn.SOFirstPass(s.mp, s.uf, fi);
    var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    var connections := conn.GetConnection(s.mp);
    if head in fi.inputs {
      assert head in fi.inputs;
      assert head in fi_second_pass.inputs;
      conn.FISecondPassMatchingKeyMatchingValue(s.mp, s.uf, fi);
      assert fi.inputs[head] == fi_second_pass.inputs[head];
    } else if head in fi_second_pass.inputs {
      assert head !in fi.inputs;
      // We've gone from an onp to one of the connected inps;
      // We need to prove that these two things are equal.
      // EvaluateINPInner(new_c, path, fi_second_pass)
      // EvaluateINPInner(new_c, path, fi))

      // If fi_second_pass is used, then the value is just the value in fi_second_pass.
      assert EvaluateINPInner(new_c, path, fi_second_pass) == EvalOk(fi_second_pass.inputs[head]);
      // But if we're using 'fi' then  we propagate back to the connected onp.



      assert head in s.mp.inputs &&  head !in new_s.mp.inputs by {
        reveal Seq.ToSet();
        assert head !in fi.inputs;
        assert fi.inputs.Keys == Seq.ToSet(new_s.mp.inputs);
      }
      assert head in connections.Keys by {
        reveal Seq.ToSet();
        assert new_s.mp == ConnectScufMap(s.mp, conn);
      }
      var onp: NP := new_c.PortSource[head];
      //assert head !in c.PortSource;
      assert onp !in path by {
        // We know there are no paths from onp to Seq.Last(path) because onp is one of the connected outputs,
        // and Seq.Last(path) is one of the connected inputs, and we know there are no pathes between.
        if onp in path {
          var index := Seq.IndexOf(path, onp);
          var path_contradict := ValidPathSegment(c, path, index, |path|);
          assert PathFromTo(c, path_contradict, onp, Seq.Last(path));
        }
      }
      // Prove has no duplicates
      StillHasNoDuplicates(path, onp);
      assert EvaluateINPInner(new_c, path, fi) == EvaluateONPInner(new_c, path + [onp], fi);
       
      //assert head in Seq.ToSet(s.mp.inputs);
      //assert head in connections.Keys;
      assert head !in c.PortSource by {
        reveal ScufConnectionConsistent();
      }
      assert onp !in path;
      reveal Circuit.Valid();
      NodesNotInPathDecreases(new_c, path, onp);
      StillHasNoDuplicates(path, onp);
      AppendPathValid(new_c, path, onp);
      // Look back around to ONP.
      var connection := conn.GetConnection(s.mp); 
      assert onp == connection[head];
      assert ONPValid(new_c, onp);
      assert EvaluateONPInnerRequirements(new_c, path + [onp], fi) by {
          assert EvaluateConstRequirements(new_c, fi);
          assert EvaluatePathRequirements(new_c, path + [onp]);
          assert ONPValid(new_c, Seq.Last(path + [onp]));
      }
      assert EvaluateONPInnerRequirements(new_c, path + [onp], fi_second_pass);
      assert FICircuitValid(new_c, fi);
      assert FICircuitValid(new_c, fi_second_pass) && FICircuitValid(new_c, fi_first_pass) by {
        reveal FICircuitValid();
      }
      var output_width := |s.mp.outputs|;
      var fake_output := seq(output_width, (index: nat) requires index < output_width => false);
      var sni := new_s.mp.fi2si(fi);
      var si_second_pass_inputs := conn.NIO2I(sni.inputs, so_first_pass.outputs);
      var si_second_pass := SI(si_second_pass_inputs, sni.state);
      assert fi_second_pass == s.mp.si2fi(si_second_pass);

      var actual_output := so_first_pass.outputs;
      assert |actual_output| == |s.mp.outputs| by {
        assert ScufMapUpdateFunctionConsistent(s.mp, s.uf);
        assert s.uf.output_width == |s.mp.outputs|;
        reveal UpdateFunction.Valid();
        assert|so_first_pass.outputs| == s.uf.output_width;
      }
      EvaluateONPInnerConnectedOutputs(c, s, conn, path + [onp], fi, fake_output);
      EvaluateONPInnerConnectedOutputs(c, s, conn, path + [onp], fi, actual_output);
      assert EvaluateONPInner(new_c, path + [onp], fi_first_pass) == EvaluateONPInner(new_c, path + [onp], fi);
      assert EvaluateONPInner(new_c, path + [onp], fi_second_pass) == EvaluateONPInner(new_c, path + [onp], fi);
  //if head in fi.inputs then
  //  EvalOk(fi.inputs[head])
  //else
  //  if head in c.PortSource then
  //    var onp := c.PortSource[head];
  //    if onp in path then
  //      EvalError({}, {path + [onp]})
  //    else
      calc {
        EvaluateINPInner(new_c, path, fi);
        EvaluateONPInner(new_c, path + [onp], fi);
        EvaluateONPInner(new_c, path + [onp], fi_first_pass);
        Evaluate(new_c, onp, fi_first_pass);
        EvalOk(MFLookup(s, fi_first_pass, onp));
        //EvalOk(fo_first_pass.outputs[onp]);
        EvalOk(fi_second_pass.inputs[head]);
        EvaluateINPInner(new_c, path, fi_second_pass);
      }
      assert EvaluateINPInner(new_c, path, fi_second_pass) == EvaluateINPInner(new_c, path, fi);

    } else if head in new_c.PortSource {
      assert head !in Seq.ToSet(new_s.mp.inputs);
      assert fi.inputs.Keys == Seq.ToSet(new_s.mp.inputs);
      assert Seq.ToSet(new_s.mp.inputs) == Seq.ToSet(s.mp.inputs) - connections.Keys;
      var onp: NP := new_c.PortSource[head];
      if head in fi_second_pass.inputs {
      } else {
        reveal Circuit.Valid();
        NodesNotInPathDecreases(new_c, path, onp);
        StillHasNoDuplicates(path, onp);
        AppendPathValid(new_c, path, onp);
        EvaluateONPInnerSelfConnect(c, s, conn, path + [onp], fi);
      }
      assert SubcircuitWeaklyConserved(c, new_c, s.sc);
      assert new_c.PortSource[head] == c.PortSource[head] by {
        reveal SubcircuitWeaklyConserved();
      }
    } else {
      //EvalError({head}, {})
    }
  }

  lemma EvaluateONPUnarySelfConnect(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    requires
      && var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && EvaluateONPUnaryRequirements(new_c, path, fi_second_pass)
      && EvaluateONPUnaryRequirements(new_c, path, fi)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (EvaluateONPUnary(new_c, path, fi_second_pass) == EvaluateONPUnary(new_c, path, fi))
    decreases
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      |NodesNotInPath(new_c, path)|, 3
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var head := Seq.Last(path);
    var nk := c.NodeKind[head.n];
    assert nk == new_c.NodeKind[head.n];
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(new_c, path, inp_0);
      var new_path_0 := path + [inp_0];
      assert PathValid(new_c, new_path_0);
      assert |NodesNotInPath(new_c, path + [inp_0])| < |NodesNotInPath(new_c, path)|;
      StillHasNoDuplicates(path, inp_0);
      EvaluateINPInnerSelfConnect(c, s, conn, path + [inp_0], fi);
    }
  }

  lemma EvaluateONPBinarySelfConnect(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    requires
      && var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && EvaluateONPBinaryRequirements(new_c, path, fi_second_pass)
      && EvaluateONPBinaryRequirements(new_c, path, fi)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (EvaluateONPBinary(new_c, path, fi_second_pass) == EvaluateONPBinary(new_c, path, fi))
    decreases
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      |NodesNotInPath(new_c, path)|, 3
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var head := Seq.Last(path);
    var nk := c.NodeKind[head.n];
    assert nk == new_c.NodeKind[head.n];
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path {
    } else if inp_1 in path {
    } else {
      NodesNotInPathDecreases(new_c, path, inp_0);
      NodesNotInPathDecreases(new_c, path, inp_1);
      var new_path_0 := path + [inp_0];
      var new_path_1 := path + [inp_1];
      assert PathValid(new_c, new_path_0);
      assert PathValid(new_c, new_path_1);
      assert |NodesNotInPath(new_c, path + [inp_0])| < |NodesNotInPath(new_c, path)|;
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      EvaluateINPInnerSelfConnect(c, s, conn, path + [inp_0], fi);
      EvaluateINPInnerSelfConnect(c, s, conn, path + [inp_1], fi);
    }
  }

  lemma EvaluateONPInnerSelfConnect(c: Circuit, s: Scuf, conn: InternalConnection, path: seq<NP>, fi: FI)
    requires c.Valid()
    requires s.Valid(c)
    requires conn.Valid()
    requires ScufConnectionConsistent(c, s, conn)
    requires
      && var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && EvaluateONPInnerRequirements(new_c, path, fi_second_pass)
      && EvaluateONPInnerRequirements(new_c, path, fi)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && (EvaluateONPInner(new_c, path, fi_second_pass) == EvaluateONPInner(new_c, path, fi))
    decreases
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      |NodesNotInPath(new_c, path)|, 4
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
    var head := path[|path|-1];
    var nk := c.NodeKind[head.n];
    assert nk == new_c.NodeKind[head.n];
    if head.n in fi.state {
      assert nk.CSeq? by {
        reveal FICircuitValid();
      }
      match nk
        case CSeq() => {
          assert fi.state[head.n] == fi_second_pass.state[head.n];
        }
    } else {
      match nk
        case CXor() => {
            EvaluateONPBinarySelfConnect(c, s, conn, path, fi);
        }
        case CAnd() => {
            EvaluateONPBinarySelfConnect(c, s, conn, path, fi);
        }
        case CInv() => {
            EvaluateONPUnarySelfConnect(c, s, conn, path, fi);
        }
        case CIden() => {
            EvaluateONPUnarySelfConnect(c, s, conn, path, fi);
        }
        case CConst(b) => {
        }
        case CSeq() => {
        }
    }
  }

  //lemma EvaluateONP(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
  //  //
  //  // Here we need to prove that when we take a circuit and connect some of the input points to
  //  // other nodes it doesn't effect the evaluation.
  //  // This is because at the input points the evaluation is terminated.
  //  //
  //  //
  //  requires c.Valid()
  //  requires s.Valid(c)
  //  requires conn.Valid()
  //  requires ScufConnectionConsistent(c, s, conn)
  //  requires FIValid(fi, s.mp.inputs, s.mp.state)
  //  requires NPValid(c, np)
  //  requires np in s.mp.outputs || np in StateINPs(s.mp.state)
  //  ensures
  //    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
  //    && FICircuitValid(new_c, fi)
  //    && FICircuitValid(c, fi)
  //    && (Evaluate(new_c, np, fi) == Evaluate(c, np, fi))
  //{
  //}
}
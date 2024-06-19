module ConnectEval {

  import opened Circ
  import opened Scuf
  import opened SelfConnect
  import opened MapFunction
  import opened Eval
  import opened Subcircuit

  ghost predicate ConnectRequirements(c: Circuit, s: Scuf, conn: InternalConnection, fi: FI)
  {
    && c.Valid()
    && s.Valid(c)
    && conn.Valid()
    && ScufConnectionConsistent(c, s, conn)
    && assert conn.i_width == |s.mp.inputs| by {
      reveal ScufConnectionConsistent();
    }
    && FIValid(fi, conn.I2NI(s.mp.inputs), s.mp.state)
    //&& var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    //&& FICircuitValid(new_c, fi)
  }

  //lemma EvaluateONPInnerFirstPass(c: Circuit, s: Scuf, conn: InternalConnection, fi: FI, path: seq<NP>)
  //  requires
  //    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
  //    && EvaluateONPInnerRequirements(new_c, path, fi)
  //    && PathInSubcircuit(path, s.sc)
  //  ensures
  //    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
  //    var fi_first_pass := conn.FIFirstPass(s.mp, fi);
  //    && var np := Seq.Last(path);
  //    && (EvaluateONPInner(new_c, path, fi) == EvaluateONPInner(new_c, path, fi_first_pass))
  //  decreases
  //    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
  //    |NodesNotInPath(new_c, path)|, 6
  //{
  //}
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
      && (Evaluate(new_c, np, fi) == Evaluate(c, np, fi))

  lemma EvaluateSelfConnectFirstPassONP(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    //
    // Here we prove that if when we evaluate one of the outputs that we have connected to an input,
    // the result of the evaluation is not effected is we remove the connected inputs from the
    // termination points.
    // This is true because we enforce that there are not paths from the connected outputs to the connected
    // inputs.
    //
    requires ConnectRequirements(c, s, conn, fi)
    requires
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && NPValid(new_c, np)
      && (np in conn.GetConnectedOutputs(s.mp))
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_first_pass := conn.FIFirstPass(s.mp, fi);
      && FICircuitValid(new_c, fi)
      && FICircuitValid(new_c, fi_first_pass)
      && (Evaluate(new_c, np, fi_first_pass) == Evaluate(new_c, np, fi))

  lemma EvaluateSelfConnectSecondPassONP(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    //
    // Here we prove that if when we evaluate an output using inputs created by fi_second_pass
    // it is equivalent to using the fi inputs.
    //
    // The different between these two inputs is that `fi` does not contain elements from the connected
    // inputs so to prove this we need to show that the values in fi_second_pass match match the values
    // that are calculated using fi.
    //
    requires ConnectRequirements(c, s, conn, fi)
    requires
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && NPValid(new_c, np)
      && (np in new_s.mp.outputs || np in StateINPs(new_s.mp.state))
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);
      && FICircuitValid(new_c, fi)
      && FICircuitValid(new_c, fi_second_pass)
      && (Evaluate(new_c, np, fi_second_pass) == Evaluate(new_c, np, fi))

  //lemma EvaluateSelfConnectFirstPass(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
  //  //
  //  // Here we prove that our evaluation of the circuit matches the UF model.
  //  // We know that the old scuf is still valid but we still need to prove that the updated
  //  // update function matches this conserved behavior.
  //  //
  //  requires ConnectRequirements(c, s, conn, fi)
  //  requires
  //    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
  //    && NPValid(new_c, np)
  //    && (np in conn.GetConnectedOutputs(s.mp))
  //    && s.SomewhatValidRelaxInputs(new_c)
  //    && new_s.SomewhatValidRelaxInputs(new_c)
  //  ensures
  //    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
  //    var fi_first_pass := conn.FIFirstPass(s.mp, fi);
  //    && FICircuitValid(new_c, fi)
  //    && FICircuitValid(new_c, fi_first_pass)
  //    && assert np in new_s.mp.outputs by {
  //      reveal Seq.ToSet();
  //    }
  //    && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(new_s, fi, np)))
  //{
  //  var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
  //  var fi_first_pass := conn.FIFirstPass(s.mp, fi);

  //  assert FICircuitValid(new_c, fi ) by {
  //    assert FIValid(fi, new_s.mp.inputs, new_s.mp.state);
  //    ScufValidFiValidToFICircuitValid(new_c, new_s, fi);
  //    reveal FICircuitValid();
  //  }

  //  assert FICircuitValid(new_c, fi_first_pass) by {
  //    assert FIValid(fi_first_pass, s.mp.inputs, s.mp.state);
  //    ScufValidFiValidToFICircuitValid(new_c, s, fi_first_pass);
  //    reveal FICircuitValid();
  //  }

  //  calc {
  //    Evaluate(new_c, np, fi);
  //    {
  //      EvaluateSelfConnectFirstPassONP(c, s, conn, np, fi);
  //    }
  //    Evaluate(new_c, np, fi_first_pass);
  //    {
  //      EvaluateSelfConnectOldONP(c, s, conn, np, fi_first_pass);
  //    }
  //    Evaluate(c, np, fi_first_pass);
  //    {
  //      assert s.Valid(c);
  //      reveal Seq.ToSet();
  //      reveal Scuf.EvaluatesCorrectly();
  //    }
  //    EvalOk(MFLookup(s, fi_first_pass, np));
  //    {
  //      SelfConnectFirstPassMFLookup(s, conn, np, fi);
  //    }
  //    EvalOk(MFLookup(new_s, fi, np));
  //  }
  //}

  lemma EvaluateSelfConnect(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    requires ConnectRequirements(c, s, conn, fi)
    requires
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && (np in new_s.mp.outputs || np in StateINPs(new_s.mp.state))
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && s.SomewhatValidRelaxInputs(new_c)
      && new_s.SomewhatValidRelaxInputs(new_c)
    ensures
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && FICircuitValid(new_c, fi)
      && NPValid(new_c, np)
      && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(new_s, fi, np)))
  {
    var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
    var connection := conn.GetConnection(s.mp);
    var fi_first_pass := conn.FIFirstPass(s.mp, fi);
    var fi_second_pass := conn.FISecondPass(s.mp, s.uf, fi);

    assert NPValid(c, np) && NPValid(new_c, np) by {
      assert np in s.mp.outputs || np in StateINPs(s.mp.state);
      ScufFInputsAreValid(c, s);
      ScufFOutputsAreValid(c, s);
      ScufFInputsAreValid(new_c, s);
      ScufFOutputsAreValid(new_c, s);
    }

    assert FICircuitValid(new_c, fi ) by {
      assert FIValid(fi, new_s.mp.inputs, new_s.mp.state);
      ScufValidFiValidToFICircuitValid(new_c, new_s, fi);
      reveal FICircuitValid();
    }
    assert FICircuitValid(new_c, fi_second_pass) by {
      assert FIValid(fi_second_pass, s.mp.inputs, s.mp.state);
      ScufValidFiValidToFICircuitValid(new_c, s, fi_second_pass);
    }
    assert FICircuitValid(c, fi_second_pass) by {
      assert FIValid(fi_second_pass, s.mp.inputs, s.mp.state);
      ScufValidFiValidToFICircuitValid(c, s, fi_second_pass);
    }

    calc {
      Evaluate(new_c, np, fi);
      {
        EvaluateSelfConnectSecondPassONP(c, s, conn, np, fi);
      }
      Evaluate(new_c, np, fi_second_pass);
      {
        EvaluateSelfConnectOldONP(c, s, conn, np, fi_second_pass);
      }
      Evaluate(c, np, fi_second_pass);
      {
        assert s.Valid(c);
        reveal Seq.ToSet();
        reveal Scuf.EvaluatesCorrectly();
      }
      EvalOk(MFLookup(s, fi_second_pass, np));
      {
        SelfConnectSecondPassMFLookup(s, conn, np, fi);
      }
      EvalOk(MFLookup(new_s, fi, np));
    }

  }

}
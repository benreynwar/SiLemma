module SelfConnectEval {

  import opened Circ
  import opened Scuf
  import opened SelfConnect
  import opened MapFunction
  import opened Eval
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened SelfConnectEval2
  import opened Path

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


  lemma EvaluateSelfConnect(c: Circuit, s: Scuf, conn: InternalConnection, np: NP, fi: FI)
    requires ConnectRequirements(c, s, conn, fi)
    requires
      var (new_c, new_s) := ConnectCircuitScufImpl(c, s, conn);
      && (np in new_s.mp.outputs || np in StateINPs(new_s.mp.state))
      && FIValid(fi, new_s.mp.inputs, new_s.mp.state)
      && s.SomewhatValidRelaxInputs(new_c)
      && new_s.SomewhatValidRelaxInputs(new_c)
      && var conn_outputs := conn.GetConnectedOutputs(s.mp);
      && var conn_inputs := conn.GetConnectedInputs(s.mp);
      && !PathExistsBetweenNPSets(new_c, conn_outputs, conn_inputs)
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
        EvaluateWithActual(c, s, conn, np, fi);
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
      assert new_s.SomewhatValid(new_c) by {
      }
      assert new_s.SomewhatValidRelaxInputs(new_c) by {
        new_s.SomewhatValidToRelaxInputs(new_c);
      }
      assert new_s.EvaluatesCorrectly(new_c) by {
        reveal ScValid();
        ScufFOutputsAreValid(new_c, new_s);
        reveal Seq.ToSet();
        forall fi: FI | FIValid(fi, new_s.mp.inputs, new_s.mp.state)
          ensures forall np :: np in Seq.ToSet(new_s.mp.outputs) || np in StateINPs(new_s.mp.state) ==>
            && FICircuitValid(new_c, fi)
            && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(new_s, fi, np)))
        {
          assert FICircuitValid(new_c, fi) by {ScufValidFiValidToFICircuitValid(new_c, new_s, fi);}
          forall np | np in Seq.ToSet(new_s.mp.outputs) || np in StateINPs(new_s.mp.state)
            ensures Evaluate(new_c, np, fi) == EvalOk(MFLookup(new_s, fi, np))
          {
            reveal ScufConnectionConsistent();
            var conn_outputs := conn.GetConnectedOutputs(s.mp);
            var conn_inputs := conn.GetConnectedInputs(s.mp);
            ScufFInputsAreValid(c, s);
            ScufFOutputsAreValid(c, s);
            reveal ONPsValid();
            StillNoPathExistsBetweenNPSets(c, new_c, conn_outputs, conn_inputs);
            EvaluateSelfConnect(c, s, conn, np, fi);
          }
        }
        reveal Scuf.EvaluatesCorrectly();
      }
      assert new_s.MapValid() by {
      }
    }
    assert s.ValidRelaxInputs(new_c) by {
      assert s.MapValid();
      assert ScValid(new_c, s.sc);
      assert s.SomewhatValidRelaxInputs(new_c);
      reveal Scuf.EvaluatesCorrectly();
      assert s.EvaluatesCorrectly(new_c) by {
        reveal ScValid();
        ScufFOutputsAreValid(new_c, s);
        reveal Seq.ToSet();
        forall fi: FI | FIValid(fi, s.mp.inputs, s.mp.state)
          ensures forall np :: np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state) ==>
            && FICircuitValid(new_c, fi)
            && (Evaluate(new_c, np, fi) == EvalOk(MFLookup(s, fi, np)))
        {
          assert FICircuitValid(new_c, fi) by {ScufValidFiValidToFICircuitValid(new_c, s, fi);}
          forall np | np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state)
            ensures Evaluate(new_c, np, fi) == EvalOk(MFLookup(s, fi, np))
          {
            EvaluateSelfConnectOldONP(c, s, conn, np, fi);
          }
        }
      }
    }
    (new_c, new_s)
  }


}
module Build.AndN {

  import opened Std.Wrappers

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Utils
  import opened Entity
  import opened MapFunction
  import opened ConnectionEval
  import opened Connection
  import opened IslandBundle
  import opened Subcircuit
  import opened MapConnection

  import opened AndBuilder
  import opened IdentBuilder
  import opened ConstBuilder

  function AndNBehav(a: seq<bool>): bool
  {
    if |a| == 0 then
      true
    else
      var n := |a|;
      a[n-1] && AndNBehav(a[..n-1])
  }

  function AndNSF(n: nat, si: SI): (so: SO)
    requires |si.inputs| == n
    requires |si.state| == 0
  {
    SO([AndNBehav(si.inputs)], [])
  }

  ghost predicate MFReqs(n: nat, mf_andn: MapFunction, mf_and: MapFunction, mf_combined: MapFunction)
  {
    && n > 0
    && AndNMFValid(n-1, mf_andn)
    && AndNMFValid(n, mf_combined)
    && AndMFValid(mf_and)
    && mf_andn.NPs() !! mf_and.NPs()
    && mf_combined.inputs == mf_andn.inputs + [mf_and.inputs[0]]
    && mf_combined.outputs == mf_and.outputs
  }

  function ABI2AI(n: nat): (abi2ai: seq<nat>)
    requires n > 0
  {
    seq(n-1, (index: nat) requires index < n-1 => index)
  }

  lemma ABI2AICorrect(n: nat, mf_andn: MapFunction, mf_and: MapFunction, mf_combined: MapFunction)
    requires MFReqs(n, mf_andn, mf_and, mf_combined)
    ensures
      var abi2ai := ABI2AI(n);
      ConnectionX(mf_combined.inputs, mf_andn.inputs, abi2ai).Valid()
  {
    reveal Seq.HasNoDuplicates();
    reveal ConnectionX<NP>.Valid();
  }

  function ABIAO2BI(n: nat): (abiao2bi: seq<(bool, nat)>)
    requires n > 0
  {
    [(false, n-1), (true, 0)]
  }

  lemma ABIAO2BICorrect(n: nat, mf_andn: MapFunction, mf_and: MapFunction, mf_combined: MapFunction)
    requires MFReqs(n, mf_andn, mf_and, mf_combined)
    ensures
      var abiao2bi := ABIAO2BI(n);
      ConnectionXY(mf_combined.inputs, mf_andn.outputs, mf_and.inputs, true, false, abiao2bi).Valid()
  {
    var abiao2bi: seq<(bool, nat)> := [(false, n-1), (true, 0)];
    var conn := abiao2bi;
    var out := mf_and.inputs;
    var in1 := mf_combined.inputs;
    var in2 := mf_andn.outputs;
    var in1out_direct := true;
    var in2out_direct := false;
    assert Seq.HasNoDuplicates(conn) by {
      reveal Seq.HasNoDuplicates();
    }
    assert mf_and.inputs[0] !in mf_andn.inputs by {
      reveal Seq.ToSet();
      assert Seq.ToSet(mf_and.inputs) !! Seq.ToSet(mf_andn.inputs);
      assert mf_and.inputs[0] in Seq.ToSet(mf_and.inputs);
    }
    assert Seq.HasNoDuplicates(in1) by {
      reveal Seq.ToSet();
      reveal Seq.HasNoDuplicates();
      assert mf_combined.inputs == mf_andn.inputs + [mf_and.inputs[0]];
      mf_andn.InputsHasNoDuplicates();
      assert Seq.HasNoDuplicates(mf_andn.inputs);
      assert Seq.ToSet(mf_andn.inputs) <= mf_andn.NPs();
      assert Seq.ToSet(mf_and.inputs) <= mf_and.NPs();
      assert Seq.ToSet(mf_and.inputs) !! Seq.ToSet(mf_andn.inputs);
      assert mf_and.inputs[0] in Seq.ToSet(mf_and.inputs);
      assert mf_and.inputs[0] !in mf_andn.inputs;
    }
    assert Seq.HasNoDuplicates(in2) by {
      reveal Seq.HasNoDuplicates();
    }
    assert Seq.HasNoDuplicates(out) by {
      mf_and.InputsHasNoDuplicates();
    }
    assert (forall index: nat :: index < |conn| ==> (
       var (in_type, pos) := conn[index];
       && (!in_type && in1out_direct ==> out[index] == in1[conn[index].1])
       && ( in_type && in2out_direct ==> out[index] == in2[conn[index].1])
     ));
    forall index_out: nat, index1: nat | index_out < |out| && index1 < |in1| && in1out_direct && out[index_out] == in1[index1]
      ensures conn[index_out] == (false, index1)
      {
        mf_and.InputsHasNoDuplicates();
        reveal Seq.HasNoDuplicates();
        reveal Seq.ToSet();
        assert in1 == mf_andn.inputs + [out[0]];
        assert Seq.ToSet(out) !! Seq.ToSet(mf_andn.inputs);
        assert out[0] !in Seq.ToSet(mf_andn.inputs);
        if index1 < |in1|-1 {
          assert in1[index1] == mf_andn.inputs[index1];
          assert in1[index1] in Seq.ToSet(mf_andn.inputs);
          assert in1[index1] !in Seq.ToSet(out);
          assert in1[index1] !in out;
          assert false;
        } else {
          assert index1 == |in1|-1;
          assert index_out == 0;
        }
       }
    assert (forall index_out: nat, index2: nat :: index_out < |out| && index2 < |in2| && in2out_direct
       && out[index_out] == in2[index2] ==> (conn[index_out] == (true, index2)));
    assert ConnectionXY(mf_combined.inputs, mf_andn.outputs, mf_and.inputs, true, false, abiao2bi).Valid() by {
      reveal ConnectionXY<NP>.Valid();
      reveal Seq.HasNoDuplicates();
    }
  }

  function AOBO2ABO(n: nat): (aobo2abo: seq<(bool, nat)>)
    requires n > 0
  {
    [(true, 0)]
  }

  lemma AOBO2ABOCorrect(n: nat, mf_andn: MapFunction, mf_and: MapFunction, mf_combined: MapFunction)
    requires MFReqs(n, mf_andn, mf_and, mf_combined)
    ensures
      var aobo2abo := AOBO2ABO(n);
      ConnectionXY(mf_andn.outputs, mf_and.outputs, mf_combined.outputs, true, true, aobo2abo).Valid()
  {
      var aobo2abo := AOBO2ABO(n);
      var cn := ConnectionXY(mf_andn.outputs, mf_and.outputs, mf_combined.outputs, true, true, aobo2abo);
      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
      forall index_out: nat, index1: nat | index_out < |cn.out| && index1 < |cn.in1| && cn.in1out_direct
        ensures cn.out[index_out] != cn.in1[index1]
      {
        if cn.out[index_out] == cn.in1[index1] {
          assert cn.out[index_out] in mf_combined.outputs;
          assert cn.out[index_out] in mf_andn.outputs;
          assert cn.out[index_out] in Seq.ToSet(mf_andn.outputs) * Seq.ToSet(mf_combined.outputs);
          assert false;
        }
      }
      assert cn.Valid() by {
        reveal cn.Valid();
      }
  }


  function ConnectAndNImpl(n: nat, mf_andn: MapFunction,
      mf_and: MapFunction, mf_combined: MapFunction): (r: MFConnection)
    requires MFReqs(n, mf_andn, mf_and, mf_combined)
    ensures r.SomewhatValid()
    //requires
    //  reveal mf_andn.Valid();
    //  forall si :: SIValid(si, mf_andn.inputs, mf_andn.state) ==> mf_andn.sf(si) == AndNSF(n-1, si)
    //requires
    //  reveal mf_and.Valid();
    //  forall si :: SIValid(si, mf_and.inputs, mf_and.state) ==> mf_and.sf(si) == AndSF(n, si)
    //requires
    //  forall si :: SIValid(si, mf_combined.inputs, mf_combined.state) ==>
    //    mf_combined.sf.requires(si) && mf_combined.sf(si) == AndNSF(n, si)
  {
    var abi2ai: seq<nat> := ABI2AI(n);
    var abiao2bi: seq<(bool, nat)> := ABIAO2BI(n);
    var aobo2abo: seq<(bool, nat)> := AOBO2ABO(n);
    var abs2as: seq<nat> := [];
    var abs2bs: seq<nat> := [];
    var asbs2abs: seq<(bool, nat)> := [];
    ABI2AICorrect(n, mf_andn, mf_and, mf_combined);
    ABIAO2BICorrect(n, mf_andn, mf_and, mf_combined);
    AOBO2ABOCorrect(n, mf_andn, mf_and, mf_combined);
    ConnectionX(mf_combined.state, mf_andn.state, abs2as).EmptyThenValid();
    ConnectionX(mf_combined.state, mf_and.state, abs2bs).EmptyThenValid();
    ConnectionXY(mf_andn.state, mf_and.state, mf_combined.state, true, true, asbs2abs).EmptyThenValid();
    assert MakeConnectionsReqs(mf_andn, mf_and, mf_combined, abi2ai, abiao2bi, aobo2abo,
                               abs2as, abs2bs, asbs2abs);
    var conn := MakeConnections(mf_andn, mf_and, mf_combined, abi2ai, abiao2bi, aobo2abo, [], [], []);
    assert conn.SomewhatValid();
    conn
  }

  lemma ConnectAndNCorrect(n: nat, mf_andn: MapFunction, mf_and: MapFunction, mf_combined: MapFunction)
    requires MFReqs(n, mf_andn, mf_and, mf_combined)
    ensures ConnectAndNImpl(n, mf_andn, mf_and, mf_combined).Valid()
  {
      var conn := ConnectAndNImpl(n, mf_andn, mf_and, mf_combined);
      assert conn.SomewhatValid();
      assert conn.SeqEvaluatesCorrectly() by {
        forall si: SI | SIValid(si, mf_combined.inputs, mf_combined.state)
          ensures mf_combined.sf.requires(si)
          ensures conn.SeqEvaluateSeparately(si) == mf_combined.sf(si)
        {
          assert mf_combined.sf.requires(si) by {
            reveal mf_combined.Valid();
          }
          var so := mf_combined.sf(si);
          var si_a := conn.si2sia(si);
          assert si_a.inputs == si.inputs[..n-1];
          assert si_a.state == [];
          assert mf_andn.sf.requires(si_a) by {
            reveal mf_andn.Valid();
          }
          var so_a := mf_andn.sf(si_a);
          assert so_a.outputs == [AndNBehav(si_a.inputs)] by {
            reveal mf_andn.Valid();
          }
          assert so_a.state == [];
          var si_b := conn.si2sib(si);
          assert si_b.inputs == conn.abiao2bi.MapSeq(si.inputs, so_a.outputs);
          assert si_b.inputs == [si.inputs[n-1], so_a.outputs[0]];
          var so_b := mf_and.sf(si_b);
          assert so_b.outputs == [si.inputs[n-1] && so_a.outputs[0]];
          assert so_b.outputs == [si.inputs[n-1] && AndNBehav(si_a.inputs)];
          assert so_b.outputs == [si.inputs[n-1] && AndNBehav(si.inputs[..n-1])];
          assert so_b.outputs == [AndNBehav(si.inputs)];
          assert conn.SeqEvaluateSeparately(si) == mf_combined.sf(si);
        }
        reveal conn.SeqEvaluatesCorrectly();
      }
      assert conn.ABValid() by {
        reveal Seq.ToSet();
      }

  }

  ghost predicate AndNMFValid(n: nat, mf: MapFunction)
  {
    && mf.Valid()
    && (|mf.inputs| == n)
    && (|mf.state| == 0)
    && (|mf.outputs| == 1)
    && (forall si :: SIValid(si, mf.inputs, mf.state) ==> (
      && mf.sf.requires(si)
      && (mf.sf(si) == AndNSF(n, si))))
  }

  function AndNMF(c: Circuit, e1: Entity, e2: Entity): (combined_mf: MapFunction)
    requires CircuitValid(c)
    requires EntityValid(c, e1)
    requires EntityValid(c, e2)
    requires e1.sc !! e2.sc
    requires |e2.mf.inputs| == 2
    requires |e2.mf.outputs| == 1
    ensures combined_mf.Valid()
  {
    var b_i0 := e2.mf.inputs[0];
    var b_o := e2.mf.outputs[0];
    var combined_inputs := e1.mf.inputs + [b_i0];
    var combined_outputs := [b_o];
    var combined_mf := MapFunction(combined_inputs, combined_outputs, [],
      (si: SI) requires SIValid(si, combined_inputs, []) =>
      reveal Seq.ToSet();
      SO([AndNBehav(si.inputs)], [])
    );
    assert combined_mf.Valid() by {
      reveal Seq.ToSet();
      reveal Seq.HasNoDuplicates();
      reveal MapFunction.Valid();
      assert (forall si: SI :: SIValid(si, combined_mf.inputs, combined_mf.state) ==> (
        && combined_mf.sf.requires(si)
        && SOValid(combined_mf.sf(si), combined_mf.outputs, combined_mf.state)
      ));
      FInputsInSc(c, e1);
      FInputsInSc(c, e2);
      FOutputsInSc(c, e1);
      FOutputsInSc(c, e2);
      reveal NPsInSc();
      ScNoIntersectionNPsNoIntersection(e1.sc, e2.sc, Seq.ToSet(e1.mf.inputs), {b_i0, b_o});
      e1.mf.InputsHasNoDuplicates();
      var inputs := combined_mf.inputs;
      var outputs := combined_mf.outputs;
      var state := combined_mf.state;
      assert (forall si: SI :: SIValid(si, inputs, state) ==> (
          && combined_mf.sf.requires(si)
          && SOValid(combined_mf.sf(si), outputs, state)
      ));
      assert Seq.HasNoDuplicates(e1.mf.inputs);
      assert Seq.HasNoDuplicates([b_i0, b_o]) by {
        assert Seq.HasNoDuplicates(e2.mf.inputs + e2.mf.outputs);
        SubSeqsNoDuplicates(e2.mf.inputs, e2.mf.outputs);
        assert b_i0 in e2.mf.inputs;
        assert b_o in e2.mf.outputs;
        if b_i0 == b_o {
          assert b_i0 in Seq.ToSet(e2.mf.inputs) && b_i0 in Seq.ToSet(e2.mf.outputs);
          assert !(Seq.ToSet(e2.mf.inputs) !! Seq.ToSet(e2.mf.outputs));
          assert false;
        }
      }
      assert Seq.ToSet(e1.mf.inputs) !! Seq.ToSet([b_i0, b_o]);
      assert Seq.HasNoDuplicates(inputs + outputs) by {
        assert inputs + outputs == e1.mf.inputs + [b_i0, b_o];
        Seq.LemmaNoDuplicatesInConcat(e1.mf.inputs, [b_i0, b_o]);
      }
      assert Seq.HasNoDuplicates(state);
      assert Seq.HasNoDuplicates(inputs + StateONPsSeq(state));
      assert Seq.HasNoDuplicates(outputs + StateINPsSeq(state));
      reveal combined_mf.Valid();
    }
    combined_mf
  }

  function InsertAndNImpl(c: Circuit, n: nat): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures CircuitValid(r.0)
    ensures EntityValid(r.0, r.1)
    ensures CircuitUnconnected(c, r.0)
    ensures CircuitConserved(c, r.0)
    ensures r.0.NodeKind.Keys == c.NodeKind.Keys + r.1.sc
    ensures c.NodeKind.Keys !! r.1.sc
    ensures |r.1.mf.inputs| == n
  {
    if n == 0 then
      InsertConst(c, true)
    else
      var eb1 := IslandBundleFromCircuit(c);
      var (c1, e1) := InsertAndNImpl(c, n-1);
      assert c1.NodeKind.Keys == c.NodeKind.Keys + e1.sc;
      var (eb2, a_ref) := AddEntity(eb1, c1, e1);
      //assert e1.sc == {e1.mf.outputs[0].n};
      assert EntityValid(c1, e1);

      assert e1 == eb2.es[a_ref].value;

      var (c2, e2) := InsertAnd(c1);
      assert c2.NodeKind.Keys == c.NodeKind.Keys + e1.sc + e2.sc;
      var (eb3, b_ref) := AddEntity(eb2, c2, e2);
      assert e2.sc == {e2.mf.outputs[0].n};

      assert e1 == eb3.es[a_ref].value;
      assert EntityValid(eb3.c, e1) && IsIsland(eb3.c, e1.sc) by {
        reveal IslandBundleValid();
      }

      // e1 has (n-1) inputs and 1 output.
      // e2 has 2 inputs and 1 output.

      var a_i := e1.mf.inputs;
      var a_o := e1.mf.outputs[0];

      var b_i0 := e2.mf.inputs[0];
      var b_i1 := e2.mf.inputs[1];
      var b_o := e2.mf.outputs[0];

      assert e1.sc !! e2.sc;

      var combined_inputs := e1.mf.inputs + [b_i0];
      var combined_outputs := [b_o];

      var combined_mf := AndNMF(eb3.c, e1, e2);
      var combined_e := Entity(e1.sc + e2.sc, combined_mf);
      assert c2.NodeKind.Keys == c.NodeKind.Keys + combined_e.sc;
      assert eb3.c.NodeKind.Keys == c.NodeKind.Keys + combined_e.sc;
      assert e1.mf.NPs() !! e2.mf.NPs() by {
        EntitiesSeparate(eb3.c, e1, e2);
      }
      var conn := ConnectAndNImpl(n, e1.mf, e2.mf, combined_mf);
      assert conn.Valid() by {
        ConnectAndNCorrect(n, e1.mf, e2.mf, combined_mf);
      }

      IsIslandInputsNotInPortSource(eb3.c, e2);
      assert ConnectEntitiesRequirements(eb3.c, e1, e2, combined_e, conn);
      var (eb4, ab_ref) := IBConnectEntities(eb3, a_ref, b_ref, combined_e, conn);
      var e_ab := eb4.es[ab_ref].value;
      assert eb4.es == [None, None, Some(e_ab)];

      assert IsIsland(eb4.c, e_ab.sc) by {
        reveal IslandBundleValid();
      }
      assert IsIsland(eb4.c, e_ab.sc);
      IsIslandNoOutputs(eb4.c, e_ab.sc);
      assert eb4.c.NodeKind.Keys == c.NodeKind.Keys + combined_e.sc by {
        reveal ConnectEntitiesImpl();
      }
      assert c == eb4.bg;
      reveal IslandBundleValid();
      assert CircuitUnconnected(c, eb4.c);
      assert CircuitConserved(c, eb4.c);

      (eb4.c, e_ab)
  }

}
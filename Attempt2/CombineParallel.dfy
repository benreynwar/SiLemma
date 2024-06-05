module CombineParallel {

  import Std.Collections.Seq
  import opened MapFunction
  import opened MapConnection
  import opened Utils
  import opened Circ
  import opened Entity
  import opened Subcircuit
  import opened Connection

  datatype ParallelCombiner = ParallelCombiner(
    mf_a: MapFunction,
    mf_b: MapFunction
  ) {
    
    ghost predicate Valid()
    {
      && mf_a.Valid()
      && mf_b.Valid()
      && (mf_a.NPs() !! mf_b.NPs())
      && (Seq.ToSet(mf_a.state) !! Seq.ToSet(mf_b.state))
    }

    function ABI2AI(): (abi2ai: seq<nat>)
    {
      seq(|mf_a.inputs|, (index: nat) requires index < |mf_a.inputs| => index)
    }

    function ABIAO2BI(): (abiao2bi: seq<(bool, nat)>)
    {
      seq(|mf_b.inputs|, (index: nat) requires index < |mf_b.inputs| => (false, |mf_a.inputs| + index))
    }

    function AOBO2ABO(): (aobo2abo: seq<(bool, nat)>)
    {
      seq(|mf_a.outputs|+|mf_b.outputs|, (index: nat) requires index < |mf_a.outputs| + |mf_b.outputs| =>
        if index < |mf_a.outputs| then (false, index) else (true, index - |mf_a.outputs|))
    }

    function ABS2AS(): (abs2as: seq<nat>)
    {
      seq(|mf_a.state|, (index: nat) requires index < |mf_a.state| => index)
    }

    function ABS2BS(): (abs2bs: seq<nat>)
    {
      seq(|mf_b.state|, (index: nat) requires index < |mf_b.state| => |mf_a.state| + index)
    }

    function ASBS2ABS(): (asbs2abs: seq<(bool, nat)>)
    {
      seq(|mf_a.state + mf_b.state|, (index: nat) requires index < |mf_a.state + mf_b.state| =>
        if index < |mf_a.state| then (false, index) else (true, index - |mf_a.state|))
    }

    function sf(si: SI): (so: SO)
      requires Valid()
      requires SIValid(si, mf_a.inputs + mf_b.inputs, mf_a.state + mf_b.state)
      ensures SOValid(so, mf_a.outputs + mf_b.outputs, mf_a.state + mf_b.state)
    {
      reveal MapFunction.Valid();
      SubSeqsNoDuplicates(mf_a.inputs, mf_a.outputs);
      SubSeqsNoDuplicates(mf_b.inputs, mf_b.outputs);
      var si_a := SI(si.inputs[..|mf_a.inputs|], si.state[..|mf_a.state|]);
      var si_b := SI(si.inputs[|mf_a.inputs|..], si.state[|mf_a.state|..]);
      var so_a := mf_a.sf(si_a);
      var so_b := mf_b.sf(si_b);
      var so := SO(so_a.outputs + so_b.outputs, so_a.state + so_b.state);
      assert Seq.ToSet(mf_a.outputs) !! Seq.ToSet(mf_b.outputs);
      NoDuplicatesInConcat(mf_a.outputs, mf_b.outputs);
      assert SOValid(so, mf_a.outputs + mf_b.outputs, mf_a.state + mf_b.state);
      so
    }

    function mf(): (r: MapFunction)
      requires Valid()
      ensures r.Valid()
    {
      reveal MapFunction.Valid();
      var r := MapFunction(mf_a.inputs+mf_b.inputs, mf_a.outputs+mf_b.outputs, mf_a.state + mf_b.state, sf);
      var inputs := r.inputs;
      var state := r.state;
      var outputs := r.outputs;
      SubSeqsNoDuplicates(mf_a.inputs, mf_a.outputs);
      SubSeqsNoDuplicates(mf_b.inputs, mf_b.outputs);
      NoDuplicatesInConcat(mf_a.inputs, mf_b.inputs);
      NoDuplicatesInConcat(mf_a.outputs, mf_b.outputs);
      assert Seq.ToSet(mf_a.inputs + mf_b.inputs) !! Seq.ToSet(mf_a.outputs + mf_b.outputs) by {
        assert (Seq.ToSet(mf_a.inputs) + Seq.ToSet(mf_b.inputs)) !! (Seq.ToSet(mf_a.outputs) + Seq.ToSet(mf_b.outputs));
        ConcatSeqToSet(mf_a.inputs, mf_b.inputs);
        ConcatSeqToSet(mf_a.outputs, mf_b.outputs);
      }
      NoDuplicatesInConcat(inputs, outputs);
      assert Seq.HasNoDuplicates(mf_a.inputs + mf_b.inputs);
      assert (forall si: SI :: SIValid(si, inputs, state) ==> (
          && sf.requires(si)
          && SOValid(sf(si), outputs, state)
      ));
      assert Seq.HasNoDuplicates(inputs + outputs);
      NoDuplicatesInConcat(mf_a.state, mf_b.state);
      assert Seq.HasNoDuplicates(state);
      assert Seq.ToSet(mf_a.inputs + mf_b.inputs) !! Seq.ToSet(StateONPsSeq(mf_a.state + mf_b.state)) by {
        StateONPsSeqSame(mf_a.state + mf_b.state);
        StateONPsSeqSame(mf_a.state);
        StateONPsSeqSame(mf_b.state);
        assert Seq.ToSet(StateONPsSeq(mf_a.state + mf_b.state)) == StateONPs(mf_a.state + mf_b.state);
        ConcatSeqToSet(mf_a.inputs, mf_b.inputs);
        assert StateONPs(mf_a.state + mf_b.state) == StateONPs(mf_a.state) + StateONPs(mf_b.state);
        SubSeqsNoDuplicates(mf_a.inputs, StateONPsSeq(mf_a.state));
        SubSeqsNoDuplicates(mf_b.inputs, StateONPsSeq(mf_b.state));
      }
      StateONPsSeqNoDuplicates(state);
      NoDuplicatesInConcat(inputs, StateONPsSeq(state));
      assert Seq.HasNoDuplicates(inputs + StateONPsSeq(state));
      assert Seq.ToSet(mf_a.outputs + mf_b.outputs) !! Seq.ToSet(StateINPsSeq(mf_a.state + mf_b.state)) by {
        StateINPsSeqSame(mf_a.state + mf_b.state);
        StateINPsSeqSame(mf_a.state);
        StateINPsSeqSame(mf_b.state);
        assert Seq.ToSet(StateINPsSeq(mf_a.state + mf_b.state)) == StateINPs(mf_a.state + mf_b.state);
        ConcatSeqToSet(mf_a.outputs, mf_b.outputs);
        assert StateINPs(mf_a.state + mf_b.state) == StateINPs(mf_a.state) + StateINPs(mf_b.state);
        SubSeqsNoDuplicates(mf_a.outputs, StateINPsSeq(mf_a.state));
        SubSeqsNoDuplicates(mf_b.outputs, StateINPsSeq(mf_b.state));
      }
      StateINPsSeqNoDuplicates(state);
      NoDuplicatesInConcat(outputs, StateINPsSeq(state));
      assert Seq.HasNoDuplicates(outputs + StateINPsSeq(state));
      r
    }

    lemma ABI2AICorrect()
      ensures
        ConnectionX(mf_a.inputs + mf_b.inputs, mf_a.inputs, ABI2AI()).Valid()
    {
      reveal Seq.HasNoDuplicates();
      reveal ConnectionX<NP>.Valid();
      var out := mf_a.inputs;
      var conn := ABI2AI();
      var in1 := mf_a.inputs + mf_b.inputs;
      assert (|conn| == |out|);
      assert (forall x :: x in conn ==> x < |in1|);
      assert (forall index: nat :: index < |out| ==> conn[index] < |in1|);
      assert Seq.HasNoDuplicates(conn);
      assert (forall index: nat :: index < |out| ==> out[index] == in1[conn[index]]);
    }

    lemma ABIAO2BICorrect()
      requires Valid()
      ensures
        ConnectionXY(mf_a.inputs + mf_b.inputs, mf_a.outputs, mf_b.inputs, true, false, ABIAO2BI()).Valid()
    {
      reveal Seq.HasNoDuplicates();
      reveal ConnectionXY<NP>.Valid();
      var out := mf_b.inputs;
      var conn := ABIAO2BI();
      var in1 := mf_a.inputs + mf_b.inputs;
      var in2 := mf_a.outputs;
      var in1out_direct := true;
      var in2out_direct := false;
      assert (|conn| == |out|);
      assert (forall x :: x in conn && !x.0 ==> 0 <= x.1 < |in1|);
      assert (forall x :: x in conn &&  x.0 ==> 0 <= x.1 < |in2|);
      assert Seq.HasNoDuplicates(conn);
      assert
        && Seq.HasNoDuplicates(in1)
        && Seq.HasNoDuplicates(in2)
        && Seq.HasNoDuplicates(out)
      by {
        reveal MapFunction.Valid();
        SubSeqsNoDuplicates(mf_a.inputs, mf_a.outputs);
        SubSeqsNoDuplicates(mf_b.inputs, mf_b.outputs);
        NoDuplicatesInConcat(mf_a.inputs, mf_b.inputs);
      }
      assert (
        forall index: nat :: index < |conn| ==> (
          var (in_type, pos) := conn[index];
          && (!in_type && in1out_direct ==> out[index] == in1[conn[index].1])
          && ( in_type && in2out_direct ==> out[index] == in2[conn[index].1])
        ));
      assert (
        forall index_out: nat, index1: nat :: index_out < |out| && index1 < |in1| && in1out_direct
          && out[index_out] == in1[index1]
          ==> (conn[index_out] == (false, index1)));
      assert (
        forall index_out: nat, index2: nat :: index_out < |out| && index2 < |in2| && in2out_direct
          && out[index_out] == in2[index2]
          ==> (conn[index_out] == (true, index2)));
    }

    lemma AOBO2ABOCorrect()
      requires Valid()
      ensures
        ConnectionXY(mf_a.outputs, mf_b.outputs, mf_a.outputs + mf_b.outputs, true, true, AOBO2ABO()).Valid()
    {
      reveal Seq.HasNoDuplicates();
      reveal ConnectionXY<NP>.Valid();
      var out := mf_a.outputs + mf_b.outputs;
      var conn := AOBO2ABO();
      var in1 := mf_a.outputs;
      var in2 := mf_b.outputs;
      var in1out_direct := true;
      var in2out_direct := true;
      assert (|conn| == |out|);
      assert (forall x :: x in conn && !x.0 ==> 0 <= x.1 < |in1|);
      assert (forall x :: x in conn &&  x.0 ==> 0 <= x.1 < |in2|);
      assert Seq.HasNoDuplicates(conn);
      assert
        && Seq.HasNoDuplicates(in1)
        && Seq.HasNoDuplicates(in2)
        && Seq.HasNoDuplicates(out)
      by {
        reveal MapFunction.Valid();
        SubSeqsNoDuplicates(mf_a.inputs, mf_a.outputs);
        SubSeqsNoDuplicates(mf_b.inputs, mf_b.outputs);
        NoDuplicatesInConcat(mf_a.outputs, mf_b.outputs);
      }
      assert (forall index: nat :: index < |conn| ==> (
            var (in_type, pos) := conn[index];
            && (!in_type && in1out_direct ==> out[index] == in1[conn[index].1])
            && ( in_type && in2out_direct ==> out[index] == in2[conn[index].1])
          ));
      forall index_out: nat, index1: nat, index2: nat | index_out < |out| && index1 < |in1| && index2 < |in2|
        ensures in1out_direct && out[index_out] == in1[index1] ==> (conn[index_out] == (false, index1))
        ensures in2out_direct && out[index_out] == in2[index2] ==> (conn[index_out] == (true, index2))
      {
        assert Seq.ToSet(in1) !! Seq.ToSet(in2);
        reveal Seq.ToSet();
        if in1out_direct && out[index_out] == in1[index1] {
          if index_out < |in1| {
            assert index_out == index1;
          } else {
            assert out[index_out] == in2[index_out-|in1|];
            assert in1[index1] == in2[index_out-|in1|];
            assert in1[index1] in Seq.ToSet(in1) && in1[index1] in Seq.ToSet(in2);
            assert false;
          }
        }
        if in2out_direct && out[index_out] == in2[index2] {
          if index_out >= |in1| {
            assert index_out-|in1| == index2;
          } else {
            assert out[index_out] == in1[index_out];
            assert out[index_out] in Seq.ToSet(in1);
            assert false;
          }
        }
      }
      assert (forall index_out: nat, index1: nat :: index_out < |out| && index1 < |in1| && in1out_direct
                && out[index_out] == in1[index1]
                ==> (conn[index_out] == (false, index1)));
      assert (forall index_out: nat, index2: nat :: index_out < |out| && index2 < |in2| && in2out_direct
                && out[index_out] == in2[index2]
                ==> (conn[index_out] == (true, index2)));
    }

    lemma ABS2ASCorrect()
      ensures
        ConnectionX(mf_a.state + mf_b.state, mf_a.state, ABS2AS()).Valid()
    {
      reveal Seq.HasNoDuplicates();
      reveal ConnectionX<CNode>.Valid();
      var out := mf_a.state;
      var conn := ABS2AS();
      var in1 := mf_a.state + mf_b.state;
      assert (|conn| == |out|);
      assert (forall x :: x in conn ==> x < |in1|);
      assert (forall index: nat :: index < |out| ==> conn[index] < |in1|);
      assert Seq.HasNoDuplicates(conn);
      assert (forall index: nat :: index < |out| ==> out[index] == in1[conn[index]]);
    }

    lemma ABS2BSCorrect()
      ensures
        ConnectionX(mf_a.state + mf_b.state, mf_b.state, ABS2BS()).Valid()
    {
      reveal Seq.HasNoDuplicates();
      reveal ConnectionX<CNode>.Valid();
      var out := mf_b.state;
      var conn := ABS2BS();
      var in1 := mf_a.state + mf_b.state;
      assert (|conn| == |out|);
      assert (forall x :: x in conn ==> x < |in1|);
      assert (forall index: nat :: index < |out| ==> conn[index] < |in1|);
      assert Seq.HasNoDuplicates(conn);
      assert (forall index: nat :: index < |out| ==>
        && out[index] == in1[conn[index]]);
    }

    lemma ASBS2ABSCorrect()
      requires Valid()
      ensures
        ConnectionXY(mf_a.state, mf_b.state, mf_a.state + mf_b.state, true, true, ASBS2ABS()).Valid()
    {
      reveal Seq.HasNoDuplicates();
      reveal ConnectionXY<NP>.Valid();
      var out := mf_a.state + mf_b.state;
      var conn := ASBS2ABS();
      var in1 := mf_a.state;
      var in2 := mf_b.state;
      var in1out_direct := true;
      var in2out_direct := true;
      assert (|conn| == |out|);
      assert (forall x :: x in conn && !x.0 ==> 0 <= x.1 < |in1|);
      assert (forall x :: x in conn &&  x.0 ==> 0 <= x.1 < |in2|);
      assert Seq.HasNoDuplicates(conn);
      assert
        && Seq.HasNoDuplicates(in1)
        && Seq.HasNoDuplicates(in2)
        && Seq.HasNoDuplicates(out)
      by {
        reveal MapFunction.Valid();
        SubSeqsNoDuplicates(mf_a.inputs, mf_a.outputs);
        SubSeqsNoDuplicates(mf_b.inputs, mf_b.outputs);
        NoDuplicatesInConcat(mf_a.state, mf_b.state);
      }
      assert (forall index: nat :: index < |conn| ==> (
            var (in_type, pos) := conn[index];
            && (!in_type && in1out_direct ==> out[index] == in1[conn[index].1])
            && ( in_type && in2out_direct ==> out[index] == in2[conn[index].1])
          ));
      forall index_out: nat, index1: nat, index2: nat | index_out < |out| && index1 < |in1| && index2 < |in2|
        ensures in1out_direct && out[index_out] == in1[index1] ==> (conn[index_out] == (false, index1))
        ensures in2out_direct && out[index_out] == in2[index2] ==> (conn[index_out] == (true, index2))
      {
        assert Seq.ToSet(in1) !! Seq.ToSet(in2);
        reveal Seq.ToSet();
        if in1out_direct && out[index_out] == in1[index1] {
          if index_out < |in1| {
            assert index_out == index1;
          } else {
            assert out[index_out] == in2[index_out-|in1|];
            assert in1[index1] == in2[index_out-|in1|];
            assert in1[index1] in Seq.ToSet(in1) && in1[index1] in Seq.ToSet(in2);
            assert false;
          }
        }
        if in2out_direct && out[index_out] == in2[index2] {
          if index_out >= |in1| {
            assert index_out-|in1| == index2;
          } else {
            assert out[index_out] == in1[index_out];
            assert out[index_out] in Seq.ToSet(in1);
            assert false;
          }
        }
      }
      assert (forall index_out: nat, index1: nat :: index_out < |out| && index1 < |in1| && in1out_direct
                && out[index_out] == in1[index1]
                ==> (conn[index_out] == (false, index1)));
      assert (forall index_out: nat, index2: nat :: index_out < |out| && index2 < |in2| && in2out_direct
                && out[index_out] == in2[index2]
                ==> (conn[index_out] == (true, index2)));
    }

    function ConnImpl(): (conn: MFConnection)
      requires Valid()
      ensures conn.SomewhatValid()
    {
      ABI2AICorrect();
      ABIAO2BICorrect();
      AOBO2ABOCorrect();
      ABS2ASCorrect();
      ABS2BSCorrect();
      ASBS2ABSCorrect();
      MakeConnections(mf_a, mf_b, mf(), ABI2AI(), ABIAO2BI(), AOBO2ABO(), ABS2AS(), ABS2BS(), ASBS2ABS())
    }

    lemma ConnCorrect()
      requires Valid()
      ensures ConnImpl().Valid()
    {
      var conn := ConnImpl();
      assert conn.SomewhatValid();
      reveal Seq.ToSet();
      assert (Seq.ToSet(conn.mf_ab.state) == Seq.ToSet(conn.mf_a.state) + Seq.ToSet(conn.mf_b.state));
      assert (Seq.ToSet(conn.mf_ab.inputs) == Seq.ToSet(conn.mf_a.inputs) + (Seq.ToSet(conn.mf_b.inputs) - conn.GetConnection().Keys));
      assert (Seq.ToSet(conn.mf_ab.outputs) <= Seq.ToSet(conn.mf_a.outputs) + Seq.ToSet(conn.mf_b.outputs));
      assert conn.ABValid();
      forall si: SI | SIValid(si, conn.mf_ab.inputs, conn.mf_ab.state)
        ensures conn.SeqEvaluateSeparately(si) == conn.mf_ab.sf(si)
      {
        // By SeqEvaluateSeperately
        var si1_a := conn.si2sia(si);
        var si1_b := conn.si2sib(si);
        reveal MapFunction.Valid();
        var so1_a := conn.mf_a.sf(si1_a);
        var so1_b := conn.mf_b.sf(si1_b);
        var so1 := conn.soasob2so(so1_a, so1_b);
        // By mf_ab
        var si2_a := SI(si.inputs[..|mf_a.inputs|], si.state[..|mf_a.state|]);
        var si2_b := SI(si.inputs[|mf_a.inputs|..], si.state[|mf_a.state|..]);
        var so2_a := mf_a.sf(si2_a);
        var so2_b := mf_b.sf(si2_b);
        var so2 := SO(so2_a.outputs + so2_b.outputs, so2_a.state + so2_b.state);
        // Comparison
        assert si1_a == si2_a;
        assert si1_b == si2_b;
        assert so1_a == so2_a;
        assert so1_b == so2_b;
        assert so1 == so2;

        assert so1 == conn.SeqEvaluateSeparately(si);
        assert so2 == conn.mf_ab.sf(si);

        assert conn.SeqEvaluateSeparately(si) == conn.mf_ab.sf(si);
      }
      reveal conn.SeqEvaluatesCorrectly();
      assert conn.SeqEvaluatesCorrectly();
    }

    function Conn(): (conn: MFConnection)
      requires Valid()
      ensures conn.Valid()
    {
      ConnCorrect();
      ConnImpl()
    }

    lemma ConnectionEmpty()
      requires Valid()
      ensures Conn().GetConnection() == map[]
    {
      var conn := Conn();
      var connection := conn.GetConnection();
      assert connection.Keys == Seq.ToSet(conn.mf_b.inputs) - Seq.ToSet(conn.mf_ab.inputs);
      reveal Seq.ToSet();
    }

  }

  ghost predicate CombineParallelEntitiesRequirements(c: Circuit, e1: Entity, e2: Entity) {
    && CircuitValid(c)
    && EntityValid(c, e1)
    && EntityValid(c, e2)
    && e1.sc !! e2.sc
    && IsIsland(c, e1.sc)
    && IsIsland(c, e2.sc)
  }

  function CombineParallelEntityConn(c: Circuit, e1: Entity, e2: Entity): (r: (Entity, MFConnection))
    requires CombineParallelEntitiesRequirements(c, e1, e2)
    ensures ConnectEntitiesRequirements(c, e1, e2, r.0, r.1)
  {
    var combiner := ParallelCombiner(e1.mf, e2.mf);
    assert Seq.ToSet(e1.mf.state) !! Seq.ToSet(e2.mf.state) by {
      StateInSc(c, e1);
      StateInSc(c, e2);
    }
    assert e1.mf.NPs() !! e2.mf.NPs() by {
      FAllInSc(c, e1);
      FAllInSc(c, e2);
      assert e1.sc !! e2.sc;
      ScNoIntersectionNPsNoIntersection(e1.sc, e2.sc, e1.mf.NPs(), e2.mf.NPs());
    }
    var conn := combiner.Conn();
    assert conn.Valid();
    var e12 := Entity(e1.sc + e2.sc, combiner.mf());
    assert conn.mf_a == e1.mf;
    assert conn.mf_b == e2.mf;
    assert conn.mf_ab == e12.mf;
    combiner.ConnectionEmpty();
    assert conn.GetConnection().Keys !! c.PortSource.Keys;
    (e12, conn)
  }
}
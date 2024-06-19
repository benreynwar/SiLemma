module Modifiers.Merge {
  
  import opened Circ
  import opened Scuf
  import opened MapFunction
  import opened ConservedSubcircuit
  import opened Subcircuit
  import opened Utils
  import opened Eval

  predicate ScufMapsCanMerge(mp1: ScufMap, mp2: ScufMap)
  {
    && SeqsNoIntersection(mp1.inputs, mp2.inputs)
    && SeqsNoIntersection(mp1.outputs, mp2.outputs)
    && SeqsNoIntersection(mp1.inputs, mp2.outputs)
    && SeqsNoIntersection(mp1.outputs, mp2.inputs)
    && SeqsNoIntersection(mp1.state, mp2.state)
    && SeqsNoIntersection(mp1.inputs, StateONPsSeq(mp2.state))
    && SeqsNoIntersection(mp2.inputs, StateONPsSeq(mp1.state))
    && SeqsNoIntersection(mp1.outputs, StateINPsSeq(mp2.state))
    && SeqsNoIntersection(mp2.outputs, StateINPsSeq(mp1.state))
  }

  function MergeScufMaps(mp1: ScufMap, mp2: ScufMap): (mp: ScufMap)
    requires mp1.Valid()
    requires mp2.Valid()
    requires ScufMapsCanMerge(mp1, mp2)
    ensures mp.Valid()
  {
    var inputs := mp1.inputs + mp2.inputs;
    var outputs := mp1.outputs + mp2.outputs;
    var state := mp1.state + mp2.state;
    assert Seq.HasNoDuplicates(inputs) by {
      NoDuplicatesInConcat(mp1.inputs, mp2.inputs);
    }
    assert Seq.HasNoDuplicates(outputs) by {
      NoDuplicatesInConcat(mp1.outputs, mp2.outputs);
    }
    assert Seq.HasNoDuplicates(state) by {
      NoDuplicatesInConcat(mp1.state, mp2.state);
    }
    assert SeqsNoIntersection(inputs, outputs) by {
      ConcatSeqsNoIntersection(mp1.inputs, mp2.inputs, mp1.outputs, mp2.outputs);
    }
    assert SeqsNoIntersection(inputs, StateONPsSeq(state)) by {
      ConcatSeqsNoIntersection(mp1.inputs, mp2.inputs, StateONPsSeq(mp1.state), StateONPsSeq(mp2.state));
      assert StateONPsSeq(state) == StateONPsSeq(mp1.state) + StateONPsSeq(mp2.state);
    }
    assert SeqsNoIntersection(outputs, StateINPsSeq(state)) by {
      ConcatSeqsNoIntersection(mp1.outputs, mp2.outputs, StateINPsSeq(mp1.state), StateINPsSeq(mp2.state));
      assert StateINPsSeq(state) == StateINPsSeq(mp1.state) + StateINPsSeq(mp2.state);
    }
    ScufMap(inputs, outputs, state)
  }

  function MergeSF(uf1: UpdateFunction, uf2: UpdateFunction, si: SI): (so: SO)
    requires uf1.Valid()
    requires uf2.Valid()
    requires |si.inputs| == uf1.input_width + uf2.input_width
    requires |si.state| == uf1.state_width + uf2.state_width
    ensures |so.outputs| == uf1.output_width + uf2.output_width
    ensures |so.state| == uf1.state_width + uf2.state_width
  {
    var si1 := SI(si.inputs[..uf1.input_width], si.state[..uf1.state_width]);
    var si2 := SI(si.inputs[uf1.input_width..], si.state[uf1.state_width..]);
    var so1 := uf1.sf(si1);
    var so2 := uf1.sf(si2);
    var so := SO(so1.outputs + so2.outputs, so1.state + so2.state);
    so
  }

  function MergeUpdateFunctions(uf1: UpdateFunction, uf2: UpdateFunction): (uf: UpdateFunction)
    requires uf1.Valid()
    requires uf2.Valid()
    ensures uf.Valid()
  {
    var input_width := uf1.input_width + uf2.input_width;
    var output_width := uf1.output_width + uf2.output_width;
    var state_width := uf1.state_width + uf2.state_width;
    UpdateFunction(
      input_width, output_width, state_width,
      (si: SI) requires |si.inputs| == input_width && |si.state| == state_width => MergeSF(uf1, uf2, si)
    )
  }

  lemma ScufsNoIntersectionMapsCanMerge(c: Circuit, s1: Scuf, s2: Scuf)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires s1.sc !! s2.sc
    ensures ScufMapsCanMerge(s1.mp, s2.mp)
  {
  }

  lemma IslandScufsAllInputsAdd(c: Circuit, s1: Scuf, s2:Scuf)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires s1.sc !! s2.sc
    requires IsIsland(c, s1.sc)
    requires IsIsland(c, s2.sc)
    ensures
      reveal ScValid();
      AllInputs(c, s1.sc + s2.sc) == AllInputs(c, s1.sc) + AllInputs(c, s2.sc)
  {
  }

  lemma MergeEvaluatesCorrectly(c: Circuit, s1: Scuf, s2: Scuf, np: NP, fi: FI)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires s1.sc !! s2.sc
    requires IsIsland(c, s1.sc)
    requires IsIsland(c, s2.sc)
    requires np in s1.mp.outputs || np in s2.mp.outputs ||
             np in StateINPs(s1.mp.state) || np in StateINPs(s2.mp.state)
    requires FICircuitValid(c, fi)
    ensures
      var s := MergeScufsImpl(c, s1, s2);
      Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np))
  {
  }

  function MergeScufsImpl(c: Circuit, s1: Scuf, s2: Scuf): (s: Scuf)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires s1.sc !! s2.sc
    requires IsIsland(c, s1.sc)
    requires IsIsland(c, s2.sc)
  {
    var sc := s1.sc + s2.sc;
    assert ScufMapsCanMerge(s1.mp, s2.mp) by {
      ScufsNoIntersectionMapsCanMerge(c, s1, s2);
    }
    var mp := MergeScufMaps(s1.mp, s2.mp);
    var uf := MergeUpdateFunctions(s1.uf, s2.uf);
    var s := Scuf(sc, mp, uf);
    s
  }

  function MergeScufs(c: Circuit, s1: Scuf, s2: Scuf): (s: Scuf)
    requires c.Valid()
    requires s1.Valid(c)
    requires s2.Valid(c)
    requires s1.sc !! s2.sc
    requires IsIsland(c, s1.sc)
    requires IsIsland(c, s2.sc)
    ensures s.Valid(c)
  {
    var s := MergeScufsImpl(c, s1, s2);
    var mp := s.mp;
    var uf := s.uf;
    var sc := s.sc;
    assert s.Valid(c) by {
      assert s.MapValid() by {
        assert mp.Valid();
        assert mp.InSc(sc) by {
          reveal NPsInSc();
          reveal Seq.ToSet();
        }
        assert uf.Valid();
        assert ScufMapUpdateFunctionConsistent(mp, uf);
      }
      assert ScValid(c, s.sc) by {
        reveal ScValid();
      }
      assert s.SomewhatValid(c) by {
        assert ScValid(c, sc);
        reveal Seq.ToSet();
        reveal AllONPs();
        reveal ConnOutputs();
        reveal ConnInputs();
        reveal UnconnInputs();
        reveal AllSeq();
        reveal ScValid();
        reveal Scuf.SomewhatValid();
        assert (AllONPs(c, sc) >= Seq.ToSet(mp.outputs) >= ConnOutputs(c, sc)) by {
          assert AllONPs(c, sc) == AllONPs(c, s1.sc) + AllONPs(c, s2.sc);
          assert Seq.ToSet(mp.outputs) == Seq.ToSet(s1.mp.outputs) + Seq.ToSet(s2.mp.outputs);
          assert ConnOutputs(c, sc) <= ConnOutputs(c, s1.sc) + ConnOutputs(c, s2.sc);
          assert AllONPs(c, sc) >= Seq.ToSet(mp.outputs);
          assert Seq.ToSet(mp.outputs) >= ConnOutputs(c, sc);
        }
        assert (Seq.ToSet(mp.inputs) == AllInputs(c, sc)) by {
          assert Seq.ToSet(mp.inputs) == Seq.ToSet(s1.mp.inputs) + Seq.ToSet(s2.mp.inputs);
          IslandScufsAllInputsAdd(c, s1, s2);
          assert AllInputs(c, sc) == AllInputs(c, s1.sc) + AllInputs(c, s2.sc);
        }
        assert (Seq.ToSet(mp.state) == AllSeq(c, sc)) by {
          assert Seq.ToSet(mp.state) == Seq.ToSet(s1.mp.state) + Seq.ToSet(s2.mp.state);
          assert AllSeq(c, sc) == AllSeq(c, s1.sc) + AllSeq(c, s2.sc);
        }
      }
      assert s.EvaluatesCorrectly(c) by {
        reveal Seq.ToSet();
        forall np | np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state)
          ensures ONPValid(c, np) || INPValid(c, np)
        {
          ScufFInputsAreValid(c, s);
          ScufFOutputsAreValid(c, s);
        }
        forall fi: FI | FIValid(fi, s.mp.inputs, s.mp.state)
          ensures FICircuitValid(c, fi)
          ensures forall np :: np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state) ==>
            Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np))
        {
          assert FICircuitValid(c, fi) by {ScufValidFiValidToFICircuitValid(c, s, fi);}
          forall np | np in Seq.ToSet(s.mp.outputs) || np in StateINPs(s.mp.state)
            ensures Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np))
          {
            MergeEvaluatesCorrectly(c, s1, s2, np, fi);
            assert Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np));
          }
        }
        reveal Scuf.EvaluatesCorrectly();
      }
    }
    s
  }

  function MergeInserter(c: Circuit, z1: ScufInserter, z2: ScufInserter): (r: (Circuit, Scuf))
    requires c.Valid()
    requires z1.Valid()
    requires z2.Valid()
  {
    var (new_c, s1, s2) := InsertTwo(c, z1, z2);
    reveal DualInsertion();
    var s := MergeScufs(new_c, s1, s2);
    (new_c, s)
  }

  function MergeModifier(z1: ScufInserter, z2: ScufInserter): (r: ScufInserter)
    requires z1.Valid()
    requires z2.Valid()
  {
    reveal ScufInserter.Valid();
    var uf := MergeUpdateFunctions(z1.uf, z2.uf);
    ScufInserter(
      uf,
      (c: Circuit) requires c.Valid() => MergeInserter(c, z1, z2)
    )
  }

}
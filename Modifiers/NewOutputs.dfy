module Modifiers.NewOutputs {

  import opened Circ
  import opened Scuf
  import opened MapFunction
  import opened Subcircuit
  import opened ConservedSubcircuit
  import opened Utils
  import opened Eval

  function NewOutputsMap(mp: ScufMap, new_outputs: seq<nat>): (r: ScufMap)
    requires mp.Valid()
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < |mp.outputs|
    requires Seq.HasNoDuplicates(new_outputs)
    ensures r.Valid()
  {
    var mapped_outputs := seq(|new_outputs|, (i: nat) requires i < |new_outputs| =>
      mp.outputs[new_outputs[i]]);
    reveal Seq.HasNoDuplicates();
    reveal Seq.ToSet();
    ScufMap(mp.inputs, mapped_outputs, mp.state)
  }

  function NewOutputsSF(uf: UpdateFunction, new_outputs: seq<nat>, si: SI): (r: SO)
    requires uf.Valid()
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < uf.output_width
    requires uf.SIVal(si)
    requires Seq.HasNoDuplicates(new_outputs)
  {
    reveal UpdateFunction.Valid();
    var so := uf.sf(si);
    var mapped_so_outputs := seq(|new_outputs|, (i: nat) requires i < |new_outputs| => so.outputs[new_outputs[i]]);
    SO(mapped_so_outputs, so.state)
  }

  opaque function NewOutputsUpdateFunction(uf: UpdateFunction, new_outputs: seq<nat>): (r: UpdateFunction)
    requires uf.Valid()
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < uf.output_width
    requires Seq.HasNoDuplicates(new_outputs)
    ensures r.Valid()
    ensures r.input_width == uf.input_width
    ensures r.state_width == uf.state_width
    ensures r.output_width == |new_outputs|
  {
    var new_sf := (si: SI) requires uf.SIVal(si) => NewOutputsSF(uf, new_outputs, si);
    reveal UpdateFunction.Valid();
    UpdateFunction(uf.input_width, |new_outputs|, uf.state_width, new_sf)
  }

  lemma MFLookupCorrect(c: Circuit, s: Scuf, new_outputs: seq<nat>, np: NP, fi: FI)
    requires c.Valid()
    requires s.Valid(c)
    requires IsIsland(c, s.sc)
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < s.uf.output_width
    requires Seq.HasNoDuplicates(new_outputs)
    requires
      FIValid(fi, s.mp.inputs, s.mp.state)
    requires
      var new_mp := NewOutputsMap(s.mp, new_outputs);
      np in new_mp.outputs
    ensures
      var new_s := NewOutputsScufImpl(c, s, new_outputs);
      MFLookupOutput(s, fi, np) == MFLookupOutput(new_s, fi, np)
  {
    var new_s := NewOutputsScufImpl(c, s, new_outputs);
    var si := s.mp.fi2si(fi);
    var new_si := new_s.mp.fi2si(fi);
    reveal UpdateFunction.Valid();
    reveal NewOutputsUpdateFunction();
    var so := s.uf.sf(si);
    var new_so := new_s.uf.sf(new_si);
    assert so.state == new_so.state;
    assert new_so.outputs == seq(|new_outputs|, (i: nat) requires i < |new_outputs| => so.outputs[new_outputs[i]]);
    var fo := s.mp.so2fo(so);
    var new_fo := new_s.mp.so2fo(new_so);
    var index := Seq.IndexOf(new_s.mp.outputs, np);
    reveal SeqsToMap();
    assert FOValid(new_fo, new_s.mp.outputs, new_s.mp.state);
    reveal Seq.ToSet();
    assert np in new_fo.outputs;
    reveal MapMatchesSeqs();
    assert new_fo.outputs[np] == new_so.outputs[index];
    assert fo.outputs[np] == new_fo.outputs[np];
  }

  function NewOutputsScufImpl(c: Circuit, s: Scuf, new_outputs: seq<nat>): (r: Scuf)
    requires c.Valid()
    requires s.Valid(c)
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < s.uf.output_width
    requires Seq.HasNoDuplicates(new_outputs)
    ensures r.MapValid()
  {
    var new_mp := NewOutputsMap(s.mp, new_outputs);
    var new_uf := NewOutputsUpdateFunction(s.uf, new_outputs);
    var new_s := Scuf(s.sc, new_mp, new_uf);
    assert new_s.MapValid() by {
      reveal NPsInSc();
      reveal Seq.ToSet();
      assert new_s.mp.Valid();
      assert new_s.mp.InSc(new_s.sc);
      assert new_s.uf.Valid();
      reveal NewOutputsUpdateFunction();
      assert ScufMapUpdateFunctionConsistent(new_s.mp, new_s.uf);
    }
    new_s
  }

  function NewOutputsScuf(c: Circuit, s: Scuf, new_outputs: seq<nat>): (r: Scuf)
    requires c.Valid()
    requires s.Valid(c)
    requires IsIsland(c, s.sc)
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < s.uf.output_width
    requires Seq.HasNoDuplicates(new_outputs)
    ensures r.Valid(c)
  {
    var new_s := NewOutputsScufImpl(c, s, new_outputs);
    assert new_s.Valid(c) by {
      assert ScValid(c, new_s.sc);
      reveal Scuf.SomewhatValid();
      assert new_s.SomewhatValid(c) by {
        reveal Scuf.SomewhatValid();
        reveal ConnOutputs();
        assert ScValid(c, new_s.sc);
        assert |ConnOutputs(c, new_s.sc)| == 0 by {
          IsIslandNoOutputs(c, new_s.sc);
        }
        reveal  Seq.ToSet();
        assert Seq.ToSet(new_s.mp.outputs) <= Seq.ToSet(s.mp.outputs);
        assert AllONPs(c, new_s.sc) >= Seq.ToSet(new_s.mp.outputs);
        assert Seq.ToSet(new_s.mp.outputs) >= ConnOutputs(c, new_s.sc);
        assert (Seq.ToSet(new_s.mp.state) == AllSeq(c, new_s.sc));
        assert (Seq.ToSet(new_s.mp.inputs) == AllInputs(c, new_s.sc));
      }
      reveal Scuf.EvaluatesCorrectly();
      assert new_s.EvaluatesCorrectly(c) by {
        reveal Seq.ToSet();
        forall fi: FI | FIValid(fi, new_s.mp.inputs, new_s.mp.state)
          ensures
          && FICircuitValid(c, fi)
          && (forall np :: np in Seq.ToSet(new_s.mp.outputs) || np in StateINPs(new_s.mp.state) ==>
            && NPValid(c, np)
            && (Evaluate(c, np, fi) == EvalOk(MFLookup(new_s, fi, np))))
        {
          assert FICircuitValid(c, fi) by {
            ScufValidFiValidToFICircuitValid(c, new_s, fi);
            }
          forall np | np in Seq.ToSet(new_s.mp.outputs) || np in StateINPs(new_s.mp.state)
            ensures
              && NPValid(c, np)
              && (Evaluate(c, np, fi) == EvalOk(MFLookup(new_s, fi, np)))
          {
            assert s.EvaluatesCorrectly(c);
            reveal Seq.ToSet();
            ScufFOutputsAreValid(c, s);
            assert Evaluate(c, np, fi) == EvalOk(MFLookup(s, fi, np));
            if np in StateINPs(new_s.mp.state) {
              reveal NewOutputsUpdateFunction();
              assert Evaluate(c, np, fi) == EvalOk(MFLookup(new_s, fi, np));
            } else {
              MFLookupCorrect(c, s, new_outputs, np, fi);
              assert MFLookupOutput(s, fi, np) == MFLookupOutput(new_s, fi, np) by {
              }
              assert Evaluate(c, np, fi) == EvalOk(MFLookup(new_s, fi, np));
            }
          }
        }
      }
    }
    new_s
  }

  function NewOutputsInserter(c: Circuit, z: ScufInserter, new_outputs: seq<nat>): (r: (Circuit, Scuf))
    requires c.Valid()
    requires z.Valid()
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < z.uf.output_width
    requires Seq.HasNoDuplicates(new_outputs)
    ensures
      var (new_c, new_s) := r;
      && new_c.Valid()
      && new_s.Valid(new_c)
      && SimpleInsertion(c, new_c, new_s)
  {
    reveal UpdateFunctionsEquiv();
    reveal ScufInserter.Valid();
    var (new_c, s) := z.fn(c);
    reveal SimpleInsertion();
    var new_s := NewOutputsScuf(new_c, s, new_outputs);
    (new_c, new_s)
  }

  opaque function NewOutputsModifier(z: ScufInserter, new_outputs: seq<nat>): (r: ScufInserter)
    requires z.Valid()
    requires forall i: nat :: i < |new_outputs| ==> new_outputs[i] < z.uf.output_width
    requires Seq.HasNoDuplicates(new_outputs)
    ensures r.Valid()
    ensures
      && z.uf.Valid()
      && (r.uf == NewOutputsUpdateFunction(z.uf, new_outputs))
  {
    reveal ScufInserter.Valid();
    var new_uf := NewOutputsUpdateFunction(z.uf, new_outputs);
    var new_z := ScufInserter(
      new_uf,
      (c: Circuit) requires c.Valid() => NewOutputsInserter(c, z, new_outputs)
    );
    new_z
  }


}
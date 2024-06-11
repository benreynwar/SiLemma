module Build.RegBuilder {

  import opened MapFunction
  import opened Circ
  import opened Entity
  import opened CombineManyParallel
  import opened SeqBuilder
  import opened ConservedSubcircuit

  function RegSF(n: nat, si: SI): (so: SO)
    requires |si.inputs| == n
    requires |si.state| == n
  {
    SO(si.state, si.inputs)
  }

  lemma RegSFIsManyParallelSeqSF(n: nat, si: SI)
    requires |si.inputs| == n
    requires |si.state| == n
    ensures
      RegSF(n, si) == ManyParallelSF(SeqRF(), n, si)
  {
  }

  function InsertRegMF(old_mf: MapFunction, n: nat): (mf: MapFunction)
    requires |old_mf.inputs| == n
    requires |old_mf.state| == n
    requires |old_mf.outputs| == n
    requires old_mf.Valid()
    requires MFIsParallelCopies(old_mf, SeqRF(), n)
    ensures mf.Valid()
    ensures MapFunctionsEquiv(old_mf, mf)
  {
    var mf := MapFunction(
      old_mf.inputs, old_mf.outputs, old_mf.state,
      (si: SI) requires SIValid(si, old_mf.inputs, old_mf.state) =>
      RegSF(n, si));
    assert mf.Valid() by {
      reveal MapFunction.Valid();
      reveal EntityInserter.Valid();
      reveal MFIsParallelCopies();
    }
    assert MapFunctionsSFEquiv(old_mf, mf) by {
      reveal EntityInserter.Valid();
      reveal MapFunction.Valid();
      forall si: SI | SIValid(si, old_mf.inputs, old_mf.state)
        ensures old_mf.sf(si) == mf.sf(si)
      {
        reveal MFIsParallelCopies();
        reveal EntityInserter.Valid();
        RegSFIsManyParallelSeqSF(n, si);
      }
      reveal MapFunctionsSFEquiv();
    }
    MapFunctionsEquivSFEquiv(old_mf, mf);
    mf
  }

  function InsertReg(c: Circuit, n: nat): (r: (Circuit, Entity))
    requires CircuitValid(c)
    ensures SimpleInsertion(c, r.0, r.1)
  {
    var inserter := SeqInserter();
    var (new_c, e) := InsertInParallel(c, inserter, n);
    assert |e.mf.inputs| == n && |e.mf.state| == n && |e.mf.outputs| == n by {
      reveal EntityInserter.Valid();
      reveal MFIsParallelCopies();
    }
    var mf := InsertRegMF(e.mf, n);
    var new_e := EntitySwapMF(new_c, e, mf);
    StillSimpleInsertionAfterEntitySwapMF(c, new_c, e, mf);
    (new_c, new_e)
  }

}
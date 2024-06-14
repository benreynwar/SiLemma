module Inserters.Reg {

  import opened MapFunction
  import opened Circ
  import opened Entity
  import opened CombineManyParallel
  import opened ConservedSubcircuit

  import opened Seq

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
    ensures RegRF(n).MFConsistent(mf)
  {
    var mf := MapFunction(
      old_mf.inputs, old_mf.outputs, old_mf.state,
      (si: SI) requires SIValid(si, old_mf.inputs, old_mf.state) =>
      RegSF(n, si));
    assert RegRF(n).MFConsistent(mf) by {
      reveal RFunction.MFConsistent();
      reveal MapFunction.Valid();
    }
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
    ensures RegRF(n).MFConsistent(r.1.mf)
    ensures SimpleInsertion(c, r.0, r.1)
  {
    reveal SimpleInsertion();
    var inserter := SeqInserter();
    var (new_c, e) := InsertInParallel(c, inserter, n);
    assert |e.mf.inputs| == n && |e.mf.state| == n && |e.mf.outputs| == n by {
      reveal EntityInserter.Valid();
      reveal MFIsParallelCopies();
    }
    var mf := InsertRegMF(e.mf, n);
    var new_e := EntitySwapMF(new_c, e, mf);
    StillSimpleInsertionAfterEntitySwapMF(c, new_c, e, mf);
    reveal RFunction.MFConsistent();
    (new_c, new_e)
  }


  function RegRF(n: nat): (r: RFunction)
    ensures r.Valid()
  {
    reveal RFunction.Valid();
    RFunction(n, n, n, (si: SI) requires |si.inputs| == n && |si.state| == n => RegSF(n, si))
  }

  function RegInserter(n: nat): (r: EntityInserter)
    ensures r.Valid()
  {
    reveal RFunction.Valid();
    reveal EntityInserter.Valid();
    var rf := RegRF(n);
    var ei := EntityInserter(RegRF(n), (c: Circuit) requires CircuitValid(c) => InsertReg(c, n));
    assert ei.Valid() by {
      assert rf.Valid();
      forall c: Circuit | CircuitValid(c)
        ensures ei.SpecificValid(c)
      {
        assert ei.fn.requires(c);
        var (new_c, e) := ei.fn(c);
        assert ei.rf.MFConsistent(e.mf);
        assert SimpleInsertion(c, new_c, e);
      }
    }
    EntityInserter(RegRF(n), (c: Circuit) requires CircuitValid(c) => InsertReg(c, n))
  }

}
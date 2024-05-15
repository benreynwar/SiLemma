module Entity {

  import opened Subcircuit
  import opened Circ
  import opened Eval
  import opened Utils
  import opened MapFunction

  datatype Entity = Entity(
    sc: set<CNode>,
    mf: MapFunction
  )

  opaque predicate EntitySomewhatValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
  {
    && ScValid(c, e.sc)
    && (AllONPs(c, e.sc) >= e.mf.outputs >= ConnOutputs(c, e.sc))
    && (e.mf.inputs == AllInputs(c, e.sc))
    && (e.mf.state == AllSeq(c, e.sc))
  }

  lemma EntityFInputsAreValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures forall np :: np in e.mf.inputs ==> NPValid(c, np)
    ensures forall np :: np in StateONPs(e.mf.state) ==> NPValid(c, np)
  {
    reveal ScValid();
    reveal EntitySomewhatValid();
    reveal NPsValid();
  }

  lemma EntityFOutputsAreValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures forall np :: np in e.mf.outputs ==> NPValid(c, np)
    ensures forall np :: np in StateINPs(e.mf.state) ==> NPValid(c, np)
  {
    reveal ScValid();
    reveal EntitySomewhatValid();
    reveal NPsValid();
    assert e.mf.outputs <= AllONPs(c, e.sc);
    reveal ONPsValid();
    reveal AllSeq();
  }

  ghost opaque predicate EntityEvaluatesCorrectly(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires ScValid(c, e.sc)
    requires MapFunctionValid(e.mf)
    requires EntitySomewhatValid(c, e)
  {
    reveal ScValid();
    EntityFOutputsAreValid(c, e);
    reveal MapFunctionValid();
    forall fi: FI :: FIValid(fi, e.mf.inputs, e.mf.state) ==> (
      && (forall np :: np in e.mf.outputs ==>
          Evaluate(c, np, fi) == EvalOk(e.mf.f(fi).outputs[np]))
      && (forall np :: np in StateINPs(e.mf.state) ==>
          Evaluate(c, np, fi) == EvalOk(e.mf.f(fi).state[np]))
      )
  }

  ghost predicate EntityValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
  {
    && EntitySomewhatValid(c, e)
    && MapFunctionValid(e.mf)
    && ScValid(c, e.sc)
    && EntityEvaluatesCorrectly(c, e)
  }

  lemma FInputsInSc(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures NPsInSc(e.sc, e.mf.inputs)
    ensures NPsInSc(e.sc, StateONPs(e.mf.state))
  {
    reveal EntitySomewhatValid();
    reveal NPsInSc();
    reveal AllSeq();
  }

  lemma FOutputsInSc(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures NPsInSc(e.sc, e.mf.outputs)
    ensures NPsInSc(e.sc, StateINPs(e.mf.state))
  {
    reveal NPsInSc();
    reveal EntitySomewhatValid();
    reveal AllSeq();
    assert AllONPs(c, e.sc) >= e.mf.outputs;
  }

  lemma StaysInSc(c: Circuit, e: Entity, np: NP)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    requires INPValid(c, np)
    requires np.n in e.sc
    requires np !in e.mf.inputs
    ensures np in c.PortSource
    ensures c.PortSource[np].n in e.sc
  {
    reveal CircuitValid();
    reveal EntitySomewhatValid();
    reveal UnconnInputs();
    reveal ConnInputs();
  }

  predicate OutputsInFOutputs(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires ScValid(c, e.sc)
  {
    e.mf.outputs >= ConnOutputs(c, e.sc)
  }

  function SwapEntityF(c: Circuit, e: Entity, mf: MapFunction): (r: Entity)
    requires CircuitValid(c)
    requires EntityValid(c, e)
    requires mf.inputs == e.mf.inputs
    requires mf.outputs == e.mf.outputs
    requires mf.state == e.mf.state
    requires MapFunctionValid(mf)
    requires MapFunctionsEquiv(e.mf, mf)
    ensures EntityValid(c, r)
  {
    reveal EntitySomewhatValid();
    reveal MapFunctionValid();
    reveal ScValid();
    reveal EntityEvaluatesCorrectly();
    Entity(e.sc, mf)
  }

  lemma NPInFInputsOfIslandNotInPortSource(c: Circuit, e: Entity, np: NP) 
    requires CircuitValid(c)
    requires IsIsland(c, e.sc)
    requires EntityValid(c, e)
    requires np in e.mf.inputs
    ensures np !in c.PortSource
  {
    assert np in AllInputs(c, e.sc) by {
      reveal EntitySomewhatValid();
    }
    assert |ConnInputs(c, e.sc)| == 0 by {
      IsIslandNoInputs(c, e.sc);
    }
    assert np in UnconnInputs(c, e.sc) || np in SeqInputs(c, e.sc);
    if np in UnconnInputs(c, e.sc) {
      assert np !in c.PortSource by {
        reveal UnconnInputs();
      }
    }
    if np in SeqInputs(c, e.sc) {
      reveal ONPsValid();
      assert ONPValid(c, np) by {
        reveal SeqInputs();
      }
    }
  }

}
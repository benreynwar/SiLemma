module Entity {

  import opened Subcircuit
  import opened Circ
  import opened Eval
  import opened Utils
  import opened MapFunction

  datatype Entity = Entity(
    sc: set<CNode>,
    finputs: set<NP>,
    foutputs: set<NP>,
    f: map<NP, bool> --> map<NP, bool>
  )

  opaque predicate EntitySomewhatValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
  {
    && ScValid(c, e.sc)
    && (AllPossibleOutputs(c, e.sc) >= e.foutputs >= AllOutputs(c, e.sc))
    && (e.finputs == AllInputs(c, e.sc))
  }

  lemma EntityFInputsAreValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures forall np :: np in e.finputs ==> NPValid(c, np)
  {
    reveal ScValid();
    reveal EntitySomewhatValid();
    reveal NPsValid();
  }

  lemma EntityFOutputsAreValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures forall np :: np in e.foutputs ==> NPValid(c, np)
  {
    reveal ScValid();
    reveal EntitySomewhatValid();
    reveal NPsValid();
  }

  ghost opaque predicate EntityFValid(c: Circuit, e: Entity)
  {
    forall knowns: map<NP, bool> :: knowns.Keys == e.finputs ==>
      && e.f.requires(knowns)
      && (e.f(knowns).Keys == e.foutputs)
  }

  ghost opaque predicate EntityEvaluatesCorrectly(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires ScValid(c, e.sc)
    requires EntityFValid(c, e)
    requires EntitySomewhatValid(c, e)
  {
    reveal ScValid();
    EntityFOutputsAreValid(c, e);
    reveal EntityFValid();
    forall knowns: map<NP, bool> :: knowns.Keys == e.finputs ==>
      forall np :: np in e.foutputs ==>
        && Evaluate(c, np, knowns) == EvalOk(e.f(knowns)[np])
  }

  ghost predicate EntityValid(c: Circuit, e: Entity)
    requires CircuitValid(c)
  {
    && EntitySomewhatValid(c, e)
    && EntityFValid(c, e)
    && ScValid(c, e.sc)
    && EntityEvaluatesCorrectly(c, e)
  }

  lemma FInputsInSc(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures NPsInSc(e.sc, e.finputs)
  {
    reveal EntitySomewhatValid();
    reveal NPsInSc();
  }

  lemma FOutputsInSc(c: Circuit, e: Entity)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    ensures NPsInSc(e.sc, e.foutputs)
  {
    reveal NPsInSc();
    reveal EntitySomewhatValid();
    assert AllPossibleOutputs(c, e.sc) >= e.foutputs;
  }

  lemma StaysInSc(c: Circuit, e: Entity, np: NP)
    requires CircuitValid(c)
    requires EntitySomewhatValid(c, e)
    requires INPValid(c, np)
    requires np.n in e.sc
    requires np !in e.finputs
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
    e.foutputs >= ConnOutputs(c, e.sc)
  }

  function SwapEntityF(c: Circuit, e: Entity, f: map<NP, bool> --> map<NP, bool>): (r: Entity)
    requires EntityValid(c, e)
    requires MapFunctionValid(MapFunction(e.finputs, e.foutputs, f))
    ensures EntityValid(c, r)
  {
    reveal EntitySomewhatValid();
    reveal EntityFValid();
    reveal ScValid();
    reveal EntityEvaluatesCorrectly();
    Entity(e.sc, e.finputs, e.foutputs, f)
  }

  lemma NPInFInputsOfIslandNotInPortSource(c: Circuit, e: Entity, np: NP) 
    requires CircuitValid(c)
    requires IsIsland(c, e.sc)
    requires EntityValid(c, e)
    requires np in e.finputs
    ensures np !in c.PortSource
  {
    assert np in AllInputs(c, e.sc) by {
      reveal EntitySomewhatValid();
    }
    assert |ConnInputs(c, e.sc)| == 0 by {
      IsIslandNoInputs(c, e.sc);
    }
    assert np in UnconnInputs(c, e.sc) || np in FinalInputs(c, e.sc) || np in SeqInputs(c, e.sc);
    if np in UnconnInputs(c, e.sc) {
      assert np !in c.PortSource by {
        reveal UnconnInputs();
      }
    }
    if np in FinalInputs(c, e.sc) {
      assert ONPValid(c, np) by {
        reveal FinalInputs();
      }
    }
    if np in SeqInputs(c, e.sc) {
      assert ONPValid(c, np) by {
        reveal SeqInputs();
      }
    }
  }

}
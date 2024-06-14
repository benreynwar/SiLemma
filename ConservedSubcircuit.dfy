module ConservedSubcircuit {

  import opened Circ
  import opened Eval
  import opened Entity
  import opened Utils
  import opened Subcircuit
  import opened MapFunction

  ghost opaque predicate CircuitConserved(ca: Circuit, cb: Circuit)
  {
    && (forall n :: n in ca.NodeKind ==> n in cb.NodeKind)
    && (forall n :: n in ca.NodeKind ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np in ca.PortSource ==> np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np.n in ca.NodeKind && np !in ca.PortSource && np in cb.PortSource ==> cb.PortSource[np].n !in ca.NodeKind)
  }

  ghost opaque predicate CircuitUnconnected(ca: Circuit, cb: Circuit)
  {
    && (forall np :: np in cb.PortSource && np !in ca.PortSource ==> np.n !in ca.NodeKind && cb.PortSource[np].n !in ca.NodeKind)
  }

  lemma CircuitConservedToSubcircuitConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires ScValid(ca, sc)
    ensures SubcircuitConserved(ca, cb, sc)
  {
    reveal CircuitValid();
    reveal CircuitConserved();
    reveal SubcircuitConserved();
    reveal ScValid();
  }

  lemma CircuitConservedTransitive(ca: Circuit, cb: Circuit, cc: Circuit)
    requires CircuitConserved(ca, cb)
    requires CircuitConserved(cb, cc)
    ensures CircuitConserved(ca, cc)
  {
    reveal CircuitConserved();
  }

  ghost opaque predicate SubcircuitConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    // The internal connections of the subcircuit remain unchanged.
    requires ScValid(ca, sc)
  {
    reveal ScValid();
    && (forall n :: n in sc ==> n in cb.NodeKind)
    && (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np.n in sc && np in ca.PortSource ==>
        np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np.n in sc && np !in ca.PortSource && np in cb.PortSource ==>
        cb.PortSource[np].n !in sc)
  }

  ghost opaque predicate SubcircuitStronglyConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    // The internal and external connections of the subcircuit remain unchanged.
    requires ScValid(ca, sc)
  {
    reveal ScValid();
    && (forall n :: n in sc ==> n in cb.NodeKind)
    && (forall n :: n in sc ==> ca.NodeKind[n] == cb.NodeKind[n])
    && (forall np: NP :: np.n in sc && np in ca.PortSource ==>
        np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np in ca.PortSource && ca.PortSource[np].n in sc ==> np in cb.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np in cb.PortSource && cb.PortSource[np].n in sc ==> np in ca.PortSource && ca.PortSource[np] == cb.PortSource[np])
    && (forall np: NP :: np.n in sc && np !in ca.PortSource ==> np !in cb.PortSource)
    && (forall np: NP :: np.n in sc && np !in ca.PortSource.Values ==> np !in cb.PortSource.Values)
  }

  lemma EntitySomewhatValidConserved(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires EntitySomewhatValid(ca, e)
    requires ScValid(ca, e.sc)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures EntitySomewhatValid(cb, e)
  {
    reveal SubcircuitConserved();
    reveal EntitySomewhatValid();
    reveal ScValid();
    reveal ConnOutputs();
    reveal SeqOutputs();
    reveal AllONPs();
    reveal AllINPs();
    reveal SeqInputs();
    reveal UnconnInputs();
    reveal ConnInputs();
    reveal CircuitValid();
    reveal AllSeq();
  }


  ghost opaque predicate SubcircuitUnconnected(ca: Circuit, cb: Circuit, sc: set<CNode>)
  {
    && (forall np :: np in cb.PortSource && np !in ca.PortSource ==> np.n !in sc && cb.PortSource[np].n !in sc)
  }

  lemma IsIslandConserved(ca: Circuit, cb: Circuit, sc: set<CNode>)
    requires CircuitValid(ca)
    requires ScValid(ca, sc)
    requires IsIsland(ca, sc)
    requires CircuitConserved(ca, cb)
    requires CircuitUnconnected(ca, cb)
    ensures IsIsland(cb, sc)
  {
    reveal CircuitValid();
    reveal ScValid();
    reveal IsIsland();
    reveal CircuitConserved();
    reveal CircuitUnconnected();
  }
  
  lemma CircuitConservedSubcircuitConserved(ca: Circuit, cb: Circuit)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    ensures
      && ScValid(ca, ca.NodeKind.Keys)
      && SubcircuitConserved(ca, cb, ca.NodeKind.Keys)
  {
    reveal CircuitValid();
    reveal CircuitConserved();
    reveal SubcircuitConserved();
    reveal ScValid();
    var sc := ca.NodeKind.Keys;
    var nps := AllNPFromNodes(ca, sc);
    assert nps == AllNPFromNodes(cb, sc);

    // There may be some things in cb that are no longer unconnected.
    var newly_connected := (set np | np in nps && np in cb.PortSource && np !in ca.PortSource :: np);

    calc {
      ScInputBoundary(ca, sc);
      NPBetweenSubcircuitsComplement(ca, sc, sc) + UnconnectedINPs(ca, sc) + InternalInputs(ca, sc);
      (NPBetweenSubcircuitsComplement(cb, sc, sc) - newly_connected) + UnconnectedINPs(ca, sc) + InternalInputs(ca, sc);
      (NPBetweenSubcircuitsComplement(cb, sc, sc) - newly_connected) + (UnconnectedINPs(cb, sc) + newly_connected) + InternalInputs(ca, sc);
      {assert forall np :: np in newly_connected ==> np in NPBetweenSubcircuitsComplement(cb, sc, sc) && np !in UnconnectedINPs(cb, sc);}
      NPBetweenSubcircuitsComplement(cb, sc, sc) + UnconnectedINPs(cb, sc) + InternalInputs(ca, sc);
      NPBetweenSubcircuitsComplement(cb, sc, sc) + UnconnectedINPs(cb, sc) + InternalInputs(cb, sc);
      ScInputBoundary(cb, sc);
    }
    assert ScInputBoundary(ca, sc) == ScInputBoundary(cb, sc);
    assert (forall np: NP :: (np in ScInputBoundary(ca, sc)) == (np in ScInputBoundary(cb, sc)));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc ==> (np in ca.PortSource) == (np in cb.PortSource));
    assert (forall np: NP :: (np !in ScInputBoundary(ca, sc)) && np.n in sc && np in ca.PortSource ==> ca.PortSource[np] == cb.PortSource[np]);
  }

  ghost predicate ConservedValid(ca: Circuit, cb: Circuit, e: Entity, fi: FI)
  {
    && CircuitValid(ca)
    && CircuitValid(cb)
    && EntityValid(ca, e)
    && SubcircuitConserved(ca, cb, e.sc)
    && (Seq.ToSet(e.mf.inputs) == fi.inputs.Keys)
    && (Seq.ToSet(e.mf.state) == fi.state.Keys)
    && OutputsInFOutputs(cb, e)
  }

  lemma EvaluateINPInnerConserved(
    ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires forall np :: np in path ==> np.n in e.sc
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    requires INPValid(ca, Seq.Last(path))
    ensures PathValid(cb, path)
    ensures
      && CircuitValid(ca)
      && CircuitValid(cb)
      && INPValid(cb, Seq.Last(path))
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && EvaluateINPInnerRequirements(ca, path, fi)
      && EvaluateINPInnerRequirements(cb, path, fi)
      && (EvaluateINPInner(ca, path, fi) == EvaluateINPInner(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 2
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var head := Seq.Last(path);
    var tail := Seq.DropLast(path);
    if head in fi.inputs {
      assert EvaluateINPInner(ca, path, fi) == EvaluateINPInner(cb, path, fi);
    } else {
      assert head !in e.mf.inputs by {
        reveal Seq.ToSet();
      }
      StaysInSc(ca, e, head);
      assert fi.inputs.Keys == Seq.ToSet(e.mf.inputs);
      if head in ca.PortSource {
        var onp := ca.PortSource[head];
        if onp in path {
        } else {
          reveal CircuitValid();
          NodesNotInPathDecreases(ca, path, onp);
          StillHasNoDuplicates(path, onp);
          assert onp.n in e.sc;
          EvaluateONPInnerConserved(ca, cb, e, path + [onp], fi);
        }
      } else {
      }
    }
  }

  lemma EvaluateONPBinaryConserved(ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires ONPValid(ca, Seq.Last(path))
    requires Seq.Last(path).n !in fi.state
    requires forall np :: np in path ==> np.n in e.sc
    requires
      var nk := ca.NodeKind[Seq.Last(path).n];
      nk.CXor? || nk.CAnd?
    requires PathValid(ca, path)
    requires Seq.HasNoDuplicates(path)
    ensures PathValid(cb, path)
    ensures
      && CircuitValid(ca)
      && CircuitValid(cb)
      && ONPValid(cb, Seq.Last(path))
      && var nk := cb.NodeKind[Seq.Last(path).n];
      && (nk.CXor? || nk.CAnd?)
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (EvaluateONPBinary(ca, path, fi) == EvaluateONPBinary(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var nk := ca.NodeKind[path[|path|-1].n];
    var head := path[|path|-1];
    assert NodeValid(ca, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path {
    } else if inp_1 in path {
    } else {
      NodesNotInPathDecreases(ca, path, inp_0);
      NodesNotInPathDecreases(ca, path, inp_1);
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_0], fi);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_1], fi);
    }
  }

  lemma EvaluateONPUnaryConserved(ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires |path| > 0
    requires ONPValid(ca, path[|path|-1])
    requires path[|path|-1].n !in fi.state
    requires
      var nk := ca.NodeKind[path[|path|-1].n];
      nk.CInv? || nk.CIden?
    requires PathValid(ca, path)
    requires forall np :: np in path ==> np.n in e.sc
    requires Seq.HasNoDuplicates(path)
    ensures PathValid(cb, path)
    ensures
      && CircuitValid(ca)
      && CircuitValid(cb)
      && ONPValid(cb, Seq.Last(path))
      && var nk := cb.NodeKind[Seq.Last(path).n];
      && (nk.CInv? || nk.CIden?)
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (EvaluateONPUnary(ca, path, fi) == EvaluateONPUnary(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 3
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(ca, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      EvaluateINPInnerConserved(ca, cb, e, path + [inp_0], fi);
    }
  }

  lemma FICircuitValidFromConservedValid(ca: Circuit, cb: Circuit, e: Entity, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    ensures FICircuitValid(ca, fi) && FICircuitValid(cb, fi)
  {
    EntityValidFiValidToFICircuitValid(ca, e, fi);
    EntitySomewhatValidConserved(ca, cb, e);
    EntityValidFiValidToFICircuitValid(cb, e, fi);
  }

  lemma EvaluateONPInnerConserved(ca: Circuit, cb: Circuit, e: Entity, path: seq<NP>, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires EvaluateONPInnerRequirements(ca, path, fi)
    requires forall np :: np in path ==> np.n in e.sc
    ensures PathValid(cb, path)
    ensures
      && CircuitValid(ca)
      && CircuitValid(cb)
      && ONPValid(cb, Seq.Last(path))
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (EvaluateONPInner(ca, path, fi) == EvaluateONPInner(cb, path, fi))
    decreases |NodesNotInPath(ca, path)|, 4
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    var head := path[|path|-1];
    if head.n in fi.state {
    } else {
      var nk := ca.NodeKind[head.n];
      match nk
        case CXor() => EvaluateONPBinaryConserved(ca, cb, e, path, fi);
        case CAnd() => EvaluateONPBinaryConserved(ca, cb, e, path, fi);
        case CInv() => EvaluateONPUnaryConserved(ca, cb, e, path, fi);
        case CIden() => EvaluateONPUnaryConserved(ca, cb, e, path, fi);
        case CConst(b) => {}
        case CSeq() => {}
    }
  }

  lemma EvaluateConserved(ca: Circuit, cb: Circuit, e: Entity, o: NP, fi: FI)
    requires ConservedValid(ca, cb, e, fi)
    requires o.n in e.sc
    requires INPValid(ca, o) || ONPValid(ca, o)
    ensures INPValid(cb, o) || ONPValid(cb, o)
    ensures
      && CircuitValid(ca)
      && CircuitValid(cb)
      && FICircuitValid(ca, fi)
      && FICircuitValid(cb, fi)
      && (Evaluate(ca, o, fi) == Evaluate(cb, o, fi))
  {
    reveal PathValid();
    reveal CircuitValid();
    reveal SubcircuitConserved();
    assert PathValid(ca, [o]);
    FICircuitValidFromConservedValid(ca, cb, e, fi);
    LengthOneNoDuplicates([o]);
    if INPValid(ca, o) {
      EvaluateINPInnerConserved(ca, cb, e, [o], fi);
    } else {
      EvaluateONPInnerConserved(ca, cb, e, [o], fi);
    }
  }

  lemma EntityConserved2(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires CircuitConserved(ca, cb)
    requires EntityValid(ca, e)
    requires ScValid(cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures EntityValid(cb, e)
  {
    CircuitConservedToSubcircuitConserved(ca, cb, e.sc);
    reveal CircuitConserved();
    reveal CircuitUnconnected();
    reveal ScValid();
    EntityConserved(ca, cb, e);
  }

  lemma EntityConserved(ca: Circuit, cb: Circuit, e: Entity)
    requires CircuitValid(ca)
    requires CircuitValid(cb)
    requires EntityValid(ca, e)
    requires SubcircuitConserved(ca, cb, e.sc)
    requires ScValid(cb, e.sc)
    requires OutputsInFOutputs(cb, e)
    ensures EntityValid(cb, e)
  {
    reveal CircuitValid();
    reveal ScValid();
    reveal SubcircuitConserved();

    assert ScValid(ca, e.sc);
    assert ScValid(cb, e.sc) by {
      reveal ScValid();
    }

    EntitySomewhatValidConserved(ca, cb, e);

    if EntityValid(ca, e) {
      forall fi: FI | FIValid(fi, e.mf.inputs, e.mf.state)
        ensures forall np :: np in (Seq.ToSet(e.mf.outputs) + StateINPs(e.mf.state)) ==> (
          && NPValid(ca, np)
          && NPValid(cb, np)
          && FICircuitValid(ca, fi)
          && FICircuitValid(cb, fi)
          && (Evaluate(ca, np, fi) == Evaluate(cb, np, fi))
        )
      {
        EntityValidFiValidToFICircuitValid(ca, e, fi);
        EntityValidFiValidToFICircuitValid(cb, e, fi);
        forall np | np in (Seq.ToSet(e.mf.outputs) + StateINPs(e.mf.state))
          ensures
            && NPValid(ca, np) && NPValid(cb, np)
            && (Evaluate(ca, np, fi) == Evaluate(cb, np, fi))
        {
          EntityFOutputsAreValid(ca, e);
          FOutputsInSc(ca, e);
          reveal NPsInSc();
          assert NPValid(ca, np) by {
            reveal EntitySomewhatValid();
            reveal AllONPs();
            reveal AllSeq();
            reveal ONPsValid();
          }
          EvaluateConserved(ca, cb, e, np, fi);
          assert Evaluate(ca, np, fi) == Evaluate(cb, np, fi);
        }
      }
    }

    assert e.mf.Valid() by {
      reveal MapFunction.Valid();
    }
    assert ScValid(cb, e.sc);
    assert EntityEvaluatesCorrectly(cb, e) by {
      reveal EntityEvaluatesCorrectly();
    }
  }

  opaque ghost predicate SimpleInsertion(c: Circuit, new_c: Circuit, e: Entity)
  {
    && CircuitValid(new_c)
    && EntityValid(new_c, e)
    && IsIsland(new_c, e.sc)
    && CircuitUnconnected(c, new_c)
    && CircuitConserved(c, new_c)
    && (new_c.NodeKind.Keys == c.NodeKind.Keys + e.sc)
    && (c.NodeKind.Keys !! e.sc)
  }

  datatype EntityInserter = EntityInserter(
    rf: RFunction,
    fn: Circuit --> (Circuit, Entity)
  ) {

    ghost predicate SpecificValid(c: Circuit)
      requires CircuitValid(c)
      requires rf.Valid()
    {
      && fn.requires(c)
      && var (new_c, e) := fn(c);
      && rf.MFConsistent(e.mf)
      && SimpleInsertion(c, new_c, e)
    }

    opaque ghost predicate Valid() {
      && rf.Valid()
      && (forall c: Circuit :: CircuitValid(c) ==> SpecificValid(c))
    }

    lemma ValidForCircuit(c: Circuit)
      requires Valid()
      requires CircuitValid(c)
      ensures rf.Valid()
      ensures SpecificValid(c)
    {
      reveal Valid();
    }
  }

  lemma StillSimpleInsertionAfterEntitySwapMF(old_c: Circuit, new_c: Circuit, e: Entity, mf: MapFunction)
    requires SimpleInsertion(old_c, new_c, e)
    requires mf.Valid()
    requires
      reveal SimpleInsertion();
      MapFunctionsEquiv(e.mf, mf)
    ensures
      reveal SimpleInsertion();
      var new_e := EntitySwapMF(new_c, e, mf);
      SimpleInsertion(old_c, new_c, new_e)
  {
    reveal SimpleInsertion();
  }
  


}
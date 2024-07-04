module Path2 {

  import opened Circ
  import opened Eval
  import opened MapFunction
  import opened Utils
  import opened Path

  // Prove that if there are no paths from onp to inps then we can remove inps from fi with
  // no effect on the outcome.

  lemma EvaluateReduceFI(c: Circuit, np: NP, fi: FI, removed_inputs: set<NP>, removed_state: set<CNode>)
    requires c.Valid()
    requires NPValid(c, np)
    requires FICircuitValid(c, fi)
    requires !PathExistsToNPSet(c, np, removed_inputs)
    requires !PathExistsToNPSet(c, np, StateONPsFromSet(removed_state))
    ensures
      var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
      reveal FICircuitValid();
      Evaluate(c, np, fi) == Evaluate(c, np, reduced_fi)
  {
    var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
    reveal FICircuitValid();
    if ONPValid(c, np) {
      EvaluateONPReduceFI(c, np, fi, removed_inputs, removed_state);
    } else {
      EvaluateINPReduceFI(c, np, fi, removed_inputs, removed_state);
    }
  }

  lemma EvaluateONPReduceFI(c: Circuit, np: NP, fi: FI, removed_inputs: set<NP>, removed_state: set<CNode>)
    requires c.Valid()
    requires FICircuitValid(c, fi)
    requires ONPValid(c, np)
    requires !PathExistsToNPSet(c, np, removed_inputs)
    requires !PathExistsToNPSet(c, np, StateONPsFromSet(removed_state))
    ensures
      var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
      reveal FICircuitValid();
      EvaluateONP(c, np, fi) == EvaluateONP(c, np, reduced_fi)
  {
    reveal FICircuitValid();
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    var p := [np];
    assert PathValid(c, p);
    EvaluateONPInnerReduceFI(c, p, fi, removed_inputs, removed_state);
  }

  lemma EvaluateINPReduceFI(c: Circuit, np: NP, fi: FI, removed_inputs: set<NP>, removed_state: set<CNode>)
    requires c.Valid()
    requires FICircuitValid(c, fi)
    requires INPValid(c, np)
    requires !PathExistsToNPSet(c, np, removed_inputs)
    requires !PathExistsToNPSet(c, np, StateONPsFromSet(removed_state))
    ensures
      var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
      reveal FICircuitValid();
      EvaluateINP(c, np, fi) == EvaluateINP(c, np, reduced_fi)
  {
    reveal FICircuitValid();
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    EvaluateINPInnerReduceFI(c, path, fi, removed_inputs, removed_state);
  }

  lemma EvaluateONPInnerReduceFI(c: Circuit, p: seq<NP>, fi: FI, removed_inputs: set<NP>, removed_state: set<CNode>)
    requires c.Valid()
    requires PathValid(c, p)
    requires EvaluateONPInnerRequirements(c, p, fi)
    requires !PathExistsToNPSet(c, Seq.Last(p), removed_inputs)
    requires !PathExistsToNPSet(c, Seq.Last(p), StateONPsFromSet(removed_state))
    ensures
      var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
      reveal FICircuitValid();
      EvaluateONPInner(c, p, fi) == EvaluateONPInner(c, p, reduced_fi)
    decreases |NodesNotInPath(c, p)|, 4
  {
    var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
    reveal FICircuitValid();
    var head := Seq.Last(p);
    var nk := c.NodeKind[head.n];
    if head.n in fi.state {
      assert head.n in reduced_fi.state by {
        // The head can't be in the removed_state because we know there is no path to there.
        if head.n !in reduced_fi.state {
          assert head.n in removed_state;
          assert head in StateONPsFromSet(removed_state);
          reveal PathValid();
          reveal PathExistsToNPSet();
          assert PathToNPSet(c, [head], head, StateONPsFromSet(removed_state));
          assert false;
        }
      }
      assert nk.CSeq? by {
        reveal FICircuitValid();
      }
      match nk
        case CSeq() => {
          reveal PathCaught();
        }
    } else {
      match nk
        case CXor() => EvaluateONPBinaryReduceFI(c, p, fi, removed_inputs, removed_state);
        case CAnd() => EvaluateONPBinaryReduceFI(c, p, fi, removed_inputs, removed_state);
        case CInv() => EvaluateONPUnaryReduceFI(c, p, fi, removed_inputs, removed_state);
        case CIden() => EvaluateONPUnaryReduceFI(c, p, fi, removed_inputs, removed_state);
        case CConst(b) => {
          reveal PathCaught();
        }
        case CSeq() => {
        }
    }
  }

  lemma EvaluateONPBinaryReduceFI(c: Circuit, path: seq<NP>, fi: FI, removed_inputs: set<NP>, removed_state: set<CNode>)
    requires EvaluateONPBinaryRequirements(c, path, fi)
    requires !PathExistsToNPSet(c, Seq.Last(path), removed_inputs)
    requires !PathExistsToNPSet(c, Seq.Last(path), StateONPsFromSet(removed_state))
    ensures
      var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
      reveal FICircuitValid();
      EvaluateONPBinary(c, path, fi) == EvaluateONPBinary(c, path, reduced_fi)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
    reveal FICircuitValid();
    var nk := c.NodeKind[path[|path|-1].n];
    var head := Seq.Last(path);
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path {
    } else if inp_1 in path {
    } else {
      NodesNotInPathDecreases(c, path, inp_0);
      NodesNotInPathDecreases(c, path, inp_1);
      var new_path_0 := path + [inp_0];
      var new_path_1 := path + [inp_1];
      assert PathValid(c, new_path_0);
      assert PathValid(c, new_path_1);
      assert |NodesNotInPath(c, path + [inp_0])| < |NodesNotInPath(c, path)|;
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      StillNoPathExistsToNPSet(c, Seq.Last(path), inp_0, removed_inputs);
      StillNoPathExistsToNPSet(c, Seq.Last(path), inp_1, removed_inputs);
      StillNoPathExistsToNPSet(c, Seq.Last(path), inp_0, StateONPsFromSet(removed_state));
      StillNoPathExistsToNPSet(c, Seq.Last(path), inp_1, StateONPsFromSet(removed_state));
      EvaluateINPInnerReduceFI(c, path + [inp_0], fi, removed_inputs, removed_state);
      EvaluateINPInnerReduceFI(c, path + [inp_1], fi, removed_inputs, removed_state);
    }
  }

  lemma EvaluateONPUnaryReduceFI(c: Circuit, path: seq<NP>, fi: FI, removed_inputs: set<NP>, removed_state: set<CNode>)
    requires EvaluateONPUnaryRequirements(c, path, fi)
    requires !PathExistsToNPSet(c, Seq.Last(path), removed_inputs)
    requires !PathExistsToNPSet(c, Seq.Last(path), StateONPsFromSet(removed_state))
    ensures
      var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
      reveal FICircuitValid();
      EvaluateONPUnary(c, path, fi) == EvaluateONPUnary(c, path, reduced_fi)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
    reveal FICircuitValid();
    var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
    var nk := c.NodeKind[path[|path|-1].n];
    var head := Seq.Last(path);
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path {
    } else {
      NodesNotInPathDecreases(c, path, inp_0);
      var new_path_0 := path + [inp_0];
      assert PathValid(c, new_path_0);
      assert |NodesNotInPath(c, path + [inp_0])| < |NodesNotInPath(c, path)|;
      StillHasNoDuplicates(path, inp_0);
      StillNoPathExistsToNPSet(c, Seq.Last(path), inp_0, removed_inputs);
      StillNoPathExistsToNPSet(c, Seq.Last(path), inp_0, StateONPsFromSet(removed_state));
      EvaluateINPInnerReduceFI(c, path + [inp_0], fi, removed_inputs, removed_state);
    }
  }

  lemma EvaluateINPInnerReduceFI(c: Circuit, path: seq<NP>, fi: FI, removed_inputs: set<NP>, removed_state: set<CNode>)
    requires EvaluateINPInnerRequirements(c, path, fi)
    requires !PathExistsToNPSet(c, Seq.Last(path), removed_inputs)
    requires !PathExistsToNPSet(c, Seq.Last(path), StateONPsFromSet(removed_state))
    ensures
      var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
      reveal FICircuitValid();
      EvaluateINPInner(c, path, fi) == EvaluateINPInner(c, path, reduced_fi)
    decreases |NodesNotInPath(c, path)|, 2
  {
    var reduced_fi := FI(fi.inputs - removed_inputs, fi.state - removed_state);
    reveal FICircuitValid();
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in fi.inputs {
      assert head !in removed_inputs by {
        if head in removed_inputs {
          reveal PathExistsToNPSet();
          var p_contradict := [head];
          reveal PathValid();
          assert PathToNPSet(c, p_contradict, head, removed_inputs);
          assert false;
        }
      }
      assert head in reduced_fi.inputs;
    } else {
      if head in c.PortSource {
        var onp := c.PortSource[head];
        if onp in path {
        } else {
          reveal Circuit.Valid();
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          AppendPathValid(c, path, onp);
          StillNoPathExistsToNPSet(c, Seq.Last(path), onp, removed_inputs);
          StillNoPathExistsToNPSet(c, Seq.Last(path), onp, StateONPsFromSet(removed_state));
          EvaluateONPInnerReduceFI(c, path + [onp], fi, removed_inputs, removed_state);
          reveal PathCaught();
        }
      } else {
      }
    }
  }

}
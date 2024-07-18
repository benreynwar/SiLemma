module Path {

  import opened Circ
  import opened Eval
  import opened MapFunction
  import opened Utils
  import opened Subcircuit

  function PathSegment(p: seq<NP>, start: nat, stop: nat): (seg: seq<NP>)
    requires start < |p|
    requires stop <= |p|
    requires start < stop
    ensures |p| > 0
  {
    p[start..stop]
  }

  lemma PathSegmentValid(c: Circuit, p: seq<NP>, start: nat, stop: nat)
    requires c.Valid()
    requires PathValid(c, p)
    requires start < |p|
    requires stop <= |p|
    requires start < stop
    ensures
      var p := PathSegment(p, start, stop);
      PathValid(c, p)
  {
    reveal PathValid();
  }

  function ValidPathSegment(c: Circuit, p: seq<NP>, start: nat, stop: nat): (seg: seq<NP>)
    requires c.Valid()
    requires PathValid(c, p)
    requires start < |p|
    requires stop <= |p|
    requires start < stop
    ensures
      PathValid(c, seg)
  {
    PathSegmentValid(c, p, start, stop);
    PathSegment(p, start, stop)
  }

  ghost opaque predicate PathExists(c: Circuit, np_a: NP, np_b: NP)
    requires c.Valid()
  {
    exists p: seq<NP> :: (|p| > 0) && PathValid(c, p) && (Seq.First(p) == np_a) && (Seq.Last(p) == np_b)
  }

  ghost function PathExistsToPath(c: Circuit, np_a: NP, np_b: NP): (path: seq<NP>)
    requires c.Valid()
    requires PathExists(c, np_a, np_b)
  {
    reveal PathExists();
    var path :| (|path| > 0) && PathValid(c, path) && (Seq.First(path) == np_a) && (Seq.Last(path) == np_b);
    path
  }

  predicate PathToNPSet(c: Circuit, p: seq<NP>, np: NP, nps_b: set<NP>)
    requires c.Valid()
  {
    (|p| > 0) && PathValid(c, p) && (Seq.First(p) == np) && (Seq.Last(p) in nps_b)
  }

  opaque ghost predicate PathExistsToNPSet(c: Circuit, np: NP, nps_b: set<NP>)
    requires c.Valid()
  {
    exists p: seq<NP> :: PathToNPSet(c, p, np, nps_b)
  }

  lemma NoPathExistsToNPSubSet(c: Circuit, np: NP, nps: set<NP>, nps_subset: set<NP>)
    requires c.Valid()
    requires !PathExistsToNPSet(c, np, nps)
    requires nps_subset <= nps
    ensures !PathExistsToNPSet(c, np, nps_subset)
  {
    reveal PathExistsToNPSet();
    if PathExistsToNPSet(c, np, nps_subset) {
      var p :| PathToNPSet(c, p, np, nps_subset);
      assert PathToNPSet(c, p, np, nps);
      assert false;
    }
  }

  lemma StillNoPathExistsToNPSet(c: Circuit, np: NP, next_np: NP, nps_b: set<NP>)
    requires c.Valid()
    requires NPValid(c, np)
    requires NPValid(c, next_np)
    requires NPsConnected(c, np, next_np)
    requires !PathExistsToNPSet(c, np, nps_b)
    ensures !PathExistsToNPSet(c, next_np, nps_b)
  {
    reveal PathExistsToNPSet();
    if PathExistsToNPSet(c, next_np, nps_b) {
      var p :| (|p| > 0) && PathValid(c, p) && (Seq.First(p) == next_np) && (Seq.Last(p) in nps_b);
      var p_contradict := [np] + p;
      reveal PathValid();
      assert PathValid(c, p_contradict);
      assert PathToNPSet(c, p_contradict, np, nps_b);
      assert PathExistsToNPSet(c, np, nps_b);
      assert false;
    }
  }

  predicate PathBetweenNPSets(c: Circuit, p: seq<NP>, nps_a: set<NP>, nps_b: set<NP>)
    requires c.Valid()
  {
    (|p| > 0) && PathValid(c, p) && (Seq.First(p) in nps_a) && (Seq.Last(p) in nps_b)
  }

  opaque ghost predicate PathExistsBetweenNPSets(c: Circuit, nps_a: set<NP>, nps_b: set<NP>)
    requires c.Valid()
  {
    exists p: seq<NP> :: PathBetweenNPSets(c, p, nps_a, nps_b)
  }

  lemma NoPathExistsToNoPathExistsBetweenNPSets(c: Circuit, nps_a: set<NP>, nps_b: set<NP>)
    requires c.Valid()
    requires forall npa: NP, npb: NP :: npa in nps_a && npb in nps_b ==> !PathExists(c, npa, npb)
    ensures !PathExistsBetweenNPSets(c, nps_a, nps_b)
  {
    reveal PathExistsBetweenNPSets();
    reveal PathExists();
    if PathExistsBetweenNPSets(c, nps_a, nps_b) {
      var p :| PathBetweenNPSets(c, p, nps_a, nps_b);
      assert PathExists(c, Seq.First(p), Seq.Last(p));
    }
  }

  lemma NoPathExistsBetweenNPSubSets(c: Circuit, nps_a: set<NP>, nps_b: set<NP>, subset_a: set<NP>, subset_b: set<NP>)
    requires c.Valid()
    requires !PathExistsBetweenNPSets(c, nps_a, nps_b)
    requires subset_a <= nps_a
    requires subset_b <= nps_b
    ensures !PathExistsBetweenNPSets(c, subset_a, subset_b)
  {
    reveal PathExistsBetweenNPSets();
    if PathExistsBetweenNPSets(c, subset_a, subset_b) {
      var p :| PathBetweenNPSets(c, p, subset_a, subset_b);
      assert PathBetweenNPSets(c, p, nps_a, nps_b);
      assert false;
    }
  }

  lemma NoPathExistsBetweenNPSetsToNoPathExists(c: Circuit, nps_a: set<NP>, nps_b: set<NP>, np_a: NP, np_b: NP)
    requires c.Valid()
    requires np_a in nps_a
    requires np_b in nps_b
    requires !PathExistsBetweenNPSets(c, nps_a, nps_b)
    ensures !PathExists(c, np_a, np_b)
  {
    reveal PathExistsBetweenNPSets();
    reveal PathExists();
    if PathExists(c, np_a, np_b) {
      var p := PathExistsToPath(c, np_a, np_b);
      assert PathBetweenNPSets(c, p, nps_a, nps_b);
    }
  }

  lemma NoPathExistsBetweenNPSetsToToNPSet(c: Circuit, nps_a: set<NP>, nps_b: set<NP>, np: NP)
    requires c.Valid()
    requires !PathExistsBetweenNPSets(c, nps_a, nps_b)
    requires np in nps_a
    ensures !PathExistsToNPSet(c, np, nps_b)
  {
    reveal PathExistsBetweenNPSets();
    reveal PathExistsToNPSet();
    if PathExistsToNPSet(c, np, nps_b) {
      var p :| PathToNPSet(c, p, np, nps_b);
      assert PathBetweenNPSets(c, p, nps_a, nps_b);
    }
  }

  predicate PathFromTo(c: Circuit, p: seq<NP>, a: NP, b: NP)
    requires c.Valid()
  {
    PathValid(c, p) && |p| > 0 && Seq.First(p) == a && Seq.Last(p) == b && PathValid(c, p)
  }

  function JoinPaths(c: Circuit, pa: seq<NP>, pb: seq<NP>): (p: seq<NP>)
    requires c.Valid()
    requires PathNonZeroValid(c, pa)
    requires PathNonZeroValid(c, pb)
    requires Seq.Last(pa) == Seq.First(pb)
    ensures PathValid(c, p)
  {
    reveal PathValid();
    pa + pb[1..]
  }

  lemma PathsNoIntersection(c: Circuit, nps_a: set<NP>, nps_b: set<NP>, p_a: seq<NP>, p_b: seq<NP>)
    requires c.Valid()
    requires PathNonZeroValid(c, p_a)
    requires PathNonZeroValid(c, p_b)
    requires !PathExistsBetweenNPSets(c, nps_a, nps_b)
    requires Seq.Last(p_a) in nps_b
    requires Seq.First(p_b) in nps_a
    ensures Seq.ToSet(p_a) !! Seq.ToSet(p_b)
  {
    if exists np :: np in p_a && np in p_b {
      var np :| np in p_a && np in p_b;
      var index_a := Seq.IndexOf(p_a, np);
      var index_b := Seq.IndexOf(p_b, np);
      var p_c := ValidPathSegment(c, p_a, index_a, |p_a|);
      var p_d := ValidPathSegment(c, p_b, 0, index_b+1);
      var p_joined := JoinPaths(c, p_d, p_c);
      assert PathFromTo(c, p_joined, Seq.First(p_b), Seq.Last(p_a));
      assert PathBetweenNPSets(c, p_joined, nps_a, nps_b);
      reveal PathExistsBetweenNPSets();
      assert PathExistsBetweenNPSets(c, nps_a, nps_b);
      assert false;
    }
    reveal Seq.ToSet();
  }

  function PathFindTransition(c: Circuit, sc: set<CNode>, p: seq<NP>): (index: nat)
    // A path is entire in two subcircuits.
    // It starts in one and ends in another.
    // Find a transition from the sc_a set to not sc_a set.
    requires c.Valid()
    requires ScValid(c, sc)
    requires |p| > 0
    requires Seq.First(p).n in sc
    requires Seq.Last(p).n !in sc
    ensures index < |p|-1
    ensures p[index].n in sc
    ensures p[index+1].n !in sc
  {
    assert |p| > 1;
    if p[1].n !in sc then
      0
    else
      assert p[1].n in sc;
      1 + PathFindTransition(c, sc, p[1..])
  }

  lemma NoPathOutOfIsland(c: Circuit, sc: set<CNode>, np_a: NP, np_b: NP)
    requires c.Valid()
    requires ScValid(c, sc)
    requires IsIsland(c, sc)
    requires np_a.n in sc
    requires np_b.n !in sc
    ensures !PathExists(c, np_a, np_b)
  {
    if PathExists(c, np_a, np_b) {
      // A path shoudn't be able to exist because sc_a is an island so there is no connection out.
      var p := PathExistsToPath(c, np_a, np_b);
      assert Seq.First(p).n in sc;
      assert Seq.Last(p).n !in sc;
      var transition_index := PathFindTransition(c, sc, p);
      var np_in_a := p[transition_index];
      var np_not_in_a := p[transition_index+1];
      assert NPValid(c, np_in_a) && NPValid(c, np_not_in_a) && NPsConnected(c, np_in_a, np_not_in_a) by {
        reveal PathValid();
      }
      reveal IsIsland();
      assert false;
    }
  }

  ghost opaque predicate PathCaught(c: Circuit, p: seq<NP>, catcher: set<NP>)
    requires c.Valid()
    requires PathNonZeroValid(c, p)
    requires Seq.HasNoDuplicates(p)
    decreases
      |NodesNotInPath(c, p)|
  {
    var np := Seq.Last(p);
    assert NPValid(c, np) by {
      reveal PathValid();
    }
    if np in catcher then
      true
    else if c.NodeKind[np.n].CConst? then
      true
    else
      reveal PathValid();
      forall next_np: NP :: NPValid(c, next_np) && NPsConnected(c, Seq.Last(p), next_np) ==>
        && var new_p := p + [next_np];
        && (next_np !in p)
        && assert PathValid(c, new_p) && |NodesNotInPath(c, new_p)| < |NodesNotInPath(c, p)| by {
          AppendPathValid(c, p, next_np);
          NodesNotInPathDecreases(c, p, next_np);
        }
        && assert Seq.HasNoDuplicates(new_p) by {
          reveal Seq.HasNoDuplicates();
        }
        && PathCaught(c, new_p, catcher)
  }

  // Prove that if something Evaluates as EvalOK then the FI inputs catch the paths
  // from the output.  These are two different ways of saying we're not missing any inputs
  // and we don't have any loops.
  // This proof connects them.

  lemma EvaluateOkToPathCaught(c: Circuit, np: NP, fi: FI)
    requires c.Valid()
    requires NPValid(c, np)
    requires FICircuitValid(c, FItoKeys(fi))
    requires Evaluate(c, np, fi).EvalOk?
    ensures
      var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
      var p := [np];
      && PathValid(c, p)
      && Seq.HasNoDuplicates(p)
      && PathCaught(c, p, ending_set)
  {
    if ONPValid(c, np) {
      EvaluateONPOkToPathCaught(c, np, fi);
    } else {
      EvaluateINPOkToPathCaught(c, np, fi);
    }
  }

  lemma EvaluateONPOkToPathCaught(c: Circuit, np: NP, fi: FI)
    requires c.Valid()
    requires FICircuitValid(c, FItoKeys(fi))
    requires ONPValid(c, np)
    requires EvaluateONP(c, np, fi).EvalOk?
    ensures
      var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
      var p := [np];
      && PathValid(c, p)
      && Seq.HasNoDuplicates(p)
      && PathCaught(c, p, ending_set)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    var p := [np];
    assert PathValid(c, p);
    EvaluateONPInnerOkToPathCaught(c, p, fi);
  }

  lemma EvaluateINPOkToPathCaught(c: Circuit, np: NP, fi: FI)
    requires c.Valid()
    requires FICircuitValid(c, FItoKeys(fi))
    requires INPValid(c, np)
    requires EvaluateINP(c, np, fi).EvalOk?
    ensures
      var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
      var p := [np];
      && PathValid(c, p)
      && Seq.HasNoDuplicates(p)
      && PathCaught(c, p, ending_set)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    EvaluateINPInnerOkToPathCaught(c, path, fi);
  }

  lemma EvaluateONPInnerOkToPathCaught(c: Circuit, p: seq<NP>, fi: FI)
    requires c.Valid()
    requires PathValid(c, p)
    requires EvaluateONPInnerRequirements(c, p, FItoKeys(fi))
    requires EvaluateONPInner(c, p, fi).EvalOk?
    decreases |NodesNotInPath(c, p)|, 4
    ensures
      var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
      && PathCaught(c, p, ending_set)
  {
    var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
    var head := Seq.Last(p);
    var nk := c.NodeKind[head.n];
    if head.n in fi.state {
      assert nk.CSeq? by {
        reveal FICircuitValid();
      }
      match nk
        case CSeq() => {
          reveal PathCaught();
        }
    } else {
      match nk
        case CXor() => EvaluateONPBinaryOkToPathCaught(c, p, fi);
        case CAnd() => EvaluateONPBinaryOkToPathCaught(c, p, fi);
        case COr() => EvaluateONPBinaryOkToPathCaught(c, p, fi);
        case CInv() => EvaluateONPUnaryOkToPathCaught(c, p, fi);
        case CIden() => EvaluateONPUnaryOkToPathCaught(c, p, fi);
        case CConst(b) => {
          reveal PathCaught();
        }
        case CSeq() => {
        }
    }
  }

  lemma EvaluateONPBinaryOkToPathCaught(c: Circuit, path: seq<NP>, fi: FI)
    requires EvaluateONPBinaryRequirements(c, path, FItoKeys(fi))
    requires EvaluateONPBinary(c, path, fi).EvalOk?
    ensures
      var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
      && PathCaught(c, path, ending_set)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
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
      EvaluateINPInnerOkToPathCaught(c, path + [inp_0], fi);
      EvaluateINPInnerOkToPathCaught(c, path + [inp_1], fi);
      assert PathCaught(c, path, ending_set) by {
        reveal PathCaught();
      }
    }
  }

  lemma EvaluateONPUnaryOkToPathCaught(c: Circuit, path: seq<NP>, fi: FI)
    requires EvaluateONPUnaryRequirements(c, path, FItoKeys(fi))
    requires EvaluateONPUnary(c, path, fi).EvalOk?
    ensures
      var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
      && PathCaught(c, path, ending_set)
    decreases |NodesNotInPath(c, path)|, 3
  {
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
      EvaluateINPInnerOkToPathCaught(c, path + [inp_0], fi);
      assert PathCaught(c, path, ending_set) by {
        reveal PathCaught();
      }
    }
  }

  lemma EvaluateINPInnerOkToPathCaught(c: Circuit, path: seq<NP>, fi: FI)
    requires EvaluateINPInnerRequirements(c, path, FItoKeys(fi))
    requires EvaluateINPInner(c, path, fi).EvalOk?
    ensures
      var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
      && PathCaught(c, path, ending_set)
    decreases |NodesNotInPath(c, path)|, 2
  {
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in fi.inputs {
      reveal PathCaught();
    } else {
      if head in c.PortSource {
        var onp := c.PortSource[head];
        if onp in path {
        } else {
          reveal Circuit.Valid();
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          AppendPathValid(c, path, onp);
          EvaluateONPInnerOkToPathCaught(c, path + [onp], fi);
          reveal PathCaught();
        }
      } else {
      }
    }
  }

  // Prove that prepending to the beginning of the path is fine, as long as their is no way of
  // creating a loop.

  lemma EvaluateONPInnerPrepend(c: Circuit, prefix: seq<NP>, p: seq<NP>, fi: FI)
    requires EvaluateONPInnerRequirements(c, p, FItoKeys(fi))
    requires EvaluateONPInnerRequirements(c, prefix + p, FItoKeys(fi))
    requires
      var new_p := prefix + p;
      |prefix| > 0 ==> !PathExists(c, Seq.Last(new_p), Seq.Last(prefix))
    ensures
      EvaluateONPInner(c, p, fi) == EvaluateONPInner(c, prefix + p, fi)
    decreases |NodesNotInPath(c, p)|, 4
  {
    var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
    var head := Seq.Last(p);
    var nk := c.NodeKind[head.n];
    if head.n in fi.state {
      assert nk.CSeq? by {
        reveal FICircuitValid();
      }
      match nk
        case CSeq() => {
          reveal PathCaught();
        }
    } else {
      match nk
        case CXor() => EvaluateONPBinaryPrepend(c, prefix, p, fi);
        case CAnd() => EvaluateONPBinaryPrepend(c, prefix, p, fi);
        case COr() => EvaluateONPBinaryPrepend(c, prefix, p, fi);
        case CInv() => EvaluateONPUnaryPrepend(c, prefix, p, fi);
        case CIden() => EvaluateONPUnaryPrepend(c, prefix, p, fi);
        case CConst(b) => {
          reveal PathCaught();
        }
        case CSeq() => {
        }
    }
  }

  lemma NextNodeInPathAndNewPathSame(c: Circuit, prefix: seq<NP>, path: seq<NP>, np: NP)
    requires c.Valid()
    requires PathNonZeroValid(c, path)
    requires PathValid(c, prefix + path)
    requires NPValid(c, np)
    requires
      reveal PathValid();
      NPsConnected(c, Seq.Last(path), np)
    requires
      |prefix| > 0 ==> !PathExists(c, Seq.Last(path), Seq.Last(prefix))
    ensures
      var new_path := prefix + path;
      && ((np in path) == (np in new_path))
  {
    var new_path := prefix + path;
    reveal PathValid();
    if |prefix| > 0 {
      assert prefix == ValidPathSegment(c, new_path, 0, |prefix|);
    }
    assert PathValid(c, prefix);
    assert np in path ==> np in new_path;
    assert np !in path ==> np !in new_path by {
      if np !in path && np in new_path {
        var index: nat :| index < |prefix| && prefix[index] == np;
        var p_contradict := [Seq.Last(path)] + prefix[index..];
        assert PathValid(c, p_contradict);
        reveal PathExists();
        assert PathExists(c, Seq.Last(new_path), Seq.Last(prefix));
        assert false;
      }
    }
  }

  lemma StillNoPathExists(c: Circuit, a: NP, b: NP, dest: NP)
    requires c.Valid()
    requires !PathExists(c, a, dest)
    requires NPValid(c, a)
    requires NPValid(c, b)
    requires NPsConnected(c, a, b)
    ensures
      !PathExists(c, b, dest)
  {
    if PathExists(c, b, dest) {
      var path := PathExistsToPath(c, b, dest);
      var path_contradict := [a] + path;
      reveal PathValid();
      assert PathFromTo(c, path_contradict, a, dest);
      reveal PathExists();
      assert PathExists(c, a, dest);
      assert false;
    }
  }

  lemma LoopIsSame(c: Circuit, prefix: seq<NP>, path: seq<NP>, np: NP)
    requires c.Valid()
    requires np in path
    requires Seq.HasNoDuplicates(prefix + path)
    ensures
      assert Seq.HasNoDuplicates(path) by {
        SubSeqsNoDuplicates(prefix, path);
      }
      GetLoop(prefix + path, np) == GetLoop(path, np)
  {
    HasNoDuplicatesNotInBoth(prefix, path, np);
    var long_path := prefix + path;
    var long_index := Seq.IndexOf(long_path, np);
    var index := Seq.IndexOf(path, np);
    assert long_path[index + |prefix|] == np;
    assert long_index == index + |prefix|;
  }

  lemma EvaluateONPBinaryPrepend(c: Circuit, prefix: seq<NP>, path: seq<NP>, fi: FI)
    requires EvaluateONPBinaryRequirements(c, path, FItoKeys(fi))
    requires EvaluateONPBinaryRequirements(c, prefix + path, FItoKeys(fi))
    requires
      var new_p := prefix + path;
      |prefix| > 0 ==> !PathExists(c, Seq.Last(new_p), Seq.Last(prefix))
    ensures
      EvaluateONPBinary(c, path, fi) == EvaluateONPBinary(c, prefix + path, fi)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
    var nk := c.NodeKind[path[|path|-1].n];
    var head := Seq.Last(path);
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    var new_path := prefix + path;
    NextNodeInPathAndNewPathSame(c, prefix, path, inp_0);
    NextNodeInPathAndNewPathSame(c, prefix, path, inp_1);
    if inp_0 in path {
      LoopIsSame(c, prefix, path, inp_0);
      assert EvaluateONPBinary(c, path, fi) == EvaluateONPBinary(c, prefix + path, fi);
    } else if inp_1 in path {
      LoopIsSame(c, prefix, path, inp_1);
      assert EvaluateONPBinary(c, path, fi) == EvaluateONPBinary(c, prefix + path, fi);
    } else {
      NodesNotInPathDecreases(c, path, inp_0);
      NodesNotInPathDecreases(c, path, inp_1);
      var new_path_0 := path + [inp_0];
      var new_path_1 := path + [inp_1];
      assert PathValid(c, new_path_0);
      assert PathValid(c, new_path_1);
      assert (prefix + path) + [inp_0] == prefix + (path + [inp_0]);
      assert (prefix + path) + [inp_1] == prefix + (path + [inp_1]);
      assert PathValid(c, prefix + new_path_0) by {reveal PathValid();}
      assert PathValid(c, prefix + new_path_1) by {reveal PathValid();}
      assert |NodesNotInPath(c, path + [inp_0])| < |NodesNotInPath(c, path)|;
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      StillHasNoDuplicates(prefix + path, inp_0);
      StillHasNoDuplicates(prefix + path, inp_1);
      if |prefix| > 0 {
        StillNoPathExists(c, head, inp_0, Seq.Last(prefix));
        StillNoPathExists(c, head, inp_1, Seq.Last(prefix));
      }
      EvaluateINPInnerPrepend(c, prefix, path + [inp_0], fi);
      EvaluateINPInnerPrepend(c, prefix, path + [inp_1], fi);
      assert EvaluateONPBinary(c, path, fi) == EvaluateONPBinary(c, prefix + path, fi);
    }
  }

  lemma EvaluateONPUnaryPrepend(c: Circuit, prefix: seq<NP>, path: seq<NP>, fi: FI)
    requires EvaluateONPUnaryRequirements(c, path, FItoKeys(fi))
    requires EvaluateONPUnaryRequirements(c, prefix + path, FItoKeys(fi))
    requires
      var new_p := prefix + path;
      |prefix| > 0 ==> !PathExists(c, Seq.Last(new_p), Seq.Last(prefix))
    ensures
      EvaluateONPUnary(c, path, fi) == EvaluateONPUnary(c, prefix + path, fi)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var ending_set := fi.inputs.Keys + StateONPsFromSet(fi.state.Keys);
    var nk := c.NodeKind[path[|path|-1].n];
    var head := Seq.Last(path);
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    NextNodeInPathAndNewPathSame(c, prefix, path, inp_0);
    if inp_0 in path {
      LoopIsSame(c, prefix, path, inp_0);
      assert EvaluateONPUnary(c, path, fi) == EvaluateONPUnary(c, prefix + path, fi);
    } else {
      NodesNotInPathDecreases(c, path, inp_0);
      var new_path_0 := path + [inp_0];
      assert (prefix + path) + [inp_0] == prefix + (path + [inp_0]);
      assert PathValid(c, new_path_0);
      assert PathValid(c, prefix + new_path_0) by {reveal PathValid();}
      assert |NodesNotInPath(c, path + [inp_0])| < |NodesNotInPath(c, path)|;
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(prefix + path, inp_0);
      if |prefix| > 0 {
        StillNoPathExists(c, head, inp_0, Seq.Last(prefix));
      }
      EvaluateINPInnerPrepend(c, prefix, path + [inp_0], fi);
    }
  }

  lemma EvaluateINPInnerPrepend(c: Circuit, prefix: seq<NP>, path: seq<NP>, fi: FI)
    requires EvaluateINPInnerRequirements(c, path, FItoKeys(fi))
    requires EvaluateINPInnerRequirements(c, prefix + path, FItoKeys(fi))
    requires
      var new_p := prefix + path;
      |prefix| > 0 ==> !PathExists(c, Seq.Last(new_p), Seq.Last(prefix))
    ensures
      EvaluateINPInner(c, path, fi) == EvaluateINPInner(c, prefix + path, fi)
    decreases |NodesNotInPath(c, path)|, 2
  {
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in fi.inputs {
    } else {
      if head in c.PortSource {
        var onp := c.PortSource[head];
        assert ONPValid(c, onp) by {
          reveal Circuit.Valid();
        }
        NextNodeInPathAndNewPathSame(c, prefix, path, onp);
        if onp in path {
          LoopIsSame(c, prefix, path, onp);
        } else {
          reveal Circuit.Valid();
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          StillHasNoDuplicates(prefix + path, onp);
          AppendPathValid(c, path, onp);
          AppendPathValid(c, prefix + path, onp);
          assert (prefix + path) + [onp] == prefix + (path + [onp]);
          if |prefix| > 0 {
            StillNoPathExists(c, head, onp, Seq.Last(prefix));
          }
          EvaluateONPInnerPrepend(c, prefix, path + [onp], fi);
          reveal PathCaught();
        }
      } else {
      }
    }
  }


}
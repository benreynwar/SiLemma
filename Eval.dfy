module Eval {

  import opened Circ
  import opened Utils
  import opened MapFunction

  ghost predicate EvaluateConstRequirements(c: Circuit, fi: FI)
  {
    && c.Valid()
    && FICircuitValid(c, fi)
  }

  ghost predicate EvaluatePathRequirements(c: Circuit, path: seq<NP>)
  {
    && c.Valid()
    && (|path| > 0)
    && PathValid(c, path)
    && Seq.HasNoDuplicates(path)
  }

  ghost predicate EvaluateINPInnerRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    && EvaluateConstRequirements(c, fi)
    && EvaluatePathRequirements(c, path)
    && INPValid(c, Seq.Last(path))
  }

  ghost predicate EvaluateONPUnaryBinaryRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    && EvaluateConstRequirements(c, fi)
    && EvaluatePathRequirements(c, path)
    && ONPValid(c, path[|path|-1])
    && (Seq.Last(path).n !in fi.state)
    && var nk := c.NodeKind[Seq.Last(path).n];
    && (nk.CXor? || nk.CAnd? || nk.COr? || nk.CInv? || nk.CIden?)
  }

  ghost predicate EvaluateONPBinaryRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    && EvaluateConstRequirements(c, fi)
    && EvaluatePathRequirements(c, path)
    && ONPValid(c, Seq.Last(path))
    && (Seq.Last(path).n !in fi.state)
    && var nk := c.NodeKind[Seq.Last(path).n];
    && (nk.CXor? || nk.CAnd? || nk.COr?)
  }

  ghost predicate EvaluateONPUnaryRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    && EvaluateConstRequirements(c, fi)
    && EvaluatePathRequirements(c, path)
    && ONPValid(c, Seq.Last(path))
    && (Seq.Last(path).n !in fi.state)
    && var nk := c.NodeKind[Seq.Last(path).n];
    && (nk.CInv? || nk.CIden?)
  }

  ghost predicate EvaluateONPInnerRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    && EvaluateConstRequirements(c, fi)
    && EvaluatePathRequirements(c, path)
    && ONPValid(c, Seq.Last(path))
  }

  function EvaluateINPInner(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires EvaluateINPInnerRequirements(c, path, fi)
    decreases |NodesNotInPath(c, path)|, 2
  {
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in fi.inputs then
      EvalOk(fi.inputs[head])
    else
      if head in c.PortSource then
        var onp := c.PortSource[head];
        if onp in path then
          EvalError({}, {GetLoop(path, onp)})
        else
          reveal Circuit.Valid();
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          AppendPathValid(c, path, onp);
          EvaluateONPInner(c, path + [onp], fi)
      else
        EvalError({head}, {})
  }

  lemma NodesNotInPathDecreases(c: Circuit, p: seq<NP>, np: NP)
    requires c.Valid()
    requires PathValid(c, p)
    requires NPValid(c, np)
    requires
      reveal PathValid();
      |p| > 0 ==> NPsConnected(c, Seq.Last(p), np)
    requires Seq.HasNoDuplicates(p)
    requires np !in p
    ensures
      var new_p := p + [np];
      PathValid(c, new_p) &&
      (|NodesNotInPath(c, new_p)| < |NodesNotInPath(c, p)|)
  {
    reveal PathValid();
    var new_p := p + [np];
    var all_np := AllNP(c);
    var nodes_in_path := Seq.ToSet(p);
    var new_nodes_in_path := Seq.ToSet(new_p);
    reveal Seq.ToSet();
    assert new_nodes_in_path == nodes_in_path + {np};
  }

  function GetLoop(path: seq<NP>, np: NP): (loop: seq<NP>)
    requires Seq.HasNoDuplicates(path)
    requires np in path
  {
    var index := Seq.IndexOf(path, np);
    path[index..] + [np]
  }


  function EvaluateONPBinary(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires EvaluateONPBinaryRequirements(c, path, fi)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var nk := c.NodeKind[path[|path|-1].n];
    var head := Seq.Last(path);
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path then
      var loop := GetLoop(path, inp_0);
      EvalError({}, {loop})
    else if inp_1 in path then
      var loop := GetLoop(path, inp_1);
      EvalError({}, {loop})
    else
      NodesNotInPathDecreases(c, path, inp_0);
      NodesNotInPathDecreases(c, path, inp_1);
      var new_path_0 := path + [inp_0];
      var new_path_1 := path + [inp_1];
      assert PathValid(c, new_path_0);
      assert PathValid(c, new_path_1);
      assert |NodesNotInPath(c, path + [inp_0])| < |NodesNotInPath(c, path)|;
      StillHasNoDuplicates(path, inp_0);
      StillHasNoDuplicates(path, inp_1);
      var iv_0 := EvaluateINPInner(c, path + [inp_0], fi);
      var iv_1 := EvaluateINPInner(c, path + [inp_1], fi);
      match iv_0
        case EvalError(missing_0, loops_0) => (
          match iv_1
            case EvalError(missing_1, loops_1) =>
              EvalError(missing_0 + missing_1, loops_0 + loops_1)
            case EvalOk(b1) =>
              EvalError(missing_0, loops_0)
        )
        case EvalOk(b0) => (
          match iv_1
            case EvalError(missing_1, loops_1) =>
              EvalError(missing_1, loops_1)
            case EvalOk(b1) =>
              if nk.CXor? then
                EvalOk(Xor(b0, b1))
              else if nk.CAnd? then
                EvalOk(b0 && b1)
              else
                assert nk.COr?;
                EvalOk(b0 || b1)
        )
  }

  function EvaluateONPUnary(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires EvaluateONPUnaryRequirements(c, path, fi)
    requires
      var nk := c.NodeKind[Seq.Last(path).n];
      nk.CInv? || nk.CIden?
    decreases |NodesNotInPath(c, path)|, 3
  {
    var head := Seq.Last(path);
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path then
      EvalError({}, {GetLoop(path, inp_0)})
    else
      var new_path := path + [inp_0];
      AppendPathValid(c, path, inp_0);
      assert PathValid(c, new_path);
      NodesNotInPathDecreases(c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      var iv_0 := EvaluateINPInner(c, new_path, fi);
      match iv_0
        case EvalError(missing_0, loops_0) =>
          EvalError(missing_0, loops_0)
        case EvalOk(b0) =>
          var nk := c.NodeKind[head.n];
          match nk
            case CInv => EvalOk(!b0)
            case CIden => EvalOk(b0)
  }

  opaque predicate FICircuitValid(c: Circuit, fi: FI)
  {
    // It's possible a np to be in fi.inputs and a Seq sink.
    && (forall np :: np in fi.inputs.Keys ==> INPValid(c, np))
    && (forall n :: n in fi.state.Keys ==> n in c.NodeKind && c.NodeKind[n].CSeq?)
  }

  function EvaluateONPInner(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires EvaluateONPInnerRequirements(c, path, fi)
    decreases |NodesNotInPath(c, path)|, 4
  {
    var head := path[|path|-1];
    var nk := c.NodeKind[head.n];
    if head.n in fi.state then
      assert nk.CSeq? by {
        reveal FICircuitValid();
      }
      match nk
        case CSeq() => EvalOk(fi.state[head.n])
    else
      match nk
        case CXor() => EvaluateONPBinary(c, path, fi)
        case CAnd() => EvaluateONPBinary(c, path, fi)
        case COr() => EvaluateONPBinary(c, path, fi)
        case CInv() => EvaluateONPUnary(c, path, fi)
        case CIden() => EvaluateONPUnary(c, path, fi)
        case CConst(b) => EvalOk(b)
        case CSeq() => EvalError({head}, {})
  }

  lemma LengthOneNoDuplicates<X>(s: seq<X>)
    requires |s| == 1
    ensures Seq.HasNoDuplicates(s)
  {
    reveal Seq.HasNoDuplicates();
  }

  function EvaluateONP(c: Circuit, np: NP, fi: FI): EvalResult
    requires c.Valid()
    requires FICircuitValid(c, fi)
    requires ONPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    EvaluateONPInner(c, path, fi)
  }

  function EvaluateINP(c: Circuit, np: NP, fi: FI): EvalResult
    requires c.Valid()
    requires FICircuitValid(c, fi)
    requires INPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    EvaluateINPInner(c, path, fi)
  }
  
  function Evaluate(c: Circuit, np: NP, fi: FI): EvalResult
    requires c.Valid()
    requires FICircuitValid(c, fi)
    requires ONPValid(c, np) || INPValid(c, np)
  {
    if ONPValid(c, np) then
      EvaluateONP(c, np, fi)
    else
      EvaluateINP(c, np, fi)
  }


}
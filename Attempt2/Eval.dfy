module Eval {

  import opened Circ
  import opened Utils
  import opened MapFunction

  ghost predicate EvaluateINPInnerRequirements(c: Circuit, path: seq<NP>)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    INPValid(c, Seq.Last(path)) &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateINPInner(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires EvaluateINPInnerRequirements(c, path)
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
          EvalError({}, {path + [onp]})
        else
          reveal CircuitValid();
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          AppendPathValid(c, path, onp);
          EvaluateONPInner(c, path + [onp], fi)
      else
        EvalError({head}, {})
  }

  lemma NodesNotInPathDecreases(c: Circuit, p: seq<NP>, np: NP)
    requires PathValid(c, p)
    requires Seq.HasNoDuplicates(p)
    requires np !in p
    requires NPValid(c, np)
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

  ghost predicate EvaluateONPUnaryBinaryRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    ONPValid(c, path[|path|-1]) &&
    (Seq.Last(path) !in fi.inputs) &&
    var nk := c.NodeKind[Seq.Last(path).n];
    (nk.CXor? || nk.CAnd? || nk.CInv?) &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  ghost predicate EvaluateONPBinaryRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    ONPValid(c, path[|path|-1]) &&
    (Seq.Last(path) !in fi.inputs) &&
    var nk := c.NodeKind[Seq.Last(path).n];
    (nk.CXor? || nk.CAnd?) &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateONPBinary(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires CircuitValid(c)
    requires |path| > 0
    requires ONPValid(c, Seq.Last(path))
    requires Seq.Last(path) !in fi.inputs
    requires
      var nk := c.NodeKind[Seq.Last(path).n];
      nk.CXor? || nk.CAnd?
    requires PathValid(c, path)
    requires Seq.HasNoDuplicates(path)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var nk := c.NodeKind[path[|path|-1].n];
    var head := Seq.Last(path);
    assert NodeValid(c, head.n);
    var inp_0 := NP(head.n, INPUT_0);
    var inp_1 := NP(head.n, INPUT_1);
    if inp_0 in path then
      EvalError({}, {path + [inp_0]})
    else if inp_1 in path then
      EvalError({}, {path + [inp_1]})
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
              else
                EvalOk(b0 && b1)
        )
  }

  ghost predicate EvaluateONPUnaryRequirements(c: Circuit, path: seq<NP>, fi: FI)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    ONPValid(c, Seq.Last(path)) &&
    Seq.Last(path) !in fi.inputs &&
    c.NodeKind[Seq.Last(path).n].CInv? &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateONPUnary(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires EvaluateONPUnaryRequirements(c, path, fi)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var head := Seq.Last(path);
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path then
      EvalError({}, {path + [inp_0]})
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
          EvalOk(!b0)
  }

  ghost predicate EvaluateONPInnerRequirements(c: Circuit, path: seq<NP>)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    ONPValid(c, Seq.Last(path)) &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateONPInner(c: Circuit, path: seq<NP>, fi: FI): EvalResult
    requires EvaluateONPInnerRequirements(c, path)
    decreases |NodesNotInPath(c, path)|, 4
  {
    var head := path[|path|-1];
    var nk := c.NodeKind[head.n];
    if head in fi.inputs then
      match nk
        case CXor() => EvalOk(fi.inputs[head])
        case CAnd() => EvalOk(fi.inputs[head])
        case CInv() => EvalOk(fi.inputs[head])
        case CConst(b) => EvalError({head}, {})
        case CSeq() => EvalError({head}, {})
    else if head in fi.state then
      match nk
        case CXor() => EvalError({head}, {})
        case CAnd() => EvalError({head}, {})
        case CInv() => EvalError({head}, {})
        case CConst(b) => EvalError({head}, {})
        case CSeq() => EvalOk(fi.state[head])
    else
      match nk
        case CXor() => EvaluateONPBinary(c, path, fi)
        case CAnd() => EvaluateONPBinary(c, path, fi)
        case CInv() => EvaluateONPUnary(c, path, fi)
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
    requires CircuitValid(c)
    requires ONPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    EvaluateONPInner(c, path, fi)
  }

  function EvaluateINP(c: Circuit, np: NP, fi: FI): EvalResult
    requires CircuitValid(c)
    requires INPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    reveal PathValid();
    EvaluateINPInner(c, path, fi)
  }
  
  function Evaluate(c: Circuit, np: NP, fi: FI): EvalResult
    requires CircuitValid(c)
    requires ONPValid(c, np) || INPValid(c, np)
  {
    if ONPValid(c, np) then
      EvaluateONP(c, np, fi)
    else
      EvaluateINP(c, np, fi)
  }


}
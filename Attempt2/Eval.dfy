module Eval {

  import opened Circ
  import opened Utils
  import opened MapFunction

  ghost predicate EvaluateINPInnerRequirements(c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    INPValid(c, path[|path|-1]) &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateINPInner(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires EvaluateINPInnerRequirements(c, path, knowns)
    decreases |NodesNotInPath(c, path)|, 2
  {
    var head := path[|path|-1];
    var tail := path[..|path|-1];
    if head in knowns then
      EvalOk(knowns[head])
    else
      if head in c.PortSource then
        var onp := c.PortSource[head];
        if onp in path then
          EvalError({}, {path + [onp]})
        else
          NodesNotInPathDecreases(c, path, onp);
          StillHasNoDuplicates(path, onp);
          EvaluateONPInner(c, path + [onp], knowns)
      else
        EvalError({head}, {})
  }

  lemma NodesNotInPathDecreases(c: Circuit, p: seq<NP>, np: NP)
    requires PathValid(c, p)
    requires Seq.HasNoDuplicates(p)
    requires np !in p
    requires INPValid(c, np) || ONPValid(c, np)
    ensures
      var new_p := p + [np];
      |NodesNotInPath(c, new_p)| < |NodesNotInPath(c, p)|
  {
    var new_p := p + [np];
    var all_np := AllNP(c);
    var nodes_in_path := Seq.ToSet(p);
    var new_nodes_in_path := Seq.ToSet(new_p);
    reveal Seq.ToSet();
    assert new_nodes_in_path == nodes_in_path + {np};
  }

  ghost predicate EvaluateONPBinaryRequirements(c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    ONPValid(c, path[|path|-1]) &&
    path[|path|-1] !in knowns &&
    var nk := c.NodeKind[path[|path|-1].n];
    (nk.CXor? || nk.CAnd?) &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateONPBinary(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires |path| > 0
    requires ONPValid(c, path[|path|-1])
    requires path[|path|-1] !in knowns
    requires
      var nk := c.NodeKind[path[|path|-1].n];
      nk.CXor? || nk.CAnd?
    requires PathValid(c, path)
    requires Seq.HasNoDuplicates(path)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var nk := c.NodeKind[path[|path|-1].n];
    var head := path[|path|-1];
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
      var iv_0 := EvaluateINPInner(c, path + [inp_0], knowns);
      var iv_1 := EvaluateINPInner(c, path + [inp_1], knowns);
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

  ghost predicate EvaluateONPUnaryRequirements(c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    ONPValid(c, path[|path|-1]) &&
    path[|path|-1] !in knowns &&
    c.NodeKind[path[|path|-1].n].CInv? &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateONPUnary(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires EvaluateONPUnaryRequirements(c, path, knowns)
    decreases |NodesNotInPath(c, path)|, 3
  {
    var head := path[|path|-1];
    var inp_0 := NP(head.n, INPUT_0);
    if inp_0 in path then
      EvalError({}, {path + [inp_0]})
    else
      var new_path := path + [inp_0];
      assert PathValid(c, new_path);
      NodesNotInPathDecreases(c, path, inp_0);
      StillHasNoDuplicates(path, inp_0);
      var iv_0 := EvaluateINPInner(c, new_path, knowns);
      match iv_0
        case EvalError(missing_0, loops_0) =>
          EvalError(missing_0, loops_0)
        case EvalOk(b0) =>
          EvalOk(!b0)
  }

  ghost predicate EvaluateONPInnerRequirements(c: Circuit, path: seq<NP>, knowns: map<NP, bool>)
  {
    CircuitValid(c) &&
    (|path| > 0) &&
    ONPValid(c, path[|path|-1]) &&
    PathValid(c, path) &&
    Seq.HasNoDuplicates(path)
  }

  function EvaluateONPInner(c: Circuit, path: seq<NP>, knowns: map<NP, bool>): EvalResult
    requires EvaluateONPInnerRequirements(c, path, knowns)
    decreases |NodesNotInPath(c, path)|, 4
  {
    var head := path[|path|-1];
    if head in knowns then
      EvalOk(knowns[head])
    else
      var nk := c.NodeKind[head.n];
      match nk
        case CXor() => EvaluateONPBinary(c, path, knowns)
        case CAnd() => EvaluateONPBinary(c, path, knowns)
        case CInv() => EvaluateONPUnary(c, path, knowns)
        case CConst(b) => EvalOk(b)
        case CInput() => EvalError({head}, {})
        case CSeq() => EvalError({head}, {})
  }

  lemma LengthOneNoDuplicates<X>(s: seq<X>)
    requires |s| == 1
    ensures Seq.HasNoDuplicates(s)
  {
    reveal Seq.HasNoDuplicates();
  }

  function EvaluateONP(c: Circuit, np: NP, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires ONPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    EvaluateONPInner(c, path, knowns)
  }

  function EvaluateINP(c: Circuit, np: NP, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires INPValid(c, np)
  {
    var path := [np];
    LengthOneNoDuplicates(path);
    EvaluateINPInner(c, path, knowns)
  }
  
  function Evaluate(c: Circuit, np: NP, knowns: map<NP, bool>): EvalResult
    requires CircuitValid(c)
    requires ONPValid(c, np) || INPValid(c, np)
  {
    if ONPValid(c, np) then
      EvaluateONP(c, np, knowns)
    else
      EvaluateINP(c, np, knowns)
  }


}
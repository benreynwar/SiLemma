module Circ {

  import Std.Collections.Seq

  datatype CNodeKind = 
    | CXor()
    | CAnd()
    | CInv()
      // A contant 0 or 1
    | CConst(value: bool)
      // An input to the circuit.
    | CInput()
      // An output from the circuit.
    | COutput()
      // A register.
    | CSeq()

  newtype CNode = nat
  newtype CPort = nat

  const INPUT_0: CPort := 0
  const INPUT_1: CPort := 2
  const OUTPUT_0: CPort := 1

  datatype NP = NP(n: CNode, p: CPort)

  datatype Circuit = Circuit(
    NodeKind: map<CNode, CNodeKind>,
    PortSource: map<NP, NP>
  )

  predicate CircuitValid(c: Circuit)
  {
    (forall np :: np in c.PortSource.Values ==> ONPValid(c, np)) &&
    (forall np :: np in c.PortSource.Keys ==> INPValid(c, np))
  }

  function GetNewNodeInternal(c: Circuit, m: CNode, remaining_nodes: set<CNode>): (r: CNode)
    ensures r !in c.NodeKind
    requires forall n :: n in c.NodeKind && n >= m ==> n in remaining_nodes
    decreases |remaining_nodes|
  {
    if m in c.NodeKind then
      var new_remaining_nodes := remaining_nodes - {m};
      GetNewNodeInternal(c, m+1, new_remaining_nodes)
    else
      m
  }

  function GetNewNode(c: Circuit): (r: CNode)
    ensures r !in c.NodeKind
  {
    GetNewNodeInternal(c, 0, c.NodeKind.Keys)
  }

  predicate NodeValid(c: Circuit, node: CNode)
  {
    node in c.NodeKind
  }

  function AllNPfromNode(c: Circuit, node: CNode): (r: set<NP>)
    requires NodeValid(c, node)
    ensures forall np :: (INPValid(c, np) || ONPValid(c, np)) && np.n == node ==> np in r
  {
    var nk := c.NodeKind[node];
    match nk
      case CXor() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CAnd() => {NP(node, INPUT_0), NP(node, INPUT_1), NP(node, OUTPUT_0)}
      case CInv() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
      case CConst(b) => {NP(node, OUTPUT_0)}
      case CInput() => {NP(node, OUTPUT_0)}
      case COutput() => {NP(node, INPUT_0)}
      case CSeq() => {NP(node, INPUT_0), NP(node, OUTPUT_0)}
  }

  function AllNPInternal(c: Circuit, nodes: set<CNode>, nps: set<NP>): (r: set<NP>)
    requires forall n :: n in nodes ==> NodeValid(c, n)
    requires forall np :: np in nps ==> INPValid(c, np) || ONPValid(c, np)
    requires forall np :: (INPValid(c, np) || ONPValid(c, np)) && np.n !in nodes ==> np in nps
    ensures forall np :: np in r ==> INPValid(c, np) || ONPValid(c, np)
    ensures forall np :: INPValid(c, np) || ONPValid(c, np) ==> np in r
  {
    if |nodes| == 0 then
      nps
    else
      var node :| node in nodes;
      var new_nodes := nodes - {node};
      AllNPInternal(c, new_nodes, nps + AllNPfromNode(c, node))
  }

  function AllNP(c: Circuit): set<NP>
    ensures forall np :: np in AllNP(c) ==> INPValid(c, np) || ONPValid(c, np)
    ensures forall np :: INPValid(c, np) || ONPValid(c, np) ==> np in AllNP(c)
  {
    var all_nodes := (set n | n in c.NodeKind);
    AllNPInternal(c, all_nodes, {})
  }

  predicate PathValid(c: Circuit, p: seq<NP>)
  {
    forall np :: np in p ==> INPValid(c, np) || ONPValid(c, np)
  }

  ghost function NodesNotInPath(c: Circuit, p: seq<NP>): set<NP>
    requires PathValid(c, p)
  {
    var all_np := AllNP(c);
    var nodes_in_path := Seq.ToSet(p);
    var nodes_not_in_path := all_np - nodes_in_path;
    nodes_not_in_path
  }

  datatype EvalResult =
    | EvalOk(bool)
    | EvalError(missing: set<NP>, loops: set<seq<NP>>)

  predicate OutputPortValid(nk: CNodeKind, p: CPort)
  {
    match nk
      case CXor() => p == OUTPUT_0
      case CAnd() => p == OUTPUT_0
      case CInv() => p == OUTPUT_0
      case CConst(b) => p == OUTPUT_0
      case CInput() => p == OUTPUT_0
      case COutput() => false
      case CSeq() => p == OUTPUT_0
  }

  predicate InputPortValid(nk: CNodeKind, p: CPort)
  {
    match nk
      case CXor() => p == INPUT_0 || p == INPUT_1
      case CAnd() => p == INPUT_0 || p == INPUT_1
      case CInv() => p == INPUT_0
      case CConst(b) => false
      case CInput() => false
      case COutput() => p == INPUT_0
      case CSeq() => p == INPUT_0
  }

  predicate ONPValid(c: Circuit, np: NP)
  {
    np.n in c.NodeKind &&
    var nk := c.NodeKind[np.n];
    OutputPortValid(nk, np.p)
  }

  predicate INPValid(c: Circuit, np: NP)
  {
    np.n in c.NodeKind &&
    var nk := c.NodeKind[np.n];
    InputPortValid(nk, np.p)
  }

  function Xor(a: bool, b: bool): bool
  {
    (a && !b) || (!a && b)
  }

  lemma StillHasNoDuplicates<X>(s: seq<X>, x: X)
    requires Seq.HasNoDuplicates(s)
    requires x !in s
    ensures Seq.HasNoDuplicates(s + [x])
  {
    reveal Seq.HasNoDuplicates();
  }
  function Connect(c: Circuit, inp: NP, onp: NP): (r: Circuit)
    requires CircuitValid(c)
    requires INPValid(c, inp)
    requires ONPValid(c, onp)
    ensures CircuitValid(r)
  {
    var new_c := Circuit(
      c.NodeKind,
      c.PortSource[inp := onp]
    );
    assert forall np :: np in new_c.PortSource.Keys ==> (np in c.PortSource.Keys) || np == inp;
    assert forall np :: np in new_c.PortSource.Keys ==> INPValid(new_c, np);
    assert forall np :: np in new_c.PortSource.Values ==> (np in c.PortSource.Values) || np == onp;
    assert CircuitValid(new_c);
    new_c
  }

  function Replace(np: NP, f: map<NP, bool> -> bool, g: map<NP, bool> -> bool): (r: map<NP, bool> -> bool)
  {
    x =>
      var np_val := g(x);
      var new_x := x[np := np_val];
      f(new_x)
  }

  //lemma ConnectHelper(
  //    c: Circuit,
  //    o: NP,
  //    // Stuff that o depends on.
  //    o_deps: set<NP>,
  //    m: NP,
  //    // Stuff that m depends on.
  //    m_deps: set<NP>,
  //    // f maps the o_deps to o
  //    o_f: map<NP, bool> -> bool,
  //    // g maps the m_deps to m
  //    m_f: map<NP, bool> -> bool
  //    )
  //  requires CircuitValid(c)
  //  requires INPValid(c, o) || ONPValid(c, o)
  //  requires INPValid(c, m) || ONPValid(c, m)
  //  requires forall np :: np in o_deps ==> INPValid(c, np) || ONPValid(c, np)
  //  requires forall np :: np in m_deps ==> INPValid(c, np) || ONPValid(c, np)
  //  requires m in o_deps
  //  requires o !in m_deps
  //  requires m !in m_deps
  //  requires o !in o_deps
  //  requires Equiv(c, o, o_deps, o_f)
  //  requires Equiv(c, m, m_deps, m_f)
  //  ensures
  //    var new_o_f := Replace(m, o_f, m_f);
  //    var new_o_deps := o_deps - {m} + m_deps;
  //    Equiv(c, o, new_o_deps, new_o_f)
  //{
  //}

  //lemma InsertAndConversEquiv(c: Circuit, np: NP, input_nps: set<NP>, f: map<NP, bool> --> bool)
  //  requires CircuitValid(c)
  //  requires INPValid(c, np) || ONPValid(c, np)
  //  requires forall np :: np in input_nps ==> INPValid(c, np) || ONPValid(c, np)
  //  requires forall x: map<NP, bool> :: x.Keys == input_nps ==> f.requires(x)
  //  requires Equiv(c, np, input_nps, f)
  //  ensures
  //    var (new_c, (i_0, i_1), o_0, f) := InsertAnd(c);
  //    Equiv(new_c, np, input_nps, f)
  //{
  //  var (new_c, (i_0, i_1), o_0, f) := InsertAnd(c);
  //  forall knowns: map<NP, bool> | knowns.Keys == input_nps
  //    ensures Evaluate(new_c, np, knowns) == Evaluate(new_c, np, knowns);
  //  {
  //    assert Evaluate(new_c, np, knowns) == Evaluate(c, np, knowns);
  //  }
  //  assert Equiv(new_c, np, input_nps, f);
  //}

  //lemma InsertThreeAndCorrect(c: Circuit)
  //  requires CircuitValid(c)
  //  ensures
  //    var (new_c, (i_0, i_1, i_2), o_0) := InsertThreeAnd(c);
  //    var f: map<NP, bool> --> bool :=
  //      knowns requires (i_0 in knowns) && (i_1 in knowns) && (i_2 in knowns) =>
  //      knowns[i_0] && knowns[i_1] && knowns[i_2];
  //{
  //  var (new_c, (i_0, i_1, i_2), o_0) := InsertThreeAnd(c);
  //  var (c_1, (ai_0, ai_1), ao_0, a_f) := InsertAnd(c);
  //  var (c_2, (bi_0, bi_1), bo_0, b_f) := InsertAnd(c_1);
  //  assert Equiv(c_2, ao_0, {ai_0, ai_1}, a_f);
  //  assert Equiv(c_2, bo_0, {bi_0, bi_1}, b_f);
  //  var c_3 := Connect(c_2, bi_1, ao_0);
  //  assert (new_c, (i_0, i_1, i_2), o_0) == (c_3, (ai_0, ai_1, bi_0), bo_0);

  //  ////var path := [o_0];

  //  ////LengthOneNoDuplicates(path);
  //  ////assert CircuitValid(new_c);
  //  //forall iv_0: bool, iv_1: bool, iv_2: bool
  //  //  ensures EvaluateONP(new_c, o_0, map[i_0 := iv_0, i_1 := iv_1, i_2 := iv_2])
  //  //    == EvalOk(iv_0 && iv_1 && iv_2)
  //  //{
  //  //  var knowns := map[i_0 := iv_0, i_1 := iv_1, i_2 := iv_2];
  //  //  assert Seq.HasNoDuplicates(path);
  //  //  assert EvaluateONP(new_c, o_0, knowns) == EvaluateONPAnd(new_c, [o_0], knowns);
  //  //  reveal Seq.HasNoDuplicates();
  //  //  assert EvaluateINPInner(new_c, [o_0, i_0], knowns) == EvalOk(iv_0);
  //  //  assert EvaluateINPInner(new_c, [o_0, i_1], knowns) == EvalOk(iv_1);
  //  //  assert EvaluateINPInner(new_c, [o_0, i_2], knowns) == EvalOk(iv_2);
  //  //  assert EvaluateONPAnd(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
  //  //  assert EvaluateONPInner(new_c, [o_0], knowns) == EvalOk(iv_0 && iv_1);
  //  //}
  //}

}
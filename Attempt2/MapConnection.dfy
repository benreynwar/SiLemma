module MapConnection {

  import Std.Collections.Seq

  import opened MapFunction
  import opened Circ
  import opened Utils

  datatype ConnectionX<T(==)> = ConnectionX(
    in1: seq<T>,
    out: seq<T>,
    conn: seq<nat>
  )
  {
    ghost opaque predicate Valid() {
      && (|conn| == |out|)
      && (forall x :: x in conn ==> x < |in1|)
      && (forall index: nat :: index < |out| ==> conn[index] < |in1|)
      && Seq.HasNoDuplicates(conn)
      && (forall index: nat :: index < |out| ==> out[index] == in1[conn[index]])
    }

    function MapSeq(x: seq<bool>): (r: seq<bool>)
      requires |x| == |in1|
      requires Valid()
      ensures |r| == |out|
    {
      reveal Valid();
      seq(|out|, (i: nat) requires i < |out| =>
        var el := conn[i];
        x[el])
    }

    function MapMap(x: map<T, bool>): (r: map<T, bool>)
      requires x.Keys == Seq.ToSet(in1)
      requires Valid()
      ensures r.Keys == Seq.ToSet(out)
    {
      reveal Valid();
      reveal Seq.ToSet();
      (map a | a in out :: x[a])
    }

    lemma EmptyThenValid()
      requires |in1| == 0
      requires |out| == 0
      requires |conn| == 0
      ensures Valid()
    {
      reveal ConnectionX<T>.Valid();
      reveal Seq.HasNoDuplicates();
    }

  }

  datatype ConnectionXY<T(==)> = ConnectionXY(
    in1: seq<T>,
    in2: seq<T>,
    out: seq<T>,
    in1out_direct: bool,
    in2out_direct: bool,
    conn: seq<(bool, int)>
  )
  {
    ghost opaque predicate Valid() {
      && (|conn| == |out|)
      && (forall x :: x in conn && !x.0 ==> 0 <= x.1 < |in1|)
      && (forall x :: x in conn &&  x.0 ==> 0 <= x.1 < |in2|)
      //&& (forall index: nat :: index < |conn| && !conn[index].0 ==> conn[index].1 < |in1|)
      //&& (forall index: nat :: index < |conn| &&  conn[index].0 ==> conn[index].1 < |in2|)
      && Seq.HasNoDuplicates(conn)
      && Seq.HasNoDuplicates(in1)
      && Seq.HasNoDuplicates(in2)
      && Seq.HasNoDuplicates(out)
      && (forall index: nat :: index < |conn| ==> (
            var (in_type, pos) := conn[index];
            && (!in_type && in1out_direct ==> out[index] == in1[conn[index].1])
            && ( in_type && in2out_direct ==> out[index] == in2[conn[index].1])
          ))
      && (forall index_out: nat, index1: nat :: index_out < |out| && index1 < |in1| && in1out_direct
            && out[index_out] == in1[index1] ==> (conn[index_out] == (false, index1)))
      && (forall index_out: nat, index2: nat :: index_out < |out| && index2 < |in2| && in2out_direct
            && out[index_out] == in2[index2] ==> (conn[index_out] == (true, index2)))
    }

    function MapSeq(x: seq<bool>, y: seq<bool>): (r: seq<bool>)
      requires |x| == |in1|
      requires |y| == |in2|
      requires Valid()
      ensures |r| == |out|
    {
      reveal Valid();
      seq(|out|, (i: nat) requires i < |out| =>
        var el := conn[i];
        if !el.0 then x[el.1] else y[el.1])
    }

    opaque predicate MapMapCorrect(index: nat, x: map<T, bool>, y: map<T, bool>, m: map<T, bool>)
      requires x.Keys == Seq.ToSet(in1)
      requires y.Keys == Seq.ToSet(in2)
      requires Valid()
      requires index <= |out|
    {
      reveal Valid();
      reveal Seq.ToSet();
      forall ii: nat :: index <= ii < |out| ==>
        var key := out[index];
        var el := conn[index];
        var value := if !el.0 then x[in1[el.1]] else y[in2[el.1]];
        key in m && m[key] == value
    }

    opaque function MapMapInternal(index: nat, x: map<T, bool>, y: map<T, bool>): (r: map<T, bool>)
      requires x.Keys == Seq.ToSet(in1)
      requires y.Keys == Seq.ToSet(in2)
      requires Valid()
      requires index <= |out|
      ensures r.Keys == Seq.ToSet(out[index..])
      ensures MapMapCorrect(index, x, y, r)
      decreases |out| - index
    {
      reveal Seq.ToSet();
      reveal MapMapCorrect();
      reveal Seq.HasNoDuplicates();
      reveal Valid();
      assert Seq.HasNoDuplicates(out);
      if index == |out| then
        map[]
      else
        var smaller_r := MapMapInternal(index+1, x, y);
        var key := out[index];
        var el := conn[index];
        var value := if !el.0 then x[in1[el.1]] else y[in2[el.1]];
        smaller_r[key := value]
    }

    function MapMap(x: map<T, bool>, y: map<T, bool>): (r: map<T, bool>)
      requires x.Keys == Seq.ToSet(in1)
      requires y.Keys == Seq.ToSet(in2)
      requires Valid()
      ensures r.Keys == Seq.ToSet(out)
      ensures MapMapCorrect(0, x, y, r)
    {
      MapMapInternal(0, x, y)
    }

    lemma EmptyThenValid()
      requires |in1| == 0
      requires |in2| == 0
      requires |out| == 0
      requires |conn| == 0
      ensures Valid()
    {
      reveal ConnectionXY<T>.Valid();
      reveal Seq.HasNoDuplicates();
    }
  }


  ghost predicate MakeConnectionsReqs(
    mf_a: MapFunction, mf_b: MapFunction, mf_ab: MapFunction,
    abi2ai: seq<nat>,
    abiao2bi: seq<(bool, nat)>,
    aobo2abo: seq<(bool, nat)>,
    abs2as: seq<nat>,
    abs2bs: seq<nat>,
    asbs2abs: seq<(bool, nat)>
  )
  {
    && ConnectionX(mf_ab.inputs, mf_a.inputs, abi2ai).Valid()
    && ConnectionXY(mf_ab.inputs, mf_a.outputs, mf_b.inputs, true, false, abiao2bi).Valid()
    && ConnectionXY(mf_a.outputs, mf_b.outputs, mf_ab.outputs, true, true, aobo2abo).Valid()
    && ConnectionX(mf_ab.state, mf_a.state, abs2as).Valid()
    && ConnectionX(mf_ab.state, mf_b.state, abs2bs).Valid()
    && ConnectionXY(mf_a.state, mf_b.state, mf_ab.state, true, true, asbs2abs).Valid()

    && mf_a.Valid()
    && mf_b.Valid()
    && mf_ab.Valid()

  }

  function MakeConnections(
    mf_a: MapFunction, mf_b: MapFunction, mf_ab: MapFunction,
    abi2ai: seq<nat>,
    abiao2bi: seq<(bool, nat)>,
    aobo2abo: seq<(bool, nat)>,
    abs2as: seq<nat>,
    abs2bs: seq<nat>,
    asbs2abs: seq<(bool, nat)>
  ): (r: MFConnection)
    requires MakeConnectionsReqs(mf_a, mf_b, mf_ab, abi2ai, abiao2bi, aobo2abo, abs2as, abs2bs, asbs2abs)
    ensures r.SomewhatValid()
  {
    var conn := MFConnection(
      mf_a, mf_b, mf_ab,
      ConnectionX(mf_ab.inputs, mf_a.inputs, abi2ai),
      ConnectionXY(mf_ab.inputs, mf_a.outputs, mf_b.inputs, true, false, abiao2bi),
      ConnectionXY(mf_a.outputs, mf_b.outputs, mf_ab.outputs, true, true, aobo2abo),
      ConnectionX(mf_ab.state, mf_a.state, abs2as),
      ConnectionX(mf_ab.state, mf_b.state, abs2bs),
      ConnectionXY(mf_a.state, mf_b.state, mf_ab.state, true, true, asbs2abs)
    );
    assert conn.abi2ai.Valid();
    conn
  }

  datatype MFConnection = MFConnection(
    mf_a: MapFunction,
    mf_b: MapFunction,
    mf_ab: MapFunction,
    abi2ai: ConnectionX<NP>,
    abiao2bi: ConnectionXY<NP>,
    aobo2abo: ConnectionXY<NP>,
    abs2as: ConnectionX<CNode>,
    abs2bs: ConnectionX<CNode>,
    asbs2abs: ConnectionXY<CNode>
  )
  {
    ghost predicate SomewhatValid() {
      && abi2ai.in1 == mf_ab.inputs
      && abi2ai.out == mf_a.inputs
      && abi2ai.Valid()

      && abiao2bi.in1 == mf_ab.inputs
      && abiao2bi.in2 == mf_a.outputs
      && abiao2bi.out == mf_b.inputs
      && abiao2bi.in1out_direct
      && !abiao2bi.in2out_direct
      && abiao2bi.Valid()

      && aobo2abo.in1 == mf_a.outputs
      && aobo2abo.in2 == mf_b.outputs
      && aobo2abo.in1out_direct
      && aobo2abo.in2out_direct
      && aobo2abo.out == mf_ab.outputs
      && aobo2abo.Valid()

      && abs2as.in1 == mf_ab.state
      && abs2as.out == mf_a.state
      && abs2as.Valid()

      && abs2bs.in1 == mf_ab.state
      && abs2bs.out == mf_b.state
      && abs2bs.Valid()

      && asbs2abs.in1 == mf_a.state
      && asbs2abs.in2 == mf_b.state
      && asbs2abs.out == mf_ab.state
      && asbs2abs.in1out_direct
      && asbs2abs.in2out_direct
      && asbs2abs.Valid()

      && mf_a.Valid()
      && mf_b.Valid()
      && mf_ab.Valid()

    }

    predicate ABValid()
      requires SomewhatValid()
    {
      && (Seq.ToSet(mf_ab.state) == Seq.ToSet(mf_a.state) + Seq.ToSet(mf_b.state))
      && (Seq.ToSet(mf_ab.inputs) == Seq.ToSet(mf_a.inputs) + (Seq.ToSet(mf_b.inputs) - GetConnection().Keys))
      && (Seq.ToSet(mf_ab.outputs) <= Seq.ToSet(mf_a.outputs) + Seq.ToSet(mf_b.outputs))
    }

    ghost predicate Valid() {
      && SomewhatValid()
      && ABValid()
      && SeqEvaluatesCorrectly()
    }

    //lemma SeqEvaluatesCorrectlyToEvaluatesCorrectly()
    //  requires SomewhatValid()
    //  requires SeqEvaluatesCorrectly()
    //  ensures EvaluatesCorrectly()
    //{
    //  forall fi: FI | FIValid(fi, mf_ab.inputs, mf_ab.state)
    //  {
    //    var si := mf_ab.fi2si(fi);
    //    assert SIValid(si, mf_ab.inputs, mf_ab.state);
    //    reveal mf_ab.Valid();
    //    assert SeqEvaluateSeparately(si) == mf_ab.sf(si) by {
    //      reveal SeqEvaluatesCorrectly();
    //    }
    //    assert EvaluateSeparately(fi) == mf_ab.f(fi);
    //  }
    //}

    ghost opaque predicate EvaluatesCorrectly()
      requires SomewhatValid()
    {
      reveal MapFunction.Valid();
      forall fi: FI :: FIValid(fi, mf_ab.inputs, mf_ab.state) ==> EvaluateSeparately(fi) == mf_ab.f(fi)
    }

    lemma LemmaEvaluatesCorrectly()
      requires Valid()
      ensures EvaluatesCorrectly()
    {
      reveal SeqEvaluatesCorrectly();
      reveal EvaluatesCorrectly();
      forall fi: FI | FIValid(fi, mf_ab.inputs, mf_ab.state)
        ensures EvaluateSeparately(fi) == mf_ab.f(fi)
      {
        var si := mf_ab.fi2si(fi);
        assert fi == mf_ab.si2fi(si) by {
          mf_ab.fi2si2fi(fi);
        }
        reveal mf_ab.Valid();
        assert SeqEvaluateSeparately(si) == mf_ab.sf(si);
        var si_a := si2sia(si);
        var si_b := si2sib(si);
        var so_a := mf_a.sf(si_a);
        var so_b := mf_b.sf(si_b);
        var so := soasob2so(so_a, so_b);
        assert so == mf_ab.sf(si);

        var fi_a := fi2fia(fi);
        var fi_b := fi2fib(fi);
        var fo_a := mf_a.f(fi_a);
        var fo_b := mf_b.f(fi_b);
        var fo := foafob2fo(fo_a, fo_b);
        assert EvaluateSeparately(fi) == fo;

        assert fi_a == mf_a.si2fi(si_a);

        assert so_a == mf_a.fo2so(fo_a) by {
          assert fi_a == mf_a.si2fi(si_a);
          calc {
            mf_a.fo2so(fo_a);
            mf_a.fo2so(mf_a.f(fi_a));
            mf_a.fo2so(mf_a.so2fo(mf_a.sf(mf_a.fi2si(fi_a))));
            {mf_a.so2fo2so(mf_a.sf(mf_a.fi2si(fi_a)));}
            (mf_a.sf(mf_a.fi2si(fi_a)));
            {mf_a.si2fi2si(si_a);}
            (mf_a.sf(si_a));
            so_a;
          }
        }

        assert so_b == mf_b.fo2so(fo_b) by {
          assert fi_b == mf_b.si2fi(si_b);
          calc {
            mf_b.fo2so(fo_b);
            mf_b.fo2so(mf_b.f(fi_b));
            mf_b.fo2so(mf_b.so2fo(mf_b.sf(mf_b.fi2si(fi_b))));
            {mf_b.so2fo2so(mf_b.sf(mf_b.fi2si(fi_b)));}
            (mf_b.sf(mf_b.fi2si(fi_b)));
            {mf_b.si2fi2si(si_b);}
            (mf_b.sf(si_b));
            so_b;
          }
        }

        calc {
          EvaluateSeparately(fi);
          foafob2fo(fo_a, fo_b);
          mf_ab.so2fo(soasob2so(mf_a.fo2so(fo_a), mf_b.fo2so(fo_b)));
          {
            assert so_a == mf_a.fo2so(fo_a);
            assert so_b == mf_b.fo2so(fo_b);
          }
          mf_ab.so2fo(soasob2so(so_a, so_b));
          mf_ab.so2fo(so);
          mf_ab.so2fo(mf_ab.sf(si));
          {
            assert si == mf_ab.fi2si(fi);
            reveal mf_ab.Valid();
          }
          mf_ab.so2fo(mf_ab.sf(mf_ab.fi2si(fi)));
          {reveal mf_ab.Valid();}
          mf_ab.f(fi);
        }
      }
    }

    function EvaluateSeparately(fi: FI): (fo: FO)
      requires SomewhatValid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      ensures FOValid(fo, mf_ab.outputs, mf_ab.state)
    {
      reveal MapFunction.Valid();
      var fi_a := fi2fia(fi);
      var fi_b := fi2fib(fi);
      var fo_a := mf_a.f(fi_a);
      var fo_b := mf_b.f(fi_b);
      var fo := foafob2fo(fo_a, fo_b);
      fo
    }

    ghost opaque predicate SeqEvaluatesCorrectly()
      requires SomewhatValid()
    {
      reveal MapFunction.Valid();
      forall si: SI :: SIValid(si, mf_ab.inputs, mf_ab.state) ==> SeqEvaluateSeparately(si) == mf_ab.sf(si)
    }

    function SeqEvaluateSeparately(si: SI): (so: SO)
      requires SomewhatValid()
      requires SIValid(si, mf_ab.inputs, mf_ab.state)
      ensures SOValid(so, mf_ab.outputs, mf_ab.state)
    {
      reveal MapFunction.Valid();
      var si_a := si2sia(si);
      var si_b := si2sib(si);
      var so_a := mf_a.sf(si_a);
      var so_b := mf_b.sf(si_b);
      var so := soasob2so(so_a, so_b);
      so
    }

    function GetConnectionInternal(start: nat): (r: map<NP, NP>)
      requires SomewhatValid()
      requires start <= |mf_b.inputs|
      ensures r.Keys == Seq.ToSet(mf_b.inputs[start..]) - Seq.ToSet(mf_ab.inputs)
      ensures r.Values <= Seq.ToSet(mf_a.outputs)
      ensures ConnectionCorrect(r)
      decreases |mf_b.inputs| - start
    {
      reveal ConnectionX<NP>.Valid();
      reveal ConnectionXY<NP>.Valid();
      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
      reveal ConnectionCorrect();
      if start == |mf_b.inputs| then
        map[]
      else
        var smaller_m := GetConnectionInternal(start+1);
        var el := abiao2bi.conn[start];
        if el.0 then
          var new_key := mf_b.inputs[start];
          var new_value := mf_a.outputs[el.1];
          assert ConnectionKeyValueCorrect(new_key, new_value);
          smaller_m[new_key := new_value]
        else
          smaller_m
    }

    predicate ConnectionKeyValueCorrect(np: NP, onp: NP)
    {
        && (np in mf_b.inputs)
        && (onp in mf_a.outputs)
        && var index_out := Seq.IndexOf(mf_b.inputs, np);
        && var index_in2 := Seq.IndexOf(mf_a.outputs, onp);
        && (index_out < |abiao2bi.conn|)
        && (abiao2bi.conn[index_out] == (true, index_in2))
    }

    opaque predicate ConnectionCorrect(connection: map<NP, NP>)
      requires SomewhatValid()
    {
      forall np :: np in connection ==>
        var onp := connection[np];
        ConnectionKeyValueCorrect(np, onp)
    }

    function {:vcs_split_on_every_assert} GetConnection(): (r: map<NP, NP>)
      requires SomewhatValid()
      ensures r.Values <= Seq.ToSet(mf_a.outputs)
      ensures r.Keys == Seq.ToSet(mf_b.inputs) - Seq.ToSet(mf_ab.inputs)
      ensures ConnectionCorrect(r)
    {
      GetConnectionInternal(0)
    }

    function fi2fia(fi: FI): (fi_a: FI)
      requires SomewhatValid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      ensures FIValid(fi_a, mf_a.inputs, mf_a.state)
    {
      var si := mf_ab.fi2si(fi);
      var si_a := si2sia(si);
      var fi_a := mf_a.si2fi(si_a);
      fi_a
      //FI(abi2ai.MapMap(fi.inputs), abs2as.MapMap(fi.state))
    }

    function si2sia(si: SI): (si_a: SI)
      requires SomewhatValid()
      requires SIValid(si, mf_ab.inputs, mf_ab.state)
      ensures SIValid(si_a, mf_a.inputs, mf_a.state)
    {
      reveal MapFunction.Valid();
      mf_a.InputsHasNoDuplicates();
      SI(abi2ai.MapSeq(si.inputs), abs2as.MapSeq(si.state))
    }

    function fi2fib(fi: FI): (fi_b: FI)
      requires SomewhatValid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      ensures FIValid(fi_b, mf_b.inputs, mf_b.state)
    {
      reveal MapFunction.Valid();
      reveal ConnectionX<CNode>.Valid();
      var si := mf_ab.fi2si(fi);
      var si_b := si2sib(si);
      var fi_b := mf_b.si2fi(si_b);
      fi_b
    }

    lemma fi2fiaInfo(fi: FI)
      requires SomewhatValid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      ensures
        var fi_a := fi2fia(fi);
        && (forall np :: np in fi_a.inputs && np in fi.inputs ==> fi.inputs[np] == fi_a.inputs[np])
        && (forall n :: n in fi_a.state && n in fi.state ==> fi.state[n] == fi_a.state[n])
    {
      var fi_a := fi2fia(fi);
      forall np | np in fi_a.inputs && np in fi.inputs
        ensures fi.inputs[np] == fi_a.inputs[np]
      {
        reveal abi2ai.Valid();
        reveal Seq.ToSet();
        reveal MapMatchesSeqs();
      }
      forall n | n in fi_a.state && n in fi.state
        ensures fi.state[n] == fi_a.state[n]
      {
        reveal abs2as.Valid();
        reveal Seq.ToSet();
        reveal MapMatchesSeqs();
      }
    }

    lemma foafob2foInfo(fi: FI)
      requires SomewhatValid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      ensures
        var fi_a := fi2fia(fi);
        var fi_b := fi2fib(fi);
        var fo_a := mf_a.f(fi_a);
        var fo_b := mf_b.f(fi_b);
        var fo := foafob2fo(fo_a, fo_b);
        && (forall np :: np in fo_a.outputs && np in fo.outputs ==> fo.outputs[np] == fo_a.outputs[np])
        && (forall n :: n in fo_a.state && n in fo.state ==> fo.state[n] == fo_a.state[n])
        && (forall np :: np in fo_b.outputs && np in fo.outputs ==> fo.outputs[np] == fo_b.outputs[np])
        && (forall n :: n in fo_b.state && n in fo.state ==> fo.state[n] == fo_b.state[n])
    {
      var fi_a := fi2fia(fi);
      var fi_b := fi2fib(fi);
      var fo_a := mf_a.f(fi_a);
      var fo_b := mf_b.f(fi_b);
      var fo := foafob2fo(fo_a, fo_b);
      reveal aobo2abo.Valid();
      reveal Seq.ToSet();
      reveal MapMatchesSeqs();
    }

    lemma fi2fibInfo(fi: FI)
      requires SomewhatValid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      ensures
        var fi_b := fi2fib(fi);
        && (forall np :: np in fi_b.inputs && np in fi.inputs ==> fi.inputs[np] == fi_b.inputs[np])
        && (forall n :: n in fi_b.state && n in fi.state ==> fi.state[n] == fi_b.state[n])
    {
      var fi_b := fi2fib(fi);
      forall np | np in fi_b.inputs && np in fi.inputs
        ensures fi.inputs[np] == fi_b.inputs[np]
      {
        reveal abiao2bi.Valid();
        reveal Seq.ToSet();
        reveal MapMatchesSeqs();
      }
      forall n | n in fi_b.state && n in fi.state
        ensures fi.state[n] == fi_b.state[n]
      {
        reveal abs2bs.Valid();
        reveal Seq.ToSet();
        reveal MapMatchesSeqs();
      }
    }

    lemma ConnectionInfo(fi: FI, np: NP)
      requires SomewhatValid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      requires np in mf_b.inputs
      requires np !in mf_ab.inputs
      ensures
        var fi_a := fi2fia(fi);
        var fi_b := fi2fib(fi);
        var connection := GetConnection();
        && np in connection
        && var onp := connection[np];
        && (onp in mf_a.f(fi_a).outputs)
        && (fi_b.inputs[np] == mf_a.f(fi_a).outputs[onp])
    {
      var fi_a := fi2fia(fi);
      var fi_b := fi2fib(fi);
      reveal Seq.ToSet();
      var connection := GetConnection();
      assert connection.Keys == Seq.ToSet(mf_b.inputs) - Seq.ToSet(mf_ab.inputs);
      assert connection.Values <= Seq.ToSet(mf_a.outputs);
      var onp := connection[np];
      var si := mf_ab.fi2si(fi);
      var si_a := si2sia(si);
      assert fi_a == mf_a.si2fi(si_a);
      reveal mf_a.Valid();
      var so_a := mf_a.sf(si_a);
      assert onp in connection.Values;
      assert onp in mf_a.outputs;
      var index_in2 := Seq.IndexOf(mf_a.outputs, onp);
      var index_out := Seq.IndexOf(mf_b.inputs, np);
      reveal MapMatchesSeqs();
      reveal ConnectionCorrect();
      assert abiao2bi.conn[index_out] == (true, index_in2);
      calc {
        mf_a.f(fi_a);
        mf_a.f(fi_a);
        mf_a.so2fo(mf_a.sf(mf_a.fi2si(fi_a)));
        {
          assert fi_a == mf_a.si2fi(si_a);
          mf_a.si2fi2si(si_a);
        }
        mf_a.so2fo(mf_a.sf(si_a));
      }
    }

    function si2sib(si: SI): (si_b: SI)
      requires SomewhatValid()
      requires SIValid(si, mf_ab.inputs, mf_ab.state)
      ensures SIValid(si_b, mf_b.inputs, mf_b.state)
    {
      reveal MapFunction.Valid();
      mf_b.InputsHasNoDuplicates();
      reveal ConnectionX<CNode>.Valid();
      reveal Seq.HasNoDuplicates();
      var si_a := si2sia(si);
      var so_a := mf_a.sf(si_a);
      assert abs2bs.Valid();
      assert |si.state| == |mf_ab.state|;
      SI(abiao2bi.MapSeq(si.inputs, so_a.outputs), abs2bs.MapSeq(si.state))
    }

    function foafob2fo(fo_a: FO, fo_b: FO): (fo: FO)
      requires SomewhatValid()
      requires FOValid(fo_a, mf_a.outputs, mf_a.state)
      requires FOValid(fo_b, mf_b.outputs, mf_b.state)
      ensures FOValid(fo, mf_ab.outputs, mf_ab.state)
    {
      var so_a := mf_a.fo2so(fo_a);
      var so_b := mf_b.fo2so(fo_b);
      var so := soasob2so(so_a, so_b);
      var fo := mf_ab.so2fo(so);
      fo
    }

    function soasob2so(so_a: SO, so_b: SO): (so: SO)
      requires SomewhatValid()
      requires SOValid(so_a, mf_a.outputs, mf_a.state)
      requires SOValid(so_b, mf_b.outputs, mf_b.state)
      ensures SOValid(so, mf_ab.outputs, mf_ab.state)
    {
      mf_ab.OutputsHasNoDuplicates();
      reveal mf_ab.Valid();
      SO(aobo2abo.MapSeq(so_a.outputs, so_b.outputs), asbs2abs.MapSeq(so_a.state, so_b.state))
    }

    lemma MFABMFAConsistentOutputs(fi: FI, np: NP)
      requires Valid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      requires np in mf_a.outputs
      requires np in mf_ab.outputs
      ensures 
        var fi_1 := fi2fia(fi);
        MFLookupOutput(mf_a, fi_1, np) == MFLookupOutput(mf_ab, fi, np)
    {
      var fi_1 := fi2fia(fi);
      var fo_1 := mf_a.f(fi_1);
      var fi_2 := fi2fib(fi);
      var fo_2 := mf_b.f(fi_2);
      var fo := mf_ab.f(fi);
      LemmaEvaluatesCorrectly();
      assert EvaluateSeparately(fi) == mf_ab.f(fi) by {
        reveal EvaluatesCorrectly();
      }
      assert fo == foafob2fo(fo_1, fo_2);
      reveal Seq.ToSet();
      assert np in fo_1.outputs;
      assert np in fo.outputs;
      assert fo_1.outputs[np] == fo.outputs[np] by {
        foafob2foInfo(fi);
      }
    }

    lemma MFABMFAConsistentState(fi: FI, np: NP)
      requires Valid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      requires np in StateINPs(mf_a.state)
      requires np in StateINPs(mf_ab.state)
      ensures 
        var fi_1 := fi2fia(fi);
        MFLookupState(mf_a, fi_1, np) == MFLookupState(mf_ab, fi, np)
    {
      var fi_1 := fi2fia(fi);
      var fo_1 := mf_a.f(fi_1);
      var fi_2 := fi2fib(fi);
      var fo_2 := mf_b.f(fi_2);
      var fo := mf_ab.f(fi);
      LemmaEvaluatesCorrectly();
      assert EvaluateSeparately(fi) == mf_ab.f(fi) by {
        reveal EvaluatesCorrectly();
      }
      assert fo == foafob2fo(fo_1, fo_2);
      reveal Seq.ToSet();
      assert np.n in fo_1.state;
      assert np.n in fo.state;
      assert fo_1.state[np.n] == fo.state[np.n] by {
        foafob2foInfo(fi);
      }
      assert MFLookupState(mf_a, fi_1, np) == fo_1.state[np.n];
      assert MFLookupState(mf_ab, fi, np) == fo.state[np.n];
    }

    lemma MFABMFBConsistentOutputs(fi: FI, np: NP)
      requires Valid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      requires np in mf_b.outputs
      requires np in mf_ab.outputs
      ensures 
        var fi_2 := fi2fib(fi);
        MFLookupOutput(mf_b, fi_2, np) == MFLookupOutput(mf_ab, fi, np)
    {
      var fi_1 := fi2fia(fi);
      var fo_1 := mf_a.f(fi_1);
      var fi_2 := fi2fib(fi);
      var fo_2 := mf_b.f(fi_2);
      var fo := mf_ab.f(fi);
      LemmaEvaluatesCorrectly();
      assert EvaluateSeparately(fi) == mf_ab.f(fi) by {
        reveal EvaluatesCorrectly();
      }
      assert fo == foafob2fo(fo_1, fo_2);
      reveal Seq.ToSet();
      assert np in fo_2.outputs;
      assert np in fo.outputs;
      assert fo_2.outputs[np] == fo.outputs[np] by {
        foafob2foInfo(fi);
      }
    }

    lemma MFABMFBConsistentState(fi: FI, np: NP)
      requires Valid()
      requires FIValid(fi, mf_ab.inputs, mf_ab.state)
      requires np in StateINPs(mf_b.state)
      requires np in StateINPs(mf_ab.state)
      ensures 
        var fi_2 := fi2fib(fi);
        MFLookupState(mf_b, fi_2, np) == MFLookupState(mf_ab, fi, np)
    {
      var fi_1 := fi2fia(fi);
      var fo_1 := mf_a.f(fi_1);
      var fi_2 := fi2fib(fi);
      var fo_2 := mf_b.f(fi_2);
      var fo := mf_ab.f(fi);
      LemmaEvaluatesCorrectly();
      assert EvaluateSeparately(fi) == mf_ab.f(fi) by {
        reveal EvaluatesCorrectly();
      }
      assert fo == foafob2fo(fo_1, fo_2);
      reveal Seq.ToSet();
      assert np.n in fo_2.state;
      assert np.n in fo.state;
      assert fo_2.state[np.n] == fo.state[np.n] by {
        foafob2foInfo(fi);
      }
      assert MFLookupState(mf_b, fi_2, np) == fo_2.state[np.n];
      assert MFLookupState(mf_ab, fi, np) == fo.state[np.n];
    }

  }

}
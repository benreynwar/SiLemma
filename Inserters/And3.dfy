module Inserters.And3{

  import opened Std.Wrappers

  import opened Circ
  import opened Eval
  import opened ConservedSubcircuit
  import opened Utils
  import opened Entity
  import opened MapFunction
  import opened ConnectionEval
  import opened Connection
  import opened IslandBundle
  import opened Subcircuit
  import opened MapConnection

  import opened And

  function InsertAnd3Impl(c: Circuit): (r: (Circuit, Entity))
    requires c.Valid()
    ensures r.0.Valid()
    ensures EntityValid(r.0, r.1)
  {
    reveal SimpleInsertion();

    var eb1 := IslandBundleFromCircuit(c);
    var (c1, e1) := InsertAnd(c);
    var (eb2, a_ref) := AddEntity(eb1, c1, e1);
    assert e1.sc == {e1.mf.outputs[0].n};
    assert EntityValid(c1, e1);

    assert e1 == eb2.es[a_ref].value;

    var (c2, e2) := InsertAnd(c1);
    var (eb3, b_ref) := AddEntity(eb2, c2, e2);
    assert e2.sc == {e2.mf.outputs[0].n};

    assert e1 == eb3.es[a_ref].value;
    assert EntityValid(eb3.c, e1) && IsIsland(eb3.c, e1.sc) by {
      reveal IslandBundleValid();
    }

    var a_i0 := e1.mf.inputs[0];
    var a_i1 := e1.mf.inputs[1];
    var a_o := e1.mf.outputs[0];

    var b_i0 := e2.mf.inputs[0];
    var b_i1 := e2.mf.inputs[1];
    var b_o := e2.mf.outputs[0];

    var i0 := a_i0;
    var i1 := a_i1;
    var i2 := b_i0;
    var o := b_o;

    var combined_inputs := [i0, i1, i2];
    var combined_outputs := [o];

    var combined_mf := MapFunction(combined_inputs, combined_outputs, [],
      (si: SI) requires SIValid(si, combined_inputs, []) =>
      reveal Seq.ToSet();
      SO([si.inputs[0] && si.inputs[1] && si.inputs[2]], [])
    );
    assert combined_mf.Valid() by {
      reveal Seq.ToSet();
      reveal Seq.HasNoDuplicates();
      reveal MapFunction.Valid();
    }
    var combined_e := Entity(e1.sc + e2.sc, combined_mf);

    var abiaobi: seq<(bool, nat)> := [(false, 2), (true, 0)];
    var aoboabo: seq<(bool, nat)> := [(true, 0)];
    assert MakeConnectionsReqs(e1.mf, e2.mf, combined_mf, [0, 1], abiaobi, aoboabo, [], [], []) by {
      reveal Seq.HasNoDuplicates();
      reveal ConnectionX<NP>.Valid();
      reveal ConnectionX<CNode>.Valid();
      reveal ConnectionXY<NP>.Valid();
      reveal ConnectionXY<CNode>.Valid();
    }
    var conn := MakeConnections(e1.mf, e2.mf, combined_mf, [0, 1], abiaobi, aoboabo, [], [], []);
    assert conn.SomewhatValid();
    assert conn.Valid() by {
      reveal Seq.HasNoDuplicates();
      reveal MapFunction.Valid();
      reveal Seq.ToSet();
      reveal conn.SeqEvaluatesCorrectly();
    }

    IsIslandInputsNotInPortSource(eb3.c, e2);
    assert ConnectEntitiesRequirements(eb3.c, e1, e2, combined_e, conn);
    var (eb4, ab_ref) := IBConnectEntities(eb3, a_ref, b_ref, combined_e, conn);
    var e_ab := eb4.es[ab_ref].value;
    assert eb4.es == [None, None, Some(e_ab)];

    assert IsIsland(eb4.c, e_ab.sc) by {
      reveal IslandBundleValid();
    }
    assert IsIsland(eb4.c, e_ab.sc);
    IsIslandNoOutputs(eb4.c, e_ab.sc);
    (eb4.c, e_ab)
  }

}
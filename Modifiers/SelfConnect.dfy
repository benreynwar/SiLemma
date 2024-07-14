module Modifiers.Connect {

  import opened Circ
  import opened ConservedSubcircuit
  import opened Scuf
  import opened MapConnection
  import opened MapFunction
  import opened Eval
  import opened Connection
  import opened Utils
  import opened Subcircuit
  import opened SelfConnect
  import opened SelfConnectEval

  function ConnectInserter(c: Circuit, z: ScufInserter, conn: InternalConnection): (r: (Circuit, Scuf))
    requires c.Valid()
    requires z.Valid()
    requires conn.Valid()
    requires InserterConnectionConsistent(z, conn)
    ensures
      var (new_c, new_s) := r;
      && new_c.Valid()
      && new_s.Valid(new_c)
      && SimpleInsertion(c, new_c, new_s)
  {
    z.ValidForCircuit(c);
    var (c1, s) := z.fn(c);
    z.FnOutputsValid(c);
    assert ScufConnectionConsistent(c1, s, conn) by {
      reveal InserterConnectionConsistent();
    }
    assert MPConnectionConsistent(s.mp, conn) by {
      reveal ScufConnectionConsistent();
    }
    var (new_c, new_s) := ConnectCircuitScuf(c1, s, conn);
    reveal SimpleInsertion();
    assert new_c.Valid();
    assert new_s.Valid(new_c);
    assert IsIsland(new_c, new_s.sc);
    ConnectCircuitScufCircuitUnconnected(c, c1, s, conn);
    assert CircuitUnconnected(c, new_c);
    ConnectCircuitScufCircuitConserved(c, c1, s, conn);
    assert CircuitConserved(c, new_c);
    assert (new_c.NodeKind.Keys == c.NodeKind.Keys + new_s.sc);
    assert (c.NodeKind.Keys !! new_s.sc);
    (new_c, new_s)
  }

  opaque function ConnectModifier(z: ScufInserter, conn: InternalConnection): (new_z: ScufInserter)
    requires z.Valid()
    requires conn.Valid()
    requires InserterConnectionConsistent(z, conn)
    ensures new_z.Valid()
    ensures
      && z.uf.Valid()
      && new_z.uf.Valid()
      && UFConnectionConsistent(z.uf, conn)
      && new_z.uf == ConnectUpdateFunction(z.uf, conn)
  {
    reveal ScufInserter.Valid();
    reveal InserterConnectionConsistent();
    var uf := ConnectUpdateFunction(z.uf, conn);
    var new_z := ScufInserter(
      uf,
      (c: Circuit) requires c.Valid() => ConnectInserter(c, z, conn)
    );
    assert new_z.Valid() by {
      assert new_z.uf.Valid();
      forall c: Circuit | c.Valid()
        ensures new_z.SpecificValid(c) 
      {
        assert new_z.fn.requires(c);
        var (new_c, e) := new_z.fn(c);
        assert (e.uf == new_z.uf);
        assert SimpleInsertion(c, new_c, e);
      }
    }
    new_z
  }
}
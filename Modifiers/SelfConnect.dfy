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

  function {:vcs_split_on_every_assert} ConnectInserter(c: Circuit, z: ScufInserter, conn: InternalConnection): (r: (Circuit, Scuf))
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
    //var connection := conn.GetConnection(s.mp);
    //conn.GetConnectionProperties(c1, s);
    //assert ConnectCircuitRequirements(c1, connection);
    var (new_c, new_s) := ConnectCircuitScuf(c1, s, conn);
    assert new_s.Valid(new_c) by {
      assert new_s.MapValid();
      assert new_s.SomewhatValid(new_c);
      assert new_s.EvaluatesCorrectly(new_c) by {
        //reveal ScValid();
        //ScufFOutputsAreValid(c, this);
        //reveal Seq.ToSet();
        forall fi: FI | FIValid(fi, new_s.mp.inputs, new_s.mp.state) {
          assert FICircuitValid(new_c, fi) by {ScufValidFiValidToFICircuitValid(new_c, new_s, fi);}
          forall np | np in Seq.ToSet(new_s.mp.outputs) || np in StateINPs(new_s.mp.state) {
            assert Evaluate(new_c, np, fi) == EvalOk(MFLookup(new_s, fi, np));
          }
        }
      }
    }
    (new_c, new_s)
  }

  function ConnectModifier(z: ScufInserter, conn: InternalConnection): (new_z: ScufInserter)
    requires z.Valid()
    requires conn.Valid()
    requires InserterConnectionConsistent(z, conn)
    ensures new_z.Valid()
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
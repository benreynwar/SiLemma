module Modifiers.SwitchUF {

  import opened Circ
  import opened Scuf
  import opened MapFunction
  import opened ConservedSubcircuit

  function SwitchUFInserter(c: Circuit, z: ScufInserter, uf: UpdateFunction): (r: (Circuit, Scuf))
    requires c.Valid()
    requires z.Valid()
    requires uf.Valid()
    requires
      reveal ScufInserter.Valid();
      UpdateFunctionsEquiv(uf, z.uf)
    ensures
      var (new_c, new_s) := r;
      && new_c.Valid()
      && new_s.Valid(new_c)
      && SimpleInsertion(c, new_c, new_s)
  {
    reveal UpdateFunctionsEquiv();
    reveal ScufInserter.Valid();
    reveal SimpleInsertion();
    var (new_c, s) := z.fn(c);
    var new_s := Scuf(s.sc, s.mp, uf);
    assert new_s.Valid(new_c) by {
      reveal Scuf.SomewhatValid();
      assert new_s.SomewhatValid(new_c);
      assert new_s.SomewhatValidRelaxInputs(new_c) by {
        new_s.SomewhatValidToRelaxInputs(new_c);
      }
      assert new_s.EvaluatesCorrectly(new_c) by {
        reveal Scuf.EvaluatesCorrectly();
      }
    }
    (new_c, new_s)
  }

  function SwitchUFModifier(z: ScufInserter, uf: UpdateFunction): (r: ScufInserter)
    requires z.Valid()
    requires uf.Valid()
    requires
      reveal ScufInserter.Valid();
      UpdateFunctionsEquiv(uf, z.uf)
    ensures r.Valid()
  {
    reveal ScufInserter.Valid();
    var new_z := ScufInserter(
      uf,
      (c: Circuit) requires c.Valid() => SwitchUFInserter(c, z, uf)
    );
    new_z
  }

}
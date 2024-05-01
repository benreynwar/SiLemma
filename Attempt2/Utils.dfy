module Utils {

  predicate SetsNoIntersection<T>(a: set<T>, b: set<T>)
  {
    forall x :: !(x in a && x in b)
  }
    
  function ExtractMap<T, U>(a: map<T, U>, k: set<T>): (r: map<T, U>)
    requires forall x :: x in k ==> x in a
    ensures r.Keys == k
    ensures forall x :: x in k ==> r[x] == a[x]
  {
    (map x | x in k :: a[x])
  }

  function CombineSets<T>(sc1: set<T>, sc2: set<T>): (r: set<T>)
    requires SetsNoIntersection(sc1, sc2)
  {
    sc1 + sc2
  }

  function AddMaps<T, U>(a: map<T, U>, b: map<T, U>): (r: map<T, U>)
    requires SetsNoIntersection(a.Keys, b.Keys)
    ensures r.Keys == a.Keys + b.Keys
    ensures forall x :: x in a ==> r[x] == a[x]
    ensures forall x :: x in b ==> r[x] == b[x]
    decreases |b|
  {
    if |b| == 0 then
      a
    else
      var x :| x in b;
      var new_a := a[x := b[x]];
      var new_b := b - {x};
      AddMaps(new_a, new_b)
  }


}
include "router.dfy"

type Noc = seq<seq<Router>>

ghost predicate Valid(n: Noc)
{
  && |n| >= 2
  && (forall i :: 0 <= i < |n| ==> |n[i]| == |n|)
  && (forall i, j :: 0 <= i < |n| && 0 <= j < |n| ==> n[i][j].id == i*|n| + j)
}

ghost predicate containsId(n: Noc, id: Id)
  requires Valid(n)
{
  exists i, j :: n[i][j].id == id
}
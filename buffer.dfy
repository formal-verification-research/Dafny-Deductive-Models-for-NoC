include "flit.dfy"

datatype buffer =
  | Node(dest: nat, next: buffer)
  | None
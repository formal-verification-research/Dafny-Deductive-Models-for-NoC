include "flit.dfy"

datatype Buffer =
  | Node(dest: nat, next: Buffer)
  | None
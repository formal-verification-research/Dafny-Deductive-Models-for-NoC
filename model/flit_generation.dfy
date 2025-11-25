include "flit.dfy"

method discrete_uniform(min: int, max: int) returns (val: int)
  requires min <= max 
  ensures {:axiom} min <= val <= max

method generate_flits(this_id: nat, max_id: nat) returns (f: Flit)
  requires 0 <= this_id <= max_id
  requires 1 <= max_id
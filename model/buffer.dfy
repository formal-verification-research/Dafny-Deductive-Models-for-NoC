include "flit.dfy"

datatype Buffer =
  | Node(dest: nat, next: Buffer)
  | None
  {
    predicate is_prefix_of(b: Buffer) {
      match (this, b)
      case (Node(dest, next), Node(dest', next')) => dest == dest' && next.is_prefix_of(next')
      case (None, Node(_, _)) => true
      case (None, None) => true
      case (Node(_, _), None) => false
    }

    function length(): nat {
      match this
      case None => 0
      case Node(_, next) => 1 + next.length()
    }
  }
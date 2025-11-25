module NoC {
  type Length = i: nat | 1 <= i witness 1

  const BUFFER_LENGTH: Length

  datatype Buffer<T(==)> =
    | Node(payload: T, next: Buffer)
    | Tail
    {
      function length(): nat {
        match this
        case Node(_, next) => 1 + next.length()
        case Tail => 0
      }

      function append(p: T): Buffer<T>
        ensures this.is_prefix_of(append(p))
        ensures append(p).length() == this.length() + 1
      {
        match this
        case Node(payload, next) => Node(payload, next.append(p))
        case Tail => Node(p, Tail)
      }

      predicate is_prefix_of(b: Buffer<T>) {
        match (this, b)
        case (Tail, Tail) => true
        case (Node(_, _), Tail) => false
        case (Tail, Node(_, _)) => true
        case (Node(p, n), Node(p', n')) => p == p' && n.is_prefix_of(n')
      }

      static lemma EqualIsPrefix(a: Buffer<T>, b: Buffer<T>)
        requires a == b
        ensures a.is_prefix_of(b) && b.is_prefix_of(a)
      {}
    }

  datatype Direction =
    | North
    | South
    | East
    | West
    | Local

  method DiscreteRandom(low: nat, high: nat) returns (r: nat)
    ensures {:axiom} low <= r <= high

  class Router {
    var North: Buffer<nat>
    var East:  Buffer<nat>
    var South: Buffer<nat>
    var West:  Buffer<nat>
    var Local: Buffer<nat>

    constructor()
      ensures North.length() == 0 && East.length() == 0 && South.length() == 0 && West.length() == 0 && Local.length() == 0
    {
      North := Tail;
      South := Tail;
      East  := Tail;
      West  := Tail;
      Local := Tail;
    }

    method generateFlits(cycle: nat, dim: nat, id: nat)
      requires 2 <= dim
      requires 0 <= id < dim*dim
      requires this.Local.length() <= BUFFER_LENGTH
      modifies this
      ensures old(this.Local).is_prefix_of(this.Local)
      ensures this.Local.length() <= BUFFER_LENGTH
    {
      if cycle % 3 >= 3 {
        return;
      }

      if this.Local.length() < BUFFER_LENGTH {
        var dest_id := DiscreteRandom(0, dim*dim - 2);
        if dest_id >= id {
          dest_id := dest_id + 1;
        }
        assert dest_id != id;
        this.Local := this.Local.append(dest_id);
      } else {
        assert old(this.Local) == this.Local;
        Buffer.EqualIsPrefix(old(this.Local), this.Local);
      }
    }
  }

  class NoC {
    const dim: nat
    var routers: seq<seq<Router>>

    constructor(dim: nat)
      ensures dim == this.dim
      ensures |routers| == this.dim
      ensures forall y :: 0 <= y < this.dim ==> |routers[y]| == this.dim
    {
      this.dim := dim;
      new;
      routers := seq(this.dim, y => seq(x, _ => new Router()));
    }
  }
}
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

  datatype Router =
    | Router(
      North: Buffer<nat>,
      East:  Buffer<nat>,
      South: Buffer<nat>,
      West:  Buffer<nat>,
      Local: Buffer<nat>
    ) {
      static function init(): Router
        ensures
          && init().North.length() == 0
          && init().East.length()  == 0
          && init().South.length() == 0
          && init().West.length()  == 0
          && init().Local.length() == 0
      {
        Router(Tail, Tail, Tail, Tail, Tail)
      }

      function generateFlits(cycle: nat, dest: nat): (r: Router)
        requires this.Local.length() <= BUFFER_LENGTH
        ensures r.Local.length() <= BUFFER_LENGTH
      {
        Router(
          this.North,
          this.East,
          this.South,
          this.West,
          if cycle % 3 >= 3 || this.Local.length() == BUFFER_LENGTH
          then this.Local 
          else this.Local.append(dest)
        )
      }
    }

  class NoC {
    const dim: nat
    var routers: seq<seq<Router>>

    ghost predicate ValidDims()
      reads this`routers
    {
      && |routers| == this.dim
      && forall y :: 0 <= y < this.dim ==> |routers[y]| == this.dim
    }

    constructor(dim: nat)
      ensures dim == this.dim
      ensures this.ValidDims()
    {
      this.dim := dim;
      new;
      routers := seq(this.dim, y => seq(this.dim, _ => Router.init()));
    }
  }

  method run(stop: nat, n: NoC)
    requires n.ValidDims()
    modifies n`routers
  {
    var cycle := 0;

    while cycle <= stop
      invariant n.ValidDims()
    {
      assert |n.routers| == n.dim;
      n.routers :=
        seq(n.dim,
          y requires 0 <= y < n.dim reads n =>
          seq(n.dim,
            x requires 0 <= x < n.dim reads n =>
              var id := y * n.dim + x;
              assume y < |n.routers|;
              assume x < |n.routers[y]|;
              var dest: nat :| 0 <= dest < n.dim*n.dim - 1 && dest != id;
              if n.routers[y][x].Local.length() < BUFFER_LENGTH
              then
                assert n.routers[y][x].Local.length() <= BUFFER_LENGTH;
                n.routers[y][x].generateFlits(cycle, dest)
              else n.routers[y][x]
          )
        );

      cycle := cycle + 1;
    }
  }
}
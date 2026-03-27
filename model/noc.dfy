module NoC {
  type Length = i: nat | 1 <= i witness 1

  const BUFFER_LENGTH: Length

  datatype Buffer<T> =
    | Node(payload: T, next: Buffer)
    | Tail
    {
      function length(): nat {
        match this
        case Node(_, next) => 1 + next.length()
        case Tail => 0
      }

      function append(p: T): Buffer<T> {
        match this
        case Node(payload, next) => Node(payload, next.append(p))
        case Tail => Node(p, Tail)
      }
    }

  datatype Direction =
    | North
    | South
    | East
    | West
    | Local

  class Router<T> {
    var North: Buffer<T>
    var East:  Buffer<T>
    var South: Buffer<T>
    var West:  Buffer<T>
    var Local: Buffer<T>

    constructor()
      ensures North.length() == 0 && East.length() == 0 && South.length() == 0 && West.length() == 0 && Local.length() == 0
    {
      North := Tail;
      South := Tail;
      East  := Tail;
      West  := Tail;
      Local := Tail;
    }

    method insertLocal(payload: T)
      modifies this.Local 
    {
      this.Local := this.Local.append(payload);
    }
  }

  type NoC = n: seq<seq<Router<nat>>> | |n| >= 2 && (forall y :: 0 <= y < |n| ==> |n[y]| == |n|) witness *

  method generateFlits(n: NoC, cycle: nat) returns (n': NoC)
  {
    n' := n;

    if cycle % 3 >= 3 {
      return;
    }

    var dim := |n|;
    var y := 0;

    while y < dim
    {
      var x := 0;
      while x < dim
      {
        if n'[y][x].Local.length() < BUFFER_LENGTH {
          var dest_id :| 0 <= dest_id < dim * dim && dest_id != y*dim + x;
          n'[y][x].Local := n'[y][x].Local.append(dest_id);
        }
        x := x + 1;
      }
      y := y + 1;
    }
  }
}
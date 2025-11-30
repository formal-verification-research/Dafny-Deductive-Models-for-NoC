module NoC2 {
  datatype Channel =
    | Channel(buffer: seq<nat>, isEmpty: bool, isFull: bool)
    {
      static function init(): Channel
      {
        Channel([], true, false)
      }

      function length(): nat
      {
        |this.buffer|
      }

      function insert(id: nat): Channel
      {
        Channel(this.buffer + [id], this.isEmpty, this.isFull)
      }

      function setFlags(buffer_length: nat): Channel
      {
        Channel(this.buffer, this.length() == 0, this.length() >= buffer_length)
      }
    }

  type FixedSeq<T> = i: seq<T> | |i| == 5 witness *

  const N := 0
  const E := 1
  const S := 2
  const W := 3
  const L := 4

  class Router {
    const id: nat
    const dim: nat
    const buffer_length: nat
    var channels: FixedSeq<Channel>
    // var north: Channel
    // var east:  Channel
    // var south: Channel
    // var west:  Channel
    // var local: Channel
    var serviced: FixedSeq<bool>
    var totalUnserviced: nat


    constructor(buffer_length: nat, id: nat, dim: nat)
      ensures this.id == id
      ensures this.dim == dim
      ensures this.buffer_length == buffer_length
      ensures this.channels[N].length() == 0
      ensures this.channels[S].length()  == 0
      ensures this.channels[E].length() == 0
      ensures this.channels[W].length()  == 0
      ensures this.channels[L].length() == 0
      ensures this.serviced == [false, false, false, false, false]
      ensures this.totalUnserviced == 0
    {
      this.id := id;
      this.dim := dim;
      this.buffer_length := buffer_length;
      this.channels := [Channel.init(), Channel.init(), Channel.init(), Channel.init(), Channel.init()];
      this.serviced := [false, false, false, false, false];
      this.totalUnserviced := 0;
    }

    static method getDestination(id: nat, dim: nat) returns (dest: nat)
      ensures {:axiom} 0 <= id < dim*dim && dest != id

    method generateFlits(cycle: nat)
      requires this.channels[L].length() <= this.buffer_length
      modifies this`channels
      ensures old(this.channels[L].buffer) <= this.channels[L].buffer
      ensures this.channels[L].length() <= this.buffer_length
      ensures forall i :: i in {N, S, E, W} ==> old(this.channels[i]) == this.channels[i]
    {
      if cycle % 3 < 3 && |this.channels[L].buffer| < this.buffer_length {
        var dest := Router.getDestination(this.id, this.dim);
        this.channels := [this.channels[N], this.channels[E], this.channels[S], this.channels[W], this.channels[L].insert(dest)];
      }
    }

    method prepRouter(cycle: nat)
      modifies this`channels
      ensures forall i :: i in {N, S, E, W, L} ==> old(this.channels[i].buffer) == this.channels[i].buffer
      ensures forall i :: i in {N, S, E, W, L} ==> (this.channels[i].length() == 0 <==> this.channels[i].isEmpty) && (this.channels[i].length() >= this.buffer_length <==> this.channels[i].isFull)
    {
      this.channels := [this.channels[N].setFlags(this.buffer_length),
                        this.channels[E].setFlags(this.buffer_length),
                        this.channels[S].setFlags(this.buffer_length), 
                        this.channels[W].setFlags(this.buffer_length),
                        this.channels[L].setFlags(this.buffer_length)];
    }

    method send()
      modifies this`serviced

    {

    }
  }
}
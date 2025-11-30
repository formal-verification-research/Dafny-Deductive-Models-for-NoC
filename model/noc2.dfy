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
    // var channels: FixedSeq<Channel>
    var north: Channel
    var east:  Channel
    var south: Channel
    var west:  Channel
    var local: Channel
    var serviced: FixedSeq<bool>
    var totalUnserviced: nat


    constructor(buffer_length: nat, id: nat, dim: nat)
      ensures this.id == id
      ensures this.dim == dim
      ensures this.buffer_length == buffer_length
      ensures this.north.length() == 0
      ensures this.east.length()  == 0
      ensures this.south.length() == 0
      ensures this.west.length()  == 0
      ensures this.local.length() == 0
      ensures this.serviced == [false, false, false, false, false]
      ensures this.totalUnserviced == 0
    {
      this.id := id;
      this.dim := dim;
      this.buffer_length := buffer_length;
      this.north := Channel.init();
      this.east  := Channel.init();
      this.south := Channel.init();
      this.west  := Channel.init();
      this.local := Channel.init();
      this.serviced := [false, false, false, false, false];
      this.totalUnserviced := 0;
    }

    static method getDestination(id: nat, dim: nat) returns (dest: nat)
      ensures {:axiom} 0 <= id < dim*dim && dest != id

    method generateFlits(cycle: nat)
      requires this.local.length() <= this.buffer_length
      modifies this`local
      ensures old(this.local.buffer) <= this.local.buffer
      ensures this.local.length() <= this.buffer_length 
    {
      if cycle % 3 < 3 && |this.local.buffer| < this.buffer_length {
        var dest := Router.getDestination(this.id, this.dim);
        this.local := this.local.insert(dest);
      }
    }

    method prepRouter(cycle: nat)
      modifies this`north
      modifies this`east
      modifies this`south
      modifies this`west
      modifies this`local
      ensures old(this.north.buffer) == this.north.buffer
      ensures old(this.east.buffer)  == this.east.buffer
      ensures old(this.south.buffer) == this.south.buffer
      ensures old(this.west.buffer)  == this.west.buffer
      ensures old(this.local.buffer) == this.local.buffer
      ensures (this.north.length() == 0 <==> this.north.isEmpty) && (this.north.length() >= this.buffer_length <==> this.north.isFull)
      ensures (this.east.length()  == 0 <==> this.east.isEmpty)  && (this.east.length()  >= this.buffer_length <==> this.east.isFull)
      ensures (this.south.length() == 0 <==> this.south.isEmpty) && (this.south.length() >= this.buffer_length <==> this.south.isFull)
      ensures (this.west.length()  == 0 <==> this.west.isEmpty)  && (this.west.length()  >= this.buffer_length <==> this.west.isFull)
      ensures (this.local.length() == 0 <==> this.local.isEmpty) && (this.local.length() >= this.buffer_length <==> this.local.isFull)
    {
      this.north := this.north.setFlags(this.buffer_length);
      this.east  := this.east.setFlags(this.buffer_length);
      this.south := this.south.setFlags(this.buffer_length);
      this.west  := this.west.setFlags(this.buffer_length);
      this.local := this.local.setFlags(this.buffer_length);
    }

    method send()
      modifies this`serviced

    {

    }
  }
}
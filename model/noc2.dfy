module NoC2 {
  import Std.Collections.Seq

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

      function dropFirst(): Channel
        requires this.length() > 0
      {
        Channel(Seq.DropFirst(this.buffer), this.isEmpty, this.isFull)
      }

      function peekFirst(): nat
        requires this.length() > 0
      {
        this.buffer[0]
      }
    }

  type FixedSeq<T> = i: seq<T> | |i| == 5 witness *

  datatype Direction =
    | North
    | East
    | South
    | West
    | Local
    {
      function getDestinationDir(): Direction
        requires !this.Local?
      {
        match this
        case North => South
        case South => North
        case East => West
        case West => East
      }
    }

  const N := 0
  const E := 1
  const S := 2
  const W := 3
  const L := 4

  class ChannelWrapper<T> {
    var north: T
    var east:  T
    var south: T
    var west:  T
    var local: T

    constructor(north: T, east: T, south: T, west: T, local: T)
      ensures this.north == north
      ensures this.east  == east
      ensures this.south == south
      ensures this.west  == west
      ensures this.local == local
    {
      this.north := north;
      this.east  := east;
      this.south := south;
      this.west  := west;
      this.local := local;
    }

    function asSeq(): (s: seq<T>)
      reads this
      ensures |s| == 5
    {
      [this.north, this.east, this.south, this.west, this.local]
    }

    function fromDir(dir: Direction): T
      reads this`north
      reads this`east
      reads this`south
      reads this`west
      reads this`local
    {
      match dir
      case North => this.north
      case East  => this.east
      case South => this.south
      case West  => this.west
      case Local => this.local
    }

    method writeByDir(dir: Direction, data: T)
      modifies this
      ensures dir != North ==> old(this.north) == this.north
      ensures dir != East  ==> old(this.east)  == this.east
      ensures dir != South ==> old(this.south) == this.south
      ensures dir != West  ==> old(this.west)  == this.west
      ensures dir != Local ==> old(this.local) == this.local
    {
      match dir
      case North => { this.north := data; }
      case East  => { this.east  := data; }
      case South => { this.south := data; }
      case West  => { this.west  := data; }
      case Local => { this.local := data; }
    }
  }

  class Router {
    const id: nat
    const dim: nat
    const buffer_length: nat
    var channels: ChannelWrapper<Channel>
    var serviced: ChannelWrapper<bool>
    var used: ChannelWrapper<bool>
    var totalUnserviced: nat

    predicate valid() {
      && this.dim >= 2
      && 0 <= this.id < this.dim*this.dim
      && buffer_length > 0
    }

    constructor(buffer_length: nat, id: nat, dim: nat)
      requires buffer_length > 0
      requires dim >= 2
      requires 0 <= id < dim*dim
      ensures this.id == id
      ensures this.dim == dim
      ensures this.buffer_length == buffer_length
      ensures this.channels.north.length() == 0
      ensures this.channels.east.length()  == 0
      ensures this.channels.south.length() == 0
      ensures this.channels.west.length()  == 0
      ensures this.channels.local.length() == 0
      ensures this.serviced.asSeq() == [false, false, false, false, false]
      ensures this.totalUnserviced == 0
      ensures this.used.asSeq() == [false, false, false, false, false]
      ensures valid()
    {
      this.id := id;
      this.dim := dim;
      this.buffer_length := buffer_length;
      this.channels := new ChannelWrapper(Channel.init(), Channel.init(), Channel.init(), Channel.init(), Channel.init());
      this.serviced := new ChannelWrapper(false, false, false, false, false);
      this.used := new ChannelWrapper(false, false, false, false, false);
      this.totalUnserviced := 0;
    }

    static method getDestination(id: nat, dim: nat) returns (dest: nat)
      ensures {:axiom} 0 <= id < dim*dim && dest != id

    function column(): nat
      requires valid()
    {
      Router.column_s(this.id, this.dim)
    }

    static function column_s(id: nat, dim: nat): nat
      requires dim != 0
    {
      id % dim
    }

    function row(): nat
      requires valid()
    {
      Router.row_s(id, dim)
    }

    static function row_s(id: nat, dim: nat): nat
      requires dim != 0
    {
      id / dim
    }

    method generateFlits(cycle: nat)
      requires valid()
      requires this.channels.local.length() <= this.buffer_length
      modifies this.channels`local
      ensures old(this.channels.local.buffer) <= this.channels.local.buffer
      ensures this.channels.local.length() <= this.buffer_length
      ensures valid()
    {
      if cycle % 3 < 3 && |this.channels.local.buffer| < this.buffer_length {
        var dest := Router.getDestination(this.id, this.dim);
        this.channels.local := this.channels.local.insert(dest);
      }
    }

    method prepRouter(cycle: nat)
      requires valid()
      modifies this.channels`north
      modifies this.channels`east
      modifies this.channels`south
      modifies this.channels`west
      modifies this.channels`local
      ensures old(this.channels.north.buffer) == this.channels.north.buffer
      ensures old(this.channels.east.buffer)  == this.channels.east.buffer
      ensures old(this.channels.south.buffer) == this.channels.south.buffer
      ensures old(this.channels.west.buffer)  == this.channels.west.buffer
      ensures old(this.channels.local.buffer) == this.channels.local.buffer
      ensures (this.channels.north.length() == 0 <==> this.channels.north.isEmpty) && (this.channels.north.length() >= this.buffer_length <==> this.channels.north.isFull)
      ensures (this.channels.east.length()  == 0 <==> this.channels.east.isEmpty)  && (this.channels.east.length()  >= this.buffer_length <==> this.channels.east.isFull)
      ensures (this.channels.south.length() == 0 <==> this.channels.south.isEmpty) && (this.channels.south.length() >= this.buffer_length <==> this.channels.south.isFull)
      ensures (this.channels.west.length()  == 0 <==> this.channels.west.isEmpty)  && (this.channels.west.length()  >= this.buffer_length <==> this.channels.west.isFull)
      ensures (this.channels.local.length() == 0 <==> this.channels.local.isEmpty) && (this.channels.local.length() >= this.buffer_length <==> this.channels.local.isFull)
      ensures valid()
    {
      this.channels.north := this.channels.north.setFlags(this.buffer_length);
      this.channels.east  := this.channels.east.setFlags(this.buffer_length);
      this.channels.south := this.channels.south.setFlags(this.buffer_length);
      this.channels.west  := this.channels.west.setFlags(this.buffer_length);
      this.channels.local := this.channels.local.setFlags(this.buffer_length);
    }

    method send(other: Router, from: Direction, dir: Direction)
      requires valid()
      requires this.dim == other.dim
      requires this.id != other.dim
      requires dir != Local
      requires this.channels.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.channels
      modifies this`totalUnserviced
      modifies other.channels
      ensures valid()
    {
      var dest_dir := dir.getDestinationDir();

      if !other.channels.fromDir(dest_dir).isFull && !this.used.fromDir(dir) {
        // Send packet from source
        var from_channel := this.channels.fromDir(from);
        var packet := from_channel.peekFirst();
        this.channels.writeByDir(from, from_channel.dropFirst());

        // recieve packet at destination
        other.channels.writeByDir(dest_dir, other.channels.fromDir(dest_dir).insert(packet));

        // mark used
        this.used.writeByDir(dir, true);
        this.serviced.writeByDir(from, true);
      } else {
        this.totalUnserviced := this.totalUnserviced + 1;
      }
    }

    method advanceFlits(other: Router, from: Direction)
      requires valid()
      requires this.dim == other.dim
      requires this.id != other.dim
      requires this.channels.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.channels
      modifies this`totalUnserviced
      modifies other.channels
      ensures valid()
    {
      var dest_id := this.channels.fromDir(from).peekFirst();
      var column_shift := Router.column_s(dest_id, this.dim) - this.column();

      if column_shift == 0 {
        if dest_id < this.id {
          this.send(other, from, North);
        } else {
          this.send(other, from, South);
        }
      } else if column_shift < 0 {
        this.send(other, from, West);
      } else {
        this.send(other, from, East);
      }
    }
  }
}
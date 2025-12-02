module NoC2 {
  import Std.Collections.Seq

  predicate allUnique<T(==)>(s: seq) {
    forall i: nat, j: nat | i < |s| && j < |s| && i != j :: s[i] != s[j]
  }

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
  type BoundedSeq<T> = i: seq<T> | 3 <= |i| <= 5 witness *

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
      modifies this`north
      modifies this`east
      modifies this`south
      modifies this`west
      modifies this`local
      ensures dir != North ==> unchanged(`north)
      ensures dir != East  ==> unchanged(`east) 
      ensures dir != South ==> unchanged(`south)
      ensures dir != West  ==> unchanged(`west) 
      ensures dir != Local ==> unchanged(`local)
    {
      match dir
      case North => { this.north := data; }
      case East  => { this.east  := data; }
      case South => { this.south := data; }
      case West  => { this.west  := data; }
      case Local => { this.local := data; }
    }

    method setAll(data: T)
      modifies this`north
      modifies this`east
      modifies this`south
      modifies this`west
      modifies this`local
      ensures this.north == data
      ensures this.east == data 
      ensures this.south == data
      ensures this.west == data 
      ensures this.local == data
    {
      this.north := data;
      this.east  := data; 
      this.south := data;
      this.west  := data; 
      this.local := data;
    }
  }

  class Router {
    const id: nat
    const dim: nat
    const buffer_length: nat
    const channels: ChannelWrapper<Channel>
    const serviced: ChannelWrapper<bool>
    const used: ChannelWrapper<bool>
    var totalUnserviced: nat
    var priority_list: FixedSeq<Direction>

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
      ensures fresh(this.channels) && fresh(this.serviced) && fresh(this.used)
      ensures this.channels.north.length() == 0
      ensures this.channels.east.length()  == 0
      ensures this.channels.south.length() == 0
      ensures this.channels.west.length()  == 0
      ensures this.channels.local.length() == 0
      ensures this.serviced.asSeq() == [false, false, false, false, false]
      ensures this.totalUnserviced == 0
      ensures this.used.asSeq() == [false, false, false, false, false]
      ensures this.priority_list == [North, East, South, West, Local]
      ensures valid()
    {
      this.id := id;
      this.dim := dim;
      this.buffer_length := buffer_length;
      this.channels := new ChannelWrapper(Channel.init(), Channel.init(), Channel.init(), Channel.init(), Channel.init());
      this.serviced := new ChannelWrapper(false, false, false, false, false);
      this.used := new ChannelWrapper(false, false, false, false, false);
      this.totalUnserviced := 0;
      this.priority_list := [North, East, South, West, Local];
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

    predicate channelConnected(ch: Direction)
      requires valid()
      requires !ch.Local?
    {
      match ch
      case North => this.row() != 0
      case East => this.column() < dim - 1
      case South => this.row() < dim - 1
      case West => this.column() != 0
    }

    method generateFlits(cycle: nat)
      requires valid()
      modifies this.channels`local
      ensures old(this.channels.local.buffer) <= this.channels.local.buffer
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
      requires this.id != other.id
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
      requires this.id != other.id
      requires this.channels.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.channels
      modifies this`totalUnserviced
      modifies other.channels
      ensures valid()
      // ensures unchanged(this`channels)
      // ensures unchanged(this`used)
      // ensures unchanged(this`serviced)
      // ensures unchanged(other`channels)
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

    method advanceChannel(other: Router, from: Direction)
      requires valid()
      requires this.dim == other.dim
      requires this.id != other.id
      requires this.channels.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.channels
      modifies this`totalUnserviced
      modifies other.channels
      ensures valid()
      // ensures unchanged(this`channels)
      // ensures unchanged(this`used)
      // ensures unchanged(this`serviced)
      // ensures unchanged(other`channels)
    {
      if (!from.Local? && this.channelConnected(from)) || this.channels.fromDir(from).isEmpty {
        this.serviced.writeByDir(from, true);
      } else if (this.channels.fromDir(from).peekFirst() == this.id) {
        // TODO
      } else {
        advanceFlits(other, from);
      }
    }

    method advanceRouter(neighbors: ChannelWrapper<Router?>)
      requires valid()
      requires forall n: Router? | n in neighbors.asSeq() :: n != null ==> this.dim == n.dim
      requires forall n: Router? | n in neighbors.asSeq() :: n != null ==> this.id != n.id
      modifies this.serviced
      modifies this.used
      modifies this.channels
      modifies this`totalUnserviced
      ensures valid()
      // ensures unchanged(this`channels)
      // ensures unchanged(this`used)
      // ensures unchanged(this`serviced)
      // ensures neighbors.north != null ==> unchanged(neighbors.north`channels)
      // ensures neighbors.east  != null ==> unchanged(neighbors.east`channels)
      // ensures neighbors.south != null ==> unchanged(neighbors.south`channels)
      // ensures neighbors.west  != null ==> unchanged(neighbors.west`channels)
      // ensures neighbors.local != null ==> unchanged(neighbors.local`channels)
    {

    }
    
    method updatePriority()
      modifies this`priority_list
      modifies this.serviced
      modifies this.used
      modifies this`totalUnserviced
      ensures this.serviced.asSeq() == [false, false, false, false, false]
      ensures this.used.asSeq() == [false, false, false, false, false]
      ensures this.totalUnserviced == 0
    {
      var priority_list_temp: FixedSeq<Direction> := [North, East, South, West, Local];
      var serviced_index := 0;
      var unserviced_index := 0;
      var i := 0;

      while i < 4
        invariant 0 <= i <= 4
        invariant 0 <= serviced_index <= i
        invariant 0 <= unserviced_index <= i
      {
        if this.serviced.fromDir(this.priority_list[i]) {
          var index := this.totalUnserviced + serviced_index;
          assume 0 <= index < 4;
          priority_list_temp := priority_list_temp[index := this.priority_list[i]];
          serviced_index := serviced_index + 1;
        } else {
          var index := unserviced_index;
          priority_list_temp := priority_list_temp[index := this.priority_list[i]];
          unserviced_index := unserviced_index + 1;
        }

        i := i + 1;
      }

      // if all channels are empty then reset the priority list
      if Seq.FoldLeft((x, y) => x && y, true, Seq.Map((z: Channel) => z.isEmpty, this.channels.asSeq())) {
        this.priority_list := [North, East, South, West, Local];
      } else {
        this.priority_list := priority_list_temp;
      }

      // Reset other variables
      this.serviced.setAll(false);
      this.used.setAll(false);
      this.totalUnserviced := 0;
    }
  }

  datatype NoC = 
  | NoC(dim: nat)
  {
    method construct(buffer_length: nat) returns (routers: seq<Router>)
      requires dim >= 2
      requires buffer_length > 0
      ensures |routers| == dim*dim
      ensures allUnique(routers)
      ensures forall j | 0 <= j < dim*dim :: (
          && fresh(routers[j])
          && fresh(routers[j].channels)
          && fresh(routers[j].serviced)
          && fresh(routers[j].used)
          && routers[j].id == j
          && routers[j].dim == this.dim
          && routers[j].buffer_length == buffer_length
          && routers[j].channels.north.length() == 0
          && routers[j].channels.east.length()  == 0
          && routers[j].channels.south.length() == 0
          && routers[j].channels.west.length()  == 0
          && routers[j].channels.local.length() == 0
          && routers[j].serviced.asSeq() == [false, false, false, false, false]
          && routers[j].totalUnserviced == 0
          && routers[j].used.asSeq() == [false, false, false, false, false]
          && routers[j].priority_list == [North, East, South, West, Local]
          && routers[j].valid()
        )
    {
      routers := [];
      for i := 0 to dim*dim
        invariant 0 <= i <= dim*dim
        invariant |routers| == i
        invariant allUnique(routers)
        invariant forall j | 0 <= j < i :: (
          && fresh(routers[j])
          && fresh(routers[j].channels)
          && fresh(routers[j].serviced)
          && fresh(routers[j].used)
          && routers[j].id == j
          && routers[j].dim == this.dim
          && routers[j].buffer_length == buffer_length
          && routers[j].channels.north.length() == 0
          && routers[j].channels.east.length()  == 0
          && routers[j].channels.south.length() == 0
          && routers[j].channels.west.length()  == 0
          && routers[j].channels.local.length() == 0
          && routers[j].serviced.asSeq() == [false, false, false, false, false]
          && routers[j].totalUnserviced == 0
          && routers[j].used.asSeq() == [false, false, false, false, false]
          && routers[j].priority_list == [North, East, South, West, Local]
          && routers[j].valid()
        )
      {
        var r := new Router(buffer_length, i, this.dim);
        routers := routers + [r];
      }
    }

    method run(buffer_length: nat)
      requires dim >= 2
      requires buffer_length > 0
      decreases *
    {
      var routers: seq<Router> := this.construct(buffer_length);

      var cycle: nat := 0;

      while true
        decreases *
        invariant 0 <= cycle
        modifies routers[..]
        modifies (set x | x in routers :: x.serviced)
        modifies (set x | x in routers :: x.used)
        modifies (set x | x in routers :: x.channels)
      {
        for i := 0 to |routers| { routers[i].generateFlits(cycle); }
        for i := 0 to |routers| { routers[i].prepRouter(cycle); }

        for i := 0 to |routers| {
          var x := routers[i].column();
          assume false;
          var y := routers[i].row();

          var neighbors := new ChannelWrapper(null, null, null, null, null);

          if (y - 1) >= 0 {
            var id_north: int := x + (y - 1) * this.dim;
            neighbors.north := routers[id_north];
          }
          if (x - 1) >= 0 {
            var id_west: int := (x - 1) + y * this.dim;
            neighbors.west := routers[id_west];
          }
          if (x + 1) < this.dim {
            var id_east: int := (x + 1) + y * this.dim;
            neighbors.east := routers[id_east];
          }
          if (y + 1) < this.dim {
            var id_south: int := x + (y + 1) * this.dim;
            neighbors.south := routers[id_south];
          }
          routers[i].advanceRouter(neighbors);
        }
        
        for i := 0 to |routers| { routers[i].updatePriority(); }
      }
    }
  }
}
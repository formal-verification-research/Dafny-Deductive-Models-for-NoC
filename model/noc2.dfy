module NoC2 {
  import Std.Collections.Seq
  import Std.Wrappers

  predicate allUnique<T(==)>(s: seq) {
    forall i: nat, j: nat | i < |s| && j < |s| && i != j :: s[i] != s[j]
  }

  datatype Buffer =
    | Buffer(buffer: seq<nat>, isEmpty: bool, isFull: bool)
    {
      static function init(): Buffer
      {
        Buffer([], true, false)
      }

      function length(): nat
      {
        |this.buffer|
      }

      function insert(id: nat): Buffer
      {
        Buffer(this.buffer + [id], this.isEmpty, this.isFull)
      }

      function setFlags(buffer_length: nat): Buffer
      {
        Buffer(this.buffer, this.length() == 0, this.length() >= buffer_length)
      }

      function dropFirst(): Buffer
        requires this.length() > 0
      {
        Buffer(Seq.DropFirst(this.buffer), this.isEmpty, this.isFull)
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

  class DirectionWrapper<T> {
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

    method setAllTo(data: T)
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
    const buffers: DirectionWrapper<Buffer>
    const serviced: DirectionWrapper<bool>
    const used: DirectionWrapper<bool>
    var totalUnserviced: nat
    var priority_list: FixedSeq<Direction>

    predicate valid() {
      && this.dim >= 2
      && 0 <= this.id < (this.dim*this.dim)
      && buffer_length > 0
    }

    constructor(buffer_length: nat, id: nat, dim: nat)
      requires buffer_length > 0
      requires dim >= 2
      requires 0 <= id < dim*dim
      ensures this.id == id
      ensures this.dim == dim
      ensures this.buffer_length == buffer_length
      ensures fresh(this.buffers) && fresh(this.serviced) && fresh(this.used)
      ensures this.buffers.north.length() == 0
      ensures this.buffers.east.length()  == 0
      ensures this.buffers.south.length() == 0
      ensures this.buffers.west.length()  == 0
      ensures this.buffers.local.length() == 0
      ensures this.serviced.asSeq() == [false, false, false, false, false]
      ensures this.totalUnserviced == 0
      ensures this.used.asSeq() == [false, false, false, false, false]
      ensures this.priority_list == [North, East, South, West, Local]
      ensures valid()
    {
      this.id := id;
      this.dim := dim;
      this.buffer_length := buffer_length;
      this.buffers := new DirectionWrapper(Buffer.init(), Buffer.init(), Buffer.init(), Buffer.init(), Buffer.init());
      this.serviced := new DirectionWrapper(false, false, false, false, false);
      this.used := new DirectionWrapper(false, false, false, false, false);
      this.totalUnserviced := 0;
      this.priority_list := [North, East, South, West, Local];
    }

    function x(): (x: nat)
      requires valid()
    {
      this.id % this.dim
    }

    function y(): (y: nat)
      requires valid()
    {
      this.id / this.dim
    }

    static function calcX(id: nat, dim: nat): (x: nat)
      requires 2 <= dim && 0 <= id < dim*dim
    {
      id % dim
    }

    static function calcY(id: nat, dim: nat): (y: nat)
      requires 2 <= dim && 0 <= id < dim*dim
    {
      id / dim
    }

    static lemma xBoundValid(id: nat, dim: nat)
      requires 2 <= dim && 0 <= id < dim*dim
      ensures 0 <= id % dim < dim
    {}

    static lemma yBoundValid(id: nat, dim: nat)
      requires 2 <= dim && 0 <= id < dim*dim
      ensures 0 <= id / dim < dim
    {
      if id / dim >= dim {
        assert false by {
          assert id < dim*dim;
          assert id / dim < (dim*dim) / dim;
          assert id / dim < dim;
        }
      } else {
        
      }
    }

    predicate isValidId(id: int) {
      0 <= id < this.dim*this.dim
    }

    predicate isValidNeighborId(id: int) {
      && isValidId(id)
      && id != this.id
    }

    method getNeighborIds() returns (n: DirectionWrapper<Wrappers.Option<nat>>)
      requires valid()
      ensures fresh(n)
      ensures n.local.None?
      ensures
        var id := this.id - this.dim;
        && (isValidNeighborId(id) ==> n.north.Some? && n.north.value == id)
        && (!isValidNeighborId(id) ==> n.north.None?)
      ensures
        var id := this.id + 1;
        && (isValidNeighborId(id) ==> n.east.Some? && n.east.value == id)
        && (!isValidNeighborId(id) ==> n.east.None?)
      ensures
        var id := this.id + this.dim;
        && (isValidNeighborId(id) ==> n.south.Some? && n.south.value == id)
        && (!isValidNeighborId(id) ==> n.south.None?)
      ensures
        var id := this.id - 1;
        && (isValidNeighborId(id) ==> n.west.Some? && n.west.value == id)
        && (!isValidNeighborId(id) ==> n.west.None?)
    {
      n := new DirectionWrapper(Wrappers.Option.None, Wrappers.Option.None, Wrappers.Option.None, Wrappers.Option.None, Wrappers.Option.None);
      
      // North
      var id_n := this.id - this.dim;
      if isValidNeighborId(id_n) {
        n.north := Wrappers.Option.Some(id_n);
      }

      // East
      var id_e := this.id + 1;
      if isValidNeighborId(id_e) {
        n.east := Wrappers.Option.Some(id_e);
      }

      // South
      var id_s := this.id + this.dim;
      if isValidNeighborId(id_s) {
        n.south := Wrappers.Option.Some(id_s);
      }

      // West
      var id_w := this.id - 1;
      if isValidNeighborId(id_w) {
        n.west := Wrappers.Option.Some(id_w);
      }
    }

    method isConnected() returns (n: DirectionWrapper<bool>)
      requires valid()
      ensures fresh(n)
      ensures n.local
      ensures isValidNeighborId(this.id - this.dim) <==> n.north
      ensures isValidNeighborId(this.id + 1)        <==> n.east
      ensures isValidNeighborId(this.id + this.dim) <==> n.south
      ensures isValidNeighborId(this.id - 1)        <==> n.west
    {
      n := new DirectionWrapper(isValidNeighborId(this.id - this.dim),
                                isValidNeighborId(this.id + 1),
                                isValidNeighborId(this.id + this.dim),
                                isValidNeighborId(this.id - 1),
                                true);
    }

    predicate channelConnected(ch: Direction)
      requires valid()
      requires !ch.Local?
    {
      match ch
      case North => this.y() != 0
      case East  => this.x() < dim - 1
      case South => this.y() < dim - 1
      case West  => this.x() != 0
    }

    static method getDestination(id: nat, dim: nat) returns (dest: nat)
      ensures {:axiom} 0 <= dest < dim*dim && dest != id

    method generateFlits(cycle: nat)
      requires valid()
      modifies this.buffers`local
      ensures old(this.buffers.local.buffer) <= this.buffers.local.buffer
      ensures old(|this.buffers.local.buffer|) == |this.buffers.local.buffer| || old(|this.buffers.local.buffer|) + 1 == |this.buffers.local.buffer|
    {
      if cycle % 3 < 3 && |this.buffers.local.buffer| < this.buffer_length {
        var dest := Router.getDestination(this.id, this.dim);
        this.buffers.local := this.buffers.local.insert(dest);
      }
    }

    method prepRouter(cycle: nat)
      requires valid()
      modifies this.buffers
      ensures old(this.buffers.north.buffer) == this.buffers.north.buffer
      ensures old(this.buffers.east.buffer)  == this.buffers.east.buffer
      ensures old(this.buffers.south.buffer) == this.buffers.south.buffer
      ensures old(this.buffers.west.buffer)  == this.buffers.west.buffer
      ensures old(this.buffers.local.buffer) == this.buffers.local.buffer
      ensures (this.buffers.north.length() == 0 <==> this.buffers.north.isEmpty) && (this.buffers.north.length() >= this.buffer_length <==> this.buffers.north.isFull)
      ensures (this.buffers.east.length()  == 0 <==> this.buffers.east.isEmpty)  && (this.buffers.east.length()  >= this.buffer_length <==> this.buffers.east.isFull)
      ensures (this.buffers.south.length() == 0 <==> this.buffers.south.isEmpty) && (this.buffers.south.length() >= this.buffer_length <==> this.buffers.south.isFull)
      ensures (this.buffers.west.length()  == 0 <==> this.buffers.west.isEmpty)  && (this.buffers.west.length()  >= this.buffer_length <==> this.buffers.west.isFull)
      ensures (this.buffers.local.length() == 0 <==> this.buffers.local.isEmpty) && (this.buffers.local.length() >= this.buffer_length <==> this.buffers.local.isFull)
    {
      this.buffers.north := this.buffers.north.setFlags(this.buffer_length);
      this.buffers.east  := this.buffers.east.setFlags(this.buffer_length);
      this.buffers.south := this.buffers.south.setFlags(this.buffer_length);
      this.buffers.west  := this.buffers.west.setFlags(this.buffer_length);
      this.buffers.local := this.buffers.local.setFlags(this.buffer_length);
    }

    method send(other: Router, from: Direction, dir: Direction)
      requires valid()
      requires other.valid()
      requires this.dim == other.dim
      requires this.id != other.id
      requires dir != Local
      requires this.buffers.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`totalUnserviced
      modifies other.buffers
    {
      var dest_dir := dir.getDestinationDir();

      if !other.buffers.fromDir(dest_dir).isFull && !this.used.fromDir(dir) {
        // Send packet from source
        var from_channel := this.buffers.fromDir(from);
        var packet := from_channel.peekFirst();
        this.buffers.writeByDir(from, from_channel.dropFirst());

        // recieve packet at destination
        other.buffers.writeByDir(dest_dir, other.buffers.fromDir(dest_dir).insert(packet));

        // mark used
        this.used.writeByDir(dir, true);
        this.serviced.writeByDir(from, true);
      } else {
        this.totalUnserviced := this.totalUnserviced + 1;
      }
    }

    method advanceFlits(other: Router, from: Direction)
      requires valid()
      requires other.valid()
      requires this.dim == other.dim
      requires this.id != other.id
      requires this.buffers.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`totalUnserviced
      modifies other.buffers
    {
      var dest_id := this.buffers.fromDir(from).peekFirst();
      assume 0 <= dest_id < this.dim*this.dim;
      var column_shift := Router.calcX(dest_id, this.dim) - this.x();

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
      requires other.valid()
      requires this.dim == other.dim
      requires this.id != other.id
      requires this.buffers.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`totalUnserviced
      modifies other.buffers
    {
      if (!from.Local? && this.channelConnected(from)) || this.buffers.fromDir(from).isEmpty {
        this.serviced.writeByDir(from, true);
      } else if (this.buffers.fromDir(from).peekFirst() == this.id) {
        // TODO
      } else {
        advanceFlits(other, from);
      }
    }

    method advanceRouter(neighbors: DirectionWrapper<Wrappers.Option<Router>>)
      requires valid()
      requires forall n | n in neighbors.asSeq() :: n.Some? ==> this.dim == n.value.dim
      requires forall n | n in neighbors.asSeq() :: n.Some? ==> this.id != n.value.id
      requires forall n | n in neighbors.asSeq() :: n.Some? ==> n.value.valid()
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`totalUnserviced
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
      if Seq.FoldLeft((x, y) => x && y, true, Seq.Map((z: Buffer) => z.isEmpty, this.buffers.asSeq())) {
        this.priority_list := [North, East, South, West, Local];
      } else {
        this.priority_list := priority_list_temp;
      }

      // Reset other variables
      this.serviced.setAllTo(false);
      this.used.setAllTo(false);
      this.totalUnserviced := 0;
    }
  }

  datatype NoC = 
  | NoC(dim: nat)
  {
    static method northNeighborId(x: nat, y: nat, dim: nat) returns (coord: nat)
      requires 0 <= y < dim
      requires 0 <= x < dim
      requires 0 <= (y - 1) < dim
      ensures coord == x + (y - 1) * dim 
      ensures 0 <= coord < dim*dim
    {
      coord := x + (y - 1) * dim;
    }

    static method eastNeighborId(x: nat, y: nat, dim: nat) returns (coord: nat)
      requires 0 <= y < dim
      requires 0 <= x < dim
      requires 0 <= (x + 1) < dim
      ensures coord == (x + 1) + y * dim
      ensures 0 <= coord < dim*dim
    {
      coord := (x + 1) + y * dim;
      calc {
        coord;
      ==
        (x + 1) + y * dim;
      <=
        (dim - 1) + (dim - 1) * dim;
      ==
        (dim - 1) * (dim + 1);
      ==
        (dim * dim) - 1;
      }
      assert coord <= (dim*dim) - 1 <==> coord < (dim*dim);
    }

    static method southNeighborId(x: nat, y: nat, dim: nat) returns (coord: nat)
      requires 0 <= y < dim
      requires 0 <= x < dim
      requires 0 <= (y + 1) < dim
      ensures coord == x + (y + 1) * dim
      ensures 0 <= coord < dim*dim
    {
      coord := x + (y + 1) * dim;
      calc {
        coord;
      ==
        x + (y + 1) * dim;
      <=
        (dim - 1) + (dim - 1) * dim;
      ==
        (dim - 1) * (dim + 1);
      ==
        (dim * dim) - 1;
      }
      assert coord <= (dim*dim) - 1 <==> coord < (dim*dim);
    }

    static method westNeighborId(x: nat, y: nat, dim: nat) returns (coord: nat)
      requires 0 <= y < dim
      requires 0 <= x < dim
      requires 0 <= (x - 1) < dim
      ensures coord == (x - 1) + y * dim 
      ensures 0 <= coord < dim*dim
    {
      coord := (x - 1) + y * dim;
      calc {
        coord;
      ==
        (x - 1) + y * dim;
      <=
        (x - 1) + (dim - 1) * dim;
      <=
        (dim - 1) + (dim - 1) * dim;
      ==
        (dim - 1) * (dim + 1);
      ==
        (dim * dim) - 1;
      }
      assert coord <= (dim*dim) - 1 <==> coord < (dim*dim);
    }

    method construct(buffer_length: nat) returns (routers: seq<Router>)
      requires dim >= 2
      requires buffer_length > 0
      ensures |routers| == dim*dim
      ensures allUnique(routers)
      ensures forall j | 0 <= j < dim*dim :: (
          && fresh(routers[j])
          && fresh(routers[j].buffers)
          && fresh(routers[j].serviced)
          && fresh(routers[j].used)
          && routers[j].id == j
          && routers[j].dim == this.dim
          && routers[j].buffer_length == buffer_length
          && routers[j].buffers.north.length() == 0
          && routers[j].buffers.east.length()  == 0
          && routers[j].buffers.south.length() == 0
          && routers[j].buffers.west.length()  == 0
          && routers[j].buffers.local.length() == 0
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
          && fresh(routers[j].buffers)
          && fresh(routers[j].serviced)
          && fresh(routers[j].used)
          && routers[j].id == j
          && routers[j].dim == this.dim
          && routers[j].buffer_length == buffer_length
          && routers[j].buffers.north.length() == 0
          && routers[j].buffers.east.length()  == 0
          && routers[j].buffers.south.length() == 0
          && routers[j].buffers.west.length()  == 0
          && routers[j].buffers.local.length() == 0
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
      assume false;
      var routers: seq<Router> := this.construct(buffer_length);

      var cycle: nat := 0;

      while true
        decreases *
        invariant 0 <= cycle
        modifies routers[..]
        modifies (set x | x in routers :: x.serviced)
        modifies (set x | x in routers :: x.used)
        modifies (set x | x in routers :: x.buffers)
      {
        for i := 0 to |routers| { routers[i].generateFlits(cycle); }
        for i := 0 to |routers| { routers[i].prepRouter(cycle); }

        for i := 0 to |routers| {
          // routers[i].advanceRouter(neighbors);
        }
        
        for i := 0 to |routers| { routers[i].updatePriority(); }
      }
    }
  }
}
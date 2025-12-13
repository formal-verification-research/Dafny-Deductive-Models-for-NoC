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
      ensures dir == North ==> north == data
      ensures dir == East  ==> east  == data
      ensures dir == South ==> south == data
      ensures dir == West  ==> west  == data
      ensures dir == Local ==> local == data
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

  datatype DirWrapper<T> =
  | DirWrapper(north: T, east: T, south: T, west: T, local: T)

  class Router {
    const id: nat
    const dim: nat
    const buffer_length: nat
    const buffers: DirectionWrapper<Buffer>
    const serviced: DirectionWrapper<bool>
    const used: DirectionWrapper<bool>
    var priority_list: FixedSeq<Direction>
    
    ghost var all_packets: set<nat>

    predicate validMetadata() {
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
      ensures validMetadata()
      ensures fresh(this.buffers) && fresh(this.serviced) && fresh(this.used)
      ensures this.buffers.north.length() == 0
      ensures this.buffers.east.length()  == 0
      ensures this.buffers.south.length() == 0
      ensures this.buffers.west.length()  == 0
      ensures this.buffers.local.length() == 0
      ensures this.serviced.asSeq() == [false, false, false, false, false]
      ensures this.used.asSeq() == [false, false, false, false, false]
      ensures this.priority_list == [North, East, South, West, Local]
      ensures this.all_packets == {}
    {
      this.id := id;
      this.dim := dim;
      this.buffer_length := buffer_length;
      this.buffers := new DirectionWrapper(Buffer.init(), Buffer.init(), Buffer.init(), Buffer.init(), Buffer.init());
      this.serviced := new DirectionWrapper(false, false, false, false, false);
      this.used := new DirectionWrapper(false, false, false, false, false);
      this.priority_list := [North, East, South, West, Local];
      this.all_packets := {};
    }

    // --- Helper Functions ---

    function x(): (x: nat)
      requires validMetadata()
    {
      this.id % this.dim
    }

    function y(): (y: nat)
      requires validMetadata()
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
      requires validMetadata()
      ensures fresh(n)
      ensures n.local.None?
      ensures
        var id := this.id - this.dim;
        && (isValidNeighborId(id) ==> n.north.Some? && n.north.value == id)
        && (!isValidNeighborId(id) ==> n.north.None?)
      ensures
        var id := this.id + 1;
        && (isValidNeighborId(id) && this.x() < this.dim - 1 ==> n.east.Some? && n.east.value == id)
        && (!isValidNeighborId(id) || this.x() == this.dim - 1 ==> n.east.None?)
      ensures
        var id := this.id + this.dim;
        && (isValidNeighborId(id) ==> n.south.Some? && n.south.value == id)
        && (!isValidNeighborId(id) ==> n.south.None?)
      ensures
        var id := this.id - 1;
        && (isValidNeighborId(id) && this.x() != 0 ==> n.west.Some? && n.west.value == id)
        && (!isValidNeighborId(id) || this.x() == 0 ==> n.west.None?)
    {
      n := new DirectionWrapper(Wrappers.Option.None, Wrappers.Option.None, Wrappers.Option.None, Wrappers.Option.None, Wrappers.Option.None);
      
      // North
      var id_n := this.id - this.dim;
      if isValidNeighborId(id_n) {
        n.north := Wrappers.Option.Some(id_n);
      }

      // East
      var id_e := this.id + 1;
      if isValidNeighborId(id_e) && this.x() < this.dim - 1 {
        n.east := Wrappers.Option.Some(id_e);
      }

      // South
      var id_s := this.id + this.dim;
      if isValidNeighborId(id_s) {
        n.south := Wrappers.Option.Some(id_s);
      }

      // West
      var id_w := this.id - 1;
      if isValidNeighborId(id_w) && this.x() != 0 {
        n.west := Wrappers.Option.Some(id_w);
      }
    }

    function isConnected(): (n: DirWrapper<bool>)
      requires validMetadata()
    {
      DirWrapper(isValidNeighborId(this.id - this.dim),
                 isValidNeighborId(this.id + 1),
                 isValidNeighborId(this.id + this.dim),
                 isValidNeighborId(this.id - 1),
                 true)
    }

    predicate isNeighborsWith(other: Router)
      requires this.validMetadata() && other.validMetadata() && this.dim == other.dim
      reads this, other
    {
      || this.id - this.dim == other.id
      || this.id + 1        == other.id
      || this.id + this.dim == other.id
      || this.id - 1        == other.id
    }

    lemma ifNeighborsThenValidId(other: Router)
      requires this.validMetadata() && other.validMetadata() && this.dim == other.dim
      requires this.isNeighborsWith(other)
      ensures 0 <= other.id < this.dim*this.dim && other.id != this.id
    {}

    predicate channelConnected(ch: Direction)
      requires validMetadata()
      requires !ch.Local?
    {
      match ch
      case North => this.y() != 0
      case East  => this.x() < dim - 1
      case South => this.y() < dim - 1
      case West  => this.x() != 0
    }

    function flatten<T>(s: seq<seq<T>>): seq<T> {
      if s == [] then [] else s[0] + flatten(s[1..])
    }

    lemma inFlatten<T>(s: seq<seq<T>>)
      ensures forall i, j | i in s && j in i :: j in flatten(s)
    {}

    lemma existsInFlatten<T>(x: T, s: seq<seq<T>>)
      ensures (exists i | i in s :: x in i) ==> x in flatten(s)
    {}

    ghost function flattenBuffers(): seq<nat>
      reads this.buffers
    {
      this.buffers.north.buffer +
      this.buffers.east.buffer  +
      this.buffers.south.buffer +
      this.buffers.west.buffer  +
      this.buffers.local.buffer
    }

    ghost predicate bufferLengthsValid()
      reads this.buffers
    {
      && this.buffers.north.length() <= this.buffer_length
      && this.buffers.east.length()  <= this.buffer_length
      && this.buffers.south.length() <= this.buffer_length
      && this.buffers.west.length()  <= this.buffer_length
      && this.buffers.local.length() <= this.buffer_length
    }
    
    ghost predicate priorityListIsValid()
      reads this`priority_list
    {
      && North in this.priority_list
      && East  in this.priority_list
      && South in this.priority_list
      && West  in this.priority_list
      && Local in this.priority_list
    }

    lemma priorityListAllDirectionsPresent(p: seq<Direction>)
      requires |p| == 5
      requires forall i, j | 0 <= i < 5 && 0 <= j < 5 && i != j :: p[i] != p[j]
      ensures North in p && East in p && South in p && West in p && Local in p
    {
      var items := {p[0], p[1], p[2], p[3], p[4]};
      assert |items| == 5; 

      var allDirs := {North, East, South, West, Local};
      assert |allDirs| == 5;

      if North !in items {
        assert items <= {East, South, West, Local};
        assert |items| <= 4;
        assert false;
      }

      // Only prove North, then Z3 can automatically prove the rest
    }

    ghost predicate packetsInBufferAreValid(buf: Direction)
      reads this.buffers
    {
      forall j | j in this.buffers.fromDir(buf).buffer :: isValidId(j)
    }

    ghost predicate allPacketsAreValid()
      reads this`all_packets
    {
      forall p | p in this.all_packets :: isValidId(p)
    }

    lemma packetsInBufferAreValidAxiom(buf: Direction)
      requires allPacketsAreValid()
      ensures {:axiom} packetsInBufferAreValid(buf)

    // --- Router Functionality ---
    method generateFlits(dest: Wrappers.Option<nat>)
      requires validMetadata()
      requires this.bufferLengthsValid()
      requires allPacketsAreValid()
      requires packetsInBufferAreValid(Local)
      requires dest.Some? ==> this.buffers.local.length() < this.buffer_length
      requires dest.Some? ==> isValidId(dest.value) && dest.value != this.id
      modifies this.buffers`local
      modifies this`all_packets
      ensures this.bufferLengthsValid()
      ensures packetsInBufferAreValid(Local)
      ensures dest.Some? ==> dest.value in this.all_packets && this.allPacketsAreValid()
    {
      if dest.Some? {
        this.buffers.local := this.buffers.local.insert(dest.value);
        this.all_packets := this.all_packets + {dest.value};
      }
    }

    method prepRouter(cycle: nat)
      requires validMetadata()
      requires this.bufferLengthsValid()
      modifies this.buffers
      ensures this.bufferLengthsValid()
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
      requires validMetadata()
      requires this.bufferLengthsValid()
      requires this.allPacketsAreValid()
      requires other.validMetadata()
      requires other.bufferLengthsValid()
      requires other.allPacketsAreValid()
      requires this.dim == other.dim
      requires this.buffer_length == other.buffer_length
      requires this.id != other.id
      requires dir != Local
      requires this.buffers.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`all_packets
      modifies other.buffers
      modifies other`all_packets
      ensures this.bufferLengthsValid()
      ensures this.allPacketsAreValid()
      ensures other.bufferLengthsValid()
      ensures other.allPacketsAreValid()
    {
      var dest_dir := dir.getDestinationDir();

      if !other.buffers.fromDir(dest_dir).isFull && !this.used.fromDir(dir) {
        // AXIOM: todo
        assume {:axiom} other.buffers.fromDir(dest_dir).length() < other.buffer_length;

        // Other Axiom: todo
        this.packetsInBufferAreValidAxiom(from);
        other.packetsInBufferAreValidAxiom(from);

        // Send packet from source
        var from_channel := this.buffers.fromDir(from);
        var packet := from_channel.peekFirst();
        this.buffers.writeByDir(from, from_channel.dropFirst());
        this.all_packets := this.all_packets - {packet};

        // recieve packet at destination
        other.buffers.writeByDir(dest_dir, other.buffers.fromDir(dest_dir).insert(packet));
        other.all_packets := other.all_packets - {packet};

        // mark used
        this.used.writeByDir(dir, true);
        this.serviced.writeByDir(from, true);

        // Check that still valid
        assert this.packetsInBufferAreValid(from);
        assert other.packetsInBufferAreValid(from) by {
          assert packet in old(this.buffers.fromDir(from).buffer) && isValidId(packet);
        }
      }
    }

    method advanceFlits(other: Router, from: Direction)
      requires validMetadata()
      requires this.bufferLengthsValid()
      requires this.allPacketsAreValid()
      requires other.validMetadata()
      requires other.bufferLengthsValid()
      requires other.allPacketsAreValid()
      requires this.dim == other.dim
      requires this.buffer_length == other.buffer_length
      requires this.id != other.id
      requires this.isNeighborsWith(other)
      requires this.buffers.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`all_packets
      modifies other.buffers
      modifies other`all_packets
      ensures this.bufferLengthsValid()
      ensures this.allPacketsAreValid()
      ensures other.bufferLengthsValid()
      ensures other.allPacketsAreValid()
    {
      var dest_id := this.buffers.fromDir(from).peekFirst();
      assert isValidId(dest_id) by {
        this.packetsInBufferAreValidAxiom(from);
      }
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
      requires validMetadata()
      requires this.bufferLengthsValid()
      requires this.allPacketsAreValid()
      requires other.validMetadata()
      requires other.bufferLengthsValid()
      requires other.allPacketsAreValid()
      requires this.dim == other.dim
      requires this.buffer_length == other.buffer_length
      requires this.id != other.id
      requires this.isNeighborsWith(other)
      requires this.buffers.fromDir(from).length() > 0
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`all_packets
      modifies other.buffers
      modifies other`all_packets
      ensures this.bufferLengthsValid()
      ensures this.allPacketsAreValid()
      ensures other.bufferLengthsValid()
      ensures other.allPacketsAreValid()
    {
      if (!from.Local? && this.channelConnected(from)) || this.buffers.fromDir(from).isEmpty {
        this.serviced.writeByDir(from, true);
      } else if (this.buffers.fromDir(from).peekFirst() == this.id) {
        if !this.used.local {
          this.packetsInBufferAreValidAxiom(from);
          this.used.local := true;
          var b := this.buffers.fromDir(from);
          var packet := b.peekFirst();
          this.buffers.writeByDir(from, b.dropFirst());
          this.serviced.writeByDir(from, true);
          assert this.packetsInBufferAreValid(from);
          this.all_packets := this.all_packets - {packet};
        }
      } else {
        advanceFlits(other, from);
      }
    }

    method advanceRouter(routers: seq<Router>)
      requires validMetadata()
      requires |routers| == this.dim*this.dim
      requires routers[this.id] == this
      requires forall r | r in routers :: (
        && r.validMetadata()
        && r.bufferLengthsValid()
        && r.allPacketsAreValid()
        && r.dim == this.dim
        && r.buffer_length == this.buffer_length
      )
      requires forall i | 0 <= i < |routers| :: (
        && routers[i].id == i
      )
      modifies this.serviced
      modifies this.used
      modifies this.buffers
      modifies this`all_packets
      modifies set x | x in routers :: x.buffers
      modifies set x | x in routers :: x`all_packets
      ensures forall r | r in routers :: (
        && r.bufferLengthsValid()
        && r.allPacketsAreValid()
      )
    {
      for i := 0 to |this.priority_list|
        invariant forall r | r in routers :: (
          && r.bufferLengthsValid()
          && r.allPacketsAreValid()
        )
        modifies this.serviced
        modifies this.used
        modifies this.buffers
        modifies this`all_packets
        modifies set x | x in routers :: x.buffers
        modifies set x | x in routers :: x`all_packets
      {
        match this.priority_list[i]
        case North => {
          var id_ := this.id - this.dim;
          if isValidNeighborId(id_) && this.buffers.fromDir(North).length() > 0 {
            this.advanceChannel(routers[id_], North);
          }
        }

        case East => {
          var id_ := this.id + 1;
          if isValidNeighborId(id_) && this.x() < this.dim - 1 && this.buffers.fromDir(East).length() > 0 {
            this.advanceChannel(routers[id_], East);
          }
        }

        case South => {
          var id_ := this.id + this.dim;
          if isValidNeighborId(id_) && this.buffers.fromDir(South).length() > 0 {
            this.advanceChannel(routers[id_], South);
          }
        }

        case West => {
          var id_ := this.id - 1;
          if isValidNeighborId(id_) && this.x() != 0 && this.buffers.fromDir(West).length() > 0 {
            this.advanceChannel(routers[id_], West);
          }
        }

        case Local =>
      }
    }
    
    method updatePriority()
      requires this.priorityListIsValid()
      modifies this`priority_list
      modifies this.serviced
      modifies this.used
      ensures this.serviced.asSeq() == [false, false, false, false, false]
      ensures this.used.asSeq() == [false, false, false, false, false]
      ensures this.priorityListIsValid()
    {
      var priority_list_temp: FixedSeq<Direction> := [North, East, South, West, Local];
      var unserviced_index := 0;
      var indices: FixedSeq<nat> := [0, 1, 2, 3, 4];
      var s_in_order := Seq.Map((x) reads this.serviced => this.serviced.fromDir(x), this.priority_list);
      assert |s_in_order| == 5;

      for i := 0 to 5
        invariant 0 <= unserviced_index <= i
        invariant forall j: nat | j < 5 :: 0 <= indices[j] < 5
        invariant forall j: nat, k: nat | j != k && j < 5 && k < 5 :: indices[j] != indices[k]
      {
        if s_in_order[indices[unserviced_index]] {
          indices := indices[0..unserviced_index] + indices[unserviced_index+1..] + [indices[unserviced_index]];
        } else {
          unserviced_index := unserviced_index + 1;
        }
      }

      for i := 0 to 5
        invariant forall j: nat, k: nat | j != k && j < i && k < i :: indices[j] != indices[k]
        invariant forall j: nat, k: nat | j != k && j < i && k < i :: this.priority_list[j] != this.priority_list[k]
        invariant forall j: nat, k: nat | j != k && j < i && k < i :: this.priority_list[indices[j]] != this.priority_list[indices[k]]
        invariant forall j: nat | j < i :: priority_list_temp[j] == this.priority_list[indices[j]]
        invariant forall j: nat, k: nat | j != k && j < i && k < i :: priority_list_temp[j] != priority_list_temp[k]
      {
        priority_list_temp := priority_list_temp[i := this.priority_list[indices[i]]];
      }

      // if all channels are empty then reset the priority list
      if Seq.FoldLeft((x, y) => x && y, true, Seq.Map((z: Buffer) => z.isEmpty, this.buffers.asSeq())) {
        this.priority_list := [North, East, South, West, Local];
      } else {
        this.priorityListAllDirectionsPresent(priority_list_temp);
        this.priority_list := priority_list_temp;
        assert this.priorityListIsValid();
      }

      // Reset other variables
      this.serviced.setAllTo(false);
      this.used.setAllTo(false);
    }
  }


  method getPackets(id: nat, dim: nat) returns (dest: nat)
    ensures {:axiom} 0 <= dest < dim*dim && dest != id
  
  method getDestinationAllowsAllNeighbors(id: nat, dim: nat) returns (dest: nat)
    ensures 0 <= dest < dim*dim && dest != id
  {
    dest := getPackets(id, dim);
  }

  datatype NoC = NoC(dim: nat)
  {
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
          && routers[j].used.asSeq() == [false, false, false, false, false]
          && routers[j].priority_list == [North, East, South, West, Local]
          && routers[j].validMetadata()
          && routers[j].all_packets == {}
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
          && routers[j].used.asSeq() == [false, false, false, false, false]
          && routers[j].priority_list == [North, East, South, West, Local]
          && routers[j].validMetadata()
          && routers[j].all_packets == {}
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
        invariant forall r | r in routers :: fresh(r) && fresh(r.buffers) && fresh(r.serviced) && fresh(r.used)
        invariant forall r | r in routers :: r.bufferLengthsValid() && r.priorityListIsValid() && r.allPacketsAreValid()
        modifies routers[..]
        modifies set x | x in routers :: x.serviced
        modifies set x | x in routers :: x.used
        modifies set x | x in routers :: x.buffers
        modifies set x | x in routers :: x`all_packets
      {
        for i := 0 to |routers|
          invariant forall r | r in routers :: r.bufferLengthsValid() && r.priorityListIsValid() && r.allPacketsAreValid()
        {
          if cycle % 3 < 3 && routers[i].buffers.local.length() < routers[i].buffer_length {
            var dest := getPackets(routers[i].id, routers[i].dim);
            var dest_opt := Wrappers.Option.Some(dest);
            routers[i].packetsInBufferAreValidAxiom(Local);
            routers[i].generateFlits(dest_opt);
          }
        }
        for i := 0 to |routers|
          invariant forall r | r in routers :: r.bufferLengthsValid() && r.priorityListIsValid() && r.allPacketsAreValid()
        {
          routers[i].prepRouter(cycle);
        }

        for i := 0 to |routers|
          invariant {:split_here} forall r | r in routers :: r.bufferLengthsValid() && r.priorityListIsValid() && r.allPacketsAreValid()
        {
          routers[i].advanceRouter(routers);
        }

        for i := 0 to |routers|
          invariant forall r | r in routers :: r.bufferLengthsValid() && r.priorityListIsValid() && r.allPacketsAreValid()
        {
          routers[i].updatePriority();
        }

        cycle := cycle + 1;
      }
    }
  }
}
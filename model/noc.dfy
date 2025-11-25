module NoC {
  type Length = i: nat | 1 <= i witness 1

  const BUFFER_LENGTH: Length

  datatype Direction =
    | North
    | South
    | East
    | West
    | Local

  class Buffer {
    var storage: array<nat>
    var used: nat

    constructor()
      ensures used == 0
      ensures storage.Length == BUFFER_LENGTH
    {
      used := 0;
      storage := new nat[BUFFER_LENGTH](_ => 0);
    }

    function capacity(): nat
      reads this`storage
    {
      storage.Length
    }

    function length(): nat
      reads this
    {
      used
    }

    method append(n: nat)
      requires used < this.storage.Length
      modifies this`storage
      modifies this`storage[used]
      ensures old(used) + 1 == used
      ensures this.storage[old(used)] == n
    {
      this.storage[used] := n;
      used := used + 1;
    }
  }

  class Router {
    var North: Buffer
    var East:  Buffer
    var South: Buffer
    var West:  Buffer
    var Local: Buffer

    constructor()
      ensures North.length() == 0 && North.capacity() == BUFFER_LENGTH
      ensures East.length()  == 0 && East.capacity() == BUFFER_LENGTH
      ensures South.length() == 0 && South.capacity() == BUFFER_LENGTH
      ensures West.length()  == 0 && West.capacity() == BUFFER_LENGTH
      ensures Local.length() == 0 && Local.capacity() == BUFFER_LENGTH
    {
      North := new Buffer();
      South := new Buffer();
      East  := new Buffer();
      West  := new Buffer();
      Local := new Buffer();
    }

    method insertLocal(payload: nat)
      modifies this.Local.storage
    {
      this.Local.append(payload);
    }
  }
}
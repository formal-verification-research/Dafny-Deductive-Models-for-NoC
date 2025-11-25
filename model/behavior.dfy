include "noc.dfy"

import Std.Collections.Seq

type BufferLength = i: nat | 1 <= i witness 1

function neighbor_id(x: nat, y: nat, dir: Direction, dim: nat): ConnectId
{
  match dir
  case North => if y == 0 then NoConnect else Id(x + (y - 1) * dim)
  case West  => if x == 0 then NoConnect else Id((x - 1) + y * dim)
  case East  => if x + 1 >= dim then NoConnect else Id((x + 1) + y * dim)
  case South => if y + 1 >= dim then NoConnect else Id(x + (y + 1) * dim)
  case Local => Id(x + y * dim)
}

function generate_neighbors(x: nat, y: nat, dim: nat): DirSeq<ConnectId>
{
  DirSeq(
    neighbor_id(x, y, North, dim),
    neighbor_id(x, y, East, dim),
    neighbor_id(x, y, South, dim),
    neighbor_id(x, y, West, dim),
    neighbor_id(x, y, Local, dim)
  )
}

function get_pos(id: Id, dim: nat): (nat, nat)
  requires id < dim * dim
{
  (id % dim, id / dim)
}

method newNoC(dim: nat) returns (n: Noc)
  requires dim >= 2
  ensures |n| == dim && Valid(n)
{
  var id := 0;
  n := seq(dim,
    y requires 0 <= y < dim => seq(dim,
      x requires 0 <= x < dim => Router(
        y*dim + x,
        DirSeq(
          Channel(Buffer.None, false, true, false),
          Channel(Buffer.None, false, true, false),
          Channel(Buffer.None, false, true, false),
          Channel(Buffer.None, false, true, false),
          Channel(Buffer.None, false, true, false)
        ),
        generate_neighbors(x, y, dim),
        [East, West, North, South, Local],
        0,
        0,
        0,
        0,
        0,
        seq(5, _ => false)
      )
    )
  );
}

method generate_flits(r: Router, id: Id, cycle: nat, maxBufferLength: BufferLength, dim: nat) returns (r': Router)
  ensures
    && r'.id == r.id
    && r.channels.Local.buffer.is_prefix_of(r'.channels.Local.buffer)
    && r'.channels.Local.buffer.length() <= maxBufferLength
    && r'.priority_list == r.priority_list
    && r'.serviced_idx == r.serviced_idx
    && r'.unserviced_idx == r.unserviced_idx
    && r'.total_unserviced == r.total_unserviced
    && r'.thisActivity == r.thisActivity
    && r'.lastActivity == r.lastActivity
    && r'.used == r.used
{
  if cycle % 3 >= 3 || r.channels.Local.buffer.length() == maxBufferLength {
    r' := r;
    return;
  }

  var dest_id :| 0 <= dest_id < dim * dim && dest_id != r.id;

  r' := r;
  r'.channels.Local.buffer
}
// include "flit_generation.dfy"
include "channel.dfy"
include "neighbor.dfy"

datatype DirSeq<T> =
  | DirSeq(
    North: T,
    South: T,
    East:  T,
    West:  T,
    Local: T
  )

datatype Router = 
  | Router(id: Id,
           channels: DirSeq<Channel>,
           ids: DirSeq<ConnectId>,
           priority_list: seq<Direction>,
           serviced_idx: nat,
           unserviced_idx: nat,
           total_unserviced: nat,
           thisActivity: nat,
           lastActivity: nat,
           used: seq<bool>)
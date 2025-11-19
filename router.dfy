// include "flit_generation.dfy"
include "channel.dfy"
include "neighbor.dfy"

datatype Router = 
  | Router(channels: seq<Channel>,
           ids: seq<ConnectId>,
           priority_list: seq<Id>,
           priority_list_temp: seq<Id>,
           serviced_idx: nat,
           unserviced_idx: nat,
           total_unserviced: nat,
           thisActivity: nat,
           lastActivity: nat,
           used: seq<bool>)
include "buffer.dfy"

datatype Channel =
  | Channel(buffer: Buffer, serviced: bool, isEmpty: bool, isFull: bool)
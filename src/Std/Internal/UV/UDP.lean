/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.System.IO
import Init.System.Promise
import Std.Net

namespace Std
namespace Internal
namespace UV
namespace UDP

open Std.Net

private opaque SocketImpl : NonemptyType.{0}

/--
Represents a UDP socket.
-/
def Socket : Type := SocketImpl.type

instance : Nonempty Socket := SocketImpl.property

/--
Membership type for multicast operations.
-/
inductive Membership
  | leaveGroup
  | enterGroup

namespace Socket

/--
Creates a new UDP socket.
-/
@[extern "lean_uv_udp_new"]
opaque new : IO Socket

/--
Binds an UDP socket to a specific address.
-/
@[extern "lean_uv_udp_bind"]
opaque bind (socket : @& Socket) (addr : SocketAddress) : IO Unit

/--
Connects an UDP socket to the specified address.
-/
@[extern "lean_uv_udp_connect"]
opaque connect (socket : @& Socket) (addr : SocketAddress) : IO Unit

/--
Sends data through an UDP socket.
-/
@[extern "lean_uv_udp_send"]
opaque send (socket : @& Socket) (data : ByteArray) (addr : Option SocketAddress) : IO (IO.Promise (Except IO.Error Unit))

/--
Receives data from an UDP socket. `size` is for the maximum bytes to receive. The promise
resolves when some data is available or an error occurs.
-/
@[extern "lean_uv_udp_recv"]
opaque recv (socket : @& Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error ByteArray))

/--
Gets the remote address of a connected UDP socket.
-/
@[extern "lean_uv_udp_getpeername"]
opaque getpeername (socket : @& Socket) : IO SocketAddress

/--
Gets the local address of a bound UDP socket.
-/
@[extern "lean_uv_udp_getsockname"]
opaque getsockname (socket : @& Socket) : IO SocketAddress

/--
Enables or disables broadcasting on a UDP socket.
-/
@[extern "lean_uv_udp_set_broadcast"]
opaque set_broadcast (socket : @& Socket) (on : Int32) : IO Unit

/--
Enables or disables multicast loopback for a UDP socket.
-/
@[extern "lean_uv_udp_set_multicast_loop"]
opaque set_multicast_loop (socket : @& Socket) (on : Int32) : IO Unit

/--
Sets the time-to-live (TTL) value for multicast packets.
-/
@[extern "lean_uv_udp_set_multicast_ttl"]
opaque set_multicast_ttl (socket : @& Socket) (ttl : UInt32) : IO Unit

/--
Sets the membership for joining or leaving a multicast group.
-/
@[extern "lean_uv_udp_set_membership"]
opaque set_membership (socket : @& Socket) (multicast_addr interface_addr : String) (membership : Membership) : IO Unit

/--
Sets the multicast interface for sending packets.
-/
@[extern "lean_uv_udp_set_multicast_interface"]
opaque set_multicast_interface (socket : @& Socket) (interface_addr : String) : IO Unit

/--
Sets the TTL value for outgoing packets.
-/
@[extern "lean_uv_udp_set_ttl"]
opaque set_ttl (socket : @& Socket) (ttl : UInt32) : IO Unit

end Socket
end UDP
end UV
end Internal
end Std

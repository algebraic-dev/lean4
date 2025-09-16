/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Time
public import Std.Internal.Http.Data

public section

namespace Std
namespace Http
namespace H1
namespace Machine

instance : Repr ByteArray where
  reprPrec s _ := toString s

/--
Events that can occur during HTTP message processing.
-/
inductive Event
  /--
  Event received when chunk extension data is encountered in chunked encoding.
  -/
  | chunkExt (ext : ByteArray)

  /--
  Event received the headers end.
  -/
  | endHeaders (size : Data.Request.Head)

  /--
  Event received when some data arrives from the received thing.
  -/
  | gotData (final : Bool) (data : ByteSlice)

  /--
  Need more data is an event that arrives when the input ended and it requires more
  data to continue
  -/
  | needMoreData (size : Option Nat)

  /--
  Event received when parsing or processing fails with an error message.
  -/
  | failed

  /--
  Event received when connection should be closed.
  -/
  | close

  /--
  Awaiting the next request
  -/
  | next
deriving Inhabited

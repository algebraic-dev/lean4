/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Time

public section

namespace Std
namespace Http
namespace H1
namespace Machine

/--
Connection limits configuration with validation.
-/
structure Config where
  /--
  Maximum number of requests per connection.
  -/
  maxRequests : Nat := 100

  /--
  Maximum number of headers allowed per request.
  -/
  maxHeaders : Nat := 50

  /--
  Maximum size of a single header value.
  -/
  maxHeaderSize : Nat := 8192

  /--
  Connection timeout in seconds.
  -/
  timeoutSeconds : Time.Second.Offset := 10

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  Whether to enable chunked transfer encoding.
  -/
  enableChunked : Bool := true

  /--
  Size threshold for flushing output buffer.
  -/
  highMark : Nat := 4096

  /--
  Preserve header case
  -/
  preserveHeaderCase : Bool := false

  /--
  Maximum buffer size for the connection
  -/
  maximumBufferSize : Nat := 400 * 1024

  /--
  Default buffer size for the connection
  -/
  defaultPayloadBytes : Nat := 8192

  /--
  Automatic Date Header.
  -/
  autoDateHeader : Bool := false

  /--
  Allow trailer fields.
  -/
  allowTrailer : Bool := false

  /--
  The server name
  -/
  serverName : Option String := "Lean-HTTP/1.1"

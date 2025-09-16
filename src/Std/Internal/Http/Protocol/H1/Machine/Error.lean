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
Specific HTTP processing errors with detailed information.
-/
inductive Error where
  /--
  Malformed request line or status line.
  -/
  | invalidStatusLine

  /--
  Invalid or malformed header.
  -/
  | invalidHeader

  /--
  Request timeout occurred.
  -/
  | timeout

  /--
  Request entity too large.
  -/
  | entityTooLarge

  /--
  Unsupported HTTP method.
  -/
  | unsupportedMethod

  /--
  Unsupported HTTP version.
  -/
  | unsupportedVersion

  /--
  Invalid chunk encoding.
  -/
  | invalidChunk

  /--
  Bad request
  -/
  | badRequest

  /--
  Generic error with message.
  -/
  | other (message : String)
deriving Repr, BEq

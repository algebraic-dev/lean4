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
public import Std.Internal.Http.Protocol.H1.Machine.Error

public section

namespace Std
namespace Http
namespace H1
namespace Machine

inductive Reader.State : Type
  /--
  Initial state waiting for HTTP start line.
  -/
  | needStartLine : State

  /--
  State waiting for HTTP headers, tracking number of headers parsed.
  -/
  | needHeader : Nat → State

  /--
  State waiting for chunk size in chunked transfer encoding.
  -/
  | needChunkedSize : State

  /--
  State waiting for chunk body data of specified size.
  -/
  | needChunkedBody : Nat → State

  /--
  State waiting for fixed-length body data of specified size.
  -/
  | needFixedBody : Nat → State

  /--
  Requires the response to continue.
  -/
  | requireResponse : Data.Body.Length → State

  /--
  State when request is fully parsed and ready to generate response.
  -/
  | complete : State

  /--
  The input is malformed.
  -/
  | failed (error : Data.Response.Head) : State
deriving Inhabited, Repr

inductive Writer.State
  /--
  Ready to write the response
  -/
  | waitingHeaders

  /--
  This is the state that we wait for a forced flush. This happens and causes the writer to
  start actually writing to the outputData
  -/
  | waitingForFlush

  /--
  Writing the headers.
  -/
  | writingHeaders

  /--
  Writing a fixed size body output.
  -/
  | writingFixedData

  /--
  Writing chunked data.
  -/
  | writingChunkedBody

  /--
  State when response is fully sent and ready to the next request.
  -/
  | complete : State
deriving Inhabited, Repr, BEq

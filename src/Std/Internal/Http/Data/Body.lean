/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Sync
public import Std.Internal.Async
public import Std.Internal.Http.Encode
public import Std.Internal.Http.Data.Headers
public import Std.Internal.Http.Data.Method
public import Std.Internal.Http.Data.Version
public import Std.Internal.Http.Data.Body.Length
public import Std.Internal.Http.Data.Body.ByteStream

public section

open Std Internal IO Async

namespace Std
namespace Http
namespace Data

/--
Inductive type for HTTP body content
-/
inductive Body where
  | zero
  | bytes (data : ByteArray)
  | stream (channel : Body.ByteStream)
deriving Inhabited

namespace Body

/--
Get content length of a body (if known).
-/
def getContentLength (body : Body) : Length :=
  match body with
  | zero => .fixed 0
  | .bytes data => .fixed data.size
  | .stream _ => .chunked

def close (body : Body) : Async Unit :=
  match body with
  | .stream channel => channel.close
  | _ => pure ()

instance : Coe String Body where
  coe := .bytes ∘ String.toUTF8

instance : Coe Body.ByteStream Body where
  coe := .stream

instance : Coe Body Body where
  coe := id

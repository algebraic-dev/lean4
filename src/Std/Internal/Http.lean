/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.IO
public import Init.System.Promise
public import Std.Internal.Http.Basic
public import Std.Internal.Http.Data
public import Std.Internal.Http.Protocol
public import Std.Internal.Http.Connection

public section

namespace Std
namespace Http

/-!
# Http

The Lean API for Http.

# Overview

This module of the standard library defines a lot of concepts related to HTTP protocol
and the semantics in a Sans/IO format.

# Http 1.1

It's made mainly for Http 1.1 using https://httpwg.org/specs/rfc9112.html as the main
recomendation.

-/

export Std.Http.Data (Request Response Body Status Method RequestTarget Request.Head Response.Head)

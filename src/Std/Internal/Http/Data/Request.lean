/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Internal.Http.Encode
public import Std.Internal.Http.Data.Headers
public import Std.Internal.Http.Data.Method
public import Std.Internal.Http.Data.Version

public section

namespace Std
namespace Http
namespace Data

/--
The main parts of a response.
-/
structure Request.Head where
  /--

  -/
  method : Method := .get

  /--

  -/
  version : Version := .v11

  /--

  -/
  uri : String := "/"

  /--

  -/
  headers : Headers := .empty
deriving Inhabited, Repr

/--
HTTP request structure parameterized by body type
-/
structure Request (t : Type) where
  /--

  -/
  head : Request.Head

  /--

  -/
  body : t

namespace Request

instance : ToString Head where
  toString req :=
    toString req.method ++ " " ++
    req.uri ++ " " ++
    toString req.version ++
    "\r\n" ++
    toString req.headers ++ "\r\n\r\n"

@[inline]
def isInformational (request : Head) : Prop :=
  ¬request.method.allowsRequestBody

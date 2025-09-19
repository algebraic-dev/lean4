/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Lean
public import Std.Internal.Http.Encode
public import Std.Internal.Http.Data.Body
public import Std.Internal.Http.Data.Headers
public import Std.Internal.Http.Data.Method
public import Std.Internal.Http.Data.Version
public import Std.Internal.Http.Data.URI

public section

namespace Std
namespace Http
namespace Data

open Lean

/--
The main parts of a request containing the HTTP method, version, URI, and headers.
-/
structure Request.Head where
  /--
  The HTTP method (GET, POST, PUT, DELETE, etc.) for the request
  -/
  method : Method := .get

  /--
  The HTTP protocol version (HTTP/1.0, HTTP/1.1, HTTP/2.0, etc.)
  -/
  version : Version := .v11

  /--
  The request target/URI indicating the resource being requested
  -/
  uri : RequestTarget := .asteriskForm

  /--
  Collection of HTTP headers for the request (Content-Type, Authorization, etc.)
  -/
  headers : Headers := .empty
deriving Inhabited, Repr

/--
HTTP request structure parameterized by body type
-/
structure Request (t : Type) where
  /--
  The request headers and metadata
  -/
  head : Request.Head

  /--
  The request body content of type t
  -/
  body : Option t
deriving Inhabited

/--
Builds a HTTP Request
-/
structure Request.Builder where
  head : Head := {}

namespace Request

instance : ToString Head where
  toString req :=
    toString req.method ++ " " ++
    toString req.uri ++ " " ++
    toString req.version ++
    "\r\n" ++
    toString req.headers ++ "\r\n\r\n"

/--
Determines if a request method typically doesn't allow a request body
-/
@[inline]
def isInformational (request : Head) : Prop :=
  ¬request.method.allowsRequestBody

/--
Creates a new HTTP Request builder with default head (method: GET, version: HTTP/1.1, asterisk URI, empty headers)
-/
def new : Builder := { }

namespace Builder

/--
Creates a new HTTP Request builder with default head (method: GET, version: HTTP/1.1, asterisk URI, empty headers)
-/
def empty : Builder := { }

/--
Sets the HTTP method for the request being built
-/
def method (builder : Builder) (method : Method) : Builder :=
  { builder with head := { builder.head with method := method } }

/--
Sets the HTTP version for the request being built
-/
def version (builder : Builder) (version : Version) : Builder :=
  { builder with head := { builder.head with version := version } }

/--
Sets the request target/URI for the request being built
-/
def uri (builder : Builder) (uri : RequestTarget) : Builder :=
  { builder with head := { builder.head with uri := uri } }

/--
Adds a single header to the request being built
-/
def header (builder : Builder) (key : String) (value : String) : Builder :=
  { builder with head := { builder.head with headers := builder.head.headers.insert key value } }

/--
Builds and returns the final HTTP Request with the specified body
-/
def body [Coe x t] (builder : Builder) (body : x) : Request t :=
  { head := builder.head, body := body }

/--
Builds and returns the final HTTP Request without a body
-/
def build (builder : Builder) : Request t :=
  { head := builder.head, body := none }

/--
Builds and returns the final HTTP Request with the specified body as JSON
-/
def json [ToJson t] (builder : Builder) (body : t) : Request Body :=
  builder
  |>.header "Content-Type" "application/json"
  |>.body (ToJson.toJson body |> toString |>.toUTF8 |> Body.bytes)

/--
Builds and returns the final HTTP Request with the specified body as binary data
-/
def binary (builder : Builder) (bytes : ByteArray) : Request Body :=
  builder
    |>.header "Content-Type" "application/octet-stream"
    |>.body (Body.bytes bytes)

/--
Builds and returns the final HTTP Request with the specified body as plain text
-/
def text (builder : Builder) (body : String) : Request Body :=
  builder
    |>.header "Content-Type" "text/plain; charset=utf-8"
    |>.body (body.toUTF8 |> Body.bytes)

/--
Builds and returns the final HTTP Request with the specified body as HTML
-/
def html (builder : Builder) (body : String) : Request Body :=
  builder
    |>.header "Content-Type" "text/html; charset=utf-8"
    |>.body (body.toUTF8 |> Body.bytes)

/--
Builds and returns the final HTTP Request with form-encoded data
-/
def form (builder : Builder) (formData : List (String × String)) : Request Body :=
  let encoded := formData.map (fun (k, v) => k ++ "=" ++ v) |>.foldl (· ++ "&" ++ ·) ""
  builder
    |>.header "Content-Type" "application/x-www-form-urlencoded"
    |>.body (encoded.toUTF8 |> Body.bytes)

end Builder

/--
Creates a new HTTP GET Request with the specified URI
-/
def get (uri : RequestTarget) : Request t :=
  new
  |>.method .get
  |>.uri uri
  |>.build

/--
Creates a new HTTP POST Request with the specified URI and body
-/
def post [Coe x t] (uri : RequestTarget) (body : x) : Request t :=
  new
  |>.method .post
  |>.uri uri
  |>.body body

/--
Creates a new HTTP PUT Request with the specified URI and body
-/
def put [Coe x t] (uri : RequestTarget) (body : x) : Request t :=
  new
  |>.method .put
  |>.uri uri
  |>.body body

/--
Creates a new HTTP DELETE Request with the specified URI
-/
def delete (uri : RequestTarget) : Request t :=
  new
  |>.method .delete
  |>.uri uri
  |>.build

/--
Creates a new HTTP PATCH Request with the specified URI and body
-/
def patch [Coe x t] (uri : RequestTarget) (body : x) : Request t :=
  new
  |>.method .patch
  |>.uri uri
  |>.body body

end Request

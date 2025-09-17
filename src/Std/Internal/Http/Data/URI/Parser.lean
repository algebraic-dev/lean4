/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Internal.Parsec
public import Std.Internal.Parsec.ByteArray
public import Std.Internal.Http.Data.URI.Basic

public section

namespace Std
namespace Http
namespace Data
namespace Parser

open Data
open Std Internal Parsec ByteArray

structure UriComponents where
  schema : Option ByteSlice
  userinfo : Option (ByteSlice × Option ByteSlice)
  host : Option ByteSlice
  port : Option ByteSlice
  path : Option ByteArray
  query : Option ByteSlice
  fragment : Option ByteSlice

@[inline]
def isDigit (c : UInt8) : Bool :=
  c >= '0'.toUInt8 && c <= '9'.toUInt8

@[inline]
def isHexDigit (c : UInt8) : Bool :=
  isDigit c || (c >= 'A'.toUInt8 && c <= 'F'.toUInt8) || (c >= 'a'.toUInt8 && c <= 'f'.toUInt8)

@[inline]
def isAlpha (c : UInt8) : Bool :=
  (c >= 'A'.toUInt8 && c <= 'Z'.toUInt8) || (c >= 'a'.toUInt8 && c <= 'z'.toUInt8)

@[inline]
def isAlphaNum (c : UInt8) : Bool :=
  isAlpha c || isDigit c

@[inline]
def isUnreserved (c : UInt8) : Bool :=
  isAlphaNum c || c == '-'.toUInt8 || c == '.'.toUInt8 || c == '_'.toUInt8 || c == '~'.toUInt8

@[inline]
def isSubDelims (c : UInt8) : Bool :=
  c == '!'.toUInt8 || c == '$'.toUInt8 || c == '&'.toUInt8 || c == '\''.toUInt8 ||
  c == '('.toUInt8 || c == ')'.toUInt8 || c == '*'.toUInt8 || c == '+'.toUInt8 ||
  c == ','.toUInt8 || c == ';'.toUInt8 || c == '='.toUInt8

@[inline]
def isGenDelims (c : UInt8) : Bool :=
  c == ':'.toUInt8 || c == '/'.toUInt8 || c == '?'.toUInt8 || c == '#'.toUInt8 ||
  c == '['.toUInt8 || c == ']'.toUInt8 || c == '@'.toUInt8

@[inline]
def isReserved (c : UInt8) : Bool :=
  isGenDelims c || isSubDelims c

@[inline]
def isPChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c == ':'.toUInt8 || c == '@'.toUInt8 || c == '%'.toUInt8

@[inline]
def isRegNameChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c == '%'.toUInt8

@[inline]
def isSchemeChar (c : UInt8) : Bool :=
  isAlphaNum c || c == '+'.toUInt8 || c == '-'.toUInt8 || c == '.'.toUInt8

@[inline]
def isQueryChar (c : UInt8) : Bool :=
  isPChar c || c == '/'.toUInt8 || c == '?'.toUInt8

@[inline]
def isFragmentChar (c : UInt8) : Bool :=
  isPChar c || c == '/'.toUInt8 || c == '?'.toUInt8

@[inline]
def isUserInfoChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c == '%'.toUInt8

def failNone (x : Option α) : Parser α :=
  if let some res := x then
    pure res
  else
    fail "expected value but got none"

def tryOpt (p : Parser α) : Parser (Option α) := optional (attempt p)

def parsePctEncoded : Parser ByteSlice := do
  skipByte '%'.toUInt8
  takeWhileUpTo1 isHexDigit 2

def parseScheme : Parser ByteSlice := do
  takeWhileUpTo1 isSchemeChar 63

def parsePort : Parser ByteSlice := do
  takeWhileUpTo isDigit 5

def parseUserInfo : Parser (ByteSlice × Option ByteSlice) := do
  let mut userBytes : ByteArray := .empty

  -- Parse user part
  while true do
    let c? ← peek?
    match c? with
    | none => break
    | some c =>
      if c == ':'.toUInt8 then
        skip
        let mut passBytes : ByteArray := .empty
        while true do
          let pc? ← peek?
          match pc? with
          | none => break
          | some pc =>
            if pc == '@'.toUInt8 then break
            else if pc == '%'.toUInt8 then
              let encoded ← parsePctEncoded
              passBytes := passBytes ++ encoded.toByteArray
            else if isUserInfoChar pc then
              skip
              passBytes := passBytes.push pc
            else break
        return (userBytes.toByteSlice, some passBytes.toByteSlice)
      else if c == '@'.toUInt8 then
        break
      else if c == '%'.toUInt8 then
        let encoded ← parsePctEncoded
        userBytes := userBytes ++ encoded.toByteArray
      else if isUserInfoChar c then
        skip
        userBytes := userBytes.push c
      else
        break

  return (userBytes.toByteSlice, none)

-- Host parsing (simplified)
def parseHost : Parser ByteSlice := do
  if (← peek?).any (· == '['.toUInt8) then
    -- IP literal
    let mut result : ByteArray := .empty
    while true do
      let c? ← peek?
      match c? with
      | none => fail "unterminated IP literal"
      | some c =>
        skip
        result := result.push c
        if c == ']'.toUInt8 then break
    return result.toByteSlice
  else
    -- Regular name or IPv4
    takeWhileUpTo isRegNameChar 255

def parseAuthority : Parser (Option (ByteSlice × Option ByteSlice) × Option ByteSlice × Option ByteSlice) := do
  let userinfo ← tryOpt do
    let ui ← parseUserInfo
    skipByte '@'.toUInt8
    return ui

  let host ← parseHost
  if host.size == 0 then
    fail "expected host"

  let port ← optional do
    skipByte ':'.toUInt8
    parsePort

  return (userinfo, some host, port)

def parseSegment : Parser ByteSlice := do
  takeWhileUpTo (fun c => isPChar c && c != '/'.toUInt8) 1024

def parsePathSegments : Parser ByteArray := do
  let mut result : ByteArray := .empty
  let mut first := true

  while (← peek?).any (· == '/'.toUInt8) || first do
    if !first then
      skip
      result := result.push '/'.toUInt8
    first := false

    let segment ← parseSegment
    result := result ++ segment.toByteArray

    if (← peek?).any (fun c => c != '/'.toUInt8) then break

  return result

def parseQuery : Parser ByteSlice := do
  takeWhileUpTo isQueryChar 4096

def parseFragment : Parser ByteSlice := do
  takeWhileUpTo isFragmentChar 1024

public def parseUri : Parser UriComponents := do
  let mut components : UriComponents := ⟨none, none, none, none, none, none, none⟩

  let schemeResult ← tryOpt do
    let scheme ← parseScheme
    skipByte ':'.toUInt8
    return scheme

  components := { components with schema := schemeResult }

  if (← tryOpt (skipBytes "//".toUTF8)).isSome then
    let (userinfo, host, port) ← parseAuthority
    components := { components with userinfo := userinfo, host := host, port := port }

  let pathResult ← tryOpt parsePathSegments
  components := { components with path := pathResult }

  if (← optional (skipByte '?'.toUInt8)).isSome then
    let queryBytes ← parseQuery
    components := { components with query := some queryBytes }

  if (← optional (skipByte '#'.toUInt8)).isSome then
    let fragmentBytes ← parseFragment
    components := { components with fragment := some fragmentBytes }

  return components

def parsePortNumber (portBytes : ByteSlice) : Option UInt16 := do
  let portStr := String.fromUTF8! portBytes.toByteArray
  String.toNat? portStr >>= (fun n => if n ≤ 65535 then some n.toUInt16 else none)

def componentToUserInfo (userBytes : ByteSlice) (passBytes : Option ByteSlice) : Option URI.UserInfo := do
  return { user := String.fromUTF8! userBytes.toByteArray, pass := String.fromUTF8! <$> passBytes.map (·.toByteArray) }

def componentToHost (hostBytes : ByteSlice) : Option URI.Host := do
  let hostStr ← String.fromUTF8! hostBytes.toByteArray

  if hostStr.startsWith "[" && hostStr.endsWith "]" then
    return .ipv6 (← Std.Net.IPv6Addr.ofString hostStr)
  else if hostStr.all (fun c => c.isDigit || c == '.') then
    return .ipv4 (← Std.Net.IPv4Addr.ofString hostStr)
  else
    return .name hostStr

def componentToPath (pathBytes : Option ByteArray) : URI.Path :=
  match pathBytes with
  | none => { segments := #[], absolute := false }
  | some bytes =>
    let pathStr := String.fromUTF8! bytes
    let isAbsolute := pathStr.startsWith "/"
    let cleanPath := if isAbsolute then pathStr.drop 1 else pathStr
    let segments := if cleanPath.isEmpty then #[] else cleanPath.splitOn "/" |>.toArray
    { segments := segments, absolute := isAbsolute }

def componentToQuery (queryBytes : Option ByteSlice) : Option URI.Query :=
  queryBytes.map fun bytes =>
    let queryStr := String.fromUTF8! bytes.toByteArray
    let pairs := queryStr.splitOn "&" |>.map fun pair =>
      match pair.splitOn "=" with
      | [key] => (key, none)
      | key :: value :: _ => (key, some value)
      | [] => ("", none)
    pairs.toArray

def componentToAuthority (userinfo : Option (ByteSlice × Option ByteSlice)) (host : Option ByteSlice) (port : Option ByteSlice) : Parser (Option URI.Authority) := do
  let some hostBytes := host
    | return none

  let some hostValue := componentToHost hostBytes
    | fail "invalid host"

  let userinfoValue := userinfo.bind fun (user, pass) => componentToUserInfo user pass

  let portValue := port.bind parsePortNumber

  return (some { userInfo := userinfoValue, host := hostValue, port := portValue })

def componentToUri (comp : UriComponents) : Parser URI := do
  let scheme := comp.schema.map (String.fromUTF8! ∘ ByteSlice.toByteArray)
  let authority ← componentToAuthority comp.userinfo comp.host comp.port
  let path := componentToPath comp.path
  let query := componentToQuery comp.query
  let fragment := comp.fragment.map (String.fromUTF8! ∘ ByteSlice.toByteArray)

  return { scheme, authority, path, query, fragment }

public def parseRequestTarget : Parser RequestTarget := do
  if (← tryOpt (do skipByte '*'.toUInt8; eof)).isSome then
    return .asteriskForm

  let absoluteResult ← tryOpt do
    let comp ← parseUri
    if comp.schema.isSome then
      componentToUri comp
    else
      fail "not absolute URI"

  if let some uri := absoluteResult then
    return .absoluteForm uri

  let authorityResult ← tryOpt do
    let (userinfo, host, port) ← parseAuthority
    eof

    componentToAuthority userinfo host port

  if let some auth := authorityResult.bind id then
    return .authorityForm auth

  let comp ← parseUri
  let uri ← componentToUri comp

  return .originForm uri.path uri.query

end Parser
end Data
end Http
end Std

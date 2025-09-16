/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data
public import Std.Internal.Parsec
public import Std.Internal.Http.Data
public import Std.Internal.Parsec.ByteArray

namespace Std
namespace Http
namespace H1
namespace Parser

open Data
open Std Internal Parsec ByteArray

def isTokenCharacter (c : UInt8) : Bool :=
  c > 31 && c != '('.toUInt8 && c != ')'.toUInt8 && c != '<'.toUInt8 && c != '>'.toUInt8 &&
  c != '@'.toUInt8 && c != ','.toUInt8 && c != ';'.toUInt8 && c != ':'.toUInt8 &&
  c != '"'.toUInt8 && c != '/'.toUInt8 && c != '['.toUInt8 && c != ']'.toUInt8 &&
  c != '?'.toUInt8 && c != '='.toUInt8 && c != '{'.toUInt8 && c != '}'.toUInt8 && c != ' '.toUInt8

@[inline]
def isValidHeaderNameChar (c : UInt8) : Bool :=
  c > 31 && c < 127 && c != ':'.toUInt8

@[inline]
def isValidHeaderValueChar (c : UInt8) : Bool :=
  c == '\t'.toUInt8 || (c >= ' '.toUInt8 && c < 127) || c >= 128

section Util

def parseMany {α : Type} (parser : Parser (Option α)) (maxCount : Nat) : Parser (Array α) := do
  let items ← many (parser.bind (fun item => match item with
    | some x => return x
    | none => fail "end of items"))
  if items.size > maxCount then
    fail s!"Too many items: {items.size} > {maxCount}"
  return items

def failNone (x : Option α) : Parser α :=
  if let some res := x then
    pure res
  else
    fail "expected value but got none"

def parseHexDigit : Parser UInt8 := do
  let b ← any
  if b ≥ '0'.toUInt8 && b ≤ '9'.toUInt8 then return b - '0'.toUInt8
  else if b ≥ 'A'.toUInt8 && b ≤ 'F'.toUInt8 then return b - 'A'.toUInt8 + 10
  else if b ≥ 'a'.toUInt8 && b ≤ 'f'.toUInt8 then return b - 'a'.toUInt8 + 10
  else fail s!"Invalid hex digit {Char.ofUInt8 b |>.quote}"

def parseHex : Parser Nat := do
  let hexDigits ← many1 (attempt parseHexDigit)
  return (hexDigits.foldl (fun acc cur => acc * 16 + cur.toNat) 0)

@[inline]
def token (limit : Nat) : Parser ByteSlice :=
  takeWhileUpTo1 isTokenCharacter limit

@[inline]
def parseCRLF : Parser Unit :=
  skipBytes "\r\n".toUTF8

@[inline]
def parseDigitAsUInt8 : Parser UInt8 := do
  let d ← digit
  return d.toUInt8

@[inline]
def sp : Parser Unit :=
  skipByteChar ' '

@[inline]
def sps : Parser Unit :=
  skipWhile (· == ' '.toUInt8)

end Util

def parseHttpVersion : Parser Version := do
  skipBytes " HTTP/".toUTF8
  let major ← parseDigitAsUInt8
  skipByte '.'.toUInt8
  let minor ← parseDigitAsUInt8
  failNone <| Version.fromNumber? (major - 48 |>.toNat) (minor - 48 |>.toNat)

def parseMethod : Parser Method := do
  let method ← token 16
  failNone <| Method.fromString? =<< (String.fromUTF8? method.toByteArray)

def parseURI : Parser String := do
  let uri ← takeUntil (· == ' '.toUInt8)
  failNone <| String.fromUTF8? uri.toByteArray

/--
Parses the request line.
-/
public def parseRequestLine : Parser Request.Head := do
  let method ← parseMethod <* sp
  let uri ← parseURI
  let version ← parseHttpVersion
  parseCRLF
  return ⟨method, version, uri, .empty⟩

/--
This function parses a header name-value pair
-/
def parseFieldLine (headerLimit : Nat) : Parser (String × String) := do
  let name ← token 256
  skipByte ':'.toUInt8
  skipWhile (· == ' '.toUInt8)
  let value ← takeWhileUpTo1 isValidHeaderValueChar headerLimit
  parseCRLF
  return ⟨← failNone (String.fromUTF8? name.toByteArray), ← failNone (String.fromUTF8? value.toByteArray)⟩

/--
This function parses a single HTTP header or returns none if end of headers is reached
-/
public def parseHeaderLine (headerLimit : Nat) : Parser (Option (String × String)) := do
  if (← optional parseCRLF).isSome then
    return none
  else
    some <$> parseFieldLine headerLimit

/--
This function parses chunk extensions
-/
def parseChunkExt : Parser (Option ByteSlice) := do
  if (← optional (skipByte ';'.toUInt8)).isSome then
    some <$> takeUntil (· == '\r'.toUInt8)
  else
    return none

/--
This function parses the size and extension of a chunk
-/
public def parseChunkSize : Parser (Nat × Option ByteSlice) := do
  let size ← parseHex
  let ext ← parseChunkExt
  parseCRLF
  return (size, ext)

public inductive TakeResult
  | complete (data : ByteSlice)
  | incomplete (data : ByteSlice) (remaining : Nat)


/--
Parses a fixed size data that can be incomplete.
-/
public def parseFixedSizeData (size : Nat) : Parser TakeResult := fun it =>
  if it.remainingBytes = 0 then
    .error it .eof
  else if it.remainingBytes < size then
    .success (it.forward it.remainingBytes) (.incomplete it.array[it.idx...(it.idx+it.remainingBytes)] (size - it.remainingBytes))
  else
    .success (it.forward size) (.complete (it.array[it.idx...(it.idx+size)]))

/--
Parses a fixed size data that can be incomplete.
-/
public def parseChunkedSizedData (size : Nat) : Parser TakeResult := do
  match ← parseFixedSizeData size with
  | .complete data => parseCRLF *> return .complete data
  | .incomplete data res => return .incomplete data res

/--
This function parses a single chunk in chunked transfer encoding
-/
public def parseChunk : Parser (Option (Nat × Option ByteSlice × ByteSlice)) := do
  let (size, ext) ← parseChunkSize
  if size == 0 then
    return none
  else
    let data ← take size
    return some ⟨size, ext, data⟩

/--
This function parses a trailer header (used after chunked body)
-/
def parseTrailerHeader (headerLimit : Nat) : Parser (Option (String × String)) := parseHeaderLine headerLimit

/--
This function parses trailer headers after chunked body
-/
public def parseTrailers (headerLimit : Nat) : Parser (Array  (String × String)) := do
  let trailers ← parseMany (parseTrailerHeader headerLimit) 100
  parseCRLF
  return trailers

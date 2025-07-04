/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Internal.Parsec.Basic
public import Init.Data.ByteArray.Basic
public import Init.Data.String.Extra

public section

namespace Std
namespace Internal
namespace Parsec
namespace ByteArray

instance : Input ByteArray.Iterator UInt8 Nat where
  pos it := it.pos
  next it := it.next
  curr it := it.curr
  hasNext it := it.hasNext
  next' it := it.next'
  curr' it := it.curr'

abbrev Parser (e : Type := String) (α : Type) : Type := Parsec ByteArray.Iterator e α

/--
Run a `Parser` on a `ByteArray`, returns either the result or an error string with offset.
-/
protected def Parser.run (p : Parser e α) (arr : ByteArray) : Except (Error e) α :=
  match p arr.iter with
  | .success _ res => Except.ok res
  | .error _ err => Except.error err

/--
Parse a single byte equal to `b`, fails if different.
-/
@[inline]
def pbyte (b : UInt8) : Parser e UInt8 := attempt do
  if (← any) = b then pure b else fail (.expected (toString b |>.quote))

/--
Skip a single byte equal to `b`, fails if different.
-/
@[inline]
def skipByte (b : UInt8) : Parser e Unit :=
  pbyte b *> pure ()

/--
Skip a sequence of bytes equal to the given `ByteArray`.
-/
def skipBytes (arr : ByteArray) : Parser e Unit := do
  for b in arr do
    skipByte b

/--
Parse a string by matching its UTF-8 bytes, returns the string on success.
-/
@[inline]
def pstring (s : String) : Parser e String := do
  skipBytes s.toUTF8
  return s

/--
Skip a string by matching its UTF-8 bytes.
-/
@[inline]
def skipString (s : String) : Parser e Unit := pstring s *> pure ()

/--
Parse a `Char` that can be represented in 1 byte. If `c` uses more than 1 byte it is truncated.
-/
@[inline]
def pByteChar (c : Char) : Parser e Char := attempt do
  if (← any) = c.toUInt8 then pure c else fail (.expected c.quote)

/--
Skip a `Char` that can be represented in 1 byte. If `c` uses more than 1 byte it is truncated.
-/
@[inline]
def skipByteChar (c : Char) : Parser e Unit := skipByte c.toUInt8

/--
Parse an ASCII digit `0-9` as a `Char`.
-/
@[inline]
def digit : Parser e Char := attempt do
  let b ← any
  if '0'.toUInt8 ≤ b ∧ b ≤ '9'.toUInt8 then return Char.ofUInt8 b else fail (.expected "digit")

/--
Convert a byte representing `'0'..'9'` to a `Nat`.
-/
@[inline]
private def digitToNat (b : UInt8) : Nat :=
  (b - '0'.toUInt8).toNat

/--
Parse zero or more ASCII digits into a `Nat`, continuing until non-digit or EOF.
-/
@[inline]
private partial def digitsCore (acc : Nat) : Parser e Nat := fun it =>
  /-
  With this design instead of combinators we can avoid allocating and branching over .success values
  all of the time.
  -/
  let ⟨res, it⟩ := go it acc
  .success it res
where
  go (it : ByteArray.Iterator) (acc : Nat) : Nat × ByteArray.Iterator :=
    if h : it.hasNext then
      let candidate := it.curr' h
      if '0'.toUInt8 ≤ candidate ∧ candidate ≤ '9'.toUInt8 then
        let digit := digitToNat candidate
        let acc := acc * 10 + digit
        go (it.next' h) acc
      else
        (acc, it)
    else
      (acc, it)

/--
Parse one or more ASCII digits into a `Nat`.
-/
@[inline]
def digits : Parser e Nat := do
  let d ← digit
  digitsCore (digitToNat d.toUInt8)

/--
Parse a hex digit `0-9`, `a-f`, or `A-F` as a `Char`.
-/
@[inline]
def hexDigit : Parser e Char := attempt do
  let b ← any
  if ('0'.toUInt8 ≤ b ∧ b ≤ '9'.toUInt8)
   ∨ ('a'.toUInt8 ≤ b ∧ b ≤ 'f'.toUInt8)
   ∨ ('A'.toUInt8 ≤ b ∧ b ≤ 'F'.toUInt8) then return Char.ofUInt8 b else fail (.expected "hex digit")

/--
Parse an octal digit `0-7` as a `Char`.
-/
@[inline]
def octDigit : Parser e Char := attempt do
  let b ← any
  if '0'.toUInt8 ≤ b ∧ b ≤ '7'.toUInt8 then
    return Char.ofUInt8 b
  else
    fail (.expected "octal digit")

/--
Parse an ASCII letter `a-z` or `A-Z` as a `Char`.
-/
@[inline]
def asciiLetter : Parser e Char := attempt do
  let b ← any
  if ('A'.toUInt8 ≤ b ∧ b ≤ 'Z'.toUInt8) ∨ ('a'.toUInt8 ≤ b ∧ b ≤ 'z'.toUInt8) then
    return Char.ofUInt8 b
  else
    fail (.expected "ASCII letter")

private partial def skipWs (it : ByteArray.Iterator) : ByteArray.Iterator :=
  if h : it.hasNext then
    let b := it.curr' h
    if b = '\u0009'.toUInt8 ∨ b = '\u000a'.toUInt8 ∨ b = '\u000d'.toUInt8 ∨ b = '\u0020'.toUInt8 then
      skipWs (it.next' h)
    else
      it
  else
   it

/--
Skip whitespace: tabs, newlines, carriage returns, and spaces.
-/
@[inline]
def ws : Parser e Unit := fun it =>
  .success (skipWs it) ()

/--
Parse `n` bytes from the input into a `ByteArray`, errors if not enough bytes.
-/
def take (n : Nat) : Parser e ByteArray := fun it =>
  let subarr := it.array.extract it.idx (it.idx + n)
  if subarr.size != n then
    .error it .eof
  else
    .success (it.forward n) subarr

/--
Parses while a predicate is satisfied.
-/
@[inline]
partial def takeWhile (pred : UInt8 → Bool) : Parser e ByteArray :=
  fun it =>
    let rec findEnd (count : Nat) (iter : ByteArray.Iterator) : (Nat × ByteArray.Iterator) :=
      if ¬iter.hasNext then (count, iter)
      else if pred iter.curr then findEnd (count + 1) iter.next
      else (count, iter)

    let (length, newIt) := findEnd 0 it
    .success newIt (it.array.extract it.idx (it.idx + length))

/--
Parses until a predicate is satisfied (exclusive).
-/
@[inline]
def takeUntil (pred : UInt8 → Bool) : Parser e ByteArray :=
  takeWhile (fun b => ¬pred b)

/--
Skips while a predicate is satisfied.
-/
@[inline]
partial def skipWhile (pred : UInt8 → Bool) : Parser e Unit :=
  fun it =>
    let rec findEnd (count : Nat) (iter : ByteArray.Iterator) : ByteArray.Iterator :=
      if ¬iter.hasNext then iter
      else if pred iter.curr then findEnd (count + 1) iter.next
      else iter

    .success (findEnd 0 it) ()

/--
Skips until a predicate is satisfied.
-/
@[inline]
def skipUntil (pred : UInt8 → Bool) : Parser e Unit :=
  skipWhile (fun b => ¬pred b)

end ByteArray
end Parsec
end Internal
end Std

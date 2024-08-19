/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Duration is just a period between two timestamps.
-/
def Duration := Timestamp
  deriving Repr, BEq

instance : ToString Duration where
  toString s :=
    let (sign, secs, nanos) :=
      if s.second.val > 0 then ("" ,s.second.val, s.nano.val)
      else if s.second.val < 0 then ("-", -s.second.val, -s.nano.val)
      else if s.nano.val < 0 then ("-", -s.second.val, -s.nano.val) else ("", s.second.val, s.nano.val)
    sign ++ toString secs ++ "." ++ toString nanos ++ "s"

namespace Duration

/--
Calculates a `Duration` out of two `Timestamp`s.
-/
def since (f : Timestamp) : IO Duration := do
  let cur ← Timestamp.now
  return cur.sub f

/--
Adds a `Duration` to a `Timestamp`.
-/
def add (f : Timestamp) (d : Duration) : Timestamp :=
  f.add d

/--
Checks if the duration is zero seconds ands zero nanoseconds.
-/
def isZero (d : Duration) : Bool :=
  d.second.val = 0 ∧ d.nano.val = 0

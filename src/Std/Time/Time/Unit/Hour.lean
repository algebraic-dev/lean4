/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Rat
import Std.Time.Internal
import Std.Time.Time.Unit.Minute
import Std.Time.Time.Unit.Second

namespace Std
namespace Time
namespace Hour
open Std.Internal
open Internal

set_option linter.all true

/--
`Ordinal` represents a bounded value for hours, ranging from 0 to 23.
-/
def Ordinal := Bounded.LE 0 23
  deriving Repr, BEq, LE, LT

instance : ToString Ordinal where
  toString x := toString x.val

instance : OfNat Ordinal n :=
  inferInstanceAs (OfNat (Bounded.LE 0 (0 + (23 : Nat))) n)

instance : Inhabited Ordinal where
  default := 0

instance {x y : Ordinal} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))

instance {x y : Ordinal} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))

/--
`Offset` represents an offset in hours, defined as an `Int`. This can be used to express durations
or differences in hours.
-/
def Offset : Type := UnitVal 3600
  deriving Repr, BEq, Inhabited, Add, Sub, Mul, Div, Neg, ToString

instance : OfNat Offset n :=
  ⟨UnitVal.ofNat n⟩

namespace Ordinal

/--
Converts an `Ordinal` into a relative month in the range of 1 to 12.
-/
def toRelative (ordinal : Ordinal) : Bounded.LE 1 12 :=
  (ordinal.add 11).emod 12 (by decide) |>.add 1

/--
Creates an `Ordinal` from a natural number, ensuring the value is within the valid bounds for hours.
-/
@[inline]
def ofNat (data : Nat) (h : data ≤ 23) : Ordinal :=
  Bounded.LE.ofNat data h

/--
Creates an `Ordinal` from a `Fin` value.
-/
@[inline]
def ofFin (data : Fin 24) : Ordinal :=
  Bounded.LE.ofFin data

/--
Converts an `Ordinal` to an `Offset`, which represents the duration in hours as an integer value.
-/
@[inline]
def toOffset (ordinal : Ordinal) : Offset :=
  UnitVal.ofInt ordinal.val

end Ordinal
end Hour
end Time
end Std

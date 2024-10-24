/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.ZonedDateTime
import Std.Time.Zoned.Database

namespace Std
namespace Time

namespace PlainDateTime

set_option linter.all true

/--
Creaates a new `PlainDateTime` out of a `Timestamp` and a `TimeZone`.
-/
def ofTimestamp (stamp : Timestamp) (tz : TimeZone) : PlainDateTime :=
  let stamp := stamp.addSeconds tz.toSeconds
  PlainDateTime.ofUTCTimestamp stamp

/--
Get the current time.
-/
@[inline]
def now : IO PlainDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetLocalZoneRulesAt
  let transition ← rules.findTransitionForTimestamp tm |>.elim (throw <| IO.userError "cannot find timezone") pure

  return PlainDateTime.ofTimestamp tm transition.localTimeType.getTimeZone

end PlainDateTime

namespace DateTime

/--
Converts a `PlainDate` with a `TimeZone` to a `DateTime`
-/
@[inline]
def ofPlainDate (pd : PlainDate) (tz : TimeZone) : DateTime tz :=
  DateTime.ofTimestamp (Timestamp.ofPlainDateAssumingUTC pd) tz

/--
Converts a `DateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (dt : DateTime tz) : PlainDate :=
  Timestamp.toPlainDateAssumingUTC dt.toUTCTimestamp

/--
Converts a `DateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (dt : DateTime tz) : PlainTime :=
  dt.date.get.time

end DateTime
namespace ZonedDateTime

/--
Gets the current `ZonedDateTime`.
-/
@[inline]
def now : IO ZonedDateTime := do
  let tm ← Timestamp.now
  let rules ← Database.defaultGetLocalZoneRulesAt
  return ZonedDateTime.ofTimestamp tm rules

/--
Converts a `PlainDate` to a `ZonedDateTime`.
-/
@[inline]
def ofPlainDate (pd : PlainDate) (zr : TimeZone.ZoneRules) : ZonedDateTime :=
  ZonedDateTime.ofPlainDateTime (pd.atTime PlainTime.midnight) zr

/--
Converts a `ZonedDateTime` to a `PlainDate`
-/
@[inline]
def toPlainDate (dt : ZonedDateTime) : PlainDate :=
  dt.toPlainDateTime.date

/--
Converts a `ZonedDateTime` to a `PlainTime`
-/
@[inline]
def toPlainTime (dt : ZonedDateTime) : PlainTime :=
  dt.toPlainDateTime.time

/--
Creates a new `ZonedDateTime` out of a `PlainDateTime` and a time zone identifier.
-/
@[inline]
def of (pdt : PlainDateTime) (id : String) : IO ZonedDateTime := do
  let zr ← Database.defaultGetZoneRulesAt id
  return ZonedDateTime.ofPlainDateTime pdt zr

end ZonedDateTime

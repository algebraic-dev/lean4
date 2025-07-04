/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving, Sofia Rodrigues
-/
module

prelude
public import Init.NotationExtra
public import Init.Data.ToString.Macro

public section

namespace Std
namespace Internal
namespace Parsec

/--
Error type for the `ParseResult`. It separates `eof` from the rest of the errors in order to
improve the error handling for this case in parsers that can receive incomplete data and then reparse it.
-/
inductive Error (e : Type) where
  | eof
  | conditionNotSatisfied
  | notFollowedBy
  | expected (e : String)
  | other (α : e)
  deriving Repr

instance : Coe e (Error e) where
  coe := .other

instance [ToString e] : ToString (Error e) where
  toString
    | .eof => "unexpected end of input"
    | .conditionNotSatisfied => "condition not satisfied"
    | .notFollowedBy => "not followed by"
    | .expected e => s!"expected {e}"
    | .other s => toString s

/--
The result of parsing some input.
-/
inductive ParseResult (α : Type) (e : Type) (ι : Type) where
  | success (pos : ι) (res : α)
  | error (pos : ι) (err : Error e)
  deriving Repr

end Parsec

/--
A parser that takes input of type `ι` and returns a `ParseResult`.
-/
@[expose]
def Parsec (ι : Type) (e : Type) (α : Type) : Type :=
  ι → Parsec.ParseResult α e ι

namespace Parsec

/--
Type class for input streams with position tracking and element access.
-/
class Input (ι : Type) (elem : outParam Type) (idx : outParam Type) [DecidableEq idx] [DecidableEq elem] where
  pos : ι → idx
  next : ι → ι
  curr : ι → elem
  hasNext : ι → Bool
  next' (it : ι) : (hasNext it) → ι
  curr' (it : ι) : (hasNext it) → elem

variable {α : Type} {ι : Type} {elem : Type} {idx : Type}
variable [DecidableEq idx] [DecidableEq elem] [Input ι elem idx]

instance [Inhabited e] : Inhabited (Parsec ι e α) where
  default := fun it => ParseResult.error it (.other default)

@[always_inline, inline]
protected def pure (a : α) : Parsec ι e α := fun it =>
  .success it a

@[always_inline, inline]
protected def bind {α β : Type} (f : Parsec ι e α) (g : α → Parsec ι e β) : Parsec ι e β := fun it =>
  match f it with
  | .success rem a => g a rem
  | .error pos msg => .error pos msg

/--
Throws an error inside the parser.
-/
@[always_inline, inline]
def fail (msg : Error e) : Parsec ι e α := fun it =>
  .error it msg

@[inline]
def tryCatch (p : Parsec ι e α) (csuccess : α → Parsec ι e β) (cerror : Unit → Parsec ι e β)
    : Parsec ι e β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if Input.pos it = Input.pos rem then cerror () rem else .error rem err

@[always_inline]
instance : Monad (Parsec e ι) where
  pure := Parsec.pure
  bind := Parsec.bind

/--
Choice operator that tries the first parser, falls back to second on failure.
-/
@[always_inline, inline]
def orElse (p : Parsec ι e α) (q : Unit → Parsec ι e α) : Parsec ι e α :=
  tryCatch p pure q

/--
Combinator that resets position on failure.
-/
@[always_inline, inline]
def attempt (p : Parsec ι e α) : Parsec ι e α := fun it =>
  match p it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

/--
Alternative instance providing failure and choice operations.
-/
@[always_inline]
instance [Inhabited e] : Alternative (Parsec ι e) where
  failure := fail (.other default)
  orElse := orElse

/--
Succeeds only at end of input, fails otherwise.
-/
@[inline]
def eof : Parsec ι e Unit := fun it =>
  if Input.hasNext it then
    .error it .eof
  else
    .success it ()

/--
Checks if parser is at end of input without consuming.
-/
@[inline]
def isEof : Parsec ι e Bool := fun it =>
  .success it (!Input.hasNext it)

@[specialize]
partial def manyCore (p : Parsec ι e α) (acc : Array α) : Parsec ι e (Array α) :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

/--
Parses zero or more occurrences of a parser into an array.
-/
@[inline]
def many (p : Parsec ι e α) : Parsec ι e (Array α) := manyCore p #[]

/--
Parses one or more occurrences of a parser into an array.
-/
@[inline]
def many1 (p : Parsec ι e α) : Parsec ι e (Array α) := do manyCore p #[← p]

/--
Gets the next input element.
-/
@[inline]
def any : Parsec ι e elem := fun it =>
  if h : Input.hasNext it then
    let c := Input.curr' it h
    let it' := Input.next' it h
    .success it' c
  else
    .error it .eof

/--
Checks if the next input element matches some condition.
-/
@[inline]
def satisfy (p : elem → Bool) : Parsec ι e elem := attempt do
  let c ← any
  if p c then return c else fail .conditionNotSatisfied

/--
Fails if `p` succeeds, otherwise succeeds without consuming input.
-/
@[inline]
def notFollowedBy (p : Parsec ι e α) : Parsec ι e Unit := fun it =>
  match p it with
  | .success _ _ => .error it .notFollowedBy
  | .error _ _ => .success it ()

/--
Peeks at the next element, returns `some` if exists else `none`, does not consume input.
-/
@[inline]
def peek? : Parsec ι e (Option elem) := fun it =>
  if h : Input.hasNext it then
    .success it (some <| Input.curr' it h)
  else
    .success it none

/--
Peeks at the next element, returns `some elem` if it satisfies `p`, else `none`. Does not consume input.
-/
@[inline]
def peekWhen? (p : elem → Bool) : Parsec ι e (Option elem) := do
  let some data ← peek?
    | return none

  if p data then
    return some data
  else
    return none

/--
Peeks at the next element, errors on EOF, does not consume input.
-/
@[inline]
def peek! : Parsec ι e elem := fun it =>
  if h : Input.hasNext it then
    .success it (Input.curr' it h)
  else
    .error it .eof

/--
Peeks at the next element or returns a default if at EOF, does not consume input.
-/
@[inline]
def peekD (default : elem) : Parsec ι e elem := fun it =>
  if h : Input.hasNext it then
    .success it (Input.curr' it h)
  else
    .success it default

/--
Consumes one element if available, otherwise errors on EOF.
-/
@[inline]
def skip : Parsec ι e Unit := fun it =>
  if h : Input.hasNext it then
    .success (Input.next' it h) ()
  else
    .error it .eof

/--
Core implementation for parsing zero or more characters with accumulation.
-/
@[specialize]
partial def manyCharsCore (p : Parsec ι e Char) (acc : String) : Parsec ι e String :=
  tryCatch p (manyCharsCore p <| acc.push ·) (fun _ => pure acc)

/--
Parses zero or more chars with `p` into a string.
-/
@[inline]
def manyChars (p : Parsec ι e Char) : Parsec ι e String := do
  manyCharsCore p ""

/--
Parses one or more chars with `p` into a string, errors if none.
-/
@[inline]
def many1Chars (p : Parsec ι e Char) : Parsec ι e String := do
  manyCharsCore p (← p).toString

end Parsec
end Internal
end Std

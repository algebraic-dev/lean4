/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ReservedNameAction
import Lean.AddDecl
import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.Match.MatcherInfo

namespace Lean.Meta

register_builtin_option eqns.nonrecursive : Bool := {
    defValue := true
    descr    := "Create fine-grained equational lemmas even for non-recursive definitions."
  }

register_builtin_option eqns.deepRecursiveSplit : Bool := {
    defValue := true
    descr    := "Create equational lemmas for recursive functions like for non-recursive \
                functions. If disabled, match statements in recursive function definitions \
                that do not contain recursive calls do not cause further splits in the \
                equational lemmas. This was the behavior before Lean 4.12, and the purpose of \
                this option is to help migrating old code."
  }


/--
These options affect the generation of equational theorems in a significant way. For these, their
value at definition time, not realization time, should matter.

This is implemented by
 * eagerly realizing the equations when they are set to a non-default vaule
 * when realizing them lazily, reset the options to their default
-/
def eqnAffectingOptions : Array (Lean.Option Bool) := #[eqns.nonrecursive, eqns.deepRecursiveSplit]

/--
Environment extension for storing which declarations are recursive.
This information is populated by the `PreDefinition` module, but the simplifier
uses when unfolding declarations.
-/
builtin_initialize recExt : TagDeclarationExtension ← mkTagDeclarationExtension `recExt

/--
Marks the given declaration as recursive.
-/
def markAsRecursive (declName : Name) : CoreM Unit :=
  modifyEnv (recExt.tag · declName)

/--
Returns `true` if `declName` was defined using well-founded recursion, or structural recursion.
-/
def isRecursiveDefinition (declName : Name) : CoreM Bool :=
  return recExt.isTagged (← getEnv) declName

def eqnThmSuffixBase := "eq"
def eqnThmSuffixBasePrefix := eqnThmSuffixBase ++ "_"
def eqn1ThmSuffix := eqnThmSuffixBasePrefix ++ "1"
example : eqn1ThmSuffix = "eq_1" := rfl

/-- Returns `true` if `s` is of the form `eq_<idx>` -/
def isEqnReservedNameSuffix (s : String) : Bool :=
  eqnThmSuffixBasePrefix.isPrefixOf s && (s.drop 3).isNat

def unfoldThmSuffix := "eq_def"

/-- Returns `true` if `s == "eq_def"` -/
def isUnfoldReservedNameSuffix (s : String) : Bool :=
  s == unfoldThmSuffix

/--
Throw an error if names for equation theorems for `declName` are not available.
-/
def ensureEqnReservedNamesAvailable (declName : Name) : CoreM Unit := do
  ensureReservedNameAvailable declName unfoldThmSuffix
  ensureReservedNameAvailable declName eqn1ThmSuffix
  -- TODO: `declName` may need to reserve multiple `eq_<idx>` names, but we check only the first one.
  -- Possible improvement: try to efficiently compute the number of equation theorems at declaration time, and check all of them.

/--
Ensures that `f.eq_def` and `f.eq_<idx>` are reserved names if `f` is a safe definition.
-/
builtin_initialize registerReservedNamePredicate fun env n =>
  match n with
  | .str p s =>
    (isEqnReservedNameSuffix s || isUnfoldReservedNameSuffix s)
    && env.isSafeDefinition p
    -- Remark: `f.match_<idx>.eq_<idx>` are private definitions and are not treated as reserved names
    -- Reason: `f.match_<idx>.splitter is generated at the same time, and can eliminate into type.
    -- Thus, it cannot be defined in different modules since it is not a theorem, and is used to generate code.
    && !isMatcherCore env p
  | _ => false

def GetEqnsFn := Name → MetaM (Option (Array Name))

private builtin_initialize getEqnsFnsRef : IO.Ref (List GetEqnsFn) ← IO.mkRef []

/--
Registers a new function for retrieving equation theorems.
We generate equations theorems on demand, and they are generated by more than one module.
For example, the structural and well-founded recursion modules generate them.
Most recent getters are tried first.

A getter returns an `Option (Array Name)`. The result is `none` if the getter failed.
Otherwise, it is a sequence of theorem names where each one of them corresponds to
an alternative. Example: the definition

```
def f (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x::xs => (x+1)::f xs
```
should have two equational theorems associated with it
```
f [] = []
```
and
```
(x : Nat) → (xs : List Nat) → f (x :: xs) = (x+1) :: f xs
```
-/
def registerGetEqnsFn (f : GetEqnsFn) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register equation getter, this kind of extension can only be registered during initialization")
  getEqnsFnsRef.modify (f :: ·)

/-- Returns `true` iff `declName` is a definition and its type is not a proposition. -/
private def shouldGenerateEqnThms (declName : Name) : MetaM Bool := do
  if let some (.defnInfo info) := (← getEnv).find? declName then
    if (← isProp info.type) then return false
    return true
  else
    return false

structure EqnsExtState where
  map    : PHashMap Name (Array Name) := {}
  mapInv : PHashMap Name Name := {} -- TODO: delete?
  deriving Inhabited

/- We generate the equations on demand. -/
builtin_initialize eqnsExt : EnvExtension EqnsExtState ←
  registerEnvExtension (pure {})

/--
Simple equation theorem for nonrecursive definitions.
-/
private def mkSimpleEqThm (declName : Name) (suffix := Name.mkSimple unfoldThmSuffix) : MetaM (Option Name) := do
  if let some (.defnInfo info) := (← getEnv).find? declName then
    lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
      let lhs := mkAppN (mkConst info.name <| info.levelParams.map mkLevelParam) xs
      let type  ← mkForallFVars xs (← mkEq lhs body)
      let value ← mkLambdaFVars xs (← mkEqRefl lhs)
      let name := declName ++ suffix
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      return some name
  else
    return none

/--
Returns `some declName` if `thmName` is an equational theorem for `declName`.
-/
def isEqnThm? (thmName : Name) : CoreM (Option Name) := do
  return eqnsExt.getState (← getEnv) |>.mapInv.find? thmName

/--
Stores in the `eqnsExt` environment extension that `eqThms` are the equational theorems for `declName`
-/
private def registerEqnThms (declName : Name) (eqThms : Array Name) : CoreM Unit := do
  modifyEnv fun env => eqnsExt.modifyState env fun s => { s with
    map := s.map.insert declName eqThms
    mapInv := eqThms.foldl (init := s.mapInv) fun mapInv eqThm => mapInv.insert eqThm declName
  }

/--
Equation theorems are generated on demand, check whether they were generated in an imported file.
-/
private partial def alreadyGenerated? (declName : Name) : MetaM (Option (Array Name)) := do
  let env ← getEnv
  let eq1 := Name.str declName eqn1ThmSuffix
  if env.contains eq1 then
    let rec loop (idx : Nat) (eqs : Array Name) : MetaM (Array Name) := do
      let nextEq := declName ++ (`eq).appendIndexAfter idx
      if env.contains nextEq then
        loop (idx+1) (eqs.push nextEq)
      else
        return eqs
    let eqs ← loop 2 #[eq1]
    registerEqnThms declName eqs
    return some eqs
  else
    return none

private def getEqnsFor?Core (declName : Name) : MetaM (Option (Array Name)) := withLCtx {} {} do
  if let some eqs := eqnsExt.getState (← getEnv) |>.map.find? declName then
    return some eqs
  else if let some eqs ← alreadyGenerated? declName then
    return some eqs
  else if (← shouldGenerateEqnThms declName) then
    for f in (← getEqnsFnsRef.get) do
      if let some r ← f declName then
        registerEqnThms declName r
        return some r
  return none

/--
Returns equation theorems for the given declaration.
-/
def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := withLCtx {} {} do
  -- This is the entry point for lazy equaion generation. Ignore the current value
  -- of the options, and revert to the default.
  withOptions (eqnAffectingOptions.foldl fun os o => o.set os o.defValue) do
    getEqnsFor?Core declName

/--
If any equation theorem affecting option is not the default value, create the equations now.
-/
def generateEagerEqns (declName : Name) : MetaM Unit := do
  let opts ← getOptions
  if eqnAffectingOptions.any fun o => o.get opts != o.defValue then
    let _ ← getEqnsFor?Core declName

def GetUnfoldEqnFn := Name → MetaM (Option Name)

private builtin_initialize getUnfoldEqnFnsRef : IO.Ref (List GetUnfoldEqnFn) ← IO.mkRef []

/--
Registers a new function for retrieving a "unfold" equation theorem.

We generate this kind of equation theorem on demand, and it is generated by more than one module.
For example, the structural and well-founded recursion modules generate it.
Most recent getters are tried first.

A getter returns an `Option Name`. The result is `none` if the getter failed.
Otherwise, it is a theorem name. Example: the definition

```
def f (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | x::xs => (x+1)::f xs
```
should have the theorem
```
(xs : Nat) →
  f xs =
    match xs with
    | [] => []
    | x::xs => (x+1)::f xs
```
-/
def registerGetUnfoldEqnFn (f : GetUnfoldEqnFn) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "failed to register equation getter, this kind of extension can only be registered during initialization")
  getUnfoldEqnFnsRef.modify (f :: ·)

/--
Returns an "unfold" theorem for the given declaration.
By default, we do not create unfold theorems for nonrecursive definitions.
You can use `nonRec := true` to override this behavior.
-/
def getUnfoldEqnFor? (declName : Name) (nonRec := false) : MetaM (Option Name) := withLCtx {} {} do
  let env ← getEnv
  let unfoldName := Name.str declName unfoldThmSuffix
  if env.contains unfoldName then
    return some unfoldName
  if (← shouldGenerateEqnThms declName) then
    for f in (← getUnfoldEqnFnsRef.get) do
      if let some r ← f declName then
        unless r == unfoldName do
          throwError "invalid unfold theorem name `{r}` has been generated expected `{unfoldName}`"
        return some r
    if nonRec then
      return (← mkSimpleEqThm declName)
   return none

builtin_initialize
  registerReservedNameAction fun name => do
    let .str p s := name | return false
    unless (← getEnv).isSafeDefinition p do return false
    if isEqnReservedNameSuffix s then
      return (← MetaM.run' <| getEqnsFor? p).isSome
    if isUnfoldReservedNameSuffix s then
      return (← MetaM.run' <| getUnfoldEqnFor? p (nonRec := true)).isSome
    return false

end Lean.Meta

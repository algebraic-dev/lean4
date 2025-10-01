/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/

module

prelude
public import Std.Data
public import Init.System.Promise
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Std.Sync.CancellationToken
public import Std.Internal.Async.Select

public section

/-!
Context interface for cancellation and deadline management
-/

namespace Std
open Std.Internal.IO.Async

/--
Interface for contexts that support cancellation and deadline management.
A context carries deadlines, cancellation signals, and request-scoped values.
-/
class Context (α : Type) where
  /--
  Check if the context is cancelled
  -/
  isCancelled : α → BaseIO Bool

  /--
  Wait for cancellation. Returns a task that completes when cancelled
  -/
  done : α → IO (AsyncTask Unit)

  /--
  Creates a selector that waits for cancellation
  -/
  doneSelector : α → Selector Unit

  /--
  Cancel the context and all its children
  -/
  cancel : α → BaseIO Unit

/--
The central state structure shared by all context types.
-/
structure ContextState where
  /--
  Map of token IDs to optional tokens and their children.
  `none` represents a background context that cannot be cancelled.
  -/
  tokens : TreeMap UInt64 (Option CancellationToken × Array UInt64) := .empty

  /--
  Next available ID
  -/
  id : UInt64 := 1

/--
A cancellation context that allows multiple consumers to wait
until cancellation is requested. Forms a tree structure where
cancelling a parent cancels all children.
-/
structure CancellationContext where
  state : Std.Mutex ContextState
  token : CancellationToken
  id : UInt64

namespace CancellationContext

/--
Create a new root cancellation context.
-/
def new : BaseIO CancellationContext := do
  let token ← Std.CancellationToken.new
  return {
    state := ← Std.Mutex.new { tokens := .empty |>.insert 0 (some token, #[]) },
    token,
    id := 0
  }

/--
Fork a child context from a parent. If the parent is already cancelled,
returns the parent context. Otherwise, creates a new child that will be
cancelled when the parent is cancelled.
-/
def fork (root : CancellationContext) : BaseIO CancellationContext := do
  if ← root.token.isCancelled then
    return root

  let token ← Std.CancellationToken.new

  root.state.atomically do
    let st ← get
    let newId := st.id
    set { st with
      id := newId + 1,
      tokens := st.tokens.insert newId (some token, #[])
        |>.modify root.id (.map (·) (.push · newId))
    }
    return { state := root.state, token, id := newId }

/--
Recursively cancel a context and all its children.
-/
private partial def cancelChildren (state : ContextState) (id : UInt64) : BaseIO ContextState := do
  let mut state := state

  let some (tokenOpt, children) := state.tokens.get? id
    | return state

  for tokenId in children do
    state ← cancelChildren state tokenId

  if let some token := tokenOpt then
    token.cancel

  pure { state with tokens := state.tokens.erase id }

/--
Cancel this context and all child contexts.
-/
def cancel (x : CancellationContext) : BaseIO Unit := do
  if ← x.token.isCancelled then
    return

  x.state.atomically do
    let st ← get
    let st ← cancelChildren st x.id
    set st

/--
Check if the context is cancelled.
-/
@[inline]
def isCancelled (x : CancellationContext) : BaseIO Bool := do
  x.token.isCancelled

/--
Wait for cancellation. Returns a task that completes when the context is cancelled.
-/
@[inline]
def done (x : CancellationContext) : IO (AsyncTask Unit) :=
  x.token.wait

/--
Creates a selector that waits for cancellation.
-/
@[inline]
def doneSelector (x : CancellationContext) : Selector Unit :=
  x.token.selector

end CancellationContext

/--
Instance of Context interface for CancellationContext
-/
instance : Context CancellationContext where
  isCancelled := CancellationContext.isCancelled
  done := CancellationContext.done
  doneSelector := CancellationContext.doneSelector
  cancel := CancellationContext.cancel

end Std

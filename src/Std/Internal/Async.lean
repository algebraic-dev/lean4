/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.Basic
public import Std.Internal.Async.Timer
public import Std.Internal.Async.TCP
public import Std.Internal.Async.UDP
public import Std.Internal.Async.DNS
public import Std.Internal.Async.Select
public import Std.Internal.Async.Process
public import Std.Internal.Async.System
public import Std.Internal.Async.Signal
public import Std.Internal.Async.IO
public import Std.Sync.Context

public section

namespace Std
namespace Internal
namespace IO
namespace Async

/-!
?
-/
@[expose]
def ContextualAsync (α : Type) := ReaderT Std.CancellationContext Async (Option α)

namespace ContextualAsync

/--
?
-/
@[inline]
protected def runDummy (x : ContextualAsync α) : Async (Option α) := do
  x.run (← Std.CancellationContext.new)

/--
Converts a `ContextualAsync` to a `AsyncTask`.
-/
@[inline]
protected def toIO (x : ContextualAsync α) : IO (AsyncTask (Option α)) :=
  MaybeTask.toTask <$> x.runDummy.toRawBaseIO

/--
Block until the `ContextualAsync` finishes and returns its value. Propagates any error encountered during execution.
-/
@[inline]
protected def block (x : ContextualAsync α) (prio := Task.Priority.default) : IO (Option α) :=
  x.runDummy.asTask (prio := prio) >>= ETask.block

/--
Converts `Promise` into `ContextualAsync`.
-/
@[inline]
protected def ofPromise (task : IO (IO.Promise (Except IO.Error (Option α)))) : ContextualAsync α := fun _ => do
  match ← task.toBaseIO with
  | .ok data => pure (f := BaseIO) (MaybeTask.ofTask data.result!)
  | .error err => pure (f := BaseIO) (MaybeTask.pure (.error err))

/--
Converts `AsyncTask` into `ContextualAsync`.
-/
@[inline]
protected def ofAsyncTask (task : AsyncTask (Option α)) : ContextualAsync α := fun _ => do
  pure (f := BaseIO) (MaybeTask.ofTask task)

/--
Converts `IO (Task α)` into `ContextualAsync`.
-/
@[inline]
protected def ofIOTask (task : IO (Task (Option α))) : ContextualAsync α := fun _ => do
  match ← task.toBaseIO with
  | .ok data => .ofAsyncTask (data.map Except.ok)
  | .error err => pure (f := BaseIO) (MaybeTask.pure (.error err))

/--
Converts `Except` to `ContextualAsync`.
-/
@[inline]
protected def ofExcept (except : Except IO.Error (Option α)) : ContextualAsync α := fun _ =>
  pure (f := BaseIO) (MaybeTask.pure except)

/--
Converts `Task` to `ContextualAsync`.
-/
@[inline]
protected def ofTask (task : Task (Option α)) : ContextualAsync α := fun _ => do
  .ofAsyncTask (task.map Except.ok)

/--
Converts `IO (IO.Promise α)` to `ContextualAsync`.
-/
@[inline]
protected def ofPurePromise (task : IO (IO.Promise (Option α))) : ContextualAsync α := fun _ => do
  match ← task.toBaseIO with
  | .ok data => pure (f := BaseIO) (MaybeTask.ofTask <| data.result!.map (.ok))
  | .error err => pure (f := BaseIO) (MaybeTask.pure (.error err))

instance : Monad ContextualAsync :=
  inferInstanceAs (Monad (ReaderT Std.CancellationContext (EAsync IO.Error)))

instance : MonadLift (EIO IO.Error) ContextualAsync where
  monadLift y := fun _ => y

instance : MonadLift Async ContextualAsync where
  monadLift y := fun _ => y

instance : MonadExcept IO.Error ContextualAsync where
  throw := monadLift (n := ReaderT Std.CancellationContext Async) ∘ EAsync.throw
  tryCatch x c := fun ctx => EAsync.tryCatch (x.run ctx) (fun e => c e |>.run ctx)

instance : MonadFinally ContextualAsync where
  tryFinally' x f := fun ctx => EAsync.tryFinally' (x.run ctx) (fun e => f e |>.run ctx)

instance : OrElse (EAsync ε α) where
  orElse := MonadExcept.orElse

instance [Inhabited ε] : Inhabited (EAsync ε α) where
  default := .mk <| BaseAsync.pure default

instance : MonadAwait (ETask IO.Error α) ContextualAsync α where
  await t := fun _ => .mk <| BaseAsync.ofTask t

instance : MonadAwait (Task α) ContextualAsync α where
  await t := fun _ => .mk <| BaseAsync.ofTask (t.map (.ok))

instance : MonadAwait (AsyncTask α) ContextualAsync α where
  await t := fun _ => .mk <| BaseAsync.ofTask t

instance : MonadAwait (IO.Promise α) ContextualAsync α where
  await t := fun _ => .mk <| BaseAsync.ofTask (t.result!.map (.ok))

instance : MonadLift BaseIO ContextualAsync where
  monadLift x := fun _ => .mk <| (pure ∘ .ok) <$> x

@[default_instance]
instance : MonadAsync AsyncTask ContextualAsync where
  async f prio := do
    let ctx ← ReaderT.read
    let child ← ctx.fork
    let async := f child
    let async : Async _ := MonadAsync.async async prio
    fun _ => async

instance : MonadAwait (AsyncTask α) ContextualAsync α :=
  inferInstanceAs (MonadAwait (AsyncTask α) (ReaderT Std.CancellationContext (EAsync IO.Error)) α)

instance : MonadAwait (IO.Promise α) ContextualAsync α :=
  inferInstanceAs (MonadAwait (IO.Promise α) (ReaderT Std.CancellationContext (EAsync IO.Error)) α)

/--
Runs two computations concurrently and returns both results as a pair.
-/
@[inline, specialize]
def concurrently (x : ContextualAsync α) (y : ContextualAsync β) (prio := Task.Priority.default) : ContextualAsync (α × β) := do
  let taskX ← MonadAsync.async x (prio := prio)
  let taskY ← MonadAsync.async y (prio := prio)
  let resultX ← MonadAwait.await taskX
  let resultY ← MonadAwait.await taskY
  return (resultX, resultY)

/--
Runs two computations concurrently and returns the result of the one that finishes first.
The other result is lost and the other task is not cancelled, so the task will continue the execution
until the end.
-/
@[inline, specialize]
def race [Inhabited α] (x : ContextualAsync α) (y : ContextualAsync α)
    (prio := Task.Priority.default) :
    ContextualAsync α := do
  let promise ← IO.Promise.new

  let task₁ ← MonadAsync.async (t := AsyncTask) (prio := prio) x
  let task₂ ← MonadAsync.async (t := AsyncTask) (prio := prio) y

  BaseIO.chainTask task₁ (liftM ∘ promise.resolve)
  BaseIO.chainTask task₂ (liftM ∘ promise.resolve)

  let result ← MonadAwait.await promise.result!
  ContextualAsync.ofExcept result

/--
Runs all computations in an `Array` concurrently and returns all results as an array.
-/
@[inline, specialize]
def concurrentlyAll (xs : Array (ContextualAsync α)) (prio := Task.Priority.default) : ContextualAsync (Array α) := do
  let tasks : Array (AsyncTask α) ← xs.mapM (MonadAsync.async (prio := prio))
  tasks.mapM MonadAwait.await

/--
~
-/
@[inline, specialize]
def isDone : ContextualAsync (Selector Unit) := do
  let st ← ReaderT.read
  return st.doneSelector

/--
~
-/
@[inline, specialize]
def cancelContext : ContextualAsync Unit := do
  let st ← ReaderT.read
  st.cancel

/--
Runs all computations concurrently and returns the result of the first one to finish.
All other results are lost, and the tasks are not cancelled, so they'll continue their executing
until the end.
-/
@[inline, specialize]
def raceAll [ForM ContextualAsync c (ContextualAsync α)] (xs : c) (prio := Task.Priority.default) : ContextualAsync α := do
  let promise ← IO.Promise.new

  ForM.forM xs fun x => do
    let task₁ ← MonadAsync.async (t := AsyncTask) (prio := prio) x
    BaseIO.chainTask task₁ (liftM ∘ promise.resolve)

  let result ← MonadAwait.await promise.result!
  ContextualAsync.ofExcept result

end ContextualAsync
end Async
end IO
end Internal
end Std

/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.System.IO
import Init.System.Promise

namespace Std
namespace Internal
namespace UV

namespace Loop

/--
Options for configuring the event loop behavior.
-/
structure Loop.Options where
  /--
  Accumulate the amount of idle time the event loop spends in the event provider.
  -/
  accumulateIdleTime : Bool := False

  /--
  Block a SIGPROF signal when polling for new events. It's commonly used for unnecessary wakeups
  when using a sampling profiler.
  -/
  blockSigProfSignal : Bool := False

/--
Configures the event loop with the specified options.
-/
@[extern "lean_uv_event_loop_configure"]
opaque configure (options : Loop.Options) : BaseIO Unit

/--
Checks if the event loop is still active and processing events.
-/
@[extern "lean_uv_event_loop_alive"]
opaque alive : BaseIO Bool

end Loop

private opaque TimerImpl : NonemptyType.{0}

/--
`Timer`s are used to generate `IO.Promise`s that resolve after some time.

A `Timer` can be in one of 3 states:
- Right after construction it's initial.
- While it is ticking it's running.
- If it has stopped for some reason it's finished.

This together with whether it was set up as `repeating` with `Timer.new` determines the behavior
of all functions on `Timer`s.
-/
def Timer : Type := TimerImpl.type

instance : Nonempty Timer := TimerImpl.property

namespace Timer

/--
Creates a new timer associated with the given event loop and data.
-/
@[extern "lean_uv_timer_mk"]
opaque mk (timeout : UInt64) (repeating : Bool) : IO Timer

/--
Starts a timer with the specified timeout interval (both in milliseconds).
-/
@[extern "lean_uv_timer_next"]
opaque next (timer : @& Timer) : IO (IO.Promise Unit)

/--
Resets the specified timer, preventing further callbacks.
-/
@[extern "lean_uv_timer_reset"]
opaque reset (timer : @& Timer) : IO Unit

end Timer
end UV
end Internal
end Std

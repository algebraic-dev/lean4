/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init
public import Std.Net
public import Std.Time
public import Std.Internal.Async.TCP
public import Std.Internal.Http.Protocol.H1.Machine

public section

namespace Std
namespace Http

open Std Internal IO Async TCP
open Time

/--
?
-/
structure Connection where
  machine : H1.Machine
  socket : Socket.Client

namespace Connection

private def receiveWithTimeout (socket : Socket.Client) (expect : UInt64) (timeoutMs : Millisecond.Offset := 5000) : Async (Option (Option ByteArray)) := do
  let result ← socket.recv? expect

  return some result

private def processNeedMoreData (machine : H1.Machine) (socket : Socket.Client) (expect : Option Nat) : Async (Except H1.Machine.Error (Option ByteArray)) := do
  try
    let expect := expect.getD machine.config.defaultPayloadBytes
    let data ← receiveWithTimeout socket expect.toUInt64

    match data with
    | some (some bytes) => pure (.ok <| some bytes)
    | some none => pure (.ok <| none)
    | none => pure (.error H1.Machine.Error.timeout)
  catch _ => pure (.error H1.Machine.Error.timeout)


private def handle (connection : Connection) (handler : Data.Request Data.Body → Async (Data.Response Data.Body)) : Async Unit := do
  let mut machine := connection.machine
  let mut running := true
  let socket := connection.socket

  let mut requestStream ← Data.Body.ByteStream.emptyWithCapacity

  let mut response ← IO.Promise.new
  let mut errored ← IO.Promise.new
  let mut respStream := none
  let mut sentResponse := false

  try
    while running do
      machine := machine.processRead
      machine := machine.processWrite

      dbg_trace "state: {repr machine.reader.state} {repr machine.writer.state}"

      let (newMachine, events) := machine.takeEvents
      machine := newMachine

      if let some (newMachine, data) := machine.takeOutput then
        machine := newMachine

        if data.size > 0 then
          socket.sendAll data.data

      if not sentResponse ∧ (← response.isResolved) then
        sentResponse := true
        let res ← await response.result!

        if machine.isWaitingResponse then
          machine := machine.sendResponse res.head
          match res.body with
          | .bytes data => machine := machine.writeUserData data  |>.closeWriter
          | .zero => machine := machine.closeWriter
          | .stream res => do
            if let some size ← res.getKnownSize then
              machine := machine.setKnownSize size

            respStream := some res

      if let some stream := respStream then
        if machine.isWriterOpened then
          if machine.isReaderComplete ∧ events.isEmpty then
            if let some data ← stream.recv then
              machine := machine.writeUserData data
            else
              machine := machine.closeWriter
          else
            match ← stream.tryRecv with
            | some (some res) => machine := machine.writeUserData res
            | some none => pure ()
            | none => machine := machine.closeWriter

      if ← errored.isResolved then
        let _ ← await errored.result!
        machine := machine.setFailure (.other "Internal Error") .internalServerError

      for event in events do
        match event with
        | .needMoreData expect => do
          match ← processNeedMoreData machine socket expect with
          | .ok (some bs) => machine := machine.feed bs
          | .ok none =>
            running := false
            break
          | .error _ => do
            if let .needStartLine := machine.reader.state then
              running := false; break
            else
              machine := machine.setFailure .timeout .requestTimeout

        | .endHeaders head => do
          requestStream.setKnownSize <|
            match H1.Machine.getRequestSize head with
            | some (.fixed n) => some n
            | _ => none

          let newResponse := handler { head, body := .stream requestStream }
          let task ← newResponse.asTask
          BaseIO.chainTask task fun
            | .error res => errored.resolve res
            | .ok res => response.resolve res
        | .gotData final data =>
          dbg_trace "GOT DATA {final} {data.size}"
          discard <| requestStream.send data.toByteArray

          if final then
            requestStream.close

        | .chunkExt _ =>
          pure ()
        | .failed =>
          running := false
        | .close =>
          running := false
        | .next =>
          requestStream ← Data.Body.ByteStream.emptyWithCapacity

    IO.println "closing conncetion"
  catch err =>
    IO.println s!"ERR: {err}"


end Connection

/--
Serve conection
-/
def serve (addr : Net.SocketAddress) (handler : Data.Request Data.Body  → Async (Data.Response Data.Body)) (backlog : UInt32 := 128) : Async Unit := do
  let server ← Socket.Server.mk
  server.bind addr
  server.listen backlog

  while true do
    let client ← server.accept
    background (prio := .max) <|
      Connection.mk {} client
        |>.handle handler

end Http
end Std

prelude
import Lean.Util.Trace

/-! `trace.profiler.output` Firefox Profiler integration -/

namespace Lean.Firefox

-- https://github.com/firefox-devtools/profiler/blob/main/src/types/profile.js

abbrev Milliseconds := Float

structure Category where
  name : String
  color : String
  subcategories : Array String := #[]
deriving ToJson

structure ProfileMeta where
  interval : Milliseconds := 0  -- should be irrelevant with `tracing-ms`
  startTime : Milliseconds
  categories : Array Category := #[]
  processType : Nat := 0
  product : String := "lean"
  preprocessedProfileVersion : Nat := 48
  markerSchema : Array Json := #[]
deriving ToJson

structure StackTable where
  frame : Array Nat
  «prefix» : Array (Option Nat)
  category : Array Nat
  subcategory : Array Nat
  length : Nat
deriving ToJson

structure SamplesTable where
  stack : Array Nat
  time : Array Milliseconds
  weight : Array Milliseconds
  weightType : String := "tracing-ms"
  length : Nat
deriving ToJson

structure FuncTable where
  name : Array Nat
  isJS : Array Json := #[]
  relevantForJS : Array Json := #[]
  resource : Array Int
  fileName : Array (Option Nat)
  lineNumber : Array (Option Nat)
  columnNumber : Array (Option Nat)
  length : Nat
deriving ToJson

structure FrameTable where
  func : Array Nat
  inlineDepth : Array Json := #[]
  innerWindowID : Array Json := #[]
  length : Nat
deriving ToJson

structure RawMarkerTable where
  data : Array Json := #[]
  name : Array Json := #[]
  length : Nat := 0
deriving ToJson

structure ResourceTable where
  type : Array Json := #[]
  length : Nat := 0
deriving ToJson

structure Thread where
  name : String := "main"
  processType : String := "default"
  isMainThread : Bool := true
  samples : SamplesTable
  markers: RawMarkerTable := {}
  stackTable : StackTable
  frameTable : FrameTable
  resourceTable : ResourceTable := {}
  stringArray : Array String
  funcTable : FuncTable
deriving ToJson

structure Profile where
  meta : ProfileMeta
  libs : Array Json := #[]
  threads : Array Thread
deriving ToJson

structure ThreadWithMaps extends Thread where
  stringMap : HashMap String Nat := {}
  funcMap : HashMap Nat Nat := {}
  stackMap : HashMap (Nat × Option Nat) Nat := {}
  lastTime : Milliseconds := 0

def categories : Array Category := #[
  { name := "Other", color := "gray" },
  { name := "Elab", color := "red" },
  { name := "Meta", color := "yellow" }
]

partial def addTrace (thread : ThreadWithMaps) (trace : MessageData) : ThreadWithMaps :=
  StateT.run (go none trace) thread |>.2
where
  go parentStackIdx? : _ → StateM ThreadWithMaps Unit
    | .trace data _ children => do
      if data.startTime == 0 then
        return
      let mut funcName := data.cls.toString
      if !data.tag.isEmpty then
        funcName := s!"{funcName}: {data.tag}"
      let strIdx ← getStrIdx funcName
      let category := categories.findIdx? (·.name == data.cls.getRoot.toString) |>.getD 0
      let funcIdx ← modifyGet fun thread =>
        if let some idx := thread.funcMap.find? strIdx then
          (idx, thread)
        else
          (thread.funcMap.size, { thread with
            funcTable := {
              name := thread.funcTable.name.push strIdx
              resource := thread.funcTable.resource.push (-1)
              fileName := thread.funcTable.fileName.push none
              lineNumber := thread.funcTable.lineNumber.push none
              columnNumber := thread.funcTable.columnNumber.push none
              length := thread.funcTable.length + 1
            }
            frameTable := {
              func := thread.frameTable.func.push thread.funcMap.size
              length := thread.frameTable.length + 1
            }
            funcMap := thread.funcMap.insert strIdx thread.funcMap.size })
      let frameIdx := funcIdx
      let stackIdx ← modifyGet fun thread =>
        if let some idx := thread.stackMap.find? (frameIdx, parentStackIdx?) then
          (idx, thread)
        else
          (thread.stackMap.size, { thread with
            stackTable := {
              frame := thread.stackTable.frame.push frameIdx
              «prefix» := thread.stackTable.prefix.push parentStackIdx?
              category := thread.stackTable.category.push category
              subcategory := thread.stackTable.subcategory.push 0
              length := thread.stackTable.length + 1
            }
            stackMap := thread.stackMap.insert (frameIdx, parentStackIdx?) thread.stackMap.size })
      if let some nextStart := children.findSome? getNextStart? then
        modify fun thread => { thread with samples := {
          stack := thread.samples.stack.push stackIdx
          time := thread.samples.time.push (data.startTime * 1000)
          weight := thread.samples.weight.push ((nextStart - data.startTime) * 1000)
          length := thread.samples.length + 1
        } }
        children.forM <| go (some stackIdx)
        modify fun thread => { thread with
          lastTime := data.stopTime * 1000
          samples := {
            stack := thread.samples.stack.push stackIdx
            time := thread.samples.time.push thread.lastTime
            weight := thread.samples.weight.push (data.stopTime * 1000 - thread.lastTime)
            length := thread.samples.length + 1
          } }
      else
        modify fun thread => { thread with
          lastTime := data.stopTime * 1000
          samples := {
            stack := thread.samples.stack.push stackIdx
            time := thread.samples.time.push (data.startTime * 1000)
            weight := thread.samples.weight.push ((data.stopTime - data.startTime) * 1000)
            length := thread.samples.length + 1
          } }
    | .withContext _ msg => go parentStackIdx? msg
    | _ => return
  getNextStart?
    | .trace data _ children => do
      if data.startTime != 0 then
        return data.startTime
      if let some startTime := children.findSome? getNextStart? then
        return startTime
      none
    | .withContext _ msg => getNextStart? msg
    | _ => none
  getStrIdx s :=
    modifyGet fun thread =>
      if let some idx := thread.stringMap.find? s then
        (idx, thread)
      else
        (thread.stringMap.size, { thread with
          stringArray := thread.stringArray.push s
          stringMap := thread.stringMap.insert s thread.stringMap.size })

def Profile.export (startTime : Milliseconds) (traceState : TraceState) : IO String := do
  let thread : Thread := {
    samples := { stack := #[], time := #[], weight := #[], length := 0 }
    stackTable := { frame := #[], «prefix» := #[], category := #[], subcategory := #[], length := 0 }
    frameTable := { func := #[], length := 0 }
    stringArray := #[]
    funcTable := { name := #[], resource := #[], fileName := #[], lineNumber := #[], columnNumber := #[], length := 0 }
  }
  let trace := .trace {
    cls := `runFrontend, startTime, stopTime := (← IO.monoNanosNow).toFloat / 1000000000,
    collapsed := true } "" (traceState.traces.toArray.map (·.msg))
  let thread := addTrace { thread with } trace
  let profile : Profile := {
    meta := { startTime, categories }
    threads := #[thread.toThread]
  }
  return Json.compress <| toJson profile

end Firefox

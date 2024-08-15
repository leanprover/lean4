/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Util.Trace

/-! `trace.profiler.output` Firefox Profiler integration -/

namespace Lean.Firefox

/-! Definitions from https://github.com/firefox-devtools/profiler/blob/main/src/types/profile.js -/

abbrev Milliseconds := Float

structure Category where
  name : String
  color : String
  subcategories : Array String := #[]
deriving FromJson, ToJson

structure ProfileMeta where
  interval : Milliseconds := 0  -- should be irrelevant with `tracing-ms`
  startTime : Milliseconds
  categories : Array Category := #[]
  processType : Nat := 0
  product : String := "lean"
  preprocessedProfileVersion : Nat := 48
  markerSchema : Array Json := #[]
deriving FromJson, ToJson

structure StackTable where
  frame : Array Nat
  «prefix» : Array (Option Nat)
  category : Array Nat
  subcategory : Array Nat
  length : Nat
deriving FromJson, ToJson

structure SamplesTable where
  stack : Array Nat
  time : Array Milliseconds
  weight : Array Milliseconds
  weightType : String := "tracing-ms"
  length : Nat
deriving FromJson, ToJson

structure FuncTable where
  name : Array Nat
  isJS : Array Json := #[]
  relevantForJS : Array Json := #[]
  resource : Array Int
  fileName : Array (Option Nat)
  lineNumber : Array (Option Nat)
  columnNumber : Array (Option Nat)
  length : Nat
deriving FromJson, ToJson

structure FrameTable where
  func : Array Nat
  inlineDepth : Array Json := #[]
  innerWindowID : Array Json := #[]
  length : Nat
deriving FromJson, ToJson

structure RawMarkerTable where
  data : Array Json := #[]
  name : Array Json := #[]
  length : Nat := 0
deriving FromJson, ToJson

structure ResourceTable where
  type : Array Json := #[]
  length : Nat := 0
deriving FromJson, ToJson

structure Thread where
  name : String
  processType : String := "default"
  isMainThread : Bool := true
  samples : SamplesTable
  markers: RawMarkerTable := {}
  stackTable : StackTable
  frameTable : FrameTable
  resourceTable : ResourceTable := {}
  stringArray : Array String
  funcTable : FuncTable
deriving FromJson, ToJson

structure Profile where
  meta : ProfileMeta
  libs : Array Json := #[]
  threads : Array Thread
deriving FromJson, ToJson

/-- Thread with maps necessary for computing max sharing indices -/
structure ThreadWithMaps extends Thread where
  stringMap : Std.HashMap String Nat := {}
  funcMap : Std.HashMap Nat Nat := {}
  stackMap : Std.HashMap (Nat × Option Nat) Nat := {}
  /-- Last timestamp encountered: stop time of preceding sibling, or else start time of parent.  -/
  lastTime : Float := 0

-- TODO: add others, dynamically?
def categories : Array Category := #[
  { name := "Other", color := "gray" },
  { name := "Elab", color := "red" },
  { name := "Meta", color := "yellow" }
]

private partial def addTrace (pp : Bool) (thread : ThreadWithMaps) (trace : MessageData) :
    IO ThreadWithMaps :=
  (·.2) <$> StateT.run (go none trace) thread
where
  go parentStackIdx? : _ → StateT ThreadWithMaps IO Unit
    | .trace data msg children => do
      if data.startTime == 0 then
        return  -- no time data, skip
      let mut funcName := data.cls.toString
      if !data.tag.isEmpty then
        funcName := s!"{funcName}: {data.tag}"
      if pp then
        funcName := s!"{funcName}: {← msg.format}"
      let strIdx ← modifyGet fun thread =>
        if let some idx := thread.stringMap[funcName]? then
          (idx, thread)
        else
          (thread.stringMap.size, { thread with
            stringArray := thread.stringArray.push funcName
            stringMap := thread.stringMap.insert funcName thread.stringMap.size })
      let category := categories.findIdx? (·.name == data.cls.getRoot.toString) |>.getD 0
      let funcIdx ← modifyGet fun thread =>
        if let some idx := thread.funcMap[strIdx]? then
          (idx, thread)
        else
          (thread.funcMap.size, { thread with
            funcTable := {
              name := thread.funcTable.name.push strIdx
              resource := thread.funcTable.resource.push (-1)
              -- the following fields could be inferred from `Syntax` in the message
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
        if let some idx := thread.stackMap[(frameIdx, parentStackIdx?)]? then
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
      modify fun thread => { thread with lastTime := data.startTime }
      for c in children do
        if let some nextStart := getNextStart? c then
          -- add run time slice between children/before first child
          modify fun thread => { thread with samples := {
            stack := thread.samples.stack.push stackIdx
            time := thread.samples.time.push (thread.lastTime * 1000)
            weight := thread.samples.weight.push ((nextStart - thread.lastTime) * 1000)
            length := thread.samples.length + 1
          } }
          go (some stackIdx) c
      -- add remaining slice after last child
      modify fun thread => { thread with
        lastTime := data.stopTime
        samples := {
          stack := thread.samples.stack.push stackIdx
          time := thread.samples.time.push (thread.lastTime * 1000)
          weight := thread.samples.weight.push ((data.stopTime - thread.lastTime) * 1000)
          length := thread.samples.length + 1
        } }
    | .withContext _ msg => go parentStackIdx? msg
    | _ => return
  /-- Returns first `startTime` in the trace tree, if any. -/
  getNextStart?
    | .trace data _ children => do
      if data.startTime != 0 then
        return data.startTime
      if let some startTime := children.findSome? getNextStart? then
        return startTime
      none
    | .withContext _ msg => getNextStart? msg
    | _ => none

def Thread.new (name : String) : Thread := {
  name
  samples := { stack := #[], time := #[], weight := #[], length := 0 }
  stackTable := { frame := #[], «prefix» := #[], category := #[], subcategory := #[], length := 0 }
  frameTable := { func := #[], length := 0 }
  stringArray := #[]
  funcTable := {
    name := #[], resource := #[], fileName := #[], lineNumber := #[], columnNumber := #[],
    length := 0 }
}

def Profile.export (name : String) (startTime : Milliseconds) (traceState : TraceState)
    (opts : Options) : IO Profile := do
  let thread := Thread.new name
  -- wrap entire trace up to current time in `runFrontend` node
  let trace := .trace {
    cls := `runFrontend, startTime, stopTime := (← IO.monoNanosNow).toFloat / 1000000000,
    collapsed := true } "" (traceState.traces.toArray.map (·.msg))
  let thread ← addTrace (Lean.trace.profiler.output.pp.get opts) { thread with } trace
  return {
    meta := { startTime, categories }
    threads := #[thread.toThread]
  }

structure ThreadWithCollideMaps extends ThreadWithMaps where
  /-- Max sharing map for samples -/
  sampleMap : Std.HashMap Nat Nat := {}

/--
Adds samples from `add` to `thread`, increasing the weight of existing samples with identical stacks
instead of pushing new samples.
-/
private partial def collideThreads (thread : ThreadWithCollideMaps) (add : Thread) :
    ThreadWithCollideMaps :=
  StateT.run collideSamples thread |>.2
where
  collideSamples : StateM ThreadWithCollideMaps Unit := do
    for oldSampleIdx in [0:add.samples.length] do
      let oldStackIdx := add.samples.stack[oldSampleIdx]!
      let stackIdx ← collideStacks oldStackIdx
      modify fun thread =>
        if let some idx := thread.sampleMap[stackIdx]? then
          -- imperative to preserve linear use of arrays here!
          let ⟨⟨⟨t1, t2, t3, samples, t5, t6, t7, t8, t9, t10⟩, o2, o3, o4, o5⟩, o6⟩ := thread
          let ⟨s1, s2, weight, s3, s4⟩ := samples
          let weight := weight.set! idx <| weight[idx]! + add.samples.weight[oldSampleIdx]!
          let samples := ⟨s1, s2, weight, s3, s4⟩
          ⟨⟨⟨t1, t2, t3, samples, t5, t6, t7, t8, t9, t10⟩, o2, o3, o4, o5⟩, o6⟩
        else
          -- imperative to preserve linear use of arrays here!
          let ⟨⟨⟨t1, t2, t3, samples, t5, t6, t7, t8, t9, t10⟩, o2, o3, o4, o5⟩, sampleMap⟩ :=
            thread
          let ⟨stack, time, weight, _, length⟩ := samples
          let samples := {
              stack := stack.push stackIdx
              time := time.push time.size.toFloat
              weight := weight.push add.samples.weight[oldSampleIdx]!
              length := length + 1
            }
          let sampleMap := sampleMap.insert stackIdx sampleMap.size
          ⟨⟨⟨t1, t2, t3, samples, t5, t6, t7, t8, t9, t10⟩, o2, o3, o4, o5⟩, sampleMap⟩
  collideStacks oldStackIdx : StateM ThreadWithCollideMaps Nat := do
    let oldParentStackIdx? := add.stackTable.prefix[oldStackIdx]!
    let parentStackIdx? ← oldParentStackIdx?.mapM (collideStacks ·)
    let oldFrameIdx := add.stackTable.frame[oldStackIdx]!
    let oldFuncIdx := add.frameTable.func[oldFrameIdx]!
    let oldStrIdx := add.funcTable.name[oldFuncIdx]!
    let strIdx ← getStrIdx add.stringArray[oldStrIdx]!
    let funcIdx ← modifyGet fun thread =>
      if let some idx := thread.funcMap[strIdx]? then
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
    modifyGet fun thread =>
      if let some idx := thread.stackMap[(frameIdx, parentStackIdx?)]? then
        (idx, thread)
      else
        (thread.stackMap.size,
          let ⟨⟨⟨t1,t2, t3, t4, t5, stackTable, t7, t8, t9, t10⟩, o2, o3, stackMap, o5⟩, o6⟩ :=
            thread
          let { frame, «prefix», category, subcategory, length } := stackTable
          let stackTable := {
            frame := frame.push frameIdx
            «prefix» := prefix.push parentStackIdx?
            category := category.push add.stackTable.category[oldStackIdx]!
            subcategory := subcategory.push add.stackTable.subcategory[oldStackIdx]!
            length := length + 1
          }
          let stackMap := stackMap.insert (frameIdx, parentStackIdx?) stackMap.size
          ⟨⟨⟨t1,t2, t3, t4, t5, stackTable, t7, t8, t9, t10⟩, o2, o3, stackMap, o5⟩, o6⟩)
  getStrIdx (s : String) :=
    modifyGet fun thread =>
      if let some idx := thread.stringMap[s]? then
        (idx, thread)
      else
        (thread.stringMap.size, { thread with
          stringArray := thread.stringArray.push s
          stringMap := thread.stringMap.insert s thread.stringMap.size })

/--
Merges given profiles such that samples with identical stacks are deduplicated by adding up their
weights. Minimizes profile size while preserving per-stack timing information.
-/
def Profile.collide (ps : Array Profile) : Option Profile := do
  let base ← ps[0]?
  let thread := Thread.new "collided"
  let thread := ps.map (·.threads) |>.flatten.foldl collideThreads { thread with }
  return { base with threads := #[thread.toThread] }

end Lean.Firefox

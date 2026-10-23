module

public import Std.Tactic.BVDecide.Bitblast
meta import Lean.Elab.Command

/-!
Tests `profiler.import` (set in `importProfile.lean.init.sh`, along with `Elab.inServer=false`):
`importModules` records per-module import costs in `Environment.header.importProfile?`. Only the
shape of the profile is checked, not any timings.
-/

open Lean

meta def check (cond : Bool) (msg : String) : CoreM Unit :=
  unless cond do throwError msg

meta def within (r outer : MonoNanosRange) : Bool :=
  outer.start ≤ r.start && r.start ≤ r.stop && r.stop ≤ outer.stop

#eval show CoreM Unit from do
  check (!Elab.inServer.get (← getOptions)) "test must run outside the server"
  let env ← getEnv
  let some p := env.header.importProfile? | throwError "no import profile"
  let mods := env.header.modules
  check (p.modules.size == mods.size) "`modules` is not indexed by `ModuleIdx`"
  for (name, r) in [("readModules", p.readModules), ("buildConstMaps", p.buildConstMaps),
      ("setEntries", p.setEntries), ("setIREntries", p.setIREntries)] do
    check (within r p.toMonoNanosRange) s!"{name} not within the import"
  check (p.readModules.stop ≤ p.buildConstMaps.start) "steps out of order"
  check p.setServerEntries?.isNone "server entries set up outside the server"
  check p.markPersistent?.isSome "header environment should be leaked"
  for h : i in *...mods.size do
    let m := mods[i]
    let c := p.modules[i]!
    check (c.readData?.isSome == m.hasData) s!"{m.module}: `readData?` disagrees with `hasData`"
    check (within c.privateConsts p.buildConstMaps) s!"{m.module}: `privateConsts`"
    check (within c.extraConsts p.buildConstMaps) s!"{m.module}: `extraConsts`"
    check (c.privateConsts.stop ≤ c.extraConsts.start) s!"{m.module}: const steps out of order"
    if let some r := c.publicConsts? then
      check (within r p.buildConstMaps) s!"{m.module}: `publicConsts?`"
      check m.isExported s!"{m.module}: `publicConsts?` for a non-exported module"
    if let some d := c.readData? then
      check (within d.toMonoNanosRange p.readModules) s!"{m.module}: `readData?`"
      for r in [some d.olean, d.oleanServer?, d.oleanPrivate?].filterMap id do
        check (within r d.toMonoNanosRange) s!"{m.module}: data part"
    if let some d := c.readIR? then
      check (within d.toMonoNanosRange p.readModules) s!"{m.module}: `readIR?`"
      for r in [d.irSig?, d.ir?].filterMap id do
        check (within r d.toMonoNanosRange) s!"{m.module}: IR part"
    if m.irPhases matches .comptime then
      check c.readIR?.isSome s!"{m.module}: IR needed via `meta import` but not read"

  -- `meta import`ed: IR is loaded, along with all `.olean*` parts of the `module`
  let some cmd := env.getModuleIdx? `Lean.Elab.Command | throwError "Lean.Elab.Command missing"
  let cmdCost := p.modules[cmd.toNat]!
  check (mods[cmd.toNat]!.irPhases matches .comptime) "Lean.Elab.Command: not comptime"
  check (cmdCost.readIR?.any fun d => d.irSig?.isSome && d.ir?.isSome)
    "Lean.Elab.Command: IR parts not read"
  check (cmdCost.readData?.any fun d => d.oleanServer?.isSome && d.oleanPrivate?.isSome)
    "Lean.Elab.Command: data parts not read"
  check cmdCost.publicConsts?.isNone "Lean.Elab.Command: not publicly imported"
  -- `public import`ed, outside the `meta` closure: no IR is loaded
  let some bv := env.getModuleIdx? `Std.Tactic.BVDecide.Bitblast | throwError "Bitblast missing"
  let bvCost := p.modules[bv.toNat]!
  check bvCost.readIR?.isNone "Std.Tactic.BVDecide.Bitblast: IR read"
  check bvCost.publicConsts?.isSome "Std.Tactic.BVDecide.Bitblast: no public constants"

  let some e := p.exts? | throwError "no extension costs"
  check (within e.toMonoNanosRange p.toMonoNanosRange) "extensions not within the import"
  check (p.setEntries.stop ≤ e.start) "extensions out of order"
  check (e.extensions.size == (← persistentEnvExtensionsRef.get).size)
    "`extensions` is not indexed by `persistentEnvExtensionsRef`"
  for r in e.extensions do
    check (within r.toMonoNanosRange e.toMonoNanosRange) "extension cost"
    if let some n := r.newExts? then
      check (within n e.toMonoNanosRange) "`newExts?`"
  check (e.inits.size == mods.size) "`inits` is not indexed by `ModuleIdx`"
  check e.markPersistent?.isSome "header environment should be leaked"
  for h : i in *...e.inits.size do
    let c := e.inits[i]
    check (within c.toMonoNanosRange e.toMonoNanosRange) s!"{mods[i]!.module}: init"
    match c.exec with
    | .interpreted ran _ =>
      check (!ran.isEmpty) s!"{mods[i]!.module}: `interpreted` without declarations"
      for d in ran do
        check (within d.toMonoNanosRange c.toMonoNanosRange) s!"{mods[i]!.module}: init decl"
    | .allSkipped skipped =>
      check (!skipped.isEmpty) s!"{mods[i]!.module}: `allSkipped` without declarations"
    | _ => pure ()
  -- Lean's own modules are compiled into the `lean` executable
  check (e.inits[cmd.toNat]!.exec matches .native _) "Lean.Elab.Command: not initialized natively"

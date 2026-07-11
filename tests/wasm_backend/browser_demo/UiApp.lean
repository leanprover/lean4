module

import Lean
import UiAbi

/-!
Fiber UI demo using a typed effect batch and numeric handler IDs.

* All visible text is `Element.label : String` (no TextId chrome table).
* Clicks carry stable handler IDs; optional UTF-8 payloads use pointer/length slices.
* Hyp rows are clickable; inapplicable tactics get `disabled`.
-/

open Lean

/-! ### VDOM -/

public inductive Tag where
  | div | button | span | ul | li
  deriving BEq, Inhabited, Repr

def Tag.toU32 : Tag → UInt32
  | .div => 0 | .button => 1 | .span => 2 | .ul => 3 | .li => 4

/-- Virtual DOM: free-string labels + nodes with class and an optional typed handler ID. -/
public inductive Element where
  | label (s : String)
  | node (tag : Tag) (key : Option UInt32) (cls : String) (onClick : UInt32)
      (children : Array Element)
  deriving Inhabited

/-! ### JSX -/

class ToJsxChildren (α : Type) where
  toArray : α → Array Element

instance : ToJsxChildren Element where
  toArray e := #[e]

instance : ToJsxChildren (Array Element) where
  toArray a := a

partial def arrayAppend (a b : Array α) : Array α :=
  let rec go (i : Nat) (acc : Array α) : Array α :=
    if h : i < b.size then go (i + 1) (acc.push b[i]) else acc
  go 0 a

namespace Jsx

declare_syntax_cat jsxElement
declare_syntax_cat jsxChild
declare_syntax_cat jsxAttr

syntax "key={" term "}" : jsxAttr
syntax "class=" str : jsxAttr
syntax "class={" term "}" : jsxAttr
syntax "on=" str : jsxAttr
syntax "on={" term "}" : jsxAttr

syntax "<" ident jsxAttr* "/>" : jsxElement
syntax "<" ident jsxAttr* ">" jsxChild* "</" ident ">" : jsxElement

syntax "{" term "}" : jsxChild
syntax "[" term "]" : jsxChild
syntax jsxElement : jsxChild

scoped syntax:max jsxElement : term

meta def extractAttrs (attrs : Array Syntax) :
    MacroM (TSyntax `term × TSyntax `term × TSyntax `term) := do
  let mut key ← `(none)
  let mut cls ← `("")
  let mut on ← `((0 : UInt32))
  for attr in attrs do
    match attr with
    | `(jsxAttr| key={$e}) => key ← `(some ($e : UInt32))
    | `(jsxAttr| class={$e}) => cls ← `(($e : String))
    | `(jsxAttr| class=$s:str) => cls ← `($s)
    | `(jsxAttr| on={$e}) => on ← `(($e : UInt32))
    | `(jsxAttr| on="intro") => on ← `(UiAbi.Handler.intro)
    | `(jsxAttr| on="constructor") => on ← `(UiAbi.Handler.constructor)
    | `(jsxAttr| on="cases") => on ← `(UiAbi.Handler.cases)
    | `(jsxAttr| on="undo") => on ← `(UiAbi.Handler.undo)
    | `(jsxAttr| on="reset") => on ← `(UiAbi.Handler.reset)
    | _ => Macro.throwUnsupported
  return (key, cls, on)

meta def expandChildren (children : Array Syntax) : MacroM (TSyntax `term) := do
  let mut cs ← `(#[])
  for child in children do
    cs ← match child with
    | `(jsxChild|{$t}) => `(arrayAppend $cs (ToJsxChildren.toArray $t))
    | `(jsxChild|[$t]) => `(arrayAppend $cs ($t : Array Element))
    | `(jsxChild|$e:jsxElement) => `(($cs).push ($e:jsxElement : Element))
    | _ => Macro.throwUnsupported
  return cs

macro_rules
  | `(<$n $attrs* />) => do
    let (key, cls, on) ← extractAttrs attrs
    let tag := mkIdent (`Tag ++ n.getId)
    `(Element.node $tag $key $cls $on #[])
  | `(<$n $attrs* >$children*</$m>) => do
    unless n.getId == m.getId do
      withRef m <| Macro.throwError s!"Leading and trailing tags don't match: '{n.getId}', '{m.getId}'"
    let (key, cls, on) ← extractAttrs attrs
    let kids ← expandChildren children
    let tag := mkIdent (`Tag ++ n.getId)
    `(Element.node $tag $key $cls $on $kids)

end Jsx

public structure Fiber where
  id : UInt32
  tag : Tag := .div
  key : Option UInt32 := none
  cls : String := ""
  onClick : UInt32 := 0
  isLabel : Bool := false
  labelStr : String := ""
  children : Array Fiber := #[]

instance : Inhabited Fiber where
  default := { id := 0 }

/-- Typed effect lowered to one fixed-size wire record by `ui_bridge.cpp`. -/
public structure Effect where
  op : UInt32
  id : UInt32
  parent : UInt32
  index : UInt32 := 0
  payload0 : UInt32 := 0
  payload1 : UInt32 := 0
  text : String := ""

instance : Inhabited Effect where
  default := { op := 0, id := 0, parent := 0 }

/-! ### Formulas + proof state -/

public inductive Formula where
  | true_
  | atom (i : UInt32)
  | imp (a b : Formula)
  | and_ (a b : Formula)
  deriving BEq, Inhabited, Repr

partial def Formula.pp : Formula → String
  | .true_ => "True"
  | .atom 0 => "P"
  | .atom 1 => "Q"
  | .atom 2 => "R"
  | .atom _ => "?"
  | .imp a b => "(" ++ a.pp ++ " → " ++ b.pp ++ ")"
  | .and_ a b => "(" ++ a.pp ++ " ∧ " ++ b.pp ++ ")"

public structure Goal where
  hyps : Array Formula := #[]
  target : Formula := .true_

instance : Inhabited Goal where
  default := { hyps := #[], target := .true_ }

public structure Model where
  goals : Array Goal := #[]
  history : Array (Array Goal) := #[]
  msg : String := ""

instance : Inhabited Model where
  default := { goals := #[], history := #[], msg := "" }

def Model.initial : Model :=
  { goals := #[{ hyps := #[], target := .imp (.atom 0) (.imp (.atom 1) (.and_ (.atom 0) (.atom 1))) }]
    history := #[]
    msg := "Prove: P → Q → P ∧ Q" }

public inductive Event where
  | intro | constructor | cases | exact (i : UInt32) | undo | reset
  deriving BEq, Inhabited

def hypName (i : Nat) : String :=
  match i with
  | 0 => "h0" | 1 => "h1" | 2 => "h2" | 3 => "h3"
  | 4 => "h4" | 5 => "h5" | 6 => "h6" | 7 => "h7" | _ => "h?"

def goalTitle (i : Nat) : String :=
  match i with
  | 0 => "goal #1" | 1 => "goal #2" | 2 => "goal #3" | 3 => "goal #4" | _ => "goal"

def Event.ofHandlerId (id : UInt32) : Option Event :=
  if id == UiAbi.Handler.intro then some .intro
  else if id == UiAbi.Handler.constructor then some .constructor
  else if id == UiAbi.Handler.cases then some .cases
  else if id == UiAbi.Handler.undo then some .undo
  else if id == UiAbi.Handler.reset then some .reset
  else if id >= UiAbi.Handler.exactBase && id < UiAbi.Handler.exactBase + 8 then
    some (.exact (id - UiAbi.Handler.exactBase))
  else none

def Model.pack (m : Model) : UInt32 :=
  let n := m.goals.size.toUInt32 &&& (0xffff : UInt32)
  let solved : UInt32 := if m.goals.size == 0 then 1 else 0
  n ||| (solved <<< 16)

/-! ### Retained model / fiber -/

@[extern "lean_ui_load_model", never_extract]
opaque loadModelRaw : UInt32 → Option Model

@[extern "lean_ui_store_model", never_extract]
opaque storeModelRaw : UInt32 → @& Option Model → UInt32

/-! ### Host monad -/

structure World where
  token : UInt32
  deriving Inhabited

structure Host (α : Type) where
  run : World → α × World

instance : Functor Host where
  map f m := ⟨fun w =>
    let (a, w) := m.run w
    (f a, w)⟩
  mapConst a m := ⟨fun w =>
    let (_, w) := m.run w
    (a, w)⟩

instance : Pure Host where
  pure a := ⟨fun w => (a, w)⟩

instance : Seq Host where
  seq mf mx := ⟨fun w =>
    let (f, w) := mf.run w
    let (x, w) := (mx ()).run w
    (f x, w)⟩

instance : SeqLeft Host where
  seqLeft ma mb := ⟨fun w =>
    let (a, w) := ma.run w
    let (_, w) := (mb ()).run w
    (a, w)⟩

instance : SeqRight Host where
  seqRight ma mb := ⟨fun w =>
    let (_, w) := ma.run w
    (mb ()).run w⟩

instance : Applicative Host where
  map := Functor.map
  mapConst := Functor.mapConst
  pure := Pure.pure
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

instance : Bind Host where
  bind m f := ⟨fun w =>
    let (a, w) := m.run w
    (f a).run w⟩

instance : Monad Host where
  map := Functor.map
  mapConst := Functor.mapConst
  pure := Pure.pure
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight
  bind := Bind.bind

@[inline] def hostPrim (f : UInt32 → UInt32) : Host Unit :=
  ⟨fun w => ((), ⟨f w.token⟩)⟩

@[inline] def hostRead (f : UInt32 → α) : Host α :=
  ⟨fun w => (f w.token, w)⟩

@[extern "lean_ui_clear_effects", never_extract]
opaque clearEffectsRaw : UInt32 → UInt32

@[extern "lean_ui_push_effect", never_extract]
opaque pushEffectRaw :
    UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → @& String → UInt32

@[extern "lean_ui_batch_ptr", never_extract]
opaque batchPtrRaw : UInt32 → UInt32

@[extern "lean_ui_load_fiber", never_extract]
opaque loadFiberRaw : UInt32 → Option Fiber

@[extern "lean_ui_store_fiber", never_extract]
opaque storeFiberRaw : UInt32 → @& Option Fiber → UInt32

def clearEffects : Host Unit :=
  hostPrim clearEffectsRaw

def pushEffect (e : Effect) : Host Unit :=
  hostPrim fun w => pushEffectRaw w e.op e.id e.parent e.index e.payload0 e.payload1 e.text

def loadFiber : Host (Option Fiber) := hostRead loadFiberRaw
def storeFiber (f : Option Fiber) : Host Unit := hostPrim fun t => storeFiberRaw t f
def loadModel : Host (Option Model) := hostRead loadModelRaw
def storeModel (m : Option Model) : Host Unit := hostPrim fun t => storeModelRaw t m

def flushEffects (es : Array Effect) : Host Unit := do
  clearEffects
  let rec go (i : Nat) : Host Unit := do
    if h : i < es.size then
      pushEffect es[i]
      go (i + 1)
    else pure ()
  go 0

def runHost (seed : UInt32) (m : Host UInt32) : UInt32 :=
  let (v, w) := m.run ⟨seed⟩
  v ||| ((w.token &&& (1 : UInt32)) <<< 31)

/-! ### Arrays -/

partial def arrayEraseIdx (xs : Array α) (i : Nat) : Array α :=
  let rec go (j : Nat) (acc : Array α) : Array α :=
    if h : j < xs.size then
      if j == i then go (j + 1) acc else go (j + 1) (acc.push xs[j])
    else acc
  go 0 (Array.emptyWithCapacity (if xs.size = 0 then 0 else xs.size - 1))

partial def arrayFindIdx? (xs : Array α) (p : α → Bool) : Option Nat :=
  let rec go (j : Nat) : Option Nat :=
    if h : j < xs.size then
      if p xs[j] then some j else go (j + 1)
    else none
  go 0

partial def arrayMapIdx (xs : Array α) (f : Nat → α → β) : Array β :=
  let rec go (i : Nat) (acc : Array β) : Array β :=
    if h : i < xs.size then go (i + 1) (acc.push (f i xs[i])) else acc
  go 0 (Array.emptyWithCapacity xs.size)

/-! ### Tactics -/

def pushHistory (m : Model) : Model :=
  { m with history := m.history.push m.goals }

def setGoals (m : Model) (gs : Array Goal) (msg : String) : Model :=
  let m := pushHistory m
  { m with goals := gs, msg }

def focus? (m : Model) : Option Goal :=
  if h : 0 < m.goals.size then some m.goals[0] else none

def replaceFocus (m : Model) (g : Goal) (rest : Array Goal) (msg : String) : Model :=
  setGoals m (arrayAppend #[g] rest) msg

def dropFocus (m : Model) (rest : Array Goal) (msg : String) : Model :=
  setGoals m rest msg

def canIntro (g : Goal) : Bool :=
  match g.target with | .imp .. => true | _ => false

def canConstructor (g : Goal) : Bool :=
  match g.target with | .and_ .. => true | .true_ => true | _ => false

def canCases (g : Goal) : Bool :=
  if g.hyps.size == 0 then false
  else
    let i := g.hyps.size - 1
    if h : i < g.hyps.size then
      match g.hyps[i] with | .and_ .. => true | _ => false
    else false

def tacIntro (m : Model) : Model :=
  match focus? m with
  | none => { m with msg := "No goals." }
  | some g =>
    if !canIntro g then { m with msg := "intro failed: target is not an implication." }
    else
      match g.target with
      | .imp a b =>
        let g' := { hyps := g.hyps.push a, target := b }
        replaceFocus m g' (arrayEraseIdx m.goals 0) "intro"
      | _ => { m with msg := "intro failed." }

def tacConstructor (m : Model) : Model :=
  match focus? m with
  | none => { m with msg := "No goals." }
  | some g =>
    match g.target with
    | .and_ a b =>
      let rest := arrayEraseIdx m.goals 0
      setGoals m (arrayAppend (arrayAppend #[{ g with target := a }] #[{ g with target := b }]) rest)
        "constructor"
    | .true_ =>
      dropFocus m (arrayEraseIdx m.goals 0) "constructor (True.intro)"
    | _ => { m with msg := "constructor failed: target is not ∧ or True." }

def tacCases (m : Model) : Model :=
  match focus? m with
  | none => { m with msg := "No goals." }
  | some g =>
    if g.hyps.size == 0 then { m with msg := "cases failed: no hypotheses." }
    else
      let i := g.hyps.size - 1
      if h : i < g.hyps.size then
        match g.hyps[i] with
        | .and_ a b =>
          let hyps0 := arrayEraseIdx g.hyps i
          replaceFocus m { g with hyps := (hyps0.push a).push b }
            (arrayEraseIdx m.goals 0) "cases"
        | _ => { m with msg := "cases failed: last hyp is not a conjunction." }
      else { m with msg := "cases failed." }

def tacExact (m : Model) (i : UInt32) : Model :=
  match focus? m with
  | none => { m with msg := "No goals." }
  | some g =>
    let j := i.toNat
    if h : j < g.hyps.size then
      if g.hyps[j] == g.target then
        dropFocus m (arrayEraseIdx m.goals 0) ("exact " ++ hypName j)
      else { m with msg := "exact failed: type mismatch." }
    else { m with msg := "exact failed: no such hypothesis." }

def tacUndo (m : Model) : Model :=
  if m.history.size == 0 then { m with msg := "Nothing to undo." }
  else
    let i := m.history.size - 1
    { goals := m.history[i]!, history := arrayEraseIdx m.history i, msg := "undo" }

def tacReset (_m : Model) : Model :=
  { Model.initial with msg := "reset → P → Q → P ∧ Q" }

def update (m : Model) : Event → Model
  | .intro => tacIntro m
  | .constructor => tacConstructor m
  | .cases => tacCases m
  | .exact i => tacExact m i
  | .undo => tacUndo m
  | .reset => tacReset m

/-! ### View (all strings) -/

open scoped Jsx

def tacClass (base : String) (enabled : Bool) : String :=
  if enabled then base else base ++ " disabled"

def exactEvent (i : Nat) : UInt32 :=
  if i < 8 then UiAbi.Handler.exact i.toUInt32 else UiAbi.Handler.none

/-- Hyp rows carry `on="exact:N"` — click the row to exact that hypothesis. -/
def viewHyps (hyps : Array Formula) : Array Element :=
  arrayMapIdx hyps fun i f =>
    let k := i.toUInt32
    (<li key={k} class="hyp" on={exactEvent i}>
      {Element.label (hypName i ++ " : " ++ f.pp)}
    </li>)

def viewGoal (g : Goal) (idx : Nat) : Element :=
  let k := idx.toUInt32
  let focusCls := if idx == 0 then "goal focus" else "goal"
  (<div key={k} class={focusCls}>
    <div class="goal-meta">{Element.label (goalTitle idx)}</div>
    <div class="hyps-hdr">{Element.label "hypotheses"}</div>
    <ul class="hyps">{viewHyps g.hyps}</ul>
    <div class="turnstile">{Element.label "⊢"}</div>
    <div class="target">{Element.label g.target.pp}</div>
  </div>)

def viewGoals (gs : Array Goal) : Array Element :=
  arrayMapIdx gs fun i g => viewGoal g i

def view (m : Model) : Element :=
  let solved := m.goals.size == 0
  let body : Array Element :=
    if solved then
      #[(<div class="banner solved">{Element.label "Goals accomplished 🎉"}</div>)]
    else
      viewGoals m.goals
  let (canI, canC, canCs) :=
    match focus? m with
    | some g => (canIntro g, canConstructor g, canCases g)
    | none => (false, false, false)
  (<div class="root">
    <div class="title">{Element.label "Mini goal view"}</div>
    <div class="msg">{Element.label m.msg}</div>
    <div class="panel">{body}</div>
    <div class="tactics">
      <button class={tacClass "tac tac-intro" canI} on="intro">
        {Element.label "intro"}
      </button>
      <button class={tacClass "tac tac-ctor" canC} on="constructor">
        {Element.label "constructor"}
      </button>
      <button class={tacClass "tac tac-cases" canCs} on="cases">
        {Element.label "cases"}
      </button>
      <button class="tac tac-undo" on="undo">{Element.label "undo"}</button>
      <button class="tac tac-reset" on="reset">{Element.label "reset"}</button>
    </div>
    <div class="hint">
      {Element.label "Click a hypothesis to exact it. Try: intro → intro → constructor → click h0 → click h1"}
    </div>
  </div>)

/-! ### Reconciler -/

structure Recon where
  nextId : UInt32 := 1
  effects : Array Effect := #[]

instance : Inhabited Recon where
  default := { nextId := 1, effects := #[] }

def Recon.fresh (r : Recon) : UInt32 × Recon :=
  (r.nextId, { r with nextId := r.nextId + 1 })

def Recon.emit (r : Recon) (e : Effect) : Recon :=
  { r with effects := r.effects.push e }

partial def removeFiber (f : Fiber) (r : Recon) : Recon :=
  let rec dropKids (i : Nat) (r : Recon) : Recon :=
    if h : i < f.children.size then
      dropKids (i + 1) (removeFiber f.children[i] r)
    else r
  let r := dropKids 0 r
  r.emit { op := UiAbi.Effect.remove, id := f.id, parent := 0 }

def takeChild (old : Array Fiber) (el : Element) (_idx : Nat) : Option Fiber × Array Fiber :=
  let key? : Option UInt32 :=
    match el with
    | .node _ k _ _ _ => k
    | .label _ => none
  match key? with
  | some k =>
    match arrayFindIdx? old fun f => f.key == some k with
    | some j =>
      if h : j < old.size then (some old[j], arrayEraseIdx old j)
      else if h : old.size > 0 then (some old[0], arrayEraseIdx old 0) else (none, old)
    | none =>
      if h : old.size > 0 then (some old[0], arrayEraseIdx old 0) else (none, old)
  | none =>
    if h : old.size > 0 then (some old[0], arrayEraseIdx old 0) else (none, old)

mutual
partial def reconcile (parentId : UInt32) (index : UInt32) (old? : Option Fiber) (el : Element)
    (r : Recon) : Fiber × Recon :=
  match el with
  | .label s =>
    match old? with
    | some f =>
      if f.isLabel then
        let r :=
          if f.labelStr == s then r
          else r.emit { op := UiAbi.Effect.setText, id := f.id, parent := parentId, text := s }
        ({ f with labelStr := s, children := #[] }, r)
      else
        reconcile parentId index none el (removeFiber f r)
    | none =>
      let (id, r) := r.fresh
      let r := r.emit { op := UiAbi.Effect.createText, id, parent := parentId, index, text := s }
      ({ id, isLabel := true, labelStr := s, tag := .span, children := #[] }, r)
  | .node tag key cls onClick kids =>
    match old? with
    | some f =>
      if !f.isLabel && f.tag == tag && f.key == key then
        let r :=
          if f.cls == cls then r
          else r.emit { op := UiAbi.Effect.setClass, id := f.id, parent := parentId, text := cls }
        let r :=
          if f.onClick == onClick then r
          else r.emit {
            op := UiAbi.Effect.setHandler
            id := f.id
            parent := parentId
            payload0 := onClick
          }
        let (children, r) := reconcileChildren f.id f.children kids r
        ({ f with cls, onClick, children }, r)
      else
        reconcile parentId index none el (removeFiber f r)
    | none =>
      let (id, r) := r.fresh
      let r := r.emit {
        op := UiAbi.Effect.createElement, id, parent := parentId, index,
        payload0 := tag.toU32, payload1 := onClick, text := cls
      }
      let (children, r) := reconcileChildren id #[] kids r
      ({ id, tag, key, cls, onClick, isLabel := false, children }, r)

partial def reconcileChildren (parentId : UInt32) (oldKids : Array Fiber) (newEls : Array Element)
    (r : Recon) : Array Fiber × Recon :=
  let rec go (i : Nat) (old : Array Fiber) (r : Recon) (acc : Array Fiber) : Array Fiber × Recon :=
    if h : i < newEls.size then
      let el := newEls[i]
      let (child?, old) := takeChild old el i
      let (fib, r) := reconcile parentId i.toUInt32 child? el r
      go (i + 1) old r (acc.push fib)
    else
      let rec drop (j : Nat) (r : Recon) : Recon :=
        if h : j < old.size then drop (j + 1) (removeFiber old[j] r) else r
      (acc, drop 0 r)
  go 0 oldKids r #[]
end

partial def maxFiberId (f : Fiber) : UInt32 :=
  let rec go (i : Nat) (m : UInt32) : UInt32 :=
    if h : i < f.children.size then
      go (i + 1) (max m (maxFiberId f.children[i]))
    else m
  go 0 f.id

def renderFrame (m : Model) (old : Option Fiber) : Fiber × Array Effect :=
  let startId : UInt32 :=
    match old with
    | some f => maxFiberId f + 1
    | none => 1
  let (root, r) := reconcile 0 0 old (view m) { nextId := startId }
  (root, r.effects)

/-! ### Host programs -/

def bootM : Host UInt32 := do
  let m := Model.initial
  let (fiber, effects) := renderFrame m none
  flushEffects effects
  storeFiber (some fiber)
  storeModel (some m)
  pure m.pack

def dispatchM (handlerId : UInt32) : Host UInt32 := do
  let m0 ← loadModel
  let m := m0.getD Model.initial
  let m :=
    match Event.ofHandlerId handlerId with
    | some e => update m e
    | none => { m with msg := "unknown handler" }
  let old ← loadFiber
  let (fiber, effects) := renderFrame m old
  flushEffects effects
  storeFiber (some fiber)
  storeModel (some m)
  pure m.pack

@[export lean_ui_boot, noinline]
def boot (seed : UInt32) : UInt32 :=
  runHost seed bootM

@[export lean_ui_dispatch, noinline]
def dispatch (packedModel handlerId payloadPtr payloadLen : UInt32) : UInt32 :=
  let _ := payloadPtr
  let _ := payloadLen
  runHost packedModel (dispatchM handlerId)

@[export lean_ui_batch]
def uiBatch (seed : UInt32) : UInt32 := batchPtrRaw seed

@[export lean_ui_boot_effect_count]
def bootEffectCount (seed : UInt32) : UInt32 :=
  let p := boot seed
  let ptr := batchPtrRaw p
  (if ptr == 0 then (0 : UInt32) else 1) + (p >>> 31)

@[export lean_ui_smoke_click]
def smokeClick (seed : UInt32) : UInt32 :=
  let m := boot seed
  dispatch m UiAbi.Handler.intro 0 0

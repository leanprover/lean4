import init.lean init.lean.parser.syntax

namespace Lean
/-- An extension of the State held by an `environment` object. The new State
    holds objects of Type `entryTy`, which optionally are persisted to the
    .olean file and collected when loading imports. Objects can be retrieved
    using an appropriate `stateTy` data structure, which is computed on-demand. -/
constant EnvironmentExtension (entryTy stateTy : Type) : Type := Unit

namespace EnvironmentExtension
variable {entryTy stateTy : Type}
/-- Register a new environment extension. The Result should usually be bound to
    a top-Level definition, after which it can be used to access and modify the
    extension State. -/
@[extern "lean_environment_ext_register"] constant register
  /- A unique String used for identifying persisted data of this extension. If
     this key has already been used, the Lean process will halt with an error.
     If the key is `none`, data of this extension will not be persisted, i.e. is
     local to the current file. -/
  (key : Option String)
  /- initial cache value -/
  (emptyState : stateTy)
  /- Add an entry to the cache. `init` is `True` while building the initial
     cache from the loaded imports, in which case the input cache may assumed to
     be unshared and amenable to destructive updates. -/
  (addEntry : Π (init : Bool), environment → stateTy → entryTy → stateTy) :
  IO (EnvironmentExtension entryTy stateTy) := default _

variable {entryTy' stateTy' : Type}

/- Register a dependency between two environment extensions.
   That is, whenever an entry `e` is added to `fromExt`,
   Lean also adds an entry `convertEntry e` to `toExt`. -/
@[extern "lean_environment_ext_register_dep"] constant registerDep
   (fromExt : EnvironmentExtension entryTy stateTy)
   (toExt : EnvironmentExtension entryTy' stateTy')
   (convertEntry : entryTy → entryTy')
   : IO Unit := default _

@[extern "lean_environment_ext_add_entry"] constant addEntry (ext : EnvironmentExtension entryTy stateTy) (entry : entryTy) : environment → environment := id

--constant getModuleEntries (ext : EnvironmentExtension entryTy stateTy) (mod : ModID) : IO (Array entryTy)

/-- Retrieve the State of an environment extension. -/
@[extern "lean_environment_ext_get_state"] constant getState [Inhabited stateTy] : EnvironmentExtension entryTy stateTy → environment → stateTy := default _
end EnvironmentExtension

structure ScopedEnvironmentExtension.Scope (entryTy stateTy : Type) :=
(state : stateTy)
(localEntries : List entryTy)

def ScopedEnvironmentExtension (entryTy stateTy : Type) :=
EnvironmentExtension (Bool × entryTy) (List (ScopedEnvironmentExtension.Scope entryTy stateTy))

namespace ScopedEnvironmentExtension
structure Info :=
(pushScope popScope : environment → environment)

def scopedExtsRef.init : IO (IO.Ref (List Info)) := IO.mkRef []
@[init scopedExtsRef.init] private constant scopedExtsRef : IO.Ref (List Info) := default _
def scopedExts : IO (List Info) := scopedExtsRef.get

variable {entryTy stateTy : Type}

def register (key : Option String) (emptyState : stateTy)
  (addEntry : Π (init : Bool), environment → stateTy → entryTy → stateTy)
  : IO (ScopedEnvironmentExtension entryTy stateTy) :=
EnvironmentExtension.register key [{state := emptyState, localEntries := []}] $
  λ init env st ⟨persistent, e⟩,
    if persistent then st.map (λ scope, {scope with state := addEntry init env scope.state e})
    else match st with
    | ⟨st, es⟩::scopes := ⟨st, e::es⟩::scopes
    | [] := []

def addEntry (ext : ScopedEnvironmentExtension entryTy stateTy) (persistent : Bool) (entry : entryTy) (env : environment) : environment :=
EnvironmentExtension.addEntry ext (persistent, entry) env

def pushScope (env : environment) : IO environment := do
  exts ← scopedExts,
  pure $ exts.foldr Info.pushScope env

def popScope (env : environment) : IO environment := do
  exts ← scopedExts,
  pure $ exts.foldr Info.popScope env
end ScopedEnvironmentExtension

/-- A datum as used by `AttributeExtension`. -/
structure AttributeEntry :=
(decl : Name)
(args : Parser.Syntax)

/-- The Result of registering an attribute in the global State. -/
structure AttributeExtension (stateTy : Type) :=
-- global and local attribute entries as well as "active" scoped entries
(activeExt : ScopedEnvironmentExtension AttributeEntry stateTy)
-- all scoped entries
(scopedExt : EnvironmentExtension AttributeEntry (List AttributeEntry))

/-- `cacheTy`-oblivious attribute data available to the Elaborator. -/
structure AttributeInfo :=
(attr : Name)
(addActiveEntry (persistent : Bool) : AttributeEntry → environment → environment)
(scopedExt : EnvironmentExtension AttributeEntry (List AttributeEntry))

namespace AttributeInfo
def addScopedEntry (attr : AttributeInfo) : AttributeEntry → environment → environment := attr.scopedExt.addEntry
def activateScopedEntries (attr : AttributeInfo) (declOpen : Name → Bool) (env : environment) : environment :=
((attr.scopedExt.getState env).filter (λ e : AttributeEntry, declOpen e.decl)).foldr (attr.addActiveEntry true) env
end AttributeInfo

def attributesRef.init : IO (IO.Ref (List AttributeInfo)) := IO.mkRef []
@[init attributesRef.init] private constant attributesRef : IO.Ref (List AttributeInfo) := default _
/-- The List of all attributes registered by `attributeExt.register`. -/
def attributes : IO (List AttributeInfo) := attributesRef.get

namespace AttributeExtension
variable {stateTy : Type}

def register (attr : Name) (emptyState : stateTy)
  (addEntry : Π (init : Bool), environment → stateTy → AttributeEntry → stateTy)
  : IO (AttributeExtension stateTy) := do
  ext ← AttributeExtension.mk
    <$> ScopedEnvironmentExtension.register (toString attr) emptyState addEntry
    <*> EnvironmentExtension.register (some $ toString $ attr ++ `scoped) [] (λ _ _ entries e, e::entries),
  attributesRef.modify $ λ attrs, {attr := attr,
    addActiveEntry := ext.activeExt.addEntry,
    scopedExt := ext.scopedExt}::attrs,
  pure ext
end AttributeExtension
end Lean

import init.lean init.lean.parser.syntax

namespace Lean
/-- An extension of the State held by an `environment` object. The new State
    holds objects of Type `entryTy`, which optionally are persisted to the
    .olean file and collected when loading imports. Objects can be retrieved
    using an appropriate `stateTy` data structure, which is computed on-demand. -/
constant EnvironmentExt (entryTy stateTy : Type) : Type := Unit

namespace EnvironmentExt
variables {entryTy stateTy : Type}
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
  IO (EnvironmentExt entryTy stateTy) := default _

variables {entryTy' stateTy' : Type}

/- Register a dependency between two environment extensions.
   That is, whenever an entry `e` is added to `fromExt`,
   Lean also adds an entry `convertEntry e` to `toExt`. -/
@[extern "lean_environment_ext_register_dep"] constant registerDep
   (fromExt : EnvironmentExt entryTy stateTy)
   (toExt : EnvironmentExt entryTy' stateTy')
   (convertEntry : entryTy → entryTy')
   : IO Unit := default _

@[extern "lean_environment_ext_add_entry"] constant addEntry (ext : EnvironmentExt entryTy stateTy) (persistent : Bool) (entry : entryTy) : environment → environment := id

--constant getModuleEntries (ext : EnvironmentExt entryTy stateTy) (mod : ModID) : IO (Array entryTy)

/-- Retrieve the State of an environment extension. -/
@[extern "lean_environment_ext_get_state"] constant getState [Inhabited stateTy] : EnvironmentExt entryTy stateTy → environment → stateTy := default _
end EnvironmentExt

/-- A datum as used by `AttributeExt`. -/
structure AttributeEntry :=
(decl : Name)
(args : Parser.Syntax)

/-- The Result of registering an attribute in the global State. -/
structure AttributeExt (stateTy : Type) :=
-- global and local attribute entries as well as "active" scoped entries
(activeExt : EnvironmentExt AttributeEntry stateTy)
-- all scoped entries
(scopedExt : EnvironmentExt AttributeEntry (List AttributeEntry))

/-- `cacheTy`-oblivious attribute data available to the Elaborator. -/
structure AttributeInfo :=
(attr : Name)
(addActiveEntry (persistent : Bool) : AttributeEntry → environment → environment)
(scopedExt : EnvironmentExt AttributeEntry (List AttributeEntry))

namespace AttributeInfo
def addScopedEntry (attr : AttributeInfo) : AttributeEntry → environment → environment := attr.scopedExt.addEntry false
def activateScopedEntries (attr : AttributeInfo) (declOpen : Name → Bool) (env : environment) : environment :=
((attr.scopedExt.getState env).filter (λ e : AttributeEntry, declOpen e.decl)).foldr (attr.addActiveEntry true) env
end AttributeInfo

def attributesRef.init : IO (IO.Ref (List AttributeInfo)) := IO.mkRef []
@[init attributesRef.init] private constant attributesRef : IO.Ref (List AttributeInfo) := default _
/-- The List of all attributes registered by `attributeExt.register`. -/
def attributes : IO (List AttributeInfo) := attributesRef.get

namespace AttributeExt
variable {stateTy : Type}

def register (attr : Name) (emptyState : stateTy)
  (addEntry : Π (init : Bool), environment → stateTy → AttributeEntry → stateTy)
  : IO (AttributeExt stateTy) := do
  ext ← AttributeExt.mk
    <$> EnvironmentExt.register (toString attr) emptyState addEntry
    <*> EnvironmentExt.register (some $ toString $ attr ++ `scoped) [] (λ _ _ entries e, e::entries),
  attributesRef.modify $ λ attrs, {attr := attr,
    addActiveEntry := ext.activeExt.addEntry,
    scopedExt := ext.scopedExt}::attrs,
  pure ext
end AttributeExt
end Lean

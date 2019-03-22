import init.lean init.lean.parser.syntax

namespace Lean
/-- An extension of the State held by an `environment` object. The new State
    holds objects of Type `entryTy`, which optionally are persisted to the
    .olean file and collected when loading imports. Objects can be retrieved
    using an appropriate `stateTy` data structure, which is computed on-demand. -/
constant environmentExt (entryTy stateTy : Type) : Type := Unit

namespace environmentExt
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
  IO (environmentExt entryTy stateTy) := default _

variables {entryTy' stateTy' : Type}

/- Register a dependency between two environment extensions.
   That is, whenever an entry `e` is added to `fromExt`,
   Lean also adds an entry `convertEntry e` to `toExt`. -/
@[extern "lean_environment_ext_register_dep"] constant registerDep
   (fromExt : environmentExt entryTy stateTy)
   (toExt : environmentExt entryTy' stateTy')
   (convertEntry : entryTy → entryTy')
   : IO Unit := default _

@[extern "lean_environment_ext_add_entry"] constant addEntry (ext : environmentExt entryTy stateTy) (persistent : Bool) (entry : entryTy) : environment → environment := id

/-- Retrieve the State of an environment extension. -/
@[extern "lean_environment_ext_get_state"] constant getState [Inhabited stateTy] : environmentExt entryTy stateTy → environment → stateTy := default _
end environmentExt

/-- A datum as used by `attributeExt`. -/
structure attributeEntry :=
(Decl : Name)
(args : Parser.Syntax)

/-- The Result of registering an attribute in the global State. -/
structure attributeExt (stateTy : Type) :=
-- global and local attribute entries as well as "active" scoped entries
(activeExt : environmentExt attributeEntry stateTy)
-- all scoped entries
(scopedExt : environmentExt attributeEntry (List attributeEntry))

/-- `cacheTy`-oblivious attribute data available to the Elaborator. -/
structure attributeInfo :=
(attr : String)
(addActiveEntry (persistent : Bool) : attributeEntry → environment → environment)
(scopedExt : environmentExt attributeEntry (List attributeEntry))

namespace attributeInfo
def addScopedEntry (attr : attributeInfo) : attributeEntry → environment → environment := attr.scopedExt.addEntry false
def activateScopedEntries (attr : attributeInfo) (declOpen : Name → Bool) (env : environment) : environment :=
((attr.scopedExt.getState env).filter (λ e : attributeEntry, declOpen e.Decl)).foldr (attr.addActiveEntry true) env
end attributeInfo

def attributesRef.init : IO (IO.Ref (List attributeInfo)) := IO.mkRef []
@[init attributesRef.init] private constant attributesRef : IO.Ref (List attributeInfo) := default _
/-- The List of all attributes registered by `attributeExt.register`. -/
def attributes : IO (List attributeInfo) := attributesRef.get

namespace attributeExt
variable {stateTy : Type}

def register (attr : String) (emptyState : stateTy)
  (addEntry : Π (init : Bool), environment → stateTy → attributeEntry → stateTy)
  : IO (attributeExt stateTy) := do
  ext ← attributeExt.mk
    <$> environmentExt.register attr emptyState addEntry
    <*> environmentExt.register (some $ attr ++ ".scoped") [] (λ _ _ entries e, e::entries),
  attributesRef.modify $ λ attrs, {attr := attr,
    addActiveEntry := ext.activeExt.addEntry,
    scopedExt := ext.scopedExt}::attrs,
  pure ext
end attributeExt
end Lean

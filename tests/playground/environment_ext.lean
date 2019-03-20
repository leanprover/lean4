import init.lean init.lean.parser.syntax

namespace lean
/-- An extension of the state held by an `environment` object. The new state
    holds objects of type `entry_ty`, which optionally are persisted to the
    .olean file and collected when loading imports. Objects can be retrieved
    using an appropriate `state_ty` data structure, which is computed on-demand. -/
constant environment_ext (entry_ty state_ty : Type) : Type := unit

namespace environment_ext
variables {entry_ty state_ty : Type}
/-- Register a new environment extension. The result should usually be bound to
    a top-level definition, after which it can be used to access and modify the
    extension state. -/
@[extern "lean_environment_ext_register"] constant register
  /- A unique string used for identifying persisted data of this extension. If
     this key has already been used, the Lean process will halt with an error.
     If the key is `none`, data of this extension will not be persisted, i.e. is
     local to the current file. -/
  (key : option string)
  /- initial cache value -/
  (empty_state : state_ty)
  /- Add an entry to the cache. `init` is `true` while building the initial
     cache from the loaded imports, in which case the input cache may assumed to
     be unshared and amenable to destructive updates. -/
  (add_entry : Π (init : bool), environment → state_ty → entry_ty → state_ty) :
  io (environment_ext entry_ty state_ty) := default _

variables {entry_ty' state_ty' : Type}

/- Register a dependency between two environment extensions.
   That is, whenever an entry `e` is added to `from_ext`,
   Lean also adds an entry `convert_entry e` to `to_ext`. -/
@[extern "lean_environment_ext_register_dep"] constant register_dep
   (from_ext : environment_ext entry_ty state_ty)
   (to_ext : environment_ext entry_ty' state_ty')
   (convert_entry : entry_ty → entry_ty')
   : io unit := default _

@[extern "lean_environment_ext_add_entry"] constant add_entry (ext : environment_ext entry_ty state_ty) (persistent : bool) (entry : entry_ty) : environment → environment := id

/-- Retrieve the state of an environment extension. -/
@[extern "lean_environment_ext_get_state"] constant get_state [inhabited state_ty] : environment_ext entry_ty state_ty → environment → state_ty := default _
end environment_ext

/-- A datum as used by `attribute_ext`. -/
structure attribute_entry :=
(decl : name)
(args : parser.syntax)

/-- The result of registering an attribute in the global state. -/
structure attribute_ext (state_ty : Type) :=
-- global and local attribute entries as well as "active" scoped entries
(active_ext : environment_ext attribute_entry state_ty)
-- all scoped entries
(scoped_ext : environment_ext attribute_entry (list attribute_entry))

/-- `cache_ty`-oblivious attribute data available to the elaborator. -/
structure attribute_info :=
(attr : string)
(add_active_entry (persistent : bool) : attribute_entry → environment → environment)
(scoped_ext : environment_ext attribute_entry (list attribute_entry))

namespace attribute_info
def add_scoped_entry (attr : attribute_info) : attribute_entry → environment → environment := attr.scoped_ext.add_entry ff
def activate_scoped_entries (attr : attribute_info) (decl_open : name → bool) (env : environment) : environment :=
((attr.scoped_ext.get_state env).filter (λ e : attribute_entry, decl_open e.decl)).foldr (attr.add_active_entry tt) env
end attribute_info

def attributes_ref.init : io (io.ref (list attribute_info)) := io.mk_ref []
@[init attributes_ref.init] private constant attributes_ref : io.ref (list attribute_info) := default _
/-- The list of all attributes registered by `attribute_ext.register`. -/
def attributes : io (list attribute_info) := attributes_ref.read

namespace attribute_ext
variable {state_ty : Type}

def register (attr : string) (empty_state : state_ty)
  (add_entry : Π (init : bool), environment → state_ty → attribute_entry → state_ty)
  : io (attribute_ext state_ty) := do
  ext ← attribute_ext.mk
    <$> environment_ext.register attr empty_state add_entry
    <*> environment_ext.register (some $ attr ++ ".scoped") [] (λ _ _ entries e, e::entries),
  attributes_ref.modify $ λ attrs, {attr := attr,
    add_active_entry := ext.active_ext.add_entry,
    scoped_ext := ext.scoped_ext}::attrs,
  pure ext
end attribute_ext
end lean

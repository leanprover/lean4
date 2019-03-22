import init.Lean init.Lean.Parser.Syntax

namespace Lean
constant environmentExt (α σ : Type) : Type := Unit
namespace environmentExt
variables {α σ : Type}
@[extern "lean_environment_ext_register"] constant register
  (key : Option String)
  (emptyState : σ)
  (addEntry : Π (init : Bool), environment → σ → α → σ) :
  IO (environmentExt α σ) := default _

variables {β δ : Type}
@[extern "lean_environment_ext_register_dep"] constant registerDep
   (fromExt : environmentExt α σ)
   (toExt : environmentExt β δ)
   (convertEntry : α → β)
   : IO Unit := default _

@[extern "lean_environment_ext_add_entry"] constant addEntry (ext : environmentExt α σ) (persistent : Bool) (entry : α) : environment → environment := id

@[extern "lean_environment_ext_get_state"] constant getState [Inhabited σ] : environmentExt α σ → environment → σ := default _
end environmentExt
structure attributeEntry :=
(Decl : Name)
(args : Parser.Syntax)

structure attributeExt (σ : Type) :=
(activeExt : environmentExt attributeEntry σ)
(scopedExt : environmentExt attributeEntry (List attributeEntry))

structure attributeInfo :=
(attr : String)
(addActiveEntry (persistent : Bool) : attributeEntry → environment → environment)
(scopedExt : environmentExt attributeEntry (List attributeEntry))

namespace attributeInfo
def addScopedEntry (attr : attributeInfo) : attributeEntry → environment → environment := attr.scopedExt.addEntry ff
def activateScopedEntries (attr : attributeInfo) (declOpen : Name → Bool) (env : environment) : environment :=
((attr.scopedExt.getState env).filter (λ e : attributeEntry, declOpen e.Decl)).foldr (attr.addActiveEntry tt) env
end attributeInfo

def attributesRef.init : IO (IO.ref (List attributeInfo)) := IO.mkRef []
@[init attributesRef.init] private constant attributesRef : IO.ref (List attributeInfo) := default _
/-- The List of all attributes registered by `attributeExt.register`. -/
def attributes : IO (List attributeInfo) := attributesRef.read

namespace attributeExt
variable {σ : Type}

def register (attr : String) (emptyState : σ)
  (addEntry : Π (init : Bool), environment → σ → attributeEntry → σ)
  : IO (attributeExt σ) := do
  ext ← attributeExt.mk
    <$> environmentExt.register attr emptyState addEntry
    <*> environmentExt.register (some $ attr ++ ".scoped") [] (λ _ _ entries e, e::entries),
  attributesRef.modify $ λ attrs, {attr := attr,
    addActiveEntry := ext.activeExt.addEntry,
    scopedExt := ext.scopedExt}::attrs,
  pure ext
end attributeExt
end Lean

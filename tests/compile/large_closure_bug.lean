import Lean
import Std

abbrev IteratedProd (ts : List Type) : Type :=
  ts.foldr Prod Unit

abbrev IteratedArrow (codomain : Type) (ts : List Type) : Type :=
  ts.foldr (· → ·) codomain

section IteratedProdInstances

macro "infer_instance_for_iterated_prod" : tactic =>
  `(tactic| repeat' (first | infer_instance | constructor ))

end IteratedProdInstances

section SingleField

variable (fieldDomain : List Type) (FieldCodomain : Type)

local macro "⌞" t1:ident t2:ident* "⌟" : term => `($t1 $(Lean.mkIdent `fieldDomain) $t2:ident*)
local macro "⌞_" t1:ident t2:ident* "⌟" : term => `(⌞ $t1 $(Lean.mkIdent `FieldCodomain) $t2:ident* ⌟)

abbrev FieldUpdatePat : Type := IteratedProd (fieldDomain.map Option)

abbrev CanonicalField : Type := IteratedArrow FieldCodomain fieldDomain

abbrev FieldUpdateDescr := List (⌞ FieldUpdatePat ⌟ × ⌞_ CanonicalField ⌟)

class FieldRepresentation (FieldTypeConcrete : Type) where
  set : ⌞_ FieldUpdateDescr ⌟ → FieldTypeConcrete → FieldTypeConcrete

instance canonicalFieldRepresentation {fieldDomain : List Type} {FieldCodomain : Type} :
  (⌞_ FieldRepresentation ⌟) (⌞_ CanonicalField ⌟) where
  set favs fc := favs.foldr (init := fc) fun (_, v) _ => v

end SingleField

inductive NonDetT (m : Type u -> Type v) : (α : Type u) -> Type _ where
  | pure {α} (ret : α) : NonDetT m α
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) : NonDetT m α

def NonDetT.bind (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f

instance : Monad (NonDetT m) where
  pure := NonDetT.pure
  bind := NonDetT.bind

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

abbrev VeilM (σ α : Type) := NonDetT ((StateT σ (ExceptT Int Option))) α

inductive ExtractNonDet {m} : {α : Type u} -> NonDetT m α -> Type _ where
  | pure {α} : ∀ (x : α), ExtractNonDet (NonDetT.pure x)
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) :
      (∀ y, ExtractNonDet (f y)) → ExtractNonDet (.vis x f)

set_option linter.unusedVariables false in
def ExtractNonDet.bind :
  (_ : ExtractNonDet x) -> (_ : ∀ y, ExtractNonDet (f y)) -> ExtractNonDet (x >>= f)
  | .pure x, inst => by
    dsimp [Bind.bind, NonDetT.bind]; exact (inst x)
  | .vis x f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor
    intro y; apply ExtractNonDet.bind <;> solve_by_elim

instance ExtractNonDet.pure' : ExtractNonDet (Pure.pure (f := NonDetT m) x) := by
  dsimp [Pure.pure, NonDetT.pure]; constructor

instance ExtractNonDet.liftM (x : m α) :
  ExtractNonDet (liftM (n := NonDetT m) x) := by
    dsimp [_root_.liftM, monadLift, MonadLift.monadLift]; constructor
    intro y; apply ExtractNonDet.pure'

macro "extract_step" : tactic =>
  `(tactic|
    first
      | apply ExtractNonDet.bind
      | apply ExtractNonDet.pure'
      | apply ExtractNonDet.liftM
      | split )

macro "extract_tactic" : tactic =>
  `(tactic| repeat' (intros; extract_step <;> try dsimp))

abbrev VeilExecM (ε σ α : Type) := σ → Option (Except ε (α × σ))

def NonDetT.extract {α : Type} : (s : VeilM σ α) → (ex : ExtractNonDet s) → VeilExecM Int σ α
  | .pure x, _ => fun s => (Option.some (Except.ok (x, s)))
  | .vis x f, .vis _ _ _ =>
    fun s =>
      match x s with
      | Option.some (Except.ok (y, s')) =>
        extract (f y) (by rename_i a ; exact a y) s'
      | Option.none => (Option.none)
      | Option.some (Except.error e) => (Option.some (Except.error e))

inductive State.Label : Type where
      | m_client_request
      | m_marked_client_request

def State.Label.toDomain (l : State.Label) : List Type :=
      State.Label.casesOn l [Bool] [Bool, Bool, Bool]

structure State (χ : State.Label → Type) where mk ::
      m_client_request : χ State.Label.m_client_request
      m_marked_client_request : χ State.Label.m_marked_client_request

def initializer.ext {χ : State.Label → Type}
        [χ_rep : (f : State.Label) →
            FieldRepresentation (State.Label.toDomain f) Bool (χ f)] : VeilM (State χ) Unit :=
do
        let mut __veil_state := (← MonadState.get)
        let mut m_client_request_conc := __veil_state.m_client_request
        let mut m_marked_client_request_conc := __veil_state.m_marked_client_request

        let __veil_bind_m_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_client_request)) (Option.none, ())),
              (fun _ => (false)))] m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request, { st with m_client_request := __veil_bind_m_client_request })))
        let __veil_bind_m_marked_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_marked_client_request)) (Option.none, Option.none, Option.none, ())),
              (fun _ _ _ => (false)))] m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request })))

        -- NOTE: the following are just multiple copy & pastes of the do-elements above
        let __veil_bind_m_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_client_request)) (Option.none, ())),
              (fun _ => (false)))] m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request, { st with m_client_request := __veil_bind_m_client_request })))
        let __veil_bind_m_marked_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_marked_client_request)) (Option.none, Option.none, Option.none, ())),
              (fun _ _ _ => (false)))] m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request })))

        let __veil_bind_m_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_client_request)) (Option.none, ())),
              (fun _ => (false)))] m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request, { st with m_client_request := __veil_bind_m_client_request })))
        let __veil_bind_m_marked_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_marked_client_request)) (Option.none, Option.none, Option.none, ())),
              (fun _ _ _ => (false)))] m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request })))

        let __veil_bind_m_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_client_request)) (Option.none, ())),
              (fun _ => (false)))] m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request, { st with m_client_request := __veil_bind_m_client_request })))
        let __veil_bind_m_marked_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_marked_client_request)) (Option.none, Option.none, Option.none, ())),
              (fun _ _ _ => (false)))] m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request })))

        let __veil_bind_m_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_client_request)) (Option.none, ())),
              (fun _ => (false)))] m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request, { st with m_client_request := __veil_bind_m_client_request })))
        let __veil_bind_m_marked_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_marked_client_request)) (Option.none, Option.none, Option.none, ())),
              (fun _ _ _ => (false)))] m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request })))

        let __veil_bind_m_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_client_request)) (Option.none, ())),
              (fun _ => (false)))] m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request, { st with m_client_request := __veil_bind_m_client_request })))
        let __veil_bind_m_marked_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_marked_client_request)) (Option.none, Option.none, Option.none, ())),
              (fun _ _ _ => (false)))] m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request })))

        let __veil_bind_m_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_client_request)) (Option.none, ())),
              (fun _ => (false)))] m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request, { st with m_client_request := __veil_bind_m_client_request })))
        let __veil_bind_m_marked_client_request :=
          (χ_rep _).set
            [((@id (FieldUpdatePat (State.Label.toDomain State.Label.m_marked_client_request)) (Option.none, Option.none, Option.none, ())),
              (fun _ _ _ => (false)))] m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request })))

def initExec (χ : State.Label → Type) [χ_rep : ∀ f, FieldRepresentation (State.Label.toDomain f) Bool (χ f)]
  : VeilExecM Int (State χ) Unit :=
      NonDetT.extract (@initializer.ext χ χ_rep) (by (extract_tactic))

def res := initExec (fun f => CanonicalField ( (State.Label.toDomain) f) Bool) {
      m_client_request := fun _ => false,
      m_marked_client_request := fun _ _ _ => false
    }

def main : IO Unit :=
  IO.println s!"{[res].length}"

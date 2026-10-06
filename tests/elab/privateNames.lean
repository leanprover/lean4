module

public import Lean.PrivateName
import all Init.Meta.Defs
import all Lean.PrivateName

public section

namespace Lean

attribute [simp] Name.appendCore Name.hasNum

theorem Name.appendCore_eq_anonymous_iff {n n' : Name} :
    n.appendCore n' = anonymous ↔ n = anonymous ∧ n' = anonymous := by
  fun_induction appendCore with simp_all

theorem Name.appendCore_eq_right_iff {n n' : Name} :
    n.appendCore n' = n' ↔ n = anonymous := by
  fun_induction appendCore with simp_all

theorem isSome_privatePrefix? (n : Name) :
    (privatePrefix? n).isSome = isPrivateName n := by
  fun_induction privatePrefix? with simp_all [isPrivateName, isPrivatePrefix]

theorem isPrivatePrefix_of_privatePrefix?_eq_some {n : Name}
    (h : privatePrefix? n = some n') : isPrivatePrefix n' := by
  fun_induction privatePrefix? with simp_all

/-- Alternate specification of `privatePrefix?` -/
theorem appendCore_privatePrefix?_privateToUserName {n : Name} (h : isPrivateName n) :
    ((privatePrefix? n).get (by rwa [isSome_privatePrefix?])).appendCore (privateToUserName n) = n := by
  rw [privateToUserName, dite_eq_left h]
  fun_induction privateToUserNameAux with simp_all [privatePrefix?]

theorem isPrivateName_iff_privateToUserName_ne_self {n : Name} :
    isPrivateName n ↔ privateToUserName n ≠ n := by
  constructor
  · intro h h'
    have := appendCore_privatePrefix?_privateToUserName h
    rw [h', Name.appendCore_eq_right_iff] at this
    replace := isPrivatePrefix_of_privatePrefix?_eq_some (this ▸ Option.some_get _).symm
    simp [isPrivatePrefix] at this
  · intro h
    rw [privateToUserName] at h
    split at h <;> simp_all

theorem isPrivateName_appendCore_right {n n' : Name} (h : isPrivateName n) :
    isPrivateName (n.appendCore n') := by
  induction n' with simp_all [isPrivateName]

@[simp]
theorem Name.hasNum_appendCore (n n' : Name) :
    Name.hasNum (n.appendCore n') = (n.hasNum || n'.hasNum) := by
  induction n' with simp_all

@[simp ←]
theorem Name.appendCore_assoc (n n' n'' : Name) :
    (n.appendCore n').appendCore n'' = n.appendCore (n'.appendCore n'') := by
  induction n'' with simp_all

@[simp]
theorem Name.appendCore_right_cancel {n n' n'' : Name} :
    n.appendCore n'' = n'.appendCore n'' ↔ n = n' := by
  induction n'' with simp_all

@[simp]
theorem Name.anonymous_appendCore {n : Name} :
    anonymous.appendCore n = n := by
  induction n <;> simp_all

theorem Name.sizeOf_appendCore_add_one {n n' : Name} :
    (n.appendCore n').sizeOf + 1 = n.sizeOf + n'.sizeOf := by
  induction n' <;> simp_all +arith [Name.sizeOf]

@[simp]
theorem Name.sizeOf_appendCore {n n' : Name} :
    (n.appendCore n').sizeOf = n.sizeOf + n'.sizeOf - 1 := by
  simp [← Name.sizeOf_appendCore_add_one]

@[grind! .]
theorem Name.sizeOf_pos {n : Name} : 0 < n.sizeOf := by
  fun_cases Name.sizeOf <;> simp +arith

@[simp]
theorem Name.appendCore_left_cancel {n n' n'' : Name} :
    n.appendCore n' = n.appendCore n'' ↔ n' = n'' := by
  induction n' generalizing n'' <;> cases n'' <;> simp_all <;>
    apply ne_of_apply_ne Name.sizeOf <;> simp +arith [Name.sizeOf] <;> grind

private theorem isPrivatePrefix_go_implies_exists {n : Name} :
    isPrivatePrefix.go n → ∃ modNm, modNm.hasNum = false ∧ n = privateHeader.appendCore modNm := by
  induction n with
  | anonymous => simp [isPrivatePrefix.go, privateHeader]
  | str pre s ih =>
    simp only [isPrivatePrefix.go, Bool.or_eq_true, beq_iff_eq]
    rintro (h | h)
    · exists .anonymous
    · obtain ⟨modNm, h₁, h₂⟩ := ih h
      exists modNm.str s
      simp [*]
  | num => simp [isPrivatePrefix.go, privateHeader]

theorem isPrivatePrefix_appendCore_right {n n' : Name} (h : isPrivatePrefix n) :
    isPrivatePrefix (n.appendCore n') ↔ n' = .anonymous := by
  constructor
  · intro h'
    cases n' with
    | anonymous => simp
    | str => simp_all [isPrivatePrefix]
    | num pre i =>
      cases i with
      | succ => simp_all [isPrivatePrefix]
      | zero =>
        simp only [isPrivatePrefix, Name.appendCore] at h'
        obtain ⟨modNm, hmodNm, hn⟩ := isPrivatePrefix_go_implies_exists h'
        have : (privateHeader.appendCore modNm).hasNum = false := by simp_all [privateHeader]
        simp only [← hn, Name.hasNum_appendCore, Bool.or_eq_false_iff] at this
        cases n <;> simp_all [isPrivatePrefix]
  · simp_all

private theorem isPrivatePrefix_appendCore {modNm : Name} (h : modNm.hasNum = false) :
    isPrivatePrefix (privateHeader.appendCore modNm |>.num 0) := by
  rw [isPrivatePrefix]
  induction modNm with simp_all [isPrivatePrefix.go, privateHeader]

/-- Specification of `isPrivatePrefix` -/
theorem isPrivatePrefix_iff_exists_mkPrivateNameCore {n : Name} :
    isPrivatePrefix n ↔ ∃ modNm, modNm.hasNum = false ∧ n = mkPrivateNameCore modNm .anonymous := by
  cases n with
  | anonymous | str => simp [mkPrivateNameCore, isPrivatePrefix]
  | num pre i =>
    cases i with
    | zero => ?_
    | succ k => simp [mkPrivateNameCore, isPrivatePrefix]
    simp only [isPrivatePrefix, mkPrivateNameCore, Name.appendCore, Name.num.injEq, and_true]
    constructor
    · exact isPrivatePrefix_go_implies_exists
    · rintro ⟨modNm, h, rfl⟩
      exact isPrivatePrefix_appendCore h

theorem isPrivateName_mkPrivateNameCore {modNm n : Name} (h : modNm.hasNum = false) :
    isPrivateName (mkPrivateNameCore modNm n) := by
  rw [mkPrivateNameCore]
  apply isPrivateName_appendCore_right
  rw [isPrivateName, Bool.or_eq_true]
  left
  exact isPrivatePrefix_appendCore h

/-- Alternate specification of `isPrivateName` -/
theorem isPrivateName_iff_exists_isPrivatePrefix {n : Name} :
    isPrivateName n ↔ ∃ pfx nm, isPrivatePrefix pfx ∧ n = pfx.appendCore nm := by
  constructor
  · intro h
    rw [← appendCore_privatePrefix?_privateToUserName h]
    refine ⟨_, _, ?_, rfl⟩
    apply isPrivatePrefix_of_privatePrefix?_eq_some
    rw [eq_comm, Option.some_get]
  · rintro ⟨pfx, nm, h, rfl⟩
    apply isPrivateName_appendCore_right
    revert h
    fun_cases isPrivatePrefix <;> simp +contextual [isPrivateName, isPrivatePrefix]

/-- Primary specification of `isPrivateName` -/
theorem isPrivateName_iff_exists_mkPrivateNameCore {n : Name} :
    isPrivateName n ↔ ∃ modNm nm, modNm.hasNum = false ∧ n = mkPrivateNameCore modNm nm := by
  constructor
  · rw [isPrivateName_iff_exists_isPrivatePrefix]
    unfold mkPrivateNameCore
    rintro ⟨pfx, nm, h, rfl⟩; revert h
    fun_cases isPrivatePrefix
    · intro h
      obtain ⟨modNm, hmod, rfl⟩ := isPrivatePrefix_go_implies_exists h
      exists modNm, nm
    · simp
  · rintro ⟨modNm, nm, h, rfl⟩
    exact isPrivateName_mkPrivateNameCore h

/-- Specification of `privatePrefix?`, part 1 -/
theorem privatePrefix?_mkPrivateNameCore {modNm nm : Name} (h : modNm.hasNum = false) :
    privatePrefix? (mkPrivateNameCore modNm nm) = mkPrivateNameCore modNm .anonymous := by
  simp only [mkPrivateNameCore, Name.appendCore]
  induction nm with
  | anonymous => simp [privatePrefix?, isPrivatePrefix_appendCore h]
  | str => simp [privatePrefix?, *]
  | num pre i ih =>
    simp only [Name.appendCore, privatePrefix?]
    rw [ite_eq_right, ih]
    intro h'
    replace h' : isPrivatePrefix ((privateHeader.appendCore modNm).num 0 |>.appendCore (pre.num i)) := h'
    have := isPrivatePrefix_of_privatePrefix?_eq_some ih
    have := isPrivatePrefix_appendCore_right this |>.mp h'
    contradiction

/-- Specification of `privatePrefix?`, part 2 -/
theorem privatePrefix?_eq_none {n : Name} (h : isPrivateName n = false) :
    privatePrefix? n = none := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, isSome_privatePrefix?, h]

/-- Specification of `privateToUserName`, part 1 -/
theorem privateToUserName_mkPrivateNameCore {modNm nm : Name} (h : modNm.hasNum = false) :
    privateToUserName (mkPrivateNameCore modNm nm) = nm := by
  have := appendCore_privatePrefix?_privateToUserName (isPrivateName_mkPrivateNameCore (n := nm) h)
  simp only [privatePrefix?_mkPrivateNameCore h, Option.get_some] at this
  simpa [mkPrivateNameCore] using this

/-- Specification of `privateToUserName`, part 2 -/
theorem privateToUserName_eq_self {n : Name} (h : isPrivateName n = false) :
    privateToUserName n = n := by
  simp [privateToUserName, h]

/-- Specification of `privateToUserName?`, part 1 -/
theorem privateToUserName?_mkPrivateNameCore {modNm nm : Name} (h : modNm.hasNum = false) :
    privateToUserName? (mkPrivateNameCore modNm nm) = nm := by
  simpa [privateToUserName?, privateToUserName, isPrivateName_mkPrivateNameCore h]
    using privateToUserName_mkPrivateNameCore h

/-- Specification of `privateToUserName?`, part 2 -/
theorem privateToUserName_eq_none {n : Name} (h : isPrivateName n = false) :
    privateToUserName? n = none := by
  simp [privateToUserName?, h]

// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: Init.Omega.LinearCombo Init.Omega.Int Init.Omega.Logic Init.Data.BitVec.Basic Lean.Meta.AppBuilder Lean.Meta.Canonicalizer Std.Data.HashMap.Basic Std.Data.HashSet.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51;
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__3;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static uint8_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
static lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__2;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31;
static double l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16;
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81;
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34;
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_int_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__8(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2;
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78;
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__4;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_st_mk_ref(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_st_mk_ref(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_box(x_5);
lean_inc(x_13);
lean_inc(x_16);
x_19 = lean_apply_10(x_3, x_16, x_13, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_st_ref_get(x_13, x_23);
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_dec(x_16);
lean_dec(x_13);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_2);
x_10 = 3;
x_11 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__5;
x_12 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(x_9, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_cfg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_25; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_34);
lean_dec(x_4);
x_35 = lean_mk_empty_array_with_capacity(x_33);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_34);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_34);
x_25 = x_35;
goto block_32;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_37, x_37);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_34);
x_25 = x_35;
goto block_32;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(x_34, x_40, x_41, x_35);
lean_dec_ref(x_34);
x_25 = x_42;
goto block_32;
}
}
block_12:
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(x_8, x_9, x_7);
if (lean_is_scalar(x_6)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_6;
}
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
block_18:
{
lean_object* x_17; 
lean_dec(x_15);
x_17 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_13, x_14, x_16);
lean_dec(x_16);
x_7 = x_17;
goto block_12;
}
block_24:
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_22, x_19);
if (x_23 == 0)
{
lean_dec(x_19);
lean_inc(x_22);
x_13 = x_20;
x_14 = x_22;
x_15 = x_21;
x_16 = x_22;
goto block_18;
}
else
{
x_13 = x_20;
x_14 = x_22;
x_15 = x_21;
x_16 = x_19;
goto block_18;
}
}
block_32:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
x_31 = lean_nat_dec_le(x_27, x_30);
if (x_31 == 0)
{
lean_inc(x_30);
x_19 = x_30;
x_20 = x_25;
x_21 = x_26;
x_22 = x_30;
goto block_24;
}
else
{
x_19 = x_30;
x_20 = x_25;
x_21 = x_26;
x_22 = x_27;
goto block_24;
}
}
else
{
lean_dec(x_26);
x_7 = x_25;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Omega_atoms___redArg(x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_atoms___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atoms(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Elab_Tactic_Omega_atoms___redArg(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_11 = lean_array_to_list(x_8);
x_12 = l_Lean_Meta_mkListLit(x_10, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Omega_atomsList___redArg(x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Omega_atomsList___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atomsList(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Omega", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Coeffs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofList", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Omega_atomsList___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5;
x_11 = l_Lean_Expr_app___override(x_10, x_9);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5;
x_15 = l_Lean_Expr_app___override(x_14, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atomsCoeffs(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_box(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_apply_10(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec_ref(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_st_ref_take(x_3, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_st_ref_set(x_3, x_13, x_26);
lean_dec(x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_st_ref_take(x_2, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_st_ref_set(x_2, x_16, x_30);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_19, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_38);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_38);
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Elab_Tactic_Omega_commitWhen(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(x_5);
x_13 = lean_apply_10(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Elab_Tactic_Omega_withoutModifyingState(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc_ref(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec_ref(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_7);
lean_dec(x_6);
x_11 = l_Lean_Expr_nat_x3f(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec_ref(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l_Lean_Expr_nat_x3f(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_6);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_6);
x_18 = l_Lean_Expr_nat_x3f(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_array_fget(x_6, x_19);
lean_dec(x_6);
x_21 = l_Lean_Expr_nat_x3f(x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_22 = l_Lean_Expr_nat_x3f(x_1);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_23 = l_Lean_Expr_nat_x3f(x_1);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_24 = l_Lean_Expr_nat_x3f(x_1);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc_ref(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec_ref(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_7);
lean_dec(x_6);
x_11 = l_Lean_Expr_int_x3f(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec_ref(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l_Lean_Expr_int_x3f(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_6);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_6);
x_18 = l_Lean_Expr_int_x3f(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_array_fget(x_6, x_19);
lean_dec(x_6);
x_21 = l_Lean_Expr_nat_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_nat_to_int(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_nat_to_int(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
}
else
{
lean_object* x_29; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_29 = l_Lean_Expr_int_x3f(x_1);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_30 = l_Lean_Expr_int_x3f(x_1);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = l_Lean_Expr_int_x3f(x_1);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_2(x_1, x_5, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_2(x_1, x_5, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc_ref(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
x_14 = lean_string_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_16 = lean_string_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_18 = lean_string_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_20 = lean_string_dec_eq(x_8, x_19);
lean_dec_ref(x_8);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec_ref(x_7);
lean_dec(x_6);
x_21 = l_Lean_Expr_nat_x3f(x_1);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_23 = lean_string_dec_eq(x_7, x_22);
lean_dec_ref(x_7);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_6);
x_24 = l_Lean_Expr_nat_x3f(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_array_get_size(x_6);
x_26 = lean_unsigned_to_nat(6u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_6);
x_28 = l_Lean_Expr_nat_x3f(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0___boxed), 2, 0);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_array_fget(x_6, x_30);
x_32 = lean_unsigned_to_nat(5u);
x_33 = lean_array_fget(x_6, x_32);
lean_dec(x_6);
x_34 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_29, x_31, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; uint8_t x_36; 
lean_dec_ref(x_8);
x_35 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_36 = lean_string_dec_eq(x_7, x_35);
lean_dec_ref(x_7);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_6);
x_37 = l_Lean_Expr_nat_x3f(x_1);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_array_get_size(x_6);
x_39 = lean_unsigned_to_nat(6u);
x_40 = lean_nat_dec_eq(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_6);
x_41 = l_Lean_Expr_nat_x3f(x_1);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1___boxed), 2, 0);
x_43 = lean_unsigned_to_nat(4u);
x_44 = lean_array_fget(x_6, x_43);
x_45 = lean_unsigned_to_nat(5u);
x_46 = lean_array_fget(x_6, x_45);
lean_dec(x_6);
x_47 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_42, x_44, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_8);
x_48 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_49 = lean_string_dec_eq(x_7, x_48);
lean_dec_ref(x_7);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_6);
x_50 = l_Lean_Expr_nat_x3f(x_1);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_array_get_size(x_6);
x_52 = lean_unsigned_to_nat(6u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_6);
x_54 = l_Lean_Expr_nat_x3f(x_1);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_1);
x_55 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed), 2, 0);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_array_fget(x_6, x_56);
x_58 = lean_unsigned_to_nat(5u);
x_59 = lean_array_fget(x_6, x_58);
lean_dec(x_6);
x_60 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_55, x_57, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec_ref(x_8);
x_61 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_62 = lean_string_dec_eq(x_7, x_61);
lean_dec_ref(x_7);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_6);
x_63 = l_Lean_Expr_nat_x3f(x_1);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_array_get_size(x_6);
x_65 = lean_unsigned_to_nat(6u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_6);
x_67 = l_Lean_Expr_nat_x3f(x_1);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_1);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed), 2, 0);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_array_fget(x_6, x_69);
x_71 = lean_unsigned_to_nat(5u);
x_72 = lean_array_fget(x_6, x_71);
lean_dec(x_6);
x_73 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_68, x_70, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec_ref(x_8);
x_74 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
x_75 = lean_string_dec_eq(x_7, x_74);
lean_dec_ref(x_7);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_6);
x_76 = l_Lean_Expr_nat_x3f(x_1);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_array_get_size(x_6);
x_78 = lean_unsigned_to_nat(6u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_6);
x_80 = l_Lean_Expr_nat_x3f(x_1);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_1);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4___boxed), 2, 0);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_array_fget(x_6, x_82);
x_84 = lean_unsigned_to_nat(5u);
x_85 = lean_array_fget(x_6, x_84);
lean_dec(x_6);
x_86 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_81, x_83, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec_ref(x_8);
x_87 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_88 = lean_string_dec_eq(x_7, x_87);
lean_dec_ref(x_7);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_6);
x_89 = l_Lean_Expr_nat_x3f(x_1);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_array_get_size(x_6);
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_nat_dec_eq(x_90, x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_6);
x_93 = l_Lean_Expr_nat_x3f(x_1);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_1);
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_array_fget(x_6, x_94);
lean_dec(x_6);
x_1 = x_95;
goto _start;
}
}
}
}
else
{
lean_object* x_97; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_97 = l_Lean_Expr_nat_x3f(x_1);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_98 = l_Lean_Expr_nat_x3f(x_1);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_99 = l_Lean_Expr_nat_x3f(x_1);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_2(x_1, x_5, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_2(x_1, x_5, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_ediv(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc_ref(x_1);
x_2 = l_Lean_Expr_getAppFnArgs(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
x_14 = lean_string_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_16 = lean_string_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_18 = lean_string_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_20 = lean_string_dec_eq(x_8, x_19);
lean_dec_ref(x_8);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec_ref(x_7);
lean_dec(x_6);
x_21 = l_Lean_Expr_int_x3f(x_1);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_23 = lean_string_dec_eq(x_7, x_22);
lean_dec_ref(x_7);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_6);
x_24 = l_Lean_Expr_int_x3f(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_array_get_size(x_6);
x_26 = lean_unsigned_to_nat(6u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_6);
x_28 = l_Lean_Expr_int_x3f(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_1);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_array_fget(x_6, x_29);
x_31 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_unsigned_to_nat(5u);
x_34 = lean_array_fget(x_6, x_33);
lean_dec(x_6);
x_35 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_32);
x_36 = lean_box(0);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = l_Int_pow(x_32, x_38);
lean_dec(x_38);
lean_dec(x_32);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Int_pow(x_32, x_40);
lean_dec(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
}
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec_ref(x_8);
x_43 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_44 = lean_string_dec_eq(x_7, x_43);
lean_dec_ref(x_7);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_6);
x_45 = l_Lean_Expr_int_x3f(x_1);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_array_get_size(x_6);
x_47 = lean_unsigned_to_nat(6u);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_6);
x_49 = l_Lean_Expr_int_x3f(x_1);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_1);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed), 2, 0);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_array_fget(x_6, x_51);
x_53 = lean_unsigned_to_nat(5u);
x_54 = lean_array_fget(x_6, x_53);
lean_dec(x_6);
x_55 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_50, x_52, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec_ref(x_8);
x_56 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_57 = lean_string_dec_eq(x_7, x_56);
lean_dec_ref(x_7);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_6);
x_58 = l_Lean_Expr_int_x3f(x_1);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_array_get_size(x_6);
x_60 = lean_unsigned_to_nat(6u);
x_61 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_6);
x_62 = l_Lean_Expr_int_x3f(x_1);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_1);
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed), 2, 0);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_array_fget(x_6, x_64);
x_66 = lean_unsigned_to_nat(5u);
x_67 = lean_array_fget(x_6, x_66);
lean_dec(x_6);
x_68 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_63, x_65, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec_ref(x_8);
x_69 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_70 = lean_string_dec_eq(x_7, x_69);
lean_dec_ref(x_7);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_6);
x_71 = l_Lean_Expr_int_x3f(x_1);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_array_get_size(x_6);
x_73 = lean_unsigned_to_nat(6u);
x_74 = lean_nat_dec_eq(x_72, x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_6);
x_75 = l_Lean_Expr_int_x3f(x_1);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_1);
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed), 2, 0);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_array_fget(x_6, x_77);
x_79 = lean_unsigned_to_nat(5u);
x_80 = lean_array_fget(x_6, x_79);
lean_dec(x_6);
x_81 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_76, x_78, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec_ref(x_8);
x_82 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
x_83 = lean_string_dec_eq(x_7, x_82);
lean_dec_ref(x_7);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_6);
x_84 = l_Lean_Expr_int_x3f(x_1);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_array_get_size(x_6);
x_86 = lean_unsigned_to_nat(6u);
x_87 = lean_nat_dec_eq(x_85, x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_6);
x_88 = l_Lean_Expr_int_x3f(x_1);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_1);
x_89 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed), 2, 0);
x_90 = lean_unsigned_to_nat(4u);
x_91 = lean_array_fget(x_6, x_90);
x_92 = lean_unsigned_to_nat(5u);
x_93 = lean_array_fget(x_6, x_92);
lean_dec(x_6);
x_94 = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_89, x_91, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_95; uint8_t x_96; 
lean_dec_ref(x_8);
x_95 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_96 = lean_string_dec_eq(x_7, x_95);
lean_dec_ref(x_7);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_6);
x_97 = l_Lean_Expr_int_x3f(x_1);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_array_get_size(x_6);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_nat_dec_eq(x_98, x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_6);
x_101 = l_Lean_Expr_int_x3f(x_1);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_1);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_array_fget(x_6, x_102);
lean_dec(x_6);
x_104 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_box(0);
return x_105;
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_104, 0);
x_108 = lean_nat_to_int(x_107);
lean_ctor_set(x_104, 0, x_108);
return x_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
lean_dec(x_104);
x_110 = lean_nat_to_int(x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
}
else
{
lean_object* x_112; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_112 = l_Lean_Expr_int_x3f(x_1);
return x_112;
}
}
else
{
lean_object* x_113; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_113 = l_Lean_Expr_int_x3f(x_1);
return x_113;
}
}
else
{
lean_object* x_114; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_114 = l_Lean_Expr_int_x3f(x_1);
return x_114;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_Meta_mkEqRefl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Meta_mkEq(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Meta_mkExpectedPropHint(x_9, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Lean_Meta_mkExpectedPropHint(x_9, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_expr_eqv(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_disjunction", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_right", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_right", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_ofNat_nonneg", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTNat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
x_2 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_pos_of_pos", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
x_2 = lean_int_dec_le(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTInt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64;
x_5 = l_Lean_mkApp3(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul_ediv_self_le", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_mul_ediv_self_add", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg_le_natAbs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_nonneg", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isLt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_natAbs", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("val", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natAbs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_sub_dichotomy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_16; lean_object* x_20; lean_object* x_24; lean_object* x_28; lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_getAppFnArgs(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
switch (lean_obj_tag(x_34)) {
case 0:
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_33);
x_39 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
x_40 = lean_string_dec_eq(x_38, x_39);
lean_dec_ref(x_38);
if (x_40 == 0)
{
lean_free_object(x_32);
lean_dec(x_36);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_array_get_size(x_36);
x_42 = lean_unsigned_to_nat(5u);
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_free_object(x_32);
lean_dec(x_36);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_fget(x_36, x_44);
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_48 = lean_expr_eqv(x_45, x_47);
if (x_48 == 0)
{
lean_dec_ref(x_45);
lean_dec(x_36);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 0, x_46);
return x_32;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_array_fget(x_36, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_array_fget(x_36, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_array_fget(x_36, x_53);
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_array_fget(x_36, x_55);
lean_dec(x_36);
x_57 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
x_58 = l_Lean_mkApp5(x_57, x_45, x_50, x_52, x_54, x_56);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_46);
lean_ctor_set(x_32, 0, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_32);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_32, 1);
lean_inc(x_60);
lean_dec(x_32);
x_61 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_61);
lean_dec_ref(x_33);
x_62 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
x_63 = lean_string_dec_eq(x_61, x_62);
lean_dec_ref(x_61);
if (x_63 == 0)
{
lean_dec(x_60);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_array_get_size(x_60);
x_65 = lean_unsigned_to_nat(5u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_dec(x_60);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_array_fget(x_60, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_71 = lean_expr_eqv(x_68, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec_ref(x_68);
lean_dec(x_60);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_7);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_array_fget(x_60, x_73);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_array_fget(x_60, x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_array_fget(x_60, x_77);
x_79 = lean_unsigned_to_nat(4u);
x_80 = lean_array_fget(x_60, x_79);
lean_dec(x_60);
x_81 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
x_82 = l_Lean_mkApp5(x_81, x_68, x_74, x_76, x_78, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_69);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_7);
return x_84;
}
}
}
}
}
case 1:
{
lean_object* x_85; 
lean_inc_ref(x_34);
x_85 = lean_ctor_get(x_34, 0);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_32, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_87 = x_32;
} else {
 lean_dec_ref(x_32);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_88);
lean_dec_ref(x_33);
x_89 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_89);
lean_dec_ref(x_34);
x_90 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_91 = lean_string_dec_eq(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_93 = lean_string_dec_eq(x_89, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6;
x_95 = lean_string_dec_eq(x_89, x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_96 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7;
x_97 = lean_string_dec_eq(x_89, x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_99 = lean_string_dec_eq(x_89, x_98);
lean_dec_ref(x_89);
if (x_99 == 0)
{
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9;
x_101 = lean_string_dec_eq(x_88, x_100);
lean_dec_ref(x_88);
if (x_101 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_array_get_size(x_86);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_dec_eq(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_105 = lean_unsigned_to_nat(2u);
x_106 = lean_array_fget(x_86, x_105);
x_107 = lean_unsigned_to_nat(3u);
x_108 = lean_array_fget(x_86, x_107);
lean_dec(x_86);
x_109 = lean_box(0);
x_110 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12;
lean_inc_ref(x_108);
lean_inc_ref(x_106);
x_111 = l_Lean_mkAppB(x_110, x_106, x_108);
x_112 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15;
x_113 = l_Lean_mkAppB(x_112, x_106, x_108);
if (lean_is_scalar(x_87)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_87;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_7);
return x_116;
}
}
}
}
else
{
lean_object* x_117; uint8_t x_118; 
lean_dec_ref(x_89);
x_117 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16;
x_118 = lean_string_dec_eq(x_88, x_117);
lean_dec_ref(x_88);
if (x_118 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_array_get_size(x_86);
x_120 = lean_unsigned_to_nat(4u);
x_121 = lean_nat_dec_eq(x_119, x_120);
lean_dec(x_119);
if (x_121 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_array_fget(x_86, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_array_fget(x_86, x_124);
lean_dec(x_86);
x_126 = lean_box(0);
x_127 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19;
lean_inc_ref(x_125);
lean_inc_ref(x_123);
x_128 = l_Lean_mkAppB(x_127, x_123, x_125);
x_129 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
x_130 = l_Lean_mkAppB(x_129, x_123, x_125);
if (lean_is_scalar(x_87)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_87;
 lean_ctor_set_tag(x_131, 1);
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_7);
return x_133;
}
}
}
}
else
{
lean_object* x_134; uint8_t x_135; 
lean_dec_ref(x_89);
x_134 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23;
x_135 = lean_string_dec_eq(x_88, x_134);
lean_dec_ref(x_88);
if (x_135 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_array_get_size(x_86);
x_137 = lean_unsigned_to_nat(6u);
x_138 = lean_nat_dec_eq(x_136, x_137);
lean_dec(x_136);
if (x_138 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_unsigned_to_nat(5u);
x_140 = lean_array_fget(x_86, x_139);
lean_inc_ref(x_140);
x_141 = l_Lean_Expr_getAppFnArgs(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 1)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 1)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_208; uint8_t x_209; 
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_146 = x_141;
} else {
 lean_dec_ref(x_141);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_142, 1);
lean_inc_ref(x_147);
lean_dec_ref(x_142);
x_148 = lean_ctor_get(x_143, 1);
lean_inc_ref(x_148);
lean_dec_ref(x_143);
x_149 = lean_unsigned_to_nat(4u);
x_150 = lean_array_fget(x_86, x_149);
lean_dec(x_86);
x_208 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_209 = lean_string_dec_eq(x_148, x_208);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = lean_string_dec_eq(x_148, x_90);
lean_dec_ref(x_148);
if (x_210 == 0)
{
lean_dec_ref(x_150);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
else
{
lean_object* x_211; uint8_t x_212; 
x_211 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_212 = lean_string_dec_eq(x_147, x_211);
lean_dec_ref(x_147);
if (x_212 == 0)
{
lean_dec_ref(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_213 = lean_array_get_size(x_145);
x_214 = lean_unsigned_to_nat(3u);
x_215 = lean_nat_dec_eq(x_213, x_214);
lean_dec(x_213);
if (x_215 == 0)
{
lean_dec_ref(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_unsigned_to_nat(0u);
x_217 = lean_array_fget(x_145, x_216);
if (lean_obj_tag(x_217) == 4)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 1)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_218, 0);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec_ref(x_217);
x_221 = lean_ctor_get(x_218, 1);
lean_inc_ref(x_221);
lean_dec_ref(x_218);
x_222 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_223 = lean_string_dec_eq(x_221, x_222);
lean_dec_ref(x_221);
if (x_223 == 0)
{
lean_dec(x_220);
lean_dec_ref(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
else
{
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_unsigned_to_nat(2u);
x_225 = lean_array_fget(x_145, x_224);
lean_dec(x_145);
lean_inc_ref(x_225);
x_226 = l_Lean_Expr_getAppFnArgs(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 1)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 1)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_226);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_226, 1);
x_232 = lean_ctor_get(x_226, 0);
lean_dec(x_232);
x_233 = lean_ctor_get(x_227, 1);
lean_inc_ref(x_233);
lean_dec_ref(x_227);
x_234 = lean_ctor_get(x_228, 1);
lean_inc_ref(x_234);
lean_dec_ref(x_228);
x_235 = lean_string_dec_eq(x_234, x_208);
lean_dec_ref(x_234);
if (x_235 == 0)
{
lean_dec_ref(x_233);
lean_free_object(x_226);
lean_dec(x_231);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
else
{
lean_object* x_236; uint8_t x_237; 
x_236 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_237 = lean_string_dec_eq(x_233, x_236);
lean_dec_ref(x_233);
if (x_237 == 0)
{
lean_free_object(x_226);
lean_dec(x_231);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
else
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_array_get_size(x_231);
x_239 = lean_nat_dec_eq(x_238, x_137);
lean_dec(x_238);
if (x_239 == 0)
{
lean_free_object(x_226);
lean_dec(x_231);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_146);
x_240 = lean_array_fget(x_231, x_149);
lean_inc_ref(x_240);
x_241 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_dec_ref(x_240);
lean_free_object(x_226);
lean_dec(x_231);
lean_dec_ref(x_225);
lean_dec_ref(x_150);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_28 = x_7;
goto block_31;
}
else
{
lean_object* x_242; uint8_t x_243; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec_ref(x_241);
x_243 = lean_nat_dec_eq(x_242, x_216);
lean_dec(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_244 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28;
x_245 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
lean_ctor_set_tag(x_226, 1);
lean_ctor_set(x_226, 1, x_220);
lean_ctor_set(x_226, 0, x_245);
lean_inc_ref(x_226);
x_246 = l_Lean_Expr_const___override(x_244, x_226);
x_247 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29;
x_248 = l_Lean_Expr_const___override(x_247, x_220);
x_249 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31;
x_250 = l_Lean_Expr_const___override(x_249, x_220);
x_251 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32;
lean_inc_ref(x_240);
x_252 = l_Lean_mkApp4(x_246, x_248, x_250, x_251, x_240);
x_253 = l_Lean_Meta_mkDecideProof(x_252, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_279; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
x_257 = lean_array_fget(x_231, x_139);
lean_dec(x_231);
x_258 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34;
x_259 = l_Lean_Expr_const___override(x_258, x_220);
x_260 = l_Lean_mkApp3(x_259, x_240, x_257, x_254);
x_261 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36;
x_262 = l_Lean_Expr_const___override(x_261, x_220);
x_263 = l_Lean_mkAppB(x_262, x_225, x_260);
x_264 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
x_265 = l_Lean_Expr_const___override(x_264, x_220);
x_266 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40;
x_267 = l_Lean_Expr_const___override(x_266, x_220);
x_279 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_280 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
x_281 = l_Lean_Expr_const___override(x_280, x_226);
x_282 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
x_283 = l_Lean_Expr_const___override(x_282, x_220);
x_284 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
x_285 = l_Lean_Expr_const___override(x_284, x_220);
x_286 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
x_287 = l_Lean_mkApp3(x_281, x_283, x_285, x_286);
x_268 = x_287;
goto block_278;
}
else
{
lean_object* x_288; 
lean_dec_ref(x_226);
x_288 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
x_268 = x_288;
goto block_278;
}
block_278:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_inc_ref(x_263);
lean_inc_ref(x_140);
x_269 = l_Lean_mkApp3(x_267, x_140, x_268, x_263);
lean_inc_ref(x_140);
lean_inc_ref(x_150);
x_270 = l_Lean_mkApp3(x_265, x_150, x_140, x_269);
x_271 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
x_272 = l_Lean_Expr_const___override(x_271, x_220);
x_273 = l_Lean_mkApp3(x_272, x_150, x_140, x_263);
x_274 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_87;
 lean_ctor_set_tag(x_275, 1);
}
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_270);
lean_ctor_set(x_276, 1, x_275);
if (lean_is_scalar(x_256)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_256;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_255);
return x_277;
}
}
else
{
uint8_t x_289; 
lean_dec_ref(x_226);
lean_dec_ref(x_240);
lean_dec(x_231);
lean_dec_ref(x_225);
lean_dec_ref(x_150);
lean_dec_ref(x_140);
lean_dec(x_87);
x_289 = !lean_is_exclusive(x_253);
if (x_289 == 0)
{
return x_253;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_253, 0);
x_291 = lean_ctor_get(x_253, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_253);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
lean_dec_ref(x_240);
lean_free_object(x_226);
lean_dec(x_231);
lean_dec_ref(x_225);
lean_dec_ref(x_150);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_28 = x_7;
goto block_31;
}
}
}
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_293 = lean_ctor_get(x_226, 1);
lean_inc(x_293);
lean_dec(x_226);
x_294 = lean_ctor_get(x_227, 1);
lean_inc_ref(x_294);
lean_dec_ref(x_227);
x_295 = lean_ctor_get(x_228, 1);
lean_inc_ref(x_295);
lean_dec_ref(x_228);
x_296 = lean_string_dec_eq(x_295, x_208);
lean_dec_ref(x_295);
if (x_296 == 0)
{
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
else
{
lean_object* x_297; uint8_t x_298; 
x_297 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_298 = lean_string_dec_eq(x_294, x_297);
lean_dec_ref(x_294);
if (x_298 == 0)
{
lean_dec(x_293);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
else
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_array_get_size(x_293);
x_300 = lean_nat_dec_eq(x_299, x_137);
lean_dec(x_299);
if (x_300 == 0)
{
lean_dec(x_293);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
else
{
lean_object* x_301; lean_object* x_302; 
lean_dec(x_146);
x_301 = lean_array_fget(x_293, x_149);
lean_inc_ref(x_301);
x_302 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_dec_ref(x_301);
lean_dec(x_293);
lean_dec_ref(x_225);
lean_dec_ref(x_150);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_28 = x_7;
goto block_31;
}
else
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec_ref(x_302);
x_304 = lean_nat_dec_eq(x_303, x_216);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_305 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28;
x_306 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_220);
lean_inc_ref(x_307);
x_308 = l_Lean_Expr_const___override(x_305, x_307);
x_309 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29;
x_310 = l_Lean_Expr_const___override(x_309, x_220);
x_311 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31;
x_312 = l_Lean_Expr_const___override(x_311, x_220);
x_313 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32;
lean_inc_ref(x_301);
x_314 = l_Lean_mkApp4(x_308, x_310, x_312, x_313, x_301);
x_315 = l_Lean_Meta_mkDecideProof(x_314, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_341; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_318 = x_315;
} else {
 lean_dec_ref(x_315);
 x_318 = lean_box(0);
}
x_319 = lean_array_fget(x_293, x_139);
lean_dec(x_293);
x_320 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34;
x_321 = l_Lean_Expr_const___override(x_320, x_220);
x_322 = l_Lean_mkApp3(x_321, x_301, x_319, x_316);
x_323 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36;
x_324 = l_Lean_Expr_const___override(x_323, x_220);
x_325 = l_Lean_mkAppB(x_324, x_225, x_322);
x_326 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
x_327 = l_Lean_Expr_const___override(x_326, x_220);
x_328 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40;
x_329 = l_Lean_Expr_const___override(x_328, x_220);
x_341 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_342 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
x_343 = l_Lean_Expr_const___override(x_342, x_307);
x_344 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
x_345 = l_Lean_Expr_const___override(x_344, x_220);
x_346 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
x_347 = l_Lean_Expr_const___override(x_346, x_220);
x_348 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
x_349 = l_Lean_mkApp3(x_343, x_345, x_347, x_348);
x_330 = x_349;
goto block_340;
}
else
{
lean_object* x_350; 
lean_dec_ref(x_307);
x_350 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
x_330 = x_350;
goto block_340;
}
block_340:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_inc_ref(x_325);
lean_inc_ref(x_140);
x_331 = l_Lean_mkApp3(x_329, x_140, x_330, x_325);
lean_inc_ref(x_140);
lean_inc_ref(x_150);
x_332 = l_Lean_mkApp3(x_327, x_150, x_140, x_331);
x_333 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
x_334 = l_Lean_Expr_const___override(x_333, x_220);
x_335 = l_Lean_mkApp3(x_334, x_150, x_140, x_325);
x_336 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_87;
 lean_ctor_set_tag(x_337, 1);
}
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_332);
lean_ctor_set(x_338, 1, x_337);
if (lean_is_scalar(x_318)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_318;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_317);
return x_339;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec_ref(x_307);
lean_dec_ref(x_301);
lean_dec(x_293);
lean_dec_ref(x_225);
lean_dec_ref(x_150);
lean_dec_ref(x_140);
lean_dec(x_87);
x_351 = lean_ctor_get(x_315, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_315, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_353 = x_315;
} else {
 lean_dec_ref(x_315);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
else
{
lean_dec_ref(x_301);
lean_dec(x_293);
lean_dec_ref(x_225);
lean_dec_ref(x_150);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_28 = x_7;
goto block_31;
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
}
else
{
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
}
else
{
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec_ref(x_225);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_151 = x_7;
goto block_207;
}
}
else
{
lean_dec_ref(x_220);
lean_dec_ref(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
}
}
else
{
lean_dec_ref(x_218);
lean_dec_ref(x_217);
lean_dec_ref(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
}
else
{
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec_ref(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
}
else
{
lean_dec_ref(x_217);
lean_dec_ref(x_150);
lean_dec(x_146);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
}
}
}
}
else
{
lean_object* x_355; uint8_t x_356; 
lean_dec_ref(x_148);
lean_dec(x_146);
x_355 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_356 = lean_string_dec_eq(x_147, x_355);
lean_dec_ref(x_147);
if (x_356 == 0)
{
lean_dec_ref(x_150);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
else
{
lean_object* x_357; uint8_t x_358; 
x_357 = lean_array_get_size(x_145);
x_358 = lean_nat_dec_eq(x_357, x_137);
lean_dec(x_357);
if (x_358 == 0)
{
lean_dec_ref(x_150);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
else
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_array_fget(x_145, x_149);
lean_inc_ref(x_359);
x_360 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_dec_ref(x_359);
lean_dec_ref(x_150);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
lean_dec_ref(x_360);
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_dec_eq(x_361, x_362);
lean_dec(x_361);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_402; 
x_364 = lean_array_fget(x_145, x_139);
lean_dec(x_145);
x_365 = lean_box(0);
x_366 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55;
x_367 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_368 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58;
x_402 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
if (x_402 == 0)
{
lean_object* x_403; 
x_403 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66;
x_369 = x_403;
goto block_401;
}
else
{
lean_object* x_404; 
x_404 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
x_369 = x_404;
goto block_401;
}
block_401:
{
lean_object* x_370; lean_object* x_371; 
lean_inc_ref(x_359);
lean_inc_ref(x_369);
x_370 = l_Lean_mkApp4(x_366, x_367, x_368, x_369, x_359);
x_371 = l_Lean_Meta_mkDecideProof(x_370, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_371) == 0)
{
uint8_t x_372; 
x_372 = !lean_is_exclusive(x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_373 = lean_ctor_get(x_371, 0);
x_374 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60;
x_375 = l_Lean_mkApp3(x_374, x_359, x_364, x_373);
x_376 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61;
x_377 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62;
lean_inc_ref(x_375);
lean_inc_ref(x_140);
x_378 = l_Lean_mkApp3(x_377, x_140, x_369, x_375);
lean_inc_ref(x_140);
lean_inc_ref(x_150);
x_379 = l_Lean_mkApp3(x_376, x_150, x_140, x_378);
x_380 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63;
x_381 = l_Lean_mkApp3(x_380, x_150, x_140, x_375);
if (lean_is_scalar(x_87)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_87;
 lean_ctor_set_tag(x_382, 1);
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_365);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_379);
lean_ctor_set(x_383, 1, x_382);
lean_ctor_set(x_371, 0, x_383);
return x_371;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_384 = lean_ctor_get(x_371, 0);
x_385 = lean_ctor_get(x_371, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_371);
x_386 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60;
x_387 = l_Lean_mkApp3(x_386, x_359, x_364, x_384);
x_388 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61;
x_389 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62;
lean_inc_ref(x_387);
lean_inc_ref(x_140);
x_390 = l_Lean_mkApp3(x_389, x_140, x_369, x_387);
lean_inc_ref(x_140);
lean_inc_ref(x_150);
x_391 = l_Lean_mkApp3(x_388, x_150, x_140, x_390);
x_392 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63;
x_393 = l_Lean_mkApp3(x_392, x_150, x_140, x_387);
if (lean_is_scalar(x_87)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_87;
 lean_ctor_set_tag(x_394, 1);
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_365);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_391);
lean_ctor_set(x_395, 1, x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_385);
return x_396;
}
}
else
{
uint8_t x_397; 
lean_dec_ref(x_369);
lean_dec_ref(x_364);
lean_dec_ref(x_359);
lean_dec_ref(x_150);
lean_dec_ref(x_140);
lean_dec(x_87);
x_397 = !lean_is_exclusive(x_371);
if (x_397 == 0)
{
return x_371;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_371, 0);
x_399 = lean_ctor_get(x_371, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_371);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
}
else
{
lean_dec_ref(x_359);
lean_dec_ref(x_150);
lean_dec(x_145);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = x_7;
goto block_15;
}
}
}
}
}
block_207:
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Lean_Expr_getAppFnArgs(x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 1)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 1)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_154, 0);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_152);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_152, 1);
x_158 = lean_ctor_get(x_152, 0);
lean_dec(x_158);
x_159 = lean_ctor_get(x_153, 1);
lean_inc_ref(x_159);
lean_dec_ref(x_153);
x_160 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_160);
lean_dec_ref(x_154);
x_161 = lean_string_dec_eq(x_160, x_90);
lean_dec_ref(x_160);
if (x_161 == 0)
{
lean_dec_ref(x_159);
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_163 = lean_string_dec_eq(x_159, x_162);
lean_dec_ref(x_159);
if (x_163 == 0)
{
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_array_get_size(x_157);
x_165 = lean_unsigned_to_nat(3u);
x_166 = lean_nat_dec_eq(x_164, x_165);
lean_dec(x_164);
if (x_166 == 0)
{
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_array_fget(x_157, x_167);
if (lean_obj_tag(x_168) == 4)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 1)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec_ref(x_168);
x_172 = lean_ctor_get(x_169, 1);
lean_inc_ref(x_172);
lean_dec_ref(x_169);
x_173 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_174 = lean_string_dec_eq(x_172, x_173);
lean_dec_ref(x_172);
if (x_174 == 0)
{
lean_dec(x_171);
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_unsigned_to_nat(2u);
x_176 = lean_array_fget(x_157, x_175);
lean_dec(x_157);
x_177 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25;
x_178 = l_Lean_Expr_const___override(x_177, x_171);
x_179 = l_Lean_mkAppB(x_178, x_176, x_140);
x_180 = lean_box(0);
lean_ctor_set_tag(x_152, 1);
lean_ctor_set(x_152, 1, x_180);
lean_ctor_set(x_152, 0, x_179);
if (lean_is_scalar(x_146)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_146;
}
lean_ctor_set(x_181, 0, x_152);
lean_ctor_set(x_181, 1, x_151);
return x_181;
}
else
{
lean_dec_ref(x_171);
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
}
else
{
lean_dec_ref(x_169);
lean_dec_ref(x_168);
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
else
{
lean_dec(x_169);
lean_dec_ref(x_168);
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
else
{
lean_dec_ref(x_168);
lean_free_object(x_152);
lean_dec(x_157);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_152, 1);
lean_inc(x_182);
lean_dec(x_152);
x_183 = lean_ctor_get(x_153, 1);
lean_inc_ref(x_183);
lean_dec_ref(x_153);
x_184 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_184);
lean_dec_ref(x_154);
x_185 = lean_string_dec_eq(x_184, x_90);
lean_dec_ref(x_184);
if (x_185 == 0)
{
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
lean_object* x_186; uint8_t x_187; 
x_186 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_187 = lean_string_dec_eq(x_183, x_186);
lean_dec_ref(x_183);
if (x_187 == 0)
{
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = lean_array_get_size(x_182);
x_189 = lean_unsigned_to_nat(3u);
x_190 = lean_nat_dec_eq(x_188, x_189);
lean_dec(x_188);
if (x_190 == 0)
{
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_unsigned_to_nat(0u);
x_192 = lean_array_fget(x_182, x_191);
if (lean_obj_tag(x_192) == 4)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 1)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec_ref(x_192);
x_196 = lean_ctor_get(x_193, 1);
lean_inc_ref(x_196);
lean_dec_ref(x_193);
x_197 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_198 = lean_string_dec_eq(x_196, x_197);
lean_dec_ref(x_196);
if (x_198 == 0)
{
lean_dec(x_195);
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
else
{
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_199 = lean_unsigned_to_nat(2u);
x_200 = lean_array_fget(x_182, x_199);
lean_dec(x_182);
x_201 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25;
x_202 = l_Lean_Expr_const___override(x_201, x_195);
x_203 = l_Lean_mkAppB(x_202, x_200, x_140);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
if (lean_is_scalar(x_146)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_146;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_151);
return x_206;
}
else
{
lean_dec_ref(x_195);
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
}
else
{
lean_dec_ref(x_193);
lean_dec_ref(x_192);
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
else
{
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
else
{
lean_dec_ref(x_192);
lean_dec(x_182);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
}
}
}
}
else
{
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
else
{
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
else
{
lean_dec(x_153);
lean_dec_ref(x_152);
lean_dec(x_146);
lean_dec_ref(x_140);
x_24 = x_151;
goto block_27;
}
}
}
else
{
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
}
else
{
lean_dec(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
}
else
{
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_140);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = x_7;
goto block_23;
}
}
}
}
}
else
{
lean_object* x_405; uint8_t x_406; 
lean_dec_ref(x_89);
x_405 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_406 = lean_string_dec_eq(x_88, x_405);
lean_dec_ref(x_88);
if (x_406 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_407 = lean_array_get_size(x_86);
x_408 = lean_unsigned_to_nat(6u);
x_409 = lean_nat_dec_eq(x_407, x_408);
lean_dec(x_407);
if (x_409 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_unsigned_to_nat(5u);
x_411 = lean_array_fget(x_86, x_410);
lean_inc_ref(x_411);
x_412 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_411);
if (lean_obj_tag(x_412) == 0)
{
lean_dec_ref(x_411);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = x_7;
goto block_11;
}
else
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
x_414 = lean_unsigned_to_nat(0u);
x_415 = lean_nat_dec_eq(x_413, x_414);
lean_dec(x_413);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_456; 
x_416 = lean_unsigned_to_nat(4u);
x_417 = lean_array_fget(x_86, x_416);
lean_dec(x_86);
x_418 = lean_box(0);
x_419 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71;
x_420 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_456 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
if (x_456 == 0)
{
lean_object* x_457; 
x_457 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66;
x_421 = x_457;
goto block_455;
}
else
{
lean_object* x_458; 
x_458 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
x_421 = x_458;
goto block_455;
}
block_455:
{
lean_object* x_422; lean_object* x_423; 
lean_inc_ref(x_421);
lean_inc_ref(x_411);
x_422 = l_Lean_mkApp3(x_419, x_420, x_411, x_421);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_423 = l_Lean_Meta_mkDecideProof(x_422, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec_ref(x_423);
x_426 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55;
x_427 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58;
lean_inc_ref(x_411);
x_428 = l_Lean_mkApp4(x_426, x_420, x_427, x_421, x_411);
x_429 = l_Lean_Meta_mkDecideProof(x_428, x_3, x_4, x_5, x_6, x_425);
if (lean_obj_tag(x_429) == 0)
{
uint8_t x_430; 
x_430 = !lean_is_exclusive(x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_431 = lean_ctor_get(x_429, 0);
x_432 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74;
lean_inc_ref(x_411);
lean_inc_ref(x_417);
x_433 = l_Lean_mkApp3(x_432, x_417, x_411, x_424);
x_434 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77;
x_435 = l_Lean_mkApp3(x_434, x_417, x_411, x_431);
if (lean_is_scalar(x_87)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_87;
 lean_ctor_set_tag(x_436, 1);
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_418);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_436);
lean_ctor_set(x_429, 0, x_437);
return x_429;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_438 = lean_ctor_get(x_429, 0);
x_439 = lean_ctor_get(x_429, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_429);
x_440 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74;
lean_inc_ref(x_411);
lean_inc_ref(x_417);
x_441 = l_Lean_mkApp3(x_440, x_417, x_411, x_424);
x_442 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77;
x_443 = l_Lean_mkApp3(x_442, x_417, x_411, x_438);
if (lean_is_scalar(x_87)) {
 x_444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_444 = x_87;
 lean_ctor_set_tag(x_444, 1);
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_418);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_439);
return x_446;
}
}
else
{
uint8_t x_447; 
lean_dec(x_424);
lean_dec_ref(x_417);
lean_dec_ref(x_411);
lean_dec(x_87);
x_447 = !lean_is_exclusive(x_429);
if (x_447 == 0)
{
return x_429;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_429, 0);
x_449 = lean_ctor_get(x_429, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_429);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
lean_dec_ref(x_421);
lean_dec_ref(x_417);
lean_dec_ref(x_411);
lean_dec(x_87);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_451 = !lean_is_exclusive(x_423);
if (x_451 == 0)
{
return x_423;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_423, 0);
x_453 = lean_ctor_get(x_423, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_423);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
}
else
{
lean_dec_ref(x_411);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = x_7;
goto block_11;
}
}
}
}
}
}
else
{
lean_object* x_459; uint8_t x_460; 
lean_dec_ref(x_89);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_459 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_460 = lean_string_dec_eq(x_88, x_459);
lean_dec_ref(x_88);
if (x_460 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_461; lean_object* x_462; uint8_t x_463; 
x_461 = lean_array_get_size(x_86);
x_462 = lean_unsigned_to_nat(3u);
x_463 = lean_nat_dec_eq(x_461, x_462);
lean_dec(x_461);
if (x_463 == 0)
{
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_464; lean_object* x_465; 
x_464 = lean_unsigned_to_nat(0u);
x_465 = lean_array_fget(x_86, x_464);
if (lean_obj_tag(x_465) == 4)
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 1)
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_466, 0);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_482; 
x_468 = lean_ctor_get(x_465, 1);
lean_inc(x_468);
lean_dec_ref(x_465);
x_469 = lean_ctor_get(x_466, 1);
lean_inc_ref(x_469);
lean_dec_ref(x_466);
x_470 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_482 = lean_string_dec_eq(x_469, x_470);
lean_dec_ref(x_469);
if (x_482 == 0)
{
lean_dec(x_468);
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
else
{
if (lean_obj_tag(x_468) == 0)
{
uint8_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_513; lean_object* x_514; 
x_483 = lean_ctor_get_uint8(x_2, 1);
x_484 = lean_unsigned_to_nat(2u);
x_485 = lean_array_fget(x_86, x_484);
lean_dec(x_86);
x_486 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81;
x_487 = l_Lean_Expr_const___override(x_486, x_468);
lean_inc_ref(x_485);
x_488 = l_Lean_Expr_app___override(x_487, x_485);
x_489 = lean_box(0);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
if (x_483 == 0)
{
lean_object* x_521; lean_object* x_522; 
x_521 = l_Lean_Expr_getAppFnArgs(x_485);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
if (lean_obj_tag(x_522) == 1)
{
lean_object* x_523; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
if (lean_obj_tag(x_523) == 1)
{
lean_object* x_524; 
x_524 = lean_ctor_get(x_523, 0);
if (lean_obj_tag(x_524) == 0)
{
uint8_t x_525; 
x_525 = !lean_is_exclusive(x_521);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; 
x_526 = lean_ctor_get(x_521, 1);
x_527 = lean_ctor_get(x_521, 0);
lean_dec(x_527);
x_528 = lean_ctor_get(x_522, 1);
lean_inc_ref(x_528);
lean_dec_ref(x_522);
x_529 = lean_ctor_get(x_523, 1);
lean_inc_ref(x_529);
lean_dec_ref(x_523);
x_530 = lean_string_dec_eq(x_529, x_470);
if (x_530 == 0)
{
lean_object* x_531; uint8_t x_532; 
lean_dec(x_87);
x_531 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
x_532 = lean_string_dec_eq(x_529, x_531);
if (x_532 == 0)
{
lean_object* x_533; uint8_t x_534; 
x_533 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
x_534 = lean_string_dec_eq(x_529, x_533);
lean_dec_ref(x_529);
if (x_534 == 0)
{
lean_dec_ref(x_528);
lean_dec(x_526);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_535; uint8_t x_536; 
x_535 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89;
x_536 = lean_string_dec_eq(x_528, x_535);
lean_dec_ref(x_528);
if (x_536 == 0)
{
lean_dec(x_526);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_537; uint8_t x_538; 
x_537 = lean_array_get_size(x_526);
x_538 = lean_nat_dec_eq(x_537, x_484);
lean_dec(x_537);
if (x_538 == 0)
{
lean_dec(x_526);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_free_object(x_521);
x_539 = lean_array_fget(x_526, x_464);
x_540 = lean_unsigned_to_nat(1u);
x_541 = lean_array_fget(x_526, x_540);
lean_dec(x_526);
x_491 = x_539;
x_492 = x_541;
x_493 = x_7;
goto block_501;
}
}
}
}
else
{
lean_object* x_542; uint8_t x_543; 
lean_dec_ref(x_529);
x_542 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
x_543 = lean_string_dec_eq(x_528, x_542);
lean_dec_ref(x_528);
if (x_543 == 0)
{
lean_dec(x_526);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_544; uint8_t x_545; 
x_544 = lean_array_get_size(x_526);
x_545 = lean_nat_dec_eq(x_544, x_484);
lean_dec(x_544);
if (x_545 == 0)
{
lean_dec(x_526);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_free_object(x_521);
x_546 = lean_array_fget(x_526, x_464);
x_547 = lean_unsigned_to_nat(1u);
x_548 = lean_array_fget(x_526, x_547);
lean_dec(x_526);
x_502 = x_546;
x_503 = x_548;
x_504 = x_7;
goto block_512;
}
}
}
}
else
{
lean_object* x_549; uint8_t x_550; 
lean_dec_ref(x_529);
x_549 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
x_550 = lean_string_dec_eq(x_528, x_549);
lean_dec_ref(x_528);
if (x_550 == 0)
{
lean_dec(x_526);
lean_dec(x_87);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_551 = lean_array_get_size(x_526);
x_552 = lean_unsigned_to_nat(1u);
x_553 = lean_nat_dec_eq(x_551, x_552);
lean_dec(x_551);
if (x_553 == 0)
{
lean_dec(x_526);
lean_dec(x_87);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_554; 
lean_free_object(x_521);
x_554 = lean_array_fget(x_526, x_464);
lean_dec(x_526);
x_513 = x_554;
x_514 = x_7;
goto block_520;
}
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; 
x_555 = lean_ctor_get(x_521, 1);
lean_inc(x_555);
lean_dec(x_521);
x_556 = lean_ctor_get(x_522, 1);
lean_inc_ref(x_556);
lean_dec_ref(x_522);
x_557 = lean_ctor_get(x_523, 1);
lean_inc_ref(x_557);
lean_dec_ref(x_523);
x_558 = lean_string_dec_eq(x_557, x_470);
if (x_558 == 0)
{
lean_object* x_559; uint8_t x_560; 
lean_dec(x_87);
x_559 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
x_560 = lean_string_dec_eq(x_557, x_559);
if (x_560 == 0)
{
lean_object* x_561; uint8_t x_562; 
x_561 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
x_562 = lean_string_dec_eq(x_557, x_561);
lean_dec_ref(x_557);
if (x_562 == 0)
{
lean_object* x_563; 
lean_dec_ref(x_556);
lean_dec(x_555);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_490);
lean_ctor_set(x_563, 1, x_7);
return x_563;
}
else
{
lean_object* x_564; uint8_t x_565; 
x_564 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89;
x_565 = lean_string_dec_eq(x_556, x_564);
lean_dec_ref(x_556);
if (x_565 == 0)
{
lean_object* x_566; 
lean_dec(x_555);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_490);
lean_ctor_set(x_566, 1, x_7);
return x_566;
}
else
{
lean_object* x_567; uint8_t x_568; 
x_567 = lean_array_get_size(x_555);
x_568 = lean_nat_dec_eq(x_567, x_484);
lean_dec(x_567);
if (x_568 == 0)
{
lean_object* x_569; 
lean_dec(x_555);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_490);
lean_ctor_set(x_569, 1, x_7);
return x_569;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_array_fget(x_555, x_464);
x_571 = lean_unsigned_to_nat(1u);
x_572 = lean_array_fget(x_555, x_571);
lean_dec(x_555);
x_491 = x_570;
x_492 = x_572;
x_493 = x_7;
goto block_501;
}
}
}
}
else
{
lean_object* x_573; uint8_t x_574; 
lean_dec_ref(x_557);
x_573 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
x_574 = lean_string_dec_eq(x_556, x_573);
lean_dec_ref(x_556);
if (x_574 == 0)
{
lean_object* x_575; 
lean_dec(x_555);
x_575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_575, 0, x_490);
lean_ctor_set(x_575, 1, x_7);
return x_575;
}
else
{
lean_object* x_576; uint8_t x_577; 
x_576 = lean_array_get_size(x_555);
x_577 = lean_nat_dec_eq(x_576, x_484);
lean_dec(x_576);
if (x_577 == 0)
{
lean_object* x_578; 
lean_dec(x_555);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_490);
lean_ctor_set(x_578, 1, x_7);
return x_578;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_array_fget(x_555, x_464);
x_580 = lean_unsigned_to_nat(1u);
x_581 = lean_array_fget(x_555, x_580);
lean_dec(x_555);
x_502 = x_579;
x_503 = x_581;
x_504 = x_7;
goto block_512;
}
}
}
}
else
{
lean_object* x_582; uint8_t x_583; 
lean_dec_ref(x_557);
x_582 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
x_583 = lean_string_dec_eq(x_556, x_582);
lean_dec_ref(x_556);
if (x_583 == 0)
{
lean_object* x_584; 
lean_dec(x_555);
lean_dec(x_87);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_490);
lean_ctor_set(x_584, 1, x_7);
return x_584;
}
else
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_585 = lean_array_get_size(x_555);
x_586 = lean_unsigned_to_nat(1u);
x_587 = lean_nat_dec_eq(x_585, x_586);
lean_dec(x_585);
if (x_587 == 0)
{
lean_object* x_588; 
lean_dec(x_555);
lean_dec(x_87);
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_490);
lean_ctor_set(x_588, 1, x_7);
return x_588;
}
else
{
lean_object* x_589; 
x_589 = lean_array_fget(x_555, x_464);
lean_dec(x_555);
x_513 = x_589;
x_514 = x_7;
goto block_520;
}
}
}
}
}
else
{
uint8_t x_590; 
lean_dec_ref(x_523);
lean_dec_ref(x_522);
lean_dec(x_87);
x_590 = !lean_is_exclusive(x_521);
if (x_590 == 0)
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_521, 1);
lean_dec(x_591);
x_592 = lean_ctor_get(x_521, 0);
lean_dec(x_592);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_593; 
lean_dec(x_521);
x_593 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_593, 0, x_490);
lean_ctor_set(x_593, 1, x_7);
return x_593;
}
}
}
else
{
uint8_t x_594; 
lean_dec(x_523);
lean_dec_ref(x_522);
lean_dec(x_87);
x_594 = !lean_is_exclusive(x_521);
if (x_594 == 0)
{
lean_object* x_595; lean_object* x_596; 
x_595 = lean_ctor_get(x_521, 1);
lean_dec(x_595);
x_596 = lean_ctor_get(x_521, 0);
lean_dec(x_596);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_597; 
lean_dec(x_521);
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_490);
lean_ctor_set(x_597, 1, x_7);
return x_597;
}
}
}
else
{
uint8_t x_598; 
lean_dec(x_522);
lean_dec(x_87);
x_598 = !lean_is_exclusive(x_521);
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; 
x_599 = lean_ctor_get(x_521, 1);
lean_dec(x_599);
x_600 = lean_ctor_get(x_521, 0);
lean_dec(x_600);
lean_ctor_set(x_521, 1, x_7);
lean_ctor_set(x_521, 0, x_490);
return x_521;
}
else
{
lean_object* x_601; 
lean_dec(x_521);
x_601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_601, 0, x_490);
lean_ctor_set(x_601, 1, x_7);
return x_601;
}
}
}
else
{
lean_object* x_602; lean_object* x_603; 
x_602 = l_Lean_Expr_getAppFnArgs(x_485);
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
if (lean_obj_tag(x_603) == 1)
{
lean_object* x_604; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
if (lean_obj_tag(x_604) == 1)
{
lean_object* x_605; 
x_605 = lean_ctor_get(x_604, 0);
if (lean_obj_tag(x_605) == 0)
{
uint8_t x_606; 
x_606 = !lean_is_exclusive(x_602);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; 
x_607 = lean_ctor_get(x_602, 1);
x_608 = lean_ctor_get(x_602, 0);
lean_dec(x_608);
x_609 = lean_ctor_get(x_603, 1);
lean_inc_ref(x_609);
lean_dec_ref(x_603);
x_610 = lean_ctor_get(x_604, 1);
lean_inc_ref(x_610);
lean_dec_ref(x_604);
x_611 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_612 = lean_string_dec_eq(x_610, x_611);
if (x_612 == 0)
{
uint8_t x_613; 
x_613 = lean_string_dec_eq(x_610, x_470);
if (x_613 == 0)
{
lean_object* x_614; uint8_t x_615; 
lean_dec(x_87);
x_614 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
x_615 = lean_string_dec_eq(x_610, x_614);
if (x_615 == 0)
{
lean_object* x_616; uint8_t x_617; 
x_616 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
x_617 = lean_string_dec_eq(x_610, x_616);
lean_dec_ref(x_610);
if (x_617 == 0)
{
lean_dec_ref(x_609);
lean_dec(x_607);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_618; uint8_t x_619; 
x_618 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89;
x_619 = lean_string_dec_eq(x_609, x_618);
lean_dec_ref(x_609);
if (x_619 == 0)
{
lean_dec(x_607);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_620; uint8_t x_621; 
x_620 = lean_array_get_size(x_607);
x_621 = lean_nat_dec_eq(x_620, x_484);
lean_dec(x_620);
if (x_621 == 0)
{
lean_dec(x_607);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_free_object(x_602);
x_622 = lean_array_fget(x_607, x_464);
x_623 = lean_unsigned_to_nat(1u);
x_624 = lean_array_fget(x_607, x_623);
lean_dec(x_607);
x_491 = x_622;
x_492 = x_624;
x_493 = x_7;
goto block_501;
}
}
}
}
else
{
lean_object* x_625; uint8_t x_626; 
lean_dec_ref(x_610);
x_625 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
x_626 = lean_string_dec_eq(x_609, x_625);
lean_dec_ref(x_609);
if (x_626 == 0)
{
lean_dec(x_607);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_627; uint8_t x_628; 
x_627 = lean_array_get_size(x_607);
x_628 = lean_nat_dec_eq(x_627, x_484);
lean_dec(x_627);
if (x_628 == 0)
{
lean_dec(x_607);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_free_object(x_602);
x_629 = lean_array_fget(x_607, x_464);
x_630 = lean_unsigned_to_nat(1u);
x_631 = lean_array_fget(x_607, x_630);
lean_dec(x_607);
x_502 = x_629;
x_503 = x_631;
x_504 = x_7;
goto block_512;
}
}
}
}
else
{
lean_object* x_632; uint8_t x_633; 
lean_dec_ref(x_610);
x_632 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
x_633 = lean_string_dec_eq(x_609, x_632);
lean_dec_ref(x_609);
if (x_633 == 0)
{
lean_dec(x_607);
lean_dec(x_87);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_634; lean_object* x_635; uint8_t x_636; 
x_634 = lean_array_get_size(x_607);
x_635 = lean_unsigned_to_nat(1u);
x_636 = lean_nat_dec_eq(x_634, x_635);
lean_dec(x_634);
if (x_636 == 0)
{
lean_dec(x_607);
lean_dec(x_87);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_637; 
lean_free_object(x_602);
x_637 = lean_array_fget(x_607, x_464);
lean_dec(x_607);
x_513 = x_637;
x_514 = x_7;
goto block_520;
}
}
}
}
else
{
lean_object* x_638; uint8_t x_639; 
lean_dec_ref(x_610);
lean_dec(x_87);
x_638 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_639 = lean_string_dec_eq(x_609, x_638);
lean_dec_ref(x_609);
if (x_639 == 0)
{
lean_dec(x_607);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_640; lean_object* x_641; uint8_t x_642; 
x_640 = lean_array_get_size(x_607);
x_641 = lean_unsigned_to_nat(6u);
x_642 = lean_nat_dec_eq(x_640, x_641);
lean_dec(x_640);
if (x_642 == 0)
{
lean_dec(x_607);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; 
x_643 = lean_unsigned_to_nat(4u);
x_644 = lean_array_fget(x_607, x_643);
x_645 = lean_unsigned_to_nat(5u);
x_646 = lean_array_fget(x_607, x_645);
lean_dec(x_607);
x_647 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
x_648 = l_Lean_Expr_const___override(x_647, x_468);
x_649 = l_Lean_mkAppB(x_648, x_644, x_646);
x_650 = l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(x_649, x_490);
if (x_650 == 0)
{
lean_object* x_651; 
lean_ctor_set_tag(x_602, 1);
lean_ctor_set(x_602, 1, x_490);
lean_ctor_set(x_602, 0, x_649);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_602);
lean_ctor_set(x_651, 1, x_7);
return x_651;
}
else
{
lean_dec_ref(x_649);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; 
x_652 = lean_ctor_get(x_602, 1);
lean_inc(x_652);
lean_dec(x_602);
x_653 = lean_ctor_get(x_603, 1);
lean_inc_ref(x_653);
lean_dec_ref(x_603);
x_654 = lean_ctor_get(x_604, 1);
lean_inc_ref(x_654);
lean_dec_ref(x_604);
x_655 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_656 = lean_string_dec_eq(x_654, x_655);
if (x_656 == 0)
{
uint8_t x_657; 
x_657 = lean_string_dec_eq(x_654, x_470);
if (x_657 == 0)
{
lean_object* x_658; uint8_t x_659; 
lean_dec(x_87);
x_658 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
x_659 = lean_string_dec_eq(x_654, x_658);
if (x_659 == 0)
{
lean_object* x_660; uint8_t x_661; 
x_660 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
x_661 = lean_string_dec_eq(x_654, x_660);
lean_dec_ref(x_654);
if (x_661 == 0)
{
lean_object* x_662; 
lean_dec_ref(x_653);
lean_dec(x_652);
x_662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_662, 0, x_490);
lean_ctor_set(x_662, 1, x_7);
return x_662;
}
else
{
lean_object* x_663; uint8_t x_664; 
x_663 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89;
x_664 = lean_string_dec_eq(x_653, x_663);
lean_dec_ref(x_653);
if (x_664 == 0)
{
lean_object* x_665; 
lean_dec(x_652);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_490);
lean_ctor_set(x_665, 1, x_7);
return x_665;
}
else
{
lean_object* x_666; uint8_t x_667; 
x_666 = lean_array_get_size(x_652);
x_667 = lean_nat_dec_eq(x_666, x_484);
lean_dec(x_666);
if (x_667 == 0)
{
lean_object* x_668; 
lean_dec(x_652);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_490);
lean_ctor_set(x_668, 1, x_7);
return x_668;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_array_fget(x_652, x_464);
x_670 = lean_unsigned_to_nat(1u);
x_671 = lean_array_fget(x_652, x_670);
lean_dec(x_652);
x_491 = x_669;
x_492 = x_671;
x_493 = x_7;
goto block_501;
}
}
}
}
else
{
lean_object* x_672; uint8_t x_673; 
lean_dec_ref(x_654);
x_672 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
x_673 = lean_string_dec_eq(x_653, x_672);
lean_dec_ref(x_653);
if (x_673 == 0)
{
lean_object* x_674; 
lean_dec(x_652);
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_490);
lean_ctor_set(x_674, 1, x_7);
return x_674;
}
else
{
lean_object* x_675; uint8_t x_676; 
x_675 = lean_array_get_size(x_652);
x_676 = lean_nat_dec_eq(x_675, x_484);
lean_dec(x_675);
if (x_676 == 0)
{
lean_object* x_677; 
lean_dec(x_652);
x_677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_677, 0, x_490);
lean_ctor_set(x_677, 1, x_7);
return x_677;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_array_fget(x_652, x_464);
x_679 = lean_unsigned_to_nat(1u);
x_680 = lean_array_fget(x_652, x_679);
lean_dec(x_652);
x_502 = x_678;
x_503 = x_680;
x_504 = x_7;
goto block_512;
}
}
}
}
else
{
lean_object* x_681; uint8_t x_682; 
lean_dec_ref(x_654);
x_681 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
x_682 = lean_string_dec_eq(x_653, x_681);
lean_dec_ref(x_653);
if (x_682 == 0)
{
lean_object* x_683; 
lean_dec(x_652);
lean_dec(x_87);
x_683 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_683, 0, x_490);
lean_ctor_set(x_683, 1, x_7);
return x_683;
}
else
{
lean_object* x_684; lean_object* x_685; uint8_t x_686; 
x_684 = lean_array_get_size(x_652);
x_685 = lean_unsigned_to_nat(1u);
x_686 = lean_nat_dec_eq(x_684, x_685);
lean_dec(x_684);
if (x_686 == 0)
{
lean_object* x_687; 
lean_dec(x_652);
lean_dec(x_87);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_490);
lean_ctor_set(x_687, 1, x_7);
return x_687;
}
else
{
lean_object* x_688; 
x_688 = lean_array_fget(x_652, x_464);
lean_dec(x_652);
x_513 = x_688;
x_514 = x_7;
goto block_520;
}
}
}
}
else
{
lean_object* x_689; uint8_t x_690; 
lean_dec_ref(x_654);
lean_dec(x_87);
x_689 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_690 = lean_string_dec_eq(x_653, x_689);
lean_dec_ref(x_653);
if (x_690 == 0)
{
lean_object* x_691; 
lean_dec(x_652);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_490);
lean_ctor_set(x_691, 1, x_7);
return x_691;
}
else
{
lean_object* x_692; lean_object* x_693; uint8_t x_694; 
x_692 = lean_array_get_size(x_652);
x_693 = lean_unsigned_to_nat(6u);
x_694 = lean_nat_dec_eq(x_692, x_693);
lean_dec(x_692);
if (x_694 == 0)
{
lean_object* x_695; 
lean_dec(x_652);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_490);
lean_ctor_set(x_695, 1, x_7);
return x_695;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; 
x_696 = lean_unsigned_to_nat(4u);
x_697 = lean_array_fget(x_652, x_696);
x_698 = lean_unsigned_to_nat(5u);
x_699 = lean_array_fget(x_652, x_698);
lean_dec(x_652);
x_700 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
x_701 = l_Lean_Expr_const___override(x_700, x_468);
x_702 = l_Lean_mkAppB(x_701, x_697, x_699);
x_703 = l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(x_702, x_490);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; 
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_490);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_7);
return x_705;
}
else
{
lean_object* x_706; 
lean_dec_ref(x_702);
x_706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_706, 0, x_490);
lean_ctor_set(x_706, 1, x_7);
return x_706;
}
}
}
}
}
}
else
{
uint8_t x_707; 
lean_dec_ref(x_604);
lean_dec_ref(x_603);
lean_dec(x_87);
x_707 = !lean_is_exclusive(x_602);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; 
x_708 = lean_ctor_get(x_602, 1);
lean_dec(x_708);
x_709 = lean_ctor_get(x_602, 0);
lean_dec(x_709);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_710; 
lean_dec(x_602);
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_490);
lean_ctor_set(x_710, 1, x_7);
return x_710;
}
}
}
else
{
uint8_t x_711; 
lean_dec(x_604);
lean_dec_ref(x_603);
lean_dec(x_87);
x_711 = !lean_is_exclusive(x_602);
if (x_711 == 0)
{
lean_object* x_712; lean_object* x_713; 
x_712 = lean_ctor_get(x_602, 1);
lean_dec(x_712);
x_713 = lean_ctor_get(x_602, 0);
lean_dec(x_713);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_714; 
lean_dec(x_602);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_490);
lean_ctor_set(x_714, 1, x_7);
return x_714;
}
}
}
else
{
uint8_t x_715; 
lean_dec(x_603);
lean_dec(x_87);
x_715 = !lean_is_exclusive(x_602);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; 
x_716 = lean_ctor_get(x_602, 1);
lean_dec(x_716);
x_717 = lean_ctor_get(x_602, 0);
lean_dec(x_717);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 0, x_490);
return x_602;
}
else
{
lean_object* x_718; 
lean_dec(x_602);
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_490);
lean_ctor_set(x_718, 1, x_7);
return x_718;
}
}
}
block_501:
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_494 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84;
x_495 = l_Lean_Expr_const___override(x_494, x_468);
x_496 = l_Lean_mkAppB(x_495, x_491, x_492);
x_497 = l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(x_496, x_490);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; 
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_490);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_493);
return x_499;
}
else
{
lean_object* x_500; 
lean_dec_ref(x_496);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_490);
lean_ctor_set(x_500, 1, x_493);
return x_500;
}
}
block_512:
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_505 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
x_506 = l_Lean_Expr_const___override(x_505, x_468);
x_507 = l_Lean_mkAppB(x_506, x_502, x_503);
x_508 = l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(x_507, x_490);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_490);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_504);
return x_510;
}
else
{
lean_object* x_511; 
lean_dec_ref(x_507);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_490);
lean_ctor_set(x_511, 1, x_504);
return x_511;
}
}
block_520:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_515 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
x_516 = l_Lean_Expr_const___override(x_515, x_468);
lean_inc_ref(x_513);
x_517 = l_Lean_Expr_app___override(x_516, x_513);
x_518 = l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(x_517, x_490);
if (x_518 == 0)
{
lean_object* x_519; 
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_490);
x_471 = x_513;
x_472 = x_514;
x_473 = x_519;
goto block_481;
}
else
{
lean_dec_ref(x_517);
x_471 = x_513;
x_472 = x_514;
x_473 = x_490;
goto block_481;
}
}
}
else
{
lean_dec_ref(x_468);
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
}
block_481:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
x_474 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
x_475 = l_Lean_Expr_const___override(x_474, x_468);
x_476 = l_Lean_Expr_app___override(x_475, x_471);
x_477 = l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(x_476, x_473);
if (x_477 == 0)
{
lean_object* x_478; lean_object* x_479; 
if (lean_is_scalar(x_87)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_87;
 lean_ctor_set_tag(x_478, 1);
}
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_473);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_472);
return x_479;
}
else
{
lean_object* x_480; 
lean_dec_ref(x_476);
if (lean_is_scalar(x_87)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_87;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_472);
return x_480;
}
}
}
else
{
lean_dec_ref(x_466);
lean_dec_ref(x_465);
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
}
else
{
lean_dec(x_466);
lean_dec_ref(x_465);
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
}
else
{
lean_dec_ref(x_465);
lean_dec(x_87);
lean_dec(x_86);
x_16 = x_7;
goto block_19;
}
}
}
}
}
else
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = x_7;
goto block_19;
}
}
default: 
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = x_7;
goto block_19;
}
}
}
else
{
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = x_7;
goto block_19;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_1, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_analyzeAtom(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2_spec__2___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_1, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = lean_infer_type(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_23 = lean_infer_type(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_22;
x_2 = x_26;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofExpr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
static double _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9_spec__9(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("omega", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_lookup___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("New facts: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("New atom: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_lookup___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_st_ref_get(x_3, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_30 = l_Lean_Meta_Canonicalizer_canon(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = lean_array_get_size(x_35);
x_38 = l_Lean_Expr_hash(x_33);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_105 = lean_usize_sub(x_46, x_47);
x_106 = lean_usize_land(x_45, x_105);
x_107 = lean_array_uget(x_35, x_106);
lean_dec_ref(x_35);
x_108 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_33, x_107);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_free_object(x_30);
x_109 = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
x_197 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_109, x_9, x_34);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; 
lean_free_object(x_28);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec_ref(x_197);
x_110 = x_2;
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_200;
goto block_196;
}
else
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_197);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_197, 1);
x_203 = lean_ctor_get(x_197, 0);
lean_dec(x_203);
x_204 = l_Lean_Elab_Tactic_Omega_lookup___closed__6;
lean_inc(x_33);
x_205 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_197, 7);
lean_ctor_set(x_197, 1, x_205);
lean_ctor_set(x_197, 0, x_204);
x_206 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_206);
lean_ctor_set(x_28, 0, x_197);
x_207 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_109, x_28, x_7, x_8, x_9, x_10, x_202);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec_ref(x_207);
x_110 = x_2;
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_208;
goto block_196;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_197, 1);
lean_inc(x_209);
lean_dec(x_197);
x_210 = l_Lean_Elab_Tactic_Omega_lookup___closed__6;
lean_inc(x_33);
x_211 = l_Lean_MessageData_ofExpr(x_33);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_213);
lean_ctor_set(x_28, 0, x_212);
x_214 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_109, x_28, x_7, x_8, x_9, x_10, x_209);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec_ref(x_214);
x_110 = x_2;
x_111 = x_3;
x_112 = x_4;
x_113 = x_5;
x_114 = x_6;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_215;
goto block_196;
}
}
block_196:
{
lean_object* x_120; 
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc(x_33);
x_120 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_33, x_112, x_115, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_109, x_117, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec_ref(x_123);
x_48 = x_121;
x_49 = x_111;
x_50 = x_126;
goto block_104;
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_123);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_ctor_get(x_123, 1);
x_129 = lean_ctor_get(x_123, 0);
lean_dec(x_129);
x_130 = l_List_isEmpty___redArg(x_121);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_109, x_117, x_128);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_free_object(x_123);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec_ref(x_131);
x_48 = x_121;
x_49 = x_111;
x_50 = x_134;
goto block_104;
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_131);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_131, 1);
x_137 = lean_ctor_get(x_131, 0);
lean_dec(x_137);
x_138 = lean_box(0);
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc(x_121);
x_139 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(x_121, x_138, x_115, x_116, x_117, x_118, x_136);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec_ref(x_139);
x_142 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_143 = l_List_mapTR_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__8(x_140, x_138);
x_144 = l_Lean_MessageData_ofList(x_143);
lean_ctor_set_tag(x_131, 7);
lean_ctor_set(x_131, 1, x_144);
lean_ctor_set(x_131, 0, x_142);
x_145 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
lean_ctor_set_tag(x_123, 7);
lean_ctor_set(x_123, 1, x_145);
lean_ctor_set(x_123, 0, x_131);
x_146 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_109, x_123, x_115, x_116, x_117, x_118, x_141);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
x_48 = x_121;
x_49 = x_111;
x_50 = x_147;
goto block_104;
}
else
{
uint8_t x_148; 
lean_free_object(x_131);
lean_free_object(x_123);
lean_dec(x_121);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_33);
x_148 = !lean_is_exclusive(x_139);
if (x_148 == 0)
{
return x_139;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_139, 0);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_139);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_box(0);
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc(x_121);
x_154 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(x_121, x_153, x_115, x_116, x_117, x_118, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
x_157 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_158 = l_List_mapTR_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__8(x_155, x_153);
x_159 = l_Lean_MessageData_ofList(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
lean_ctor_set_tag(x_123, 7);
lean_ctor_set(x_123, 1, x_161);
lean_ctor_set(x_123, 0, x_160);
x_162 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_109, x_123, x_115, x_116, x_117, x_118, x_156);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec_ref(x_162);
x_48 = x_121;
x_49 = x_111;
x_50 = x_163;
goto block_104;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_free_object(x_123);
lean_dec(x_121);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_33);
x_164 = lean_ctor_get(x_154, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_154, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_166 = x_154;
} else {
 lean_dec_ref(x_154);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
}
else
{
lean_free_object(x_123);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_48 = x_121;
x_49 = x_111;
x_50 = x_128;
goto block_104;
}
}
else
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_123, 1);
lean_inc(x_168);
lean_dec(x_123);
x_169 = l_List_isEmpty___redArg(x_121);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_109, x_117, x_168);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec_ref(x_170);
x_48 = x_121;
x_49 = x_111;
x_50 = x_173;
goto block_104;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_175 = x_170;
} else {
 lean_dec_ref(x_170);
 x_175 = lean_box(0);
}
x_176 = lean_box(0);
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc(x_121);
x_177 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(x_121, x_176, x_115, x_116, x_117, x_118, x_174);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec_ref(x_177);
x_180 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_181 = l_List_mapTR_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__8(x_178, x_176);
x_182 = l_Lean_MessageData_ofList(x_181);
if (lean_is_scalar(x_175)) {
 x_183 = lean_alloc_ctor(7, 2, 0);
} else {
 x_183 = x_175;
 lean_ctor_set_tag(x_183, 7);
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_109, x_185, x_115, x_116, x_117, x_118, x_179);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec_ref(x_186);
x_48 = x_121;
x_49 = x_111;
x_50 = x_187;
goto block_104;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_175);
lean_dec(x_121);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_33);
x_188 = lean_ctor_get(x_177, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_177, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_190 = x_177;
} else {
 lean_dec_ref(x_177);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
x_48 = x_121;
x_49 = x_111;
x_50 = x_168;
goto block_104;
}
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_33);
x_192 = !lean_is_exclusive(x_120);
if (x_192 == 0)
{
return x_120;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_120, 0);
x_194 = lean_ctor_get(x_120, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_120);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_216 = lean_ctor_get(x_108, 0);
lean_inc(x_216);
lean_dec_ref(x_108);
x_217 = lean_box(0);
lean_ctor_set(x_28, 1, x_217);
lean_ctor_set(x_28, 0, x_216);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
block_104:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_take(x_49, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; size_t x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = lean_usize_sub(x_58, x_47);
x_60 = lean_usize_land(x_45, x_59);
x_61 = lean_array_uget(x_56, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_33, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_55, x_63);
lean_inc(x_55);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_33);
lean_ctor_set(x_65, 1, x_55);
lean_ctor_set(x_65, 2, x_61);
x_66 = lean_array_uset(x_56, x_60, x_65);
x_67 = lean_unsigned_to_nat(4u);
x_68 = lean_nat_mul(x_64, x_67);
x_69 = lean_unsigned_to_nat(3u);
x_70 = lean_nat_div(x_68, x_69);
lean_dec(x_68);
x_71 = lean_array_get_size(x_66);
x_72 = lean_nat_dec_le(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_66);
lean_ctor_set(x_52, 1, x_73);
lean_ctor_set(x_52, 0, x_64);
x_12 = x_49;
x_13 = x_55;
x_14 = x_53;
x_15 = x_48;
x_16 = x_52;
goto block_26;
}
else
{
lean_ctor_set(x_52, 1, x_66);
lean_ctor_set(x_52, 0, x_64);
x_12 = x_49;
x_13 = x_55;
x_14 = x_53;
x_15 = x_48;
x_16 = x_52;
goto block_26;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_box(0);
x_75 = lean_array_uset(x_56, x_60, x_74);
lean_inc(x_55);
x_76 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(x_33, x_55, x_61);
x_77 = lean_array_uset(x_75, x_60, x_76);
lean_inc(x_55);
lean_ctor_set(x_52, 1, x_77);
x_12 = x_49;
x_13 = x_55;
x_14 = x_53;
x_15 = x_48;
x_16 = x_52;
goto block_26;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_52, 0);
x_79 = lean_ctor_get(x_52, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_52);
x_80 = lean_array_get_size(x_79);
x_81 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_82 = lean_usize_sub(x_81, x_47);
x_83 = lean_usize_land(x_45, x_82);
x_84 = lean_array_uget(x_79, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_33, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_78, x_86);
lean_inc(x_78);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_33);
lean_ctor_set(x_88, 1, x_78);
lean_ctor_set(x_88, 2, x_84);
x_89 = lean_array_uset(x_79, x_83, x_88);
x_90 = lean_unsigned_to_nat(4u);
x_91 = lean_nat_mul(x_87, x_90);
x_92 = lean_unsigned_to_nat(3u);
x_93 = lean_nat_div(x_91, x_92);
lean_dec(x_91);
x_94 = lean_array_get_size(x_89);
x_95 = lean_nat_dec_le(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_12 = x_49;
x_13 = x_78;
x_14 = x_53;
x_15 = x_48;
x_16 = x_97;
goto block_26;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
x_12 = x_49;
x_13 = x_78;
x_14 = x_53;
x_15 = x_48;
x_16 = x_98;
goto block_26;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_box(0);
x_100 = lean_array_uset(x_79, x_83, x_99);
lean_inc(x_78);
x_101 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(x_33, x_78, x_84);
x_102 = lean_array_uset(x_100, x_83, x_101);
lean_inc(x_78);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_78);
lean_ctor_set(x_103, 1, x_102);
x_12 = x_49;
x_13 = x_78;
x_14 = x_53;
x_15 = x_48;
x_16 = x_103;
goto block_26;
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; uint64_t x_226; uint64_t x_227; uint64_t x_228; size_t x_229; size_t x_230; size_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; size_t x_266; size_t x_267; lean_object* x_268; lean_object* x_269; 
x_218 = lean_ctor_get(x_30, 0);
x_219 = lean_ctor_get(x_30, 1);
x_220 = lean_ctor_get(x_28, 1);
lean_inc(x_220);
lean_dec(x_28);
x_221 = lean_array_get_size(x_220);
x_222 = l_Lean_Expr_hash(x_218);
x_223 = 32;
x_224 = lean_uint64_shift_right(x_222, x_223);
x_225 = lean_uint64_xor(x_222, x_224);
x_226 = 16;
x_227 = lean_uint64_shift_right(x_225, x_226);
x_228 = lean_uint64_xor(x_225, x_227);
x_229 = lean_uint64_to_usize(x_228);
x_230 = lean_usize_of_nat(x_221);
lean_dec(x_221);
x_231 = 1;
x_266 = lean_usize_sub(x_230, x_231);
x_267 = lean_usize_land(x_229, x_266);
x_268 = lean_array_uget(x_220, x_267);
lean_dec_ref(x_220);
x_269 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_218, x_268);
lean_dec(x_268);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
lean_free_object(x_30);
x_270 = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
x_318 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_270, x_9, x_219);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_unbox(x_319);
lean_dec(x_319);
if (x_320 == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
lean_dec_ref(x_318);
x_271 = x_2;
x_272 = x_3;
x_273 = x_4;
x_274 = x_5;
x_275 = x_6;
x_276 = x_7;
x_277 = x_8;
x_278 = x_9;
x_279 = x_10;
x_280 = x_321;
goto block_317;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_323 = x_318;
} else {
 lean_dec_ref(x_318);
 x_323 = lean_box(0);
}
x_324 = l_Lean_Elab_Tactic_Omega_lookup___closed__6;
lean_inc(x_218);
x_325 = l_Lean_MessageData_ofExpr(x_218);
if (lean_is_scalar(x_323)) {
 x_326 = lean_alloc_ctor(7, 2, 0);
} else {
 x_326 = x_323;
 lean_ctor_set_tag(x_326, 7);
}
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_270, x_328, x_7, x_8, x_9, x_10, x_322);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec_ref(x_329);
x_271 = x_2;
x_272 = x_3;
x_273 = x_4;
x_274 = x_5;
x_275 = x_6;
x_276 = x_7;
x_277 = x_8;
x_278 = x_9;
x_279 = x_10;
x_280 = x_330;
goto block_317;
}
block_317:
{
lean_object* x_281; 
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc_ref(x_276);
lean_inc(x_218);
x_281 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_218, x_273, x_276, x_277, x_278, x_279, x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec_ref(x_281);
x_284 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_270, x_278, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_unbox(x_285);
lean_dec(x_285);
if (x_286 == 0)
{
lean_object* x_287; 
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_dec_ref(x_284);
x_232 = x_282;
x_233 = x_272;
x_234 = x_287;
goto block_265;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_ctor_get(x_284, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_289 = x_284;
} else {
 lean_dec_ref(x_284);
 x_289 = lean_box(0);
}
x_290 = l_List_isEmpty___redArg(x_282);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_291 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_270, x_278, x_288);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_289);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec_ref(x_291);
x_232 = x_282;
x_233 = x_272;
x_234 = x_294;
goto block_265;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_296 = x_291;
} else {
 lean_dec_ref(x_291);
 x_296 = lean_box(0);
}
x_297 = lean_box(0);
lean_inc(x_279);
lean_inc_ref(x_278);
lean_inc(x_277);
lean_inc_ref(x_276);
lean_inc(x_282);
x_298 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(x_282, x_297, x_276, x_277, x_278, x_279, x_295);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec_ref(x_298);
x_301 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_302 = l_List_mapTR_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__8(x_299, x_297);
x_303 = l_Lean_MessageData_ofList(x_302);
if (lean_is_scalar(x_296)) {
 x_304 = lean_alloc_ctor(7, 2, 0);
} else {
 x_304 = x_296;
 lean_ctor_set_tag(x_304, 7);
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_289)) {
 x_306 = lean_alloc_ctor(7, 2, 0);
} else {
 x_306 = x_289;
 lean_ctor_set_tag(x_306, 7);
}
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_270, x_306, x_276, x_277, x_278, x_279, x_300);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
lean_dec_ref(x_307);
x_232 = x_282;
x_233 = x_272;
x_234 = x_308;
goto block_265;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_296);
lean_dec(x_289);
lean_dec(x_282);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec(x_218);
x_309 = lean_ctor_get(x_298, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_298, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_311 = x_298;
} else {
 lean_dec_ref(x_298);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
}
else
{
lean_dec(x_289);
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
x_232 = x_282;
x_233 = x_272;
x_234 = x_288;
goto block_265;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_279);
lean_dec_ref(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec(x_218);
x_313 = lean_ctor_get(x_281, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_281, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_315 = x_281;
} else {
 lean_dec_ref(x_281);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_218);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_331 = lean_ctor_get(x_269, 0);
lean_inc(x_331);
lean_dec_ref(x_269);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set(x_30, 0, x_333);
return x_30;
}
block_265:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; size_t x_242; size_t x_243; size_t x_244; lean_object* x_245; uint8_t x_246; 
x_235 = lean_st_ref_take(x_233, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 1);
lean_inc_ref(x_239);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_240 = x_236;
} else {
 lean_dec_ref(x_236);
 x_240 = lean_box(0);
}
x_241 = lean_array_get_size(x_239);
x_242 = lean_usize_of_nat(x_241);
lean_dec(x_241);
x_243 = lean_usize_sub(x_242, x_231);
x_244 = lean_usize_land(x_229, x_243);
x_245 = lean_array_uget(x_239, x_244);
x_246 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_218, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_add(x_238, x_247);
lean_inc(x_238);
x_249 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_249, 0, x_218);
lean_ctor_set(x_249, 1, x_238);
lean_ctor_set(x_249, 2, x_245);
x_250 = lean_array_uset(x_239, x_244, x_249);
x_251 = lean_unsigned_to_nat(4u);
x_252 = lean_nat_mul(x_248, x_251);
x_253 = lean_unsigned_to_nat(3u);
x_254 = lean_nat_div(x_252, x_253);
lean_dec(x_252);
x_255 = lean_array_get_size(x_250);
x_256 = lean_nat_dec_le(x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_250);
if (lean_is_scalar(x_240)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_240;
}
lean_ctor_set(x_258, 0, x_248);
lean_ctor_set(x_258, 1, x_257);
x_12 = x_233;
x_13 = x_238;
x_14 = x_237;
x_15 = x_232;
x_16 = x_258;
goto block_26;
}
else
{
lean_object* x_259; 
if (lean_is_scalar(x_240)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_240;
}
lean_ctor_set(x_259, 0, x_248);
lean_ctor_set(x_259, 1, x_250);
x_12 = x_233;
x_13 = x_238;
x_14 = x_237;
x_15 = x_232;
x_16 = x_259;
goto block_26;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_box(0);
x_261 = lean_array_uset(x_239, x_244, x_260);
lean_inc(x_238);
x_262 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(x_218, x_238, x_245);
x_263 = lean_array_uset(x_261, x_244, x_262);
lean_inc(x_238);
if (lean_is_scalar(x_240)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_240;
}
lean_ctor_set(x_264, 0, x_238);
lean_ctor_set(x_264, 1, x_263);
x_12 = x_233;
x_13 = x_238;
x_14 = x_237;
x_15 = x_232;
x_16 = x_264;
goto block_26;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint64_t x_339; uint64_t x_340; uint64_t x_341; uint64_t x_342; uint64_t x_343; uint64_t x_344; uint64_t x_345; size_t x_346; size_t x_347; size_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; size_t x_383; size_t x_384; lean_object* x_385; lean_object* x_386; 
x_334 = lean_ctor_get(x_30, 0);
x_335 = lean_ctor_get(x_30, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_30);
x_336 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_336);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_337 = x_28;
} else {
 lean_dec_ref(x_28);
 x_337 = lean_box(0);
}
x_338 = lean_array_get_size(x_336);
x_339 = l_Lean_Expr_hash(x_334);
x_340 = 32;
x_341 = lean_uint64_shift_right(x_339, x_340);
x_342 = lean_uint64_xor(x_339, x_341);
x_343 = 16;
x_344 = lean_uint64_shift_right(x_342, x_343);
x_345 = lean_uint64_xor(x_342, x_344);
x_346 = lean_uint64_to_usize(x_345);
x_347 = lean_usize_of_nat(x_338);
lean_dec(x_338);
x_348 = 1;
x_383 = lean_usize_sub(x_347, x_348);
x_384 = lean_usize_land(x_346, x_383);
x_385 = lean_array_uget(x_336, x_384);
lean_dec_ref(x_336);
x_386 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_334, x_385);
lean_dec(x_385);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_387 = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
x_435 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_387, x_9, x_335);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_unbox(x_436);
lean_dec(x_436);
if (x_437 == 0)
{
lean_object* x_438; 
lean_dec(x_337);
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
lean_dec_ref(x_435);
x_388 = x_2;
x_389 = x_3;
x_390 = x_4;
x_391 = x_5;
x_392 = x_6;
x_393 = x_7;
x_394 = x_8;
x_395 = x_9;
x_396 = x_10;
x_397 = x_438;
goto block_434;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_439 = lean_ctor_get(x_435, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_440 = x_435;
} else {
 lean_dec_ref(x_435);
 x_440 = lean_box(0);
}
x_441 = l_Lean_Elab_Tactic_Omega_lookup___closed__6;
lean_inc(x_334);
x_442 = l_Lean_MessageData_ofExpr(x_334);
if (lean_is_scalar(x_440)) {
 x_443 = lean_alloc_ctor(7, 2, 0);
} else {
 x_443 = x_440;
 lean_ctor_set_tag(x_443, 7);
}
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
x_444 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_337)) {
 x_445 = lean_alloc_ctor(7, 2, 0);
} else {
 x_445 = x_337;
 lean_ctor_set_tag(x_445, 7);
}
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_387, x_445, x_7, x_8, x_9, x_10, x_439);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec_ref(x_446);
x_388 = x_2;
x_389 = x_3;
x_390 = x_4;
x_391 = x_5;
x_392 = x_6;
x_393 = x_7;
x_394 = x_8;
x_395 = x_9;
x_396 = x_10;
x_397 = x_447;
goto block_434;
}
block_434:
{
lean_object* x_398; 
lean_inc(x_396);
lean_inc_ref(x_395);
lean_inc(x_394);
lean_inc_ref(x_393);
lean_inc(x_334);
x_398 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_334, x_390, x_393, x_394, x_395, x_396, x_397);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec_ref(x_398);
x_401 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_387, x_395, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_unbox(x_402);
lean_dec(x_402);
if (x_403 == 0)
{
lean_object* x_404; 
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_394);
lean_dec_ref(x_393);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec_ref(x_401);
x_349 = x_399;
x_350 = x_389;
x_351 = x_404;
goto block_382;
}
else
{
lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_406 = x_401;
} else {
 lean_dec_ref(x_401);
 x_406 = lean_box(0);
}
x_407 = l_List_isEmpty___redArg(x_399);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; 
x_408 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_387, x_395, x_405);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_unbox(x_409);
lean_dec(x_409);
if (x_410 == 0)
{
lean_object* x_411; 
lean_dec(x_406);
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_394);
lean_dec_ref(x_393);
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_411);
lean_dec_ref(x_408);
x_349 = x_399;
x_350 = x_389;
x_351 = x_411;
goto block_382;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_412 = lean_ctor_get(x_408, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_413 = x_408;
} else {
 lean_dec_ref(x_408);
 x_413 = lean_box(0);
}
x_414 = lean_box(0);
lean_inc(x_396);
lean_inc_ref(x_395);
lean_inc(x_394);
lean_inc_ref(x_393);
lean_inc(x_399);
x_415 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___redArg(x_399, x_414, x_393, x_394, x_395, x_396, x_412);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec_ref(x_415);
x_418 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_419 = l_List_mapTR_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__8(x_416, x_414);
x_420 = l_Lean_MessageData_ofList(x_419);
if (lean_is_scalar(x_413)) {
 x_421 = lean_alloc_ctor(7, 2, 0);
} else {
 x_421 = x_413;
 lean_ctor_set_tag(x_421, 7);
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_420);
x_422 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_406)) {
 x_423 = lean_alloc_ctor(7, 2, 0);
} else {
 x_423 = x_406;
 lean_ctor_set_tag(x_423, 7);
}
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
x_424 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_387, x_423, x_393, x_394, x_395, x_396, x_417);
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_394);
lean_dec_ref(x_393);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
lean_dec_ref(x_424);
x_349 = x_399;
x_350 = x_389;
x_351 = x_425;
goto block_382;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_413);
lean_dec(x_406);
lean_dec(x_399);
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_394);
lean_dec_ref(x_393);
lean_dec(x_334);
x_426 = lean_ctor_get(x_415, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_415, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_428 = x_415;
} else {
 lean_dec_ref(x_415);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
}
else
{
lean_dec(x_406);
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_394);
lean_dec_ref(x_393);
x_349 = x_399;
x_350 = x_389;
x_351 = x_405;
goto block_382;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_396);
lean_dec_ref(x_395);
lean_dec(x_394);
lean_dec_ref(x_393);
lean_dec(x_334);
x_430 = lean_ctor_get(x_398, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_398, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_432 = x_398;
} else {
 lean_dec_ref(x_398);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_334);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_448 = lean_ctor_get(x_386, 0);
lean_inc(x_448);
lean_dec_ref(x_386);
x_449 = lean_box(0);
if (lean_is_scalar(x_337)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_337;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_335);
return x_451;
}
block_382:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; size_t x_359; size_t x_360; size_t x_361; lean_object* x_362; uint8_t x_363; 
x_352 = lean_st_ref_take(x_350, x_351);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec_ref(x_352);
x_355 = lean_ctor_get(x_353, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_353, 1);
lean_inc_ref(x_356);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_357 = x_353;
} else {
 lean_dec_ref(x_353);
 x_357 = lean_box(0);
}
x_358 = lean_array_get_size(x_356);
x_359 = lean_usize_of_nat(x_358);
lean_dec(x_358);
x_360 = lean_usize_sub(x_359, x_348);
x_361 = lean_usize_land(x_346, x_360);
x_362 = lean_array_uget(x_356, x_361);
x_363 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_334, x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_364 = lean_unsigned_to_nat(1u);
x_365 = lean_nat_add(x_355, x_364);
lean_inc(x_355);
x_366 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_366, 0, x_334);
lean_ctor_set(x_366, 1, x_355);
lean_ctor_set(x_366, 2, x_362);
x_367 = lean_array_uset(x_356, x_361, x_366);
x_368 = lean_unsigned_to_nat(4u);
x_369 = lean_nat_mul(x_365, x_368);
x_370 = lean_unsigned_to_nat(3u);
x_371 = lean_nat_div(x_369, x_370);
lean_dec(x_369);
x_372 = lean_array_get_size(x_367);
x_373 = lean_nat_dec_le(x_371, x_372);
lean_dec(x_372);
lean_dec(x_371);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
x_374 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_367);
if (lean_is_scalar(x_357)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_357;
}
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_374);
x_12 = x_350;
x_13 = x_355;
x_14 = x_354;
x_15 = x_349;
x_16 = x_375;
goto block_26;
}
else
{
lean_object* x_376; 
if (lean_is_scalar(x_357)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_357;
}
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_367);
x_12 = x_350;
x_13 = x_355;
x_14 = x_354;
x_15 = x_349;
x_16 = x_376;
goto block_26;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_377 = lean_box(0);
x_378 = lean_array_uset(x_356, x_361, x_377);
lean_inc(x_355);
x_379 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_Omega_lookup_spec__5___redArg(x_334, x_355, x_362);
x_380 = lean_array_uset(x_378, x_361, x_379);
lean_inc(x_355);
if (lean_is_scalar(x_357)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_357;
}
lean_ctor_set(x_381, 0, x_355);
lean_ctor_set(x_381, 1, x_380);
x_12 = x_350;
x_13 = x_355;
x_14 = x_354;
x_15 = x_349;
x_16 = x_381;
goto block_26;
}
}
}
}
else
{
uint8_t x_452; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_452 = !lean_is_exclusive(x_30);
if (x_452 == 0)
{
return x_30;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_30, 0);
x_454 = lean_ctor_get(x_30, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_30);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
block_26:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_set(x_12, x_16, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Elab_Tactic_Omega_lookup_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_Omega_lookup_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__6(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__7(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9_spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_lookup(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
lean_object* initialize_Init_Omega_LinearCombo(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega_Logic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Omega_OmegaM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Omega_LinearCombo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega_Logic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Canonicalizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0);
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1);
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2);
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3);
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4);
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__5 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__5);
l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0 = _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0);
l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1);
l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5);
l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0 = _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0);
l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1 = _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44();
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93);
l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__0();
l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__1);
l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__9___redArg___closed__2);
l_Lean_Elab_Tactic_Omega_lookup___closed__0 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__0);
l_Lean_Elab_Tactic_Omega_lookup___closed__1 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__1);
l_Lean_Elab_Tactic_Omega_lookup___closed__2 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__2);
l_Lean_Elab_Tactic_Omega_lookup___closed__3 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__3);
l_Lean_Elab_Tactic_Omega_lookup___closed__4 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__4);
l_Lean_Elab_Tactic_Omega_lookup___closed__5 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__5);
l_Lean_Elab_Tactic_Omega_lookup___closed__6 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64;
static size_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12;
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static uint8_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__97;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_Omega_atoms_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__96;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2;
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__98;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16;
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
static lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81;
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__95;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34;
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__7;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_int_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2;
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__6;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78;
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__4;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23;
static double l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(size_t, size_t, lean_object*);
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
lean_dec(x_12);
x_15 = lean_st_mk_ref(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
lean_dec(x_19);
x_22 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__6;
x_2 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_2);
x_10 = lean_box(3);
x_11 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__7;
x_12 = lean_unbox(x_10);
x_13 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(x_9, x_12, x_11, x_3, x_4, x_5, x_6, x_7);
return x_13;
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
lean_dec(x_5);
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
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_cfg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = lean_box(0);
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
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_mk_empty_array_with_capacity(x_33);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_34);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_37);
lean_dec(x_34);
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
lean_dec(x_34);
x_25 = x_35;
goto block_32;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_42 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(x_34, x_40, x_41, x_35);
lean_dec(x_34);
x_25 = x_42;
goto block_32;
}
}
block_12:
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(x_8, x_9, x_7);
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
lean_dec(x_13);
x_17 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_14, x_15, x_16);
lean_dec(x_16);
x_7 = x_17;
goto block_12;
}
block_24:
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_22, x_20);
if (x_23 == 0)
{
lean_dec(x_20);
lean_inc(x_22);
x_13 = x_19;
x_14 = x_21;
x_15 = x_22;
x_16 = x_22;
goto block_18;
}
else
{
x_13 = x_19;
x_14 = x_21;
x_15 = x_22;
x_16 = x_20;
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
x_19 = x_26;
x_20 = x_30;
x_21 = x_25;
x_22 = x_30;
goto block_24;
}
else
{
x_19 = x_26;
x_20 = x_30;
x_21 = x_25;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Omega_atoms_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_Elab_Tactic_Omega_atoms_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_Omega_atoms_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
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
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atoms(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_7);
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
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atomsList(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_Omega_atomsCoeffs(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_12);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_st_ref_take(x_3, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_set(x_3, x_13, x_26);
lean_dec(x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_2, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
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
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
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
lean_inc(x_1);
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
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Lean_Expr_nat_x3f(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec(x_7);
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
lean_dec(x_1);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Expr_nat_x3f(x_1);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_Lean_Expr_nat_x3f(x_1);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = l_Lean_Expr_nat_x3f(x_1);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc(x_1);
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
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Lean_Expr_int_x3f(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec(x_7);
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
lean_dec(x_1);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = l_Lean_Expr_int_x3f(x_1);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Expr_int_x3f(x_1);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
x_31 = l_Lean_Expr_int_x3f(x_1);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
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
lean_dec(x_8);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_21 = l_Lean_Expr_nat_x3f(x_1);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_23 = lean_string_dec_eq(x_7, x_22);
lean_dec(x_7);
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
lean_dec(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__0___boxed), 2, 0);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_array_fget(x_6, x_30);
x_32 = lean_unsigned_to_nat(5u);
x_33 = lean_array_fget(x_6, x_32);
lean_dec(x_6);
x_34 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_29, x_31, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_8);
x_35 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_36 = lean_string_dec_eq(x_7, x_35);
lean_dec(x_7);
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
lean_dec(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__1___boxed), 2, 0);
x_43 = lean_unsigned_to_nat(4u);
x_44 = lean_array_fget(x_6, x_43);
x_45 = lean_unsigned_to_nat(5u);
x_46 = lean_array_fget(x_6, x_45);
lean_dec(x_6);
x_47 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_42, x_44, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_8);
x_48 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_49 = lean_string_dec_eq(x_7, x_48);
lean_dec(x_7);
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
lean_dec(x_1);
x_55 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__2___boxed), 2, 0);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_array_fget(x_6, x_56);
x_58 = lean_unsigned_to_nat(5u);
x_59 = lean_array_fget(x_6, x_58);
lean_dec(x_6);
x_60 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_55, x_57, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_8);
x_61 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_62 = lean_string_dec_eq(x_7, x_61);
lean_dec(x_7);
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
lean_dec(x_1);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__3___boxed), 2, 0);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_array_fget(x_6, x_69);
x_71 = lean_unsigned_to_nat(5u);
x_72 = lean_array_fget(x_6, x_71);
lean_dec(x_6);
x_73 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_68, x_70, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_8);
x_74 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
x_75 = lean_string_dec_eq(x_7, x_74);
lean_dec(x_7);
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
lean_dec(x_1);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundNat_x3f___lam__4___boxed), 2, 0);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_array_fget(x_6, x_82);
x_84 = lean_unsigned_to_nat(5u);
x_85 = lean_array_fget(x_6, x_84);
lean_dec(x_6);
x_86 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_81, x_83, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_8);
x_87 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_88 = lean_string_dec_eq(x_7, x_87);
lean_dec(x_7);
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
lean_dec(x_1);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = l_Lean_Expr_nat_x3f(x_1);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = l_Lean_Expr_nat_x3f(x_1);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
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
lean_dec(x_8);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_21 = l_Lean_Expr_int_x3f(x_1);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_23 = lean_string_dec_eq(x_7, x_22);
lean_dec(x_7);
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
lean_dec(x_1);
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
lean_dec(x_31);
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
lean_dec(x_8);
x_43 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_44 = lean_string_dec_eq(x_7, x_43);
lean_dec(x_7);
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
lean_dec(x_1);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__0___boxed), 2, 0);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_array_fget(x_6, x_51);
x_53 = lean_unsigned_to_nat(5u);
x_54 = lean_array_fget(x_6, x_53);
lean_dec(x_6);
x_55 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_50, x_52, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_8);
x_56 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_57 = lean_string_dec_eq(x_7, x_56);
lean_dec(x_7);
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
lean_dec(x_1);
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__1___boxed), 2, 0);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_array_fget(x_6, x_64);
x_66 = lean_unsigned_to_nat(5u);
x_67 = lean_array_fget(x_6, x_66);
lean_dec(x_6);
x_68 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_63, x_65, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_8);
x_69 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_70 = lean_string_dec_eq(x_7, x_69);
lean_dec(x_7);
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
lean_dec(x_1);
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__2___boxed), 2, 0);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_array_fget(x_6, x_77);
x_79 = lean_unsigned_to_nat(5u);
x_80 = lean_array_fget(x_6, x_79);
lean_dec(x_6);
x_81 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_76, x_78, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_8);
x_82 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
x_83 = lean_string_dec_eq(x_7, x_82);
lean_dec(x_7);
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
lean_dec(x_1);
x_89 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_groundInt_x3f___lam__3___boxed), 2, 0);
x_90 = lean_unsigned_to_nat(4u);
x_91 = lean_array_fget(x_6, x_90);
x_92 = lean_unsigned_to_nat(5u);
x_93 = lean_array_fget(x_6, x_92);
lean_dec(x_6);
x_94 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_89, x_91, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_95; uint8_t x_96; 
lean_dec(x_8);
x_95 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_96 = lean_string_dec_eq(x_7, x_95);
lean_dec(x_7);
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
lean_dec(x_1);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = l_Lean_Expr_int_x3f(x_1);
return x_112;
}
}
else
{
lean_object* x_113; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = l_Lean_Expr_int_x3f(x_1);
return x_113;
}
}
else
{
lean_object* x_114; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkEqRefl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_right", 12, 12);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_right", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_ofNat_nonneg", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTNat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
x_2 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_pos_of_pos", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48;
x_2 = lean_int_dec_le(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTInt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69;
x_5 = l_Lean_mkApp3(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_mul_ediv_self_add", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul_ediv_self_le", 16, 16);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isLt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg_le_natAbs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_natAbs", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("val", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natAbs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__95() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_sub_dichotomy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__95;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__97() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_nonneg", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__98() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__97;
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
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
lean_inc(x_34);
switch (lean_obj_tag(x_34)) {
case 0:
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
x_40 = lean_string_dec_eq(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_free_object(x_32);
lean_dec(x_36);
x_12 = x_7;
goto block_15;
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
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_fget(x_36, x_44);
x_46 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_47 = lean_expr_eqv(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_36);
x_48 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 0, x_48);
return x_32;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_array_fget(x_36, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_array_fget(x_36, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_array_fget(x_36, x_53);
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_array_fget(x_36, x_55);
lean_dec(x_36);
x_57 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_58 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
x_59 = l_Lean_mkApp5(x_58, x_45, x_50, x_52, x_54, x_56);
x_60 = l_Lean_Expr_hash(x_59);
x_61 = 32;
x_62 = lean_uint64_shift_right(x_60, x_61);
x_63 = lean_uint64_xor(x_60, x_62);
x_64 = 16;
x_65 = lean_uint64_shift_right(x_63, x_64);
x_66 = lean_uint64_xor(x_63, x_65);
x_67 = lean_uint64_to_usize(x_66);
x_68 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_69 = lean_usize_land(x_67, x_68);
x_70 = lean_array_uget(x_57, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_59, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_array_uset(x_57, x_69, x_73);
x_75 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_76 = lean_array_get_size(x_74);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_74);
lean_ctor_set(x_32, 1, x_78);
lean_ctor_set(x_32, 0, x_49);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_7);
return x_79;
}
else
{
lean_object* x_80; 
lean_ctor_set(x_32, 1, x_74);
lean_ctor_set(x_32, 0, x_49);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_32);
lean_ctor_set(x_80, 1, x_7);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_70);
lean_dec(x_59);
x_81 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 0, x_81);
return x_32;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_32, 1);
lean_inc(x_82);
lean_dec(x_32);
x_83 = lean_ctor_get(x_33, 1);
lean_inc(x_83);
lean_dec(x_33);
x_84 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
x_85 = lean_string_dec_eq(x_83, x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_dec(x_82);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_array_get_size(x_82);
x_87 = lean_unsigned_to_nat(5u);
x_88 = lean_nat_dec_eq(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_dec(x_82);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_array_fget(x_82, x_89);
x_91 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_92 = lean_expr_eqv(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_90);
lean_dec(x_82);
x_93 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_7);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; size_t x_113; size_t x_114; size_t x_115; lean_object* x_116; uint8_t x_117; 
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_array_fget(x_82, x_95);
x_97 = lean_unsigned_to_nat(2u);
x_98 = lean_array_fget(x_82, x_97);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_array_fget(x_82, x_99);
x_101 = lean_unsigned_to_nat(4u);
x_102 = lean_array_fget(x_82, x_101);
lean_dec(x_82);
x_103 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_104 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
x_105 = l_Lean_mkApp5(x_104, x_90, x_96, x_98, x_100, x_102);
x_106 = l_Lean_Expr_hash(x_105);
x_107 = 32;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = 16;
x_111 = lean_uint64_shift_right(x_109, x_110);
x_112 = lean_uint64_xor(x_109, x_111);
x_113 = lean_uint64_to_usize(x_112);
x_114 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_115 = lean_usize_land(x_113, x_114);
x_116 = lean_array_uget(x_103, x_115);
x_117 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_105, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_105);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_116);
x_120 = lean_array_uset(x_103, x_115, x_119);
x_121 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_122 = lean_array_get_size(x_120);
x_123 = lean_nat_dec_le(x_121, x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_120);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_95);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_7);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_95);
lean_ctor_set(x_127, 1, x_120);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_7);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_116);
lean_dec(x_105);
x_129 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
return x_130;
}
}
}
}
}
}
case 1:
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_34, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_132 = lean_ctor_get(x_32, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_133 = x_32;
} else {
 lean_dec_ref(x_32);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_33, 1);
lean_inc(x_134);
lean_dec(x_33);
x_135 = lean_ctor_get(x_34, 1);
lean_inc(x_135);
lean_dec(x_34);
x_136 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
x_137 = lean_string_dec_eq(x_135, x_136);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_139 = lean_string_dec_eq(x_135, x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11;
x_141 = lean_string_dec_eq(x_135, x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_142 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12;
x_143 = lean_string_dec_eq(x_135, x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13;
x_145 = lean_string_dec_eq(x_135, x_144);
lean_dec(x_135);
if (x_145 == 0)
{
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_146; uint8_t x_147; 
x_146 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14;
x_147 = lean_string_dec_eq(x_134, x_146);
lean_dec(x_134);
if (x_147 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_array_get_size(x_132);
x_149 = lean_unsigned_to_nat(4u);
x_150 = lean_nat_dec_eq(x_148, x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_192; lean_object* x_193; uint64_t x_194; uint64_t x_195; uint64_t x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; uint64_t x_200; size_t x_201; size_t x_202; size_t x_203; lean_object* x_204; uint8_t x_205; 
x_151 = lean_unsigned_to_nat(2u);
x_152 = lean_array_fget(x_132, x_151);
x_153 = lean_unsigned_to_nat(3u);
x_154 = lean_array_fget(x_132, x_153);
lean_dec(x_132);
x_155 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_192 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20;
lean_inc(x_154);
lean_inc(x_152);
x_193 = l_Lean_mkAppB(x_192, x_152, x_154);
x_194 = l_Lean_Expr_hash(x_193);
x_195 = 32;
x_196 = lean_uint64_shift_right(x_194, x_195);
x_197 = lean_uint64_xor(x_194, x_196);
x_198 = 16;
x_199 = lean_uint64_shift_right(x_197, x_198);
x_200 = lean_uint64_xor(x_197, x_199);
x_201 = lean_uint64_to_usize(x_200);
x_202 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_203 = lean_usize_land(x_201, x_202);
x_204 = lean_array_uget(x_155, x_203);
x_205 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_193, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_206 = lean_box(0);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_193);
lean_ctor_set(x_208, 1, x_206);
lean_ctor_set(x_208, 2, x_204);
x_209 = lean_array_uset(x_155, x_203, x_208);
x_210 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_211 = lean_array_get_size(x_209);
x_212 = lean_nat_dec_le(x_210, x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_209);
lean_inc(x_213);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_207);
lean_ctor_set(x_214, 1, x_213);
x_156 = x_214;
x_157 = x_207;
x_158 = x_213;
goto block_191;
}
else
{
lean_object* x_215; 
lean_inc(x_209);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_207);
lean_ctor_set(x_215, 1, x_209);
x_156 = x_215;
x_157 = x_207;
x_158 = x_209;
goto block_191;
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_204);
lean_dec(x_193);
x_216 = lean_unsigned_to_nat(0u);
x_217 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_156 = x_217;
x_157 = x_216;
x_158 = x_155;
goto block_191;
}
block_191:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint64_t x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; uint64_t x_168; size_t x_169; size_t x_170; size_t x_171; size_t x_172; size_t x_173; lean_object* x_174; uint8_t x_175; 
x_159 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19;
x_160 = l_Lean_mkAppB(x_159, x_152, x_154);
x_161 = lean_array_get_size(x_158);
x_162 = l_Lean_Expr_hash(x_160);
x_163 = 32;
x_164 = lean_uint64_shift_right(x_162, x_163);
x_165 = lean_uint64_xor(x_162, x_164);
x_166 = 16;
x_167 = lean_uint64_shift_right(x_165, x_166);
x_168 = lean_uint64_xor(x_165, x_167);
x_169 = lean_uint64_to_usize(x_168);
x_170 = lean_usize_of_nat(x_161);
lean_dec(x_161);
x_171 = 1;
x_172 = lean_usize_sub(x_170, x_171);
x_173 = lean_usize_land(x_169, x_172);
x_174 = lean_array_uget(x_158, x_173);
x_175 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_160, x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_156);
x_176 = lean_box(0);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_add(x_157, x_177);
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_160);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_174);
x_180 = lean_array_uset(x_158, x_173, x_179);
x_181 = lean_nat_mul(x_178, x_149);
x_182 = lean_nat_div(x_181, x_153);
lean_dec(x_181);
x_183 = lean_array_get_size(x_180);
x_184 = lean_nat_dec_le(x_182, x_183);
lean_dec(x_183);
lean_dec(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_180);
if (lean_is_scalar(x_133)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_133;
}
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_7);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; 
if (lean_is_scalar(x_133)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_133;
}
lean_ctor_set(x_188, 0, x_178);
lean_ctor_set(x_188, 1, x_180);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_7);
return x_189;
}
}
else
{
lean_object* x_190; 
lean_dec(x_174);
lean_dec(x_160);
lean_dec(x_158);
if (lean_is_scalar(x_133)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_133;
}
lean_ctor_set(x_190, 0, x_156);
lean_ctor_set(x_190, 1, x_7);
return x_190;
}
}
}
}
}
}
else
{
lean_object* x_218; uint8_t x_219; 
lean_dec(x_135);
x_218 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21;
x_219 = lean_string_dec_eq(x_134, x_218);
lean_dec(x_134);
if (x_219 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_array_get_size(x_132);
x_221 = lean_unsigned_to_nat(4u);
x_222 = lean_nat_dec_eq(x_220, x_221);
lean_dec(x_220);
if (x_222 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_264; lean_object* x_265; uint64_t x_266; uint64_t x_267; uint64_t x_268; uint64_t x_269; uint64_t x_270; uint64_t x_271; uint64_t x_272; size_t x_273; size_t x_274; size_t x_275; lean_object* x_276; uint8_t x_277; 
x_223 = lean_unsigned_to_nat(2u);
x_224 = lean_array_fget(x_132, x_223);
x_225 = lean_unsigned_to_nat(3u);
x_226 = lean_array_fget(x_132, x_225);
lean_dec(x_132);
x_227 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_264 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27;
lean_inc(x_226);
lean_inc(x_224);
x_265 = l_Lean_mkAppB(x_264, x_224, x_226);
x_266 = l_Lean_Expr_hash(x_265);
x_267 = 32;
x_268 = lean_uint64_shift_right(x_266, x_267);
x_269 = lean_uint64_xor(x_266, x_268);
x_270 = 16;
x_271 = lean_uint64_shift_right(x_269, x_270);
x_272 = lean_uint64_xor(x_269, x_271);
x_273 = lean_uint64_to_usize(x_272);
x_274 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_275 = lean_usize_land(x_273, x_274);
x_276 = lean_array_uget(x_227, x_275);
x_277 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_265, x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_278 = lean_box(0);
x_279 = lean_unsigned_to_nat(1u);
x_280 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_280, 0, x_265);
lean_ctor_set(x_280, 1, x_278);
lean_ctor_set(x_280, 2, x_276);
x_281 = lean_array_uset(x_227, x_275, x_280);
x_282 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_283 = lean_array_get_size(x_281);
x_284 = lean_nat_dec_le(x_282, x_283);
lean_dec(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_281);
lean_inc(x_285);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_279);
lean_ctor_set(x_286, 1, x_285);
x_228 = x_286;
x_229 = x_279;
x_230 = x_285;
goto block_263;
}
else
{
lean_object* x_287; 
lean_inc(x_281);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_279);
lean_ctor_set(x_287, 1, x_281);
x_228 = x_287;
x_229 = x_279;
x_230 = x_281;
goto block_263;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_276);
lean_dec(x_265);
x_288 = lean_unsigned_to_nat(0u);
x_289 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_228 = x_289;
x_229 = x_288;
x_230 = x_227;
goto block_263;
}
block_263:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; uint64_t x_239; uint64_t x_240; size_t x_241; size_t x_242; size_t x_243; size_t x_244; size_t x_245; lean_object* x_246; uint8_t x_247; 
x_231 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26;
x_232 = l_Lean_mkAppB(x_231, x_224, x_226);
x_233 = lean_array_get_size(x_230);
x_234 = l_Lean_Expr_hash(x_232);
x_235 = 32;
x_236 = lean_uint64_shift_right(x_234, x_235);
x_237 = lean_uint64_xor(x_234, x_236);
x_238 = 16;
x_239 = lean_uint64_shift_right(x_237, x_238);
x_240 = lean_uint64_xor(x_237, x_239);
x_241 = lean_uint64_to_usize(x_240);
x_242 = lean_usize_of_nat(x_233);
lean_dec(x_233);
x_243 = 1;
x_244 = lean_usize_sub(x_242, x_243);
x_245 = lean_usize_land(x_241, x_244);
x_246 = lean_array_uget(x_230, x_245);
x_247 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_232, x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_dec(x_228);
x_248 = lean_box(0);
x_249 = lean_unsigned_to_nat(1u);
x_250 = lean_nat_add(x_229, x_249);
x_251 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_251, 0, x_232);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_246);
x_252 = lean_array_uset(x_230, x_245, x_251);
x_253 = lean_nat_mul(x_250, x_221);
x_254 = lean_nat_div(x_253, x_225);
lean_dec(x_253);
x_255 = lean_array_get_size(x_252);
x_256 = lean_nat_dec_le(x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_252);
if (lean_is_scalar(x_133)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_133;
}
lean_ctor_set(x_258, 0, x_250);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_7);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; 
if (lean_is_scalar(x_133)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_133;
}
lean_ctor_set(x_260, 0, x_250);
lean_ctor_set(x_260, 1, x_252);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_7);
return x_261;
}
}
else
{
lean_object* x_262; 
lean_dec(x_246);
lean_dec(x_232);
lean_dec(x_230);
if (lean_is_scalar(x_133)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_133;
}
lean_ctor_set(x_262, 0, x_228);
lean_ctor_set(x_262, 1, x_7);
return x_262;
}
}
}
}
}
}
else
{
lean_object* x_290; uint8_t x_291; 
lean_dec(x_135);
x_290 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28;
x_291 = lean_string_dec_eq(x_134, x_290);
lean_dec(x_134);
if (x_291 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_array_get_size(x_132);
x_293 = lean_unsigned_to_nat(6u);
x_294 = lean_nat_dec_eq(x_292, x_293);
lean_dec(x_292);
if (x_294 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_unsigned_to_nat(5u);
x_296 = lean_array_fget(x_132, x_295);
lean_inc(x_296);
x_297 = l_Lean_Expr_getAppFnArgs(x_296);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_obj_tag(x_298) == 1)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
if (lean_obj_tag(x_299) == 1)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_410; uint8_t x_411; 
x_301 = lean_ctor_get(x_297, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_302 = x_297;
} else {
 lean_dec_ref(x_297);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_298, 1);
lean_inc(x_303);
lean_dec(x_298);
x_304 = lean_ctor_get(x_299, 1);
lean_inc(x_304);
lean_dec(x_299);
x_305 = lean_unsigned_to_nat(4u);
x_306 = lean_array_fget(x_132, x_305);
lean_dec(x_132);
x_410 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_411 = lean_string_dec_eq(x_304, x_410);
if (x_411 == 0)
{
uint8_t x_412; 
x_412 = lean_string_dec_eq(x_304, x_136);
lean_dec(x_304);
if (x_412 == 0)
{
lean_dec(x_306);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_413; uint8_t x_414; 
x_413 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_414 = lean_string_dec_eq(x_303, x_413);
lean_dec(x_303);
if (x_414 == 0)
{
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_415 = lean_array_get_size(x_301);
x_416 = lean_unsigned_to_nat(3u);
x_417 = lean_nat_dec_eq(x_415, x_416);
lean_dec(x_415);
if (x_417 == 0)
{
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_unsigned_to_nat(0u);
x_419 = lean_array_fget(x_301, x_418);
if (lean_obj_tag(x_419) == 4)
{
lean_object* x_420; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_obj_tag(x_420) == 1)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
lean_dec(x_419);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_425 = lean_string_dec_eq(x_423, x_424);
lean_dec(x_423);
if (x_425 == 0)
{
lean_dec(x_422);
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
else
{
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_426 = lean_unsigned_to_nat(2u);
x_427 = lean_array_fget(x_301, x_426);
lean_dec(x_301);
lean_inc(x_427);
x_428 = l_Lean_Expr_getAppFnArgs(x_427);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 1)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 1)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
uint8_t x_432; 
x_432 = !lean_is_exclusive(x_428);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_433 = lean_ctor_get(x_428, 1);
x_434 = lean_ctor_get(x_428, 0);
lean_dec(x_434);
x_435 = lean_ctor_get(x_429, 1);
lean_inc(x_435);
lean_dec(x_429);
x_436 = lean_ctor_get(x_430, 1);
lean_inc(x_436);
lean_dec(x_430);
x_437 = lean_string_dec_eq(x_436, x_410);
lean_dec(x_436);
if (x_437 == 0)
{
lean_dec(x_435);
lean_free_object(x_428);
lean_dec(x_433);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
else
{
lean_object* x_438; uint8_t x_439; 
x_438 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_439 = lean_string_dec_eq(x_435, x_438);
lean_dec(x_435);
if (x_439 == 0)
{
lean_free_object(x_428);
lean_dec(x_433);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
else
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_array_get_size(x_433);
x_441 = lean_nat_dec_eq(x_440, x_293);
lean_dec(x_440);
if (x_441 == 0)
{
lean_free_object(x_428);
lean_dec(x_433);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
else
{
lean_object* x_442; lean_object* x_443; 
lean_dec(x_302);
x_442 = lean_array_fget(x_433, x_305);
lean_inc(x_442);
x_443 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_442);
if (lean_obj_tag(x_443) == 0)
{
lean_dec(x_442);
lean_free_object(x_428);
lean_dec(x_433);
lean_dec(x_427);
lean_dec(x_306);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = x_7;
goto block_27;
}
else
{
lean_object* x_444; uint8_t x_445; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
lean_dec(x_443);
x_445 = lean_nat_dec_eq(x_444, x_418);
lean_dec(x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_446 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
x_447 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
lean_ctor_set_tag(x_428, 1);
lean_ctor_set(x_428, 1, x_422);
lean_ctor_set(x_428, 0, x_447);
lean_inc(x_428);
x_448 = l_Lean_Expr_const___override(x_446, x_428);
x_449 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34;
x_450 = l_Lean_Expr_const___override(x_449, x_422);
x_451 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36;
x_452 = l_Lean_Expr_const___override(x_451, x_422);
x_453 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
lean_inc(x_442);
x_454 = l_Lean_mkApp4(x_448, x_450, x_452, x_453, x_442);
x_455 = l_Lean_Meta_mkDecideProof(x_454, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_535; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_458 = x_455;
} else {
 lean_dec_ref(x_455);
 x_458 = lean_box(0);
}
x_459 = lean_array_fget(x_433, x_295);
lean_dec(x_433);
x_460 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39;
x_461 = l_Lean_Expr_const___override(x_460, x_422);
x_462 = l_Lean_mkApp3(x_461, x_442, x_459, x_456);
x_463 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41;
x_464 = l_Lean_Expr_const___override(x_463, x_422);
x_465 = l_Lean_mkAppB(x_464, x_427, x_462);
x_503 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_504 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_505 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45;
x_506 = l_Lean_Expr_const___override(x_505, x_422);
x_507 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
x_508 = l_Lean_Expr_const___override(x_507, x_422);
x_535 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_536 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
x_537 = l_Lean_Expr_const___override(x_536, x_428);
x_538 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
x_539 = l_Lean_Expr_const___override(x_538, x_422);
x_540 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
x_541 = l_Lean_Expr_const___override(x_540, x_422);
x_542 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57;
x_543 = l_Lean_mkApp3(x_537, x_539, x_541, x_542);
x_509 = x_543;
goto block_534;
}
else
{
lean_object* x_544; 
lean_dec(x_428);
x_544 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
x_509 = x_544;
goto block_534;
}
block_502:
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint64_t x_473; uint64_t x_474; uint64_t x_475; uint64_t x_476; uint64_t x_477; uint64_t x_478; uint64_t x_479; size_t x_480; size_t x_481; size_t x_482; size_t x_483; size_t x_484; lean_object* x_485; uint8_t x_486; 
x_469 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
x_470 = l_Lean_Expr_const___override(x_469, x_422);
x_471 = l_Lean_mkApp3(x_470, x_306, x_296, x_465);
x_472 = lean_array_get_size(x_468);
x_473 = l_Lean_Expr_hash(x_471);
x_474 = 32;
x_475 = lean_uint64_shift_right(x_473, x_474);
x_476 = lean_uint64_xor(x_473, x_475);
x_477 = 16;
x_478 = lean_uint64_shift_right(x_476, x_477);
x_479 = lean_uint64_xor(x_476, x_478);
x_480 = lean_uint64_to_usize(x_479);
x_481 = lean_usize_of_nat(x_472);
lean_dec(x_472);
x_482 = 1;
x_483 = lean_usize_sub(x_481, x_482);
x_484 = lean_usize_land(x_480, x_483);
x_485 = lean_array_uget(x_468, x_484);
x_486 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_471, x_485);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
lean_dec(x_466);
x_487 = lean_box(0);
x_488 = lean_unsigned_to_nat(1u);
x_489 = lean_nat_add(x_467, x_488);
x_490 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_490, 0, x_471);
lean_ctor_set(x_490, 1, x_487);
lean_ctor_set(x_490, 2, x_485);
x_491 = lean_array_uset(x_468, x_484, x_490);
x_492 = lean_nat_mul(x_489, x_305);
x_493 = lean_nat_div(x_492, x_416);
lean_dec(x_492);
x_494 = lean_array_get_size(x_491);
x_495 = lean_nat_dec_le(x_493, x_494);
lean_dec(x_494);
lean_dec(x_493);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_491);
if (lean_is_scalar(x_133)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_133;
}
lean_ctor_set(x_497, 0, x_489);
lean_ctor_set(x_497, 1, x_496);
if (lean_is_scalar(x_458)) {
 x_498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_498 = x_458;
}
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_457);
return x_498;
}
else
{
lean_object* x_499; lean_object* x_500; 
if (lean_is_scalar(x_133)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_133;
}
lean_ctor_set(x_499, 0, x_489);
lean_ctor_set(x_499, 1, x_491);
if (lean_is_scalar(x_458)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_458;
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_457);
return x_500;
}
}
else
{
lean_object* x_501; 
lean_dec(x_485);
lean_dec(x_471);
lean_dec(x_468);
lean_dec(x_133);
if (lean_is_scalar(x_458)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_458;
}
lean_ctor_set(x_501, 0, x_466);
lean_ctor_set(x_501, 1, x_457);
return x_501;
}
}
block_534:
{
lean_object* x_510; lean_object* x_511; uint64_t x_512; uint64_t x_513; uint64_t x_514; uint64_t x_515; uint64_t x_516; uint64_t x_517; uint64_t x_518; size_t x_519; size_t x_520; size_t x_521; lean_object* x_522; uint8_t x_523; 
lean_inc(x_465);
lean_inc(x_296);
x_510 = l_Lean_mkApp3(x_508, x_296, x_509, x_465);
lean_inc(x_296);
lean_inc(x_306);
x_511 = l_Lean_mkApp3(x_506, x_306, x_296, x_510);
x_512 = l_Lean_Expr_hash(x_511);
x_513 = 32;
x_514 = lean_uint64_shift_right(x_512, x_513);
x_515 = lean_uint64_xor(x_512, x_514);
x_516 = 16;
x_517 = lean_uint64_shift_right(x_515, x_516);
x_518 = lean_uint64_xor(x_515, x_517);
x_519 = lean_uint64_to_usize(x_518);
x_520 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_521 = lean_usize_land(x_519, x_520);
x_522 = lean_array_uget(x_503, x_521);
x_523 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_511, x_522);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; 
x_524 = lean_box(0);
x_525 = lean_unsigned_to_nat(1u);
x_526 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_526, 0, x_511);
lean_ctor_set(x_526, 1, x_524);
lean_ctor_set(x_526, 2, x_522);
x_527 = lean_array_uset(x_503, x_521, x_526);
x_528 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_529 = lean_array_get_size(x_527);
x_530 = lean_nat_dec_le(x_528, x_529);
lean_dec(x_529);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; 
x_531 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_527);
lean_inc(x_531);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_525);
lean_ctor_set(x_532, 1, x_531);
x_466 = x_532;
x_467 = x_525;
x_468 = x_531;
goto block_502;
}
else
{
lean_object* x_533; 
lean_inc(x_527);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_525);
lean_ctor_set(x_533, 1, x_527);
x_466 = x_533;
x_467 = x_525;
x_468 = x_527;
goto block_502;
}
}
else
{
lean_dec(x_522);
lean_dec(x_511);
x_466 = x_504;
x_467 = x_418;
x_468 = x_503;
goto block_502;
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_428);
lean_dec(x_442);
lean_dec(x_433);
lean_dec(x_427);
lean_dec(x_306);
lean_dec(x_296);
lean_dec(x_133);
x_545 = !lean_is_exclusive(x_455);
if (x_545 == 0)
{
return x_455;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_455, 0);
x_547 = lean_ctor_get(x_455, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_455);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
else
{
lean_dec(x_442);
lean_free_object(x_428);
lean_dec(x_433);
lean_dec(x_427);
lean_dec(x_306);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = x_7;
goto block_27;
}
}
}
}
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; 
x_549 = lean_ctor_get(x_428, 1);
lean_inc(x_549);
lean_dec(x_428);
x_550 = lean_ctor_get(x_429, 1);
lean_inc(x_550);
lean_dec(x_429);
x_551 = lean_ctor_get(x_430, 1);
lean_inc(x_551);
lean_dec(x_430);
x_552 = lean_string_dec_eq(x_551, x_410);
lean_dec(x_551);
if (x_552 == 0)
{
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
else
{
lean_object* x_553; uint8_t x_554; 
x_553 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_554 = lean_string_dec_eq(x_550, x_553);
lean_dec(x_550);
if (x_554 == 0)
{
lean_dec(x_549);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
else
{
lean_object* x_555; uint8_t x_556; 
x_555 = lean_array_get_size(x_549);
x_556 = lean_nat_dec_eq(x_555, x_293);
lean_dec(x_555);
if (x_556 == 0)
{
lean_dec(x_549);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
else
{
lean_object* x_557; lean_object* x_558; 
lean_dec(x_302);
x_557 = lean_array_fget(x_549, x_305);
lean_inc(x_557);
x_558 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_557);
if (lean_obj_tag(x_558) == 0)
{
lean_dec(x_557);
lean_dec(x_549);
lean_dec(x_427);
lean_dec(x_306);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = x_7;
goto block_27;
}
else
{
lean_object* x_559; uint8_t x_560; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
lean_dec(x_558);
x_560 = lean_nat_dec_eq(x_559, x_418);
lean_dec(x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_561 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
x_562 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_422);
lean_inc(x_563);
x_564 = l_Lean_Expr_const___override(x_561, x_563);
x_565 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34;
x_566 = l_Lean_Expr_const___override(x_565, x_422);
x_567 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36;
x_568 = l_Lean_Expr_const___override(x_567, x_422);
x_569 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
lean_inc(x_557);
x_570 = l_Lean_mkApp4(x_564, x_566, x_568, x_569, x_557);
x_571 = l_Lean_Meta_mkDecideProof(x_570, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_651; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_574 = x_571;
} else {
 lean_dec_ref(x_571);
 x_574 = lean_box(0);
}
x_575 = lean_array_fget(x_549, x_295);
lean_dec(x_549);
x_576 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39;
x_577 = l_Lean_Expr_const___override(x_576, x_422);
x_578 = l_Lean_mkApp3(x_577, x_557, x_575, x_572);
x_579 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41;
x_580 = l_Lean_Expr_const___override(x_579, x_422);
x_581 = l_Lean_mkAppB(x_580, x_427, x_578);
x_619 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_620 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_621 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45;
x_622 = l_Lean_Expr_const___override(x_621, x_422);
x_623 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47;
x_624 = l_Lean_Expr_const___override(x_623, x_422);
x_651 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
if (x_651 == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_652 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52;
x_653 = l_Lean_Expr_const___override(x_652, x_563);
x_654 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
x_655 = l_Lean_Expr_const___override(x_654, x_422);
x_656 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54;
x_657 = l_Lean_Expr_const___override(x_656, x_422);
x_658 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57;
x_659 = l_Lean_mkApp3(x_653, x_655, x_657, x_658);
x_625 = x_659;
goto block_650;
}
else
{
lean_object* x_660; 
lean_dec(x_563);
x_660 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
x_625 = x_660;
goto block_650;
}
block_618:
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; uint64_t x_589; uint64_t x_590; uint64_t x_591; uint64_t x_592; uint64_t x_593; uint64_t x_594; uint64_t x_595; size_t x_596; size_t x_597; size_t x_598; size_t x_599; size_t x_600; lean_object* x_601; uint8_t x_602; 
x_585 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43;
x_586 = l_Lean_Expr_const___override(x_585, x_422);
x_587 = l_Lean_mkApp3(x_586, x_306, x_296, x_581);
x_588 = lean_array_get_size(x_584);
x_589 = l_Lean_Expr_hash(x_587);
x_590 = 32;
x_591 = lean_uint64_shift_right(x_589, x_590);
x_592 = lean_uint64_xor(x_589, x_591);
x_593 = 16;
x_594 = lean_uint64_shift_right(x_592, x_593);
x_595 = lean_uint64_xor(x_592, x_594);
x_596 = lean_uint64_to_usize(x_595);
x_597 = lean_usize_of_nat(x_588);
lean_dec(x_588);
x_598 = 1;
x_599 = lean_usize_sub(x_597, x_598);
x_600 = lean_usize_land(x_596, x_599);
x_601 = lean_array_uget(x_584, x_600);
x_602 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_587, x_601);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
lean_dec(x_582);
x_603 = lean_box(0);
x_604 = lean_unsigned_to_nat(1u);
x_605 = lean_nat_add(x_583, x_604);
x_606 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_606, 0, x_587);
lean_ctor_set(x_606, 1, x_603);
lean_ctor_set(x_606, 2, x_601);
x_607 = lean_array_uset(x_584, x_600, x_606);
x_608 = lean_nat_mul(x_605, x_305);
x_609 = lean_nat_div(x_608, x_416);
lean_dec(x_608);
x_610 = lean_array_get_size(x_607);
x_611 = lean_nat_dec_le(x_609, x_610);
lean_dec(x_610);
lean_dec(x_609);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_607);
if (lean_is_scalar(x_133)) {
 x_613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_613 = x_133;
}
lean_ctor_set(x_613, 0, x_605);
lean_ctor_set(x_613, 1, x_612);
if (lean_is_scalar(x_574)) {
 x_614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_614 = x_574;
}
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_573);
return x_614;
}
else
{
lean_object* x_615; lean_object* x_616; 
if (lean_is_scalar(x_133)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_133;
}
lean_ctor_set(x_615, 0, x_605);
lean_ctor_set(x_615, 1, x_607);
if (lean_is_scalar(x_574)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_574;
}
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_573);
return x_616;
}
}
else
{
lean_object* x_617; 
lean_dec(x_601);
lean_dec(x_587);
lean_dec(x_584);
lean_dec(x_133);
if (lean_is_scalar(x_574)) {
 x_617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_617 = x_574;
}
lean_ctor_set(x_617, 0, x_582);
lean_ctor_set(x_617, 1, x_573);
return x_617;
}
}
block_650:
{
lean_object* x_626; lean_object* x_627; uint64_t x_628; uint64_t x_629; uint64_t x_630; uint64_t x_631; uint64_t x_632; uint64_t x_633; uint64_t x_634; size_t x_635; size_t x_636; size_t x_637; lean_object* x_638; uint8_t x_639; 
lean_inc(x_581);
lean_inc(x_296);
x_626 = l_Lean_mkApp3(x_624, x_296, x_625, x_581);
lean_inc(x_296);
lean_inc(x_306);
x_627 = l_Lean_mkApp3(x_622, x_306, x_296, x_626);
x_628 = l_Lean_Expr_hash(x_627);
x_629 = 32;
x_630 = lean_uint64_shift_right(x_628, x_629);
x_631 = lean_uint64_xor(x_628, x_630);
x_632 = 16;
x_633 = lean_uint64_shift_right(x_631, x_632);
x_634 = lean_uint64_xor(x_631, x_633);
x_635 = lean_uint64_to_usize(x_634);
x_636 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_637 = lean_usize_land(x_635, x_636);
x_638 = lean_array_uget(x_619, x_637);
x_639 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_627, x_638);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_640 = lean_box(0);
x_641 = lean_unsigned_to_nat(1u);
x_642 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_642, 0, x_627);
lean_ctor_set(x_642, 1, x_640);
lean_ctor_set(x_642, 2, x_638);
x_643 = lean_array_uset(x_619, x_637, x_642);
x_644 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_645 = lean_array_get_size(x_643);
x_646 = lean_nat_dec_le(x_644, x_645);
lean_dec(x_645);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_643);
lean_inc(x_647);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_641);
lean_ctor_set(x_648, 1, x_647);
x_582 = x_648;
x_583 = x_641;
x_584 = x_647;
goto block_618;
}
else
{
lean_object* x_649; 
lean_inc(x_643);
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_641);
lean_ctor_set(x_649, 1, x_643);
x_582 = x_649;
x_583 = x_641;
x_584 = x_643;
goto block_618;
}
}
else
{
lean_dec(x_638);
lean_dec(x_627);
x_582 = x_620;
x_583 = x_418;
x_584 = x_619;
goto block_618;
}
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_563);
lean_dec(x_557);
lean_dec(x_549);
lean_dec(x_427);
lean_dec(x_306);
lean_dec(x_296);
lean_dec(x_133);
x_661 = lean_ctor_get(x_571, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_571, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_663 = x_571;
} else {
 lean_dec_ref(x_571);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
else
{
lean_dec(x_557);
lean_dec(x_549);
lean_dec(x_427);
lean_dec(x_306);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = x_7;
goto block_27;
}
}
}
}
}
}
}
else
{
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
}
else
{
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
}
else
{
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_307 = x_7;
goto block_409;
}
}
else
{
lean_dec(x_422);
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
}
}
else
{
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
}
else
{
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
}
else
{
lean_dec(x_419);
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
}
}
}
}
else
{
lean_object* x_665; uint8_t x_666; 
lean_dec(x_304);
lean_dec(x_302);
x_665 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_666 = lean_string_dec_eq(x_303, x_665);
lean_dec(x_303);
if (x_666 == 0)
{
lean_dec(x_306);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_667; uint8_t x_668; 
x_667 = lean_array_get_size(x_301);
x_668 = lean_nat_dec_eq(x_667, x_293);
lean_dec(x_667);
if (x_668 == 0)
{
lean_dec(x_306);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
else
{
lean_object* x_669; lean_object* x_670; 
x_669 = lean_array_fget(x_301, x_305);
lean_inc(x_669);
x_670 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_669);
if (lean_obj_tag(x_670) == 0)
{
lean_dec(x_669);
lean_dec(x_306);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = x_7;
goto block_31;
}
else
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
lean_dec(x_670);
x_672 = lean_unsigned_to_nat(0u);
x_673 = lean_nat_dec_eq(x_671, x_672);
lean_dec(x_671);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_715; lean_object* x_716; lean_object* x_717; uint8_t x_757; 
x_674 = lean_array_fget(x_301, x_295);
lean_dec(x_301);
x_675 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60;
x_715 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_716 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64;
x_757 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
if (x_757 == 0)
{
lean_object* x_758; 
x_758 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71;
x_717 = x_758;
goto block_756;
}
else
{
lean_object* x_759; 
x_759 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
x_717 = x_759;
goto block_756;
}
block_714:
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; uint64_t x_684; uint64_t x_685; uint64_t x_686; uint64_t x_687; uint64_t x_688; uint64_t x_689; uint64_t x_690; size_t x_691; size_t x_692; size_t x_693; size_t x_694; size_t x_695; lean_object* x_696; uint8_t x_697; 
x_681 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61;
x_682 = l_Lean_mkApp3(x_681, x_306, x_296, x_676);
x_683 = lean_array_get_size(x_680);
x_684 = l_Lean_Expr_hash(x_682);
x_685 = 32;
x_686 = lean_uint64_shift_right(x_684, x_685);
x_687 = lean_uint64_xor(x_684, x_686);
x_688 = 16;
x_689 = lean_uint64_shift_right(x_687, x_688);
x_690 = lean_uint64_xor(x_687, x_689);
x_691 = lean_uint64_to_usize(x_690);
x_692 = lean_usize_of_nat(x_683);
lean_dec(x_683);
x_693 = 1;
x_694 = lean_usize_sub(x_692, x_693);
x_695 = lean_usize_land(x_691, x_694);
x_696 = lean_array_uget(x_680, x_695);
x_697 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_682, x_696);
if (x_697 == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
lean_dec(x_678);
x_698 = lean_box(0);
x_699 = lean_unsigned_to_nat(1u);
x_700 = lean_nat_add(x_679, x_699);
x_701 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_701, 0, x_682);
lean_ctor_set(x_701, 1, x_698);
lean_ctor_set(x_701, 2, x_696);
x_702 = lean_array_uset(x_680, x_695, x_701);
x_703 = lean_nat_mul(x_700, x_305);
x_704 = lean_unsigned_to_nat(3u);
x_705 = lean_nat_div(x_703, x_704);
lean_dec(x_703);
x_706 = lean_array_get_size(x_702);
x_707 = lean_nat_dec_le(x_705, x_706);
lean_dec(x_706);
lean_dec(x_705);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_708 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_702);
if (lean_is_scalar(x_133)) {
 x_709 = lean_alloc_ctor(0, 2, 0);
} else {
 x_709 = x_133;
}
lean_ctor_set(x_709, 0, x_700);
lean_ctor_set(x_709, 1, x_708);
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_677);
return x_710;
}
else
{
lean_object* x_711; lean_object* x_712; 
if (lean_is_scalar(x_133)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_133;
}
lean_ctor_set(x_711, 0, x_700);
lean_ctor_set(x_711, 1, x_702);
x_712 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_677);
return x_712;
}
}
else
{
lean_object* x_713; 
lean_dec(x_696);
lean_dec(x_682);
lean_dec(x_680);
if (lean_is_scalar(x_133)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_133;
}
lean_ctor_set(x_713, 0, x_678);
lean_ctor_set(x_713, 1, x_677);
return x_713;
}
}
block_756:
{
lean_object* x_718; lean_object* x_719; 
lean_inc(x_669);
lean_inc(x_717);
x_718 = l_Lean_mkApp4(x_675, x_715, x_716, x_717, x_669);
x_719 = l_Lean_Meta_mkDecideProof(x_718, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint64_t x_729; uint64_t x_730; uint64_t x_731; uint64_t x_732; uint64_t x_733; uint64_t x_734; uint64_t x_735; size_t x_736; size_t x_737; size_t x_738; lean_object* x_739; uint8_t x_740; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66;
x_723 = l_Lean_mkApp3(x_722, x_669, x_674, x_720);
x_724 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_725 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67;
x_726 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68;
lean_inc(x_723);
lean_inc(x_296);
x_727 = l_Lean_mkApp3(x_726, x_296, x_717, x_723);
lean_inc(x_296);
lean_inc(x_306);
x_728 = l_Lean_mkApp3(x_725, x_306, x_296, x_727);
x_729 = l_Lean_Expr_hash(x_728);
x_730 = 32;
x_731 = lean_uint64_shift_right(x_729, x_730);
x_732 = lean_uint64_xor(x_729, x_731);
x_733 = 16;
x_734 = lean_uint64_shift_right(x_732, x_733);
x_735 = lean_uint64_xor(x_732, x_734);
x_736 = lean_uint64_to_usize(x_735);
x_737 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_738 = lean_usize_land(x_736, x_737);
x_739 = lean_array_uget(x_724, x_738);
x_740 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_728, x_739);
if (x_740 == 0)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; 
x_741 = lean_box(0);
x_742 = lean_unsigned_to_nat(1u);
x_743 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_743, 0, x_728);
lean_ctor_set(x_743, 1, x_741);
lean_ctor_set(x_743, 2, x_739);
x_744 = lean_array_uset(x_724, x_738, x_743);
x_745 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_746 = lean_array_get_size(x_744);
x_747 = lean_nat_dec_le(x_745, x_746);
lean_dec(x_746);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; 
x_748 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_744);
lean_inc(x_748);
x_749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_749, 0, x_742);
lean_ctor_set(x_749, 1, x_748);
x_676 = x_723;
x_677 = x_721;
x_678 = x_749;
x_679 = x_742;
x_680 = x_748;
goto block_714;
}
else
{
lean_object* x_750; 
lean_inc(x_744);
x_750 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_750, 0, x_742);
lean_ctor_set(x_750, 1, x_744);
x_676 = x_723;
x_677 = x_721;
x_678 = x_750;
x_679 = x_742;
x_680 = x_744;
goto block_714;
}
}
else
{
lean_object* x_751; 
lean_dec(x_739);
lean_dec(x_728);
x_751 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_676 = x_723;
x_677 = x_721;
x_678 = x_751;
x_679 = x_672;
x_680 = x_724;
goto block_714;
}
}
else
{
uint8_t x_752; 
lean_dec(x_717);
lean_dec(x_674);
lean_dec(x_669);
lean_dec(x_306);
lean_dec(x_296);
lean_dec(x_133);
x_752 = !lean_is_exclusive(x_719);
if (x_752 == 0)
{
return x_719;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_719, 0);
x_754 = lean_ctor_get(x_719, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_719);
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
return x_755;
}
}
}
}
else
{
lean_dec(x_669);
lean_dec(x_306);
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = x_7;
goto block_31;
}
}
}
}
}
block_409:
{
lean_object* x_308; lean_object* x_309; 
x_308 = l_Lean_Expr_getAppFnArgs(x_306);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
if (lean_obj_tag(x_309) == 1)
{
lean_object* x_310; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_obj_tag(x_310) == 1)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
if (lean_obj_tag(x_311) == 0)
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_308);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_313 = lean_ctor_get(x_308, 1);
x_314 = lean_ctor_get(x_308, 0);
lean_dec(x_314);
x_315 = lean_ctor_get(x_309, 1);
lean_inc(x_315);
lean_dec(x_309);
x_316 = lean_ctor_get(x_310, 1);
lean_inc(x_316);
lean_dec(x_310);
x_317 = lean_string_dec_eq(x_316, x_136);
lean_dec(x_316);
if (x_317 == 0)
{
lean_dec(x_315);
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
lean_object* x_318; uint8_t x_319; 
x_318 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_319 = lean_string_dec_eq(x_315, x_318);
lean_dec(x_315);
if (x_319 == 0)
{
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_320 = lean_array_get_size(x_313);
x_321 = lean_unsigned_to_nat(3u);
x_322 = lean_nat_dec_eq(x_320, x_321);
lean_dec(x_320);
if (x_322 == 0)
{
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_unsigned_to_nat(0u);
x_324 = lean_array_fget(x_313, x_323);
if (lean_obj_tag(x_324) == 4)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 1)
{
lean_object* x_326; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_dec(x_324);
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
lean_dec(x_325);
x_329 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_330 = lean_string_dec_eq(x_328, x_329);
lean_dec(x_328);
if (x_330 == 0)
{
lean_dec(x_327);
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint64_t x_337; uint64_t x_338; uint64_t x_339; uint64_t x_340; uint64_t x_341; uint64_t x_342; uint64_t x_343; size_t x_344; size_t x_345; size_t x_346; lean_object* x_347; uint8_t x_348; 
x_331 = lean_unsigned_to_nat(2u);
x_332 = lean_array_fget(x_313, x_331);
lean_dec(x_313);
x_333 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_334 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30;
x_335 = l_Lean_Expr_const___override(x_334, x_327);
x_336 = l_Lean_mkAppB(x_335, x_332, x_296);
x_337 = l_Lean_Expr_hash(x_336);
x_338 = 32;
x_339 = lean_uint64_shift_right(x_337, x_338);
x_340 = lean_uint64_xor(x_337, x_339);
x_341 = 16;
x_342 = lean_uint64_shift_right(x_340, x_341);
x_343 = lean_uint64_xor(x_340, x_342);
x_344 = lean_uint64_to_usize(x_343);
x_345 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_346 = lean_usize_land(x_344, x_345);
x_347 = lean_array_uget(x_333, x_346);
x_348 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_336, x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_349 = lean_box(0);
x_350 = lean_unsigned_to_nat(1u);
x_351 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_351, 0, x_336);
lean_ctor_set(x_351, 1, x_349);
lean_ctor_set(x_351, 2, x_347);
x_352 = lean_array_uset(x_333, x_346, x_351);
x_353 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_354 = lean_array_get_size(x_352);
x_355 = lean_nat_dec_le(x_353, x_354);
lean_dec(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_352);
lean_ctor_set(x_308, 1, x_356);
lean_ctor_set(x_308, 0, x_350);
if (lean_is_scalar(x_302)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_302;
}
lean_ctor_set(x_357, 0, x_308);
lean_ctor_set(x_357, 1, x_307);
return x_357;
}
else
{
lean_object* x_358; 
lean_ctor_set(x_308, 1, x_352);
lean_ctor_set(x_308, 0, x_350);
if (lean_is_scalar(x_302)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_302;
}
lean_ctor_set(x_358, 0, x_308);
lean_ctor_set(x_358, 1, x_307);
return x_358;
}
}
else
{
lean_object* x_359; 
lean_dec(x_347);
lean_dec(x_336);
lean_dec(x_302);
x_359 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
lean_ctor_set(x_308, 1, x_307);
lean_ctor_set(x_308, 0, x_359);
return x_308;
}
}
else
{
lean_dec(x_327);
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
}
else
{
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
else
{
lean_dec(x_325);
lean_dec(x_324);
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
else
{
lean_dec(x_324);
lean_free_object(x_308);
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_360 = lean_ctor_get(x_308, 1);
lean_inc(x_360);
lean_dec(x_308);
x_361 = lean_ctor_get(x_309, 1);
lean_inc(x_361);
lean_dec(x_309);
x_362 = lean_ctor_get(x_310, 1);
lean_inc(x_362);
lean_dec(x_310);
x_363 = lean_string_dec_eq(x_362, x_136);
lean_dec(x_362);
if (x_363 == 0)
{
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
lean_object* x_364; uint8_t x_365; 
x_364 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_365 = lean_string_dec_eq(x_361, x_364);
lean_dec(x_361);
if (x_365 == 0)
{
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_366 = lean_array_get_size(x_360);
x_367 = lean_unsigned_to_nat(3u);
x_368 = lean_nat_dec_eq(x_366, x_367);
lean_dec(x_366);
if (x_368 == 0)
{
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_unsigned_to_nat(0u);
x_370 = lean_array_fget(x_360, x_369);
if (lean_obj_tag(x_370) == 4)
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
if (lean_obj_tag(x_371) == 1)
{
lean_object* x_372; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
lean_dec(x_370);
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
lean_dec(x_371);
x_375 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_376 = lean_string_dec_eq(x_374, x_375);
lean_dec(x_374);
if (x_376 == 0)
{
lean_dec(x_373);
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
else
{
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint64_t x_383; uint64_t x_384; uint64_t x_385; uint64_t x_386; uint64_t x_387; uint64_t x_388; uint64_t x_389; size_t x_390; size_t x_391; size_t x_392; lean_object* x_393; uint8_t x_394; 
x_377 = lean_unsigned_to_nat(2u);
x_378 = lean_array_fget(x_360, x_377);
lean_dec(x_360);
x_379 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_380 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30;
x_381 = l_Lean_Expr_const___override(x_380, x_373);
x_382 = l_Lean_mkAppB(x_381, x_378, x_296);
x_383 = l_Lean_Expr_hash(x_382);
x_384 = 32;
x_385 = lean_uint64_shift_right(x_383, x_384);
x_386 = lean_uint64_xor(x_383, x_385);
x_387 = 16;
x_388 = lean_uint64_shift_right(x_386, x_387);
x_389 = lean_uint64_xor(x_386, x_388);
x_390 = lean_uint64_to_usize(x_389);
x_391 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_392 = lean_usize_land(x_390, x_391);
x_393 = lean_array_uget(x_379, x_392);
x_394 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_382, x_393);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_395 = lean_box(0);
x_396 = lean_unsigned_to_nat(1u);
x_397 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_397, 0, x_382);
lean_ctor_set(x_397, 1, x_395);
lean_ctor_set(x_397, 2, x_393);
x_398 = lean_array_uset(x_379, x_392, x_397);
x_399 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_400 = lean_array_get_size(x_398);
x_401 = lean_nat_dec_le(x_399, x_400);
lean_dec(x_400);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_398);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_396);
lean_ctor_set(x_403, 1, x_402);
if (lean_is_scalar(x_302)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_302;
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_307);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_396);
lean_ctor_set(x_405, 1, x_398);
if (lean_is_scalar(x_302)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_302;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_307);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; 
lean_dec(x_393);
lean_dec(x_382);
lean_dec(x_302);
x_407 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_307);
return x_408;
}
}
else
{
lean_dec(x_373);
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
}
else
{
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
else
{
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
else
{
lean_dec(x_370);
lean_dec(x_360);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
}
}
}
}
else
{
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
else
{
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
else
{
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_302);
lean_dec(x_296);
x_20 = x_307;
goto block_23;
}
}
}
else
{
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
}
else
{
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
}
else
{
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_7;
goto block_19;
}
}
}
}
}
else
{
lean_object* x_760; uint8_t x_761; 
lean_dec(x_135);
x_760 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_761 = lean_string_dec_eq(x_134, x_760);
lean_dec(x_134);
if (x_761 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_762; lean_object* x_763; uint8_t x_764; 
x_762 = lean_array_get_size(x_132);
x_763 = lean_unsigned_to_nat(6u);
x_764 = lean_nat_dec_eq(x_762, x_763);
lean_dec(x_762);
if (x_764 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_765 = lean_unsigned_to_nat(5u);
x_766 = lean_array_fget(x_132, x_765);
lean_inc(x_766);
x_767 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_766);
if (lean_obj_tag(x_767) == 0)
{
lean_dec(x_766);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = x_7;
goto block_11;
}
else
{
lean_object* x_768; lean_object* x_769; uint8_t x_770; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
lean_dec(x_767);
x_769 = lean_unsigned_to_nat(0u);
x_770 = lean_nat_dec_eq(x_768, x_769);
lean_dec(x_768);
if (x_770 == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_813; lean_object* x_814; uint8_t x_859; 
x_771 = lean_unsigned_to_nat(4u);
x_772 = lean_array_fget(x_132, x_771);
lean_dec(x_132);
x_773 = lean_unsigned_to_nat(1u);
x_774 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76;
x_813 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2;
x_859 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49;
if (x_859 == 0)
{
lean_object* x_860; 
x_860 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71;
x_814 = x_860;
goto block_858;
}
else
{
lean_object* x_861; 
x_861 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59;
x_814 = x_861;
goto block_858;
}
block_812:
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; uint64_t x_783; uint64_t x_784; uint64_t x_785; uint64_t x_786; uint64_t x_787; uint64_t x_788; uint64_t x_789; size_t x_790; size_t x_791; size_t x_792; size_t x_793; size_t x_794; lean_object* x_795; uint8_t x_796; 
x_780 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
x_781 = l_Lean_mkApp3(x_780, x_772, x_766, x_776);
x_782 = lean_array_get_size(x_779);
x_783 = l_Lean_Expr_hash(x_781);
x_784 = 32;
x_785 = lean_uint64_shift_right(x_783, x_784);
x_786 = lean_uint64_xor(x_783, x_785);
x_787 = 16;
x_788 = lean_uint64_shift_right(x_786, x_787);
x_789 = lean_uint64_xor(x_786, x_788);
x_790 = lean_uint64_to_usize(x_789);
x_791 = lean_usize_of_nat(x_782);
lean_dec(x_782);
x_792 = 1;
x_793 = lean_usize_sub(x_791, x_792);
x_794 = lean_usize_land(x_790, x_793);
x_795 = lean_array_uget(x_779, x_794);
x_796 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_781, x_795);
if (x_796 == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; uint8_t x_805; 
lean_dec(x_777);
x_797 = lean_box(0);
x_798 = lean_nat_add(x_778, x_773);
x_799 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_799, 0, x_781);
lean_ctor_set(x_799, 1, x_797);
lean_ctor_set(x_799, 2, x_795);
x_800 = lean_array_uset(x_779, x_794, x_799);
x_801 = lean_nat_mul(x_798, x_771);
x_802 = lean_unsigned_to_nat(3u);
x_803 = lean_nat_div(x_801, x_802);
lean_dec(x_801);
x_804 = lean_array_get_size(x_800);
x_805 = lean_nat_dec_le(x_803, x_804);
lean_dec(x_804);
lean_dec(x_803);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_800);
if (lean_is_scalar(x_133)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_133;
}
lean_ctor_set(x_807, 0, x_798);
lean_ctor_set(x_807, 1, x_806);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_807);
lean_ctor_set(x_808, 1, x_775);
return x_808;
}
else
{
lean_object* x_809; lean_object* x_810; 
if (lean_is_scalar(x_133)) {
 x_809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_809 = x_133;
}
lean_ctor_set(x_809, 0, x_798);
lean_ctor_set(x_809, 1, x_800);
x_810 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_775);
return x_810;
}
}
else
{
lean_object* x_811; 
lean_dec(x_795);
lean_dec(x_781);
lean_dec(x_779);
if (lean_is_scalar(x_133)) {
 x_811 = lean_alloc_ctor(0, 2, 0);
} else {
 x_811 = x_133;
}
lean_ctor_set(x_811, 0, x_777);
lean_ctor_set(x_811, 1, x_775);
return x_811;
}
}
block_858:
{
lean_object* x_815; lean_object* x_816; 
lean_inc(x_814);
lean_inc(x_766);
x_815 = l_Lean_mkApp3(x_774, x_813, x_766, x_814);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_816 = l_Lean_Meta_mkDecideProof(x_815, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
x_819 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60;
x_820 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64;
lean_inc(x_766);
x_821 = l_Lean_mkApp4(x_819, x_813, x_820, x_814, x_766);
x_822 = l_Lean_Meta_mkDecideProof(x_821, x_3, x_4, x_5, x_6, x_818);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; uint64_t x_828; uint64_t x_829; uint64_t x_830; uint64_t x_831; uint64_t x_832; uint64_t x_833; uint64_t x_834; size_t x_835; size_t x_836; size_t x_837; lean_object* x_838; uint8_t x_839; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
x_825 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_826 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
lean_inc(x_766);
lean_inc(x_772);
x_827 = l_Lean_mkApp3(x_826, x_772, x_766, x_817);
x_828 = l_Lean_Expr_hash(x_827);
x_829 = 32;
x_830 = lean_uint64_shift_right(x_828, x_829);
x_831 = lean_uint64_xor(x_828, x_830);
x_832 = 16;
x_833 = lean_uint64_shift_right(x_831, x_832);
x_834 = lean_uint64_xor(x_831, x_833);
x_835 = lean_uint64_to_usize(x_834);
x_836 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_837 = lean_usize_land(x_835, x_836);
x_838 = lean_array_uget(x_825, x_837);
x_839 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_827, x_838);
if (x_839 == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; uint8_t x_845; 
x_840 = lean_box(0);
x_841 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_841, 0, x_827);
lean_ctor_set(x_841, 1, x_840);
lean_ctor_set(x_841, 2, x_838);
x_842 = lean_array_uset(x_825, x_837, x_841);
x_843 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_844 = lean_array_get_size(x_842);
x_845 = lean_nat_dec_le(x_843, x_844);
lean_dec(x_844);
if (x_845 == 0)
{
lean_object* x_846; lean_object* x_847; 
x_846 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_842);
lean_inc(x_846);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_773);
lean_ctor_set(x_847, 1, x_846);
x_775 = x_824;
x_776 = x_823;
x_777 = x_847;
x_778 = x_773;
x_779 = x_846;
goto block_812;
}
else
{
lean_object* x_848; 
lean_inc(x_842);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_773);
lean_ctor_set(x_848, 1, x_842);
x_775 = x_824;
x_776 = x_823;
x_777 = x_848;
x_778 = x_773;
x_779 = x_842;
goto block_812;
}
}
else
{
lean_object* x_849; 
lean_dec(x_838);
lean_dec(x_827);
x_849 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_775 = x_824;
x_776 = x_823;
x_777 = x_849;
x_778 = x_769;
x_779 = x_825;
goto block_812;
}
}
else
{
uint8_t x_850; 
lean_dec(x_817);
lean_dec(x_772);
lean_dec(x_766);
lean_dec(x_133);
x_850 = !lean_is_exclusive(x_822);
if (x_850 == 0)
{
return x_822;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_851 = lean_ctor_get(x_822, 0);
x_852 = lean_ctor_get(x_822, 1);
lean_inc(x_852);
lean_inc(x_851);
lean_dec(x_822);
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_851);
lean_ctor_set(x_853, 1, x_852);
return x_853;
}
}
}
else
{
uint8_t x_854; 
lean_dec(x_814);
lean_dec(x_772);
lean_dec(x_766);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_854 = !lean_is_exclusive(x_816);
if (x_854 == 0)
{
return x_816;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_855 = lean_ctor_get(x_816, 0);
x_856 = lean_ctor_get(x_816, 1);
lean_inc(x_856);
lean_inc(x_855);
lean_dec(x_816);
x_857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
return x_857;
}
}
}
}
else
{
lean_dec(x_766);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_862; uint8_t x_863; 
lean_dec(x_135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_862 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_863 = lean_string_dec_eq(x_134, x_862);
lean_dec(x_134);
if (x_863 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_864; lean_object* x_865; uint8_t x_866; 
x_864 = lean_array_get_size(x_132);
x_865 = lean_unsigned_to_nat(3u);
x_866 = lean_nat_dec_eq(x_864, x_865);
lean_dec(x_864);
if (x_866 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_867; lean_object* x_868; 
x_867 = lean_unsigned_to_nat(0u);
x_868 = lean_array_fget(x_132, x_867);
if (lean_obj_tag(x_868) == 4)
{
lean_object* x_869; 
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
if (lean_obj_tag(x_869) == 1)
{
lean_object* x_870; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; 
x_871 = lean_ctor_get(x_868, 1);
lean_inc(x_871);
lean_dec(x_868);
x_872 = lean_ctor_get(x_869, 1);
lean_inc(x_872);
lean_dec(x_869);
x_873 = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
x_874 = lean_string_dec_eq(x_872, x_873);
lean_dec(x_872);
if (x_874 == 0)
{
lean_dec(x_871);
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
else
{
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1076; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; uint64_t x_1348; uint64_t x_1349; uint64_t x_1350; uint64_t x_1351; uint64_t x_1352; uint64_t x_1353; uint64_t x_1354; size_t x_1355; size_t x_1356; size_t x_1357; lean_object* x_1358; uint8_t x_1359; 
x_875 = lean_unsigned_to_nat(2u);
x_876 = lean_array_fget(x_132, x_875);
lean_dec(x_132);
x_877 = lean_unsigned_to_nat(4u);
x_1344 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__3;
x_1345 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__98;
x_1346 = l_Lean_Expr_const___override(x_1345, x_871);
lean_inc(x_876);
x_1347 = l_Lean_Expr_app___override(x_1346, x_876);
x_1348 = l_Lean_Expr_hash(x_1347);
x_1349 = 32;
x_1350 = lean_uint64_shift_right(x_1348, x_1349);
x_1351 = lean_uint64_xor(x_1348, x_1350);
x_1352 = 16;
x_1353 = lean_uint64_shift_right(x_1351, x_1352);
x_1354 = lean_uint64_xor(x_1351, x_1353);
x_1355 = lean_uint64_to_usize(x_1354);
x_1356 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
x_1357 = lean_usize_land(x_1355, x_1356);
x_1358 = lean_array_uget(x_1344, x_1357);
x_1359 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1347, x_1358);
if (x_1359 == 0)
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; uint8_t x_1366; 
x_1360 = lean_box(0);
x_1361 = lean_unsigned_to_nat(1u);
x_1362 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1362, 0, x_1347);
lean_ctor_set(x_1362, 1, x_1360);
lean_ctor_set(x_1362, 2, x_1358);
x_1363 = lean_array_uset(x_1344, x_1357, x_1362);
x_1364 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
x_1365 = lean_array_get_size(x_1363);
x_1366 = lean_nat_dec_le(x_1364, x_1365);
lean_dec(x_1365);
if (x_1366 == 0)
{
lean_object* x_1367; lean_object* x_1368; 
x_1367 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_1363);
x_1368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1368, 0, x_1361);
lean_ctor_set(x_1368, 1, x_1367);
x_1076 = x_1368;
goto block_1343;
}
else
{
lean_object* x_1369; 
x_1369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1369, 0, x_1361);
lean_ctor_set(x_1369, 1, x_1363);
x_1076 = x_1369;
goto block_1343;
}
}
else
{
lean_object* x_1370; 
lean_dec(x_1358);
lean_dec(x_1347);
x_1370 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_1076 = x_1370;
goto block_1343;
}
block_932:
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; uint64_t x_888; uint64_t x_889; uint64_t x_890; uint64_t x_891; uint64_t x_892; uint64_t x_893; uint64_t x_894; size_t x_895; size_t x_896; size_t x_897; size_t x_898; size_t x_899; lean_object* x_900; uint8_t x_901; 
x_882 = lean_ctor_get(x_878, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_878, 1);
lean_inc(x_883);
x_884 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
x_885 = l_Lean_Expr_const___override(x_884, x_871);
x_886 = l_Lean_mkAppB(x_885, x_879, x_880);
x_887 = lean_array_get_size(x_883);
x_888 = l_Lean_Expr_hash(x_886);
x_889 = 32;
x_890 = lean_uint64_shift_right(x_888, x_889);
x_891 = lean_uint64_xor(x_888, x_890);
x_892 = 16;
x_893 = lean_uint64_shift_right(x_891, x_892);
x_894 = lean_uint64_xor(x_891, x_893);
x_895 = lean_uint64_to_usize(x_894);
x_896 = lean_usize_of_nat(x_887);
lean_dec(x_887);
x_897 = 1;
x_898 = lean_usize_sub(x_896, x_897);
x_899 = lean_usize_land(x_895, x_898);
x_900 = lean_array_uget(x_883, x_899);
x_901 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_886, x_900);
if (x_901 == 0)
{
uint8_t x_902; 
x_902 = !lean_is_exclusive(x_878);
if (x_902 == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; uint8_t x_913; 
x_903 = lean_ctor_get(x_878, 1);
lean_dec(x_903);
x_904 = lean_ctor_get(x_878, 0);
lean_dec(x_904);
x_905 = lean_box(0);
x_906 = lean_unsigned_to_nat(1u);
x_907 = lean_nat_add(x_882, x_906);
lean_dec(x_882);
x_908 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_908, 0, x_886);
lean_ctor_set(x_908, 1, x_905);
lean_ctor_set(x_908, 2, x_900);
x_909 = lean_array_uset(x_883, x_899, x_908);
x_910 = lean_nat_mul(x_907, x_877);
x_911 = lean_nat_div(x_910, x_865);
lean_dec(x_910);
x_912 = lean_array_get_size(x_909);
x_913 = lean_nat_dec_le(x_911, x_912);
lean_dec(x_912);
lean_dec(x_911);
if (x_913 == 0)
{
lean_object* x_914; lean_object* x_915; 
x_914 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_909);
lean_ctor_set(x_878, 1, x_914);
lean_ctor_set(x_878, 0, x_907);
if (lean_is_scalar(x_133)) {
 x_915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_915 = x_133;
}
lean_ctor_set(x_915, 0, x_878);
lean_ctor_set(x_915, 1, x_881);
return x_915;
}
else
{
lean_object* x_916; 
lean_ctor_set(x_878, 1, x_909);
lean_ctor_set(x_878, 0, x_907);
if (lean_is_scalar(x_133)) {
 x_916 = lean_alloc_ctor(0, 2, 0);
} else {
 x_916 = x_133;
}
lean_ctor_set(x_916, 0, x_878);
lean_ctor_set(x_916, 1, x_881);
return x_916;
}
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint8_t x_925; 
lean_dec(x_878);
x_917 = lean_box(0);
x_918 = lean_unsigned_to_nat(1u);
x_919 = lean_nat_add(x_882, x_918);
lean_dec(x_882);
x_920 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_920, 0, x_886);
lean_ctor_set(x_920, 1, x_917);
lean_ctor_set(x_920, 2, x_900);
x_921 = lean_array_uset(x_883, x_899, x_920);
x_922 = lean_nat_mul(x_919, x_877);
x_923 = lean_nat_div(x_922, x_865);
lean_dec(x_922);
x_924 = lean_array_get_size(x_921);
x_925 = lean_nat_dec_le(x_923, x_924);
lean_dec(x_924);
lean_dec(x_923);
if (x_925 == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_926 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_921);
x_927 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_927, 0, x_919);
lean_ctor_set(x_927, 1, x_926);
if (lean_is_scalar(x_133)) {
 x_928 = lean_alloc_ctor(0, 2, 0);
} else {
 x_928 = x_133;
}
lean_ctor_set(x_928, 0, x_927);
lean_ctor_set(x_928, 1, x_881);
return x_928;
}
else
{
lean_object* x_929; lean_object* x_930; 
x_929 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_929, 0, x_919);
lean_ctor_set(x_929, 1, x_921);
if (lean_is_scalar(x_133)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_133;
}
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_881);
return x_930;
}
}
}
else
{
lean_object* x_931; 
lean_dec(x_900);
lean_dec(x_886);
lean_dec(x_883);
lean_dec(x_882);
if (lean_is_scalar(x_133)) {
 x_931 = lean_alloc_ctor(0, 2, 0);
} else {
 x_931 = x_133;
}
lean_ctor_set(x_931, 0, x_878);
lean_ctor_set(x_931, 1, x_881);
return x_931;
}
}
block_987:
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint64_t x_943; uint64_t x_944; uint64_t x_945; uint64_t x_946; uint64_t x_947; uint64_t x_948; uint64_t x_949; size_t x_950; size_t x_951; size_t x_952; size_t x_953; size_t x_954; lean_object* x_955; uint8_t x_956; 
x_937 = lean_ctor_get(x_933, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_933, 1);
lean_inc(x_938);
x_939 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
x_940 = l_Lean_Expr_const___override(x_939, x_871);
x_941 = l_Lean_mkAppB(x_940, x_934, x_935);
x_942 = lean_array_get_size(x_938);
x_943 = l_Lean_Expr_hash(x_941);
x_944 = 32;
x_945 = lean_uint64_shift_right(x_943, x_944);
x_946 = lean_uint64_xor(x_943, x_945);
x_947 = 16;
x_948 = lean_uint64_shift_right(x_946, x_947);
x_949 = lean_uint64_xor(x_946, x_948);
x_950 = lean_uint64_to_usize(x_949);
x_951 = lean_usize_of_nat(x_942);
lean_dec(x_942);
x_952 = 1;
x_953 = lean_usize_sub(x_951, x_952);
x_954 = lean_usize_land(x_950, x_953);
x_955 = lean_array_uget(x_938, x_954);
x_956 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_941, x_955);
if (x_956 == 0)
{
uint8_t x_957; 
x_957 = !lean_is_exclusive(x_933);
if (x_957 == 0)
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_968; 
x_958 = lean_ctor_get(x_933, 1);
lean_dec(x_958);
x_959 = lean_ctor_get(x_933, 0);
lean_dec(x_959);
x_960 = lean_box(0);
x_961 = lean_unsigned_to_nat(1u);
x_962 = lean_nat_add(x_937, x_961);
lean_dec(x_937);
x_963 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_963, 0, x_941);
lean_ctor_set(x_963, 1, x_960);
lean_ctor_set(x_963, 2, x_955);
x_964 = lean_array_uset(x_938, x_954, x_963);
x_965 = lean_nat_mul(x_962, x_877);
x_966 = lean_nat_div(x_965, x_865);
lean_dec(x_965);
x_967 = lean_array_get_size(x_964);
x_968 = lean_nat_dec_le(x_966, x_967);
lean_dec(x_967);
lean_dec(x_966);
if (x_968 == 0)
{
lean_object* x_969; lean_object* x_970; 
x_969 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_964);
lean_ctor_set(x_933, 1, x_969);
lean_ctor_set(x_933, 0, x_962);
x_970 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_970, 0, x_933);
lean_ctor_set(x_970, 1, x_936);
return x_970;
}
else
{
lean_object* x_971; 
lean_ctor_set(x_933, 1, x_964);
lean_ctor_set(x_933, 0, x_962);
x_971 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_971, 0, x_933);
lean_ctor_set(x_971, 1, x_936);
return x_971;
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; uint8_t x_980; 
lean_dec(x_933);
x_972 = lean_box(0);
x_973 = lean_unsigned_to_nat(1u);
x_974 = lean_nat_add(x_937, x_973);
lean_dec(x_937);
x_975 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_975, 0, x_941);
lean_ctor_set(x_975, 1, x_972);
lean_ctor_set(x_975, 2, x_955);
x_976 = lean_array_uset(x_938, x_954, x_975);
x_977 = lean_nat_mul(x_974, x_877);
x_978 = lean_nat_div(x_977, x_865);
lean_dec(x_977);
x_979 = lean_array_get_size(x_976);
x_980 = lean_nat_dec_le(x_978, x_979);
lean_dec(x_979);
lean_dec(x_978);
if (x_980 == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_976);
x_982 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_982, 0, x_974);
lean_ctor_set(x_982, 1, x_981);
x_983 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_936);
return x_983;
}
else
{
lean_object* x_984; lean_object* x_985; 
x_984 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_984, 0, x_974);
lean_ctor_set(x_984, 1, x_976);
x_985 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_936);
return x_985;
}
}
}
else
{
lean_object* x_986; 
lean_dec(x_955);
lean_dec(x_941);
lean_dec(x_938);
lean_dec(x_937);
x_986 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_986, 0, x_933);
lean_ctor_set(x_986, 1, x_936);
return x_986;
}
}
block_1026:
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; uint64_t x_997; uint64_t x_998; uint64_t x_999; uint64_t x_1000; uint64_t x_1001; uint64_t x_1002; uint64_t x_1003; size_t x_1004; size_t x_1005; size_t x_1006; size_t x_1007; size_t x_1008; lean_object* x_1009; uint8_t x_1010; 
x_993 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89;
x_994 = l_Lean_Expr_const___override(x_993, x_871);
x_995 = l_Lean_Expr_app___override(x_994, x_989);
x_996 = lean_array_get_size(x_992);
x_997 = l_Lean_Expr_hash(x_995);
x_998 = 32;
x_999 = lean_uint64_shift_right(x_997, x_998);
x_1000 = lean_uint64_xor(x_997, x_999);
x_1001 = 16;
x_1002 = lean_uint64_shift_right(x_1000, x_1001);
x_1003 = lean_uint64_xor(x_1000, x_1002);
x_1004 = lean_uint64_to_usize(x_1003);
x_1005 = lean_usize_of_nat(x_996);
lean_dec(x_996);
x_1006 = 1;
x_1007 = lean_usize_sub(x_1005, x_1006);
x_1008 = lean_usize_land(x_1004, x_1007);
x_1009 = lean_array_uget(x_992, x_1008);
x_1010 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_995, x_1009);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; uint8_t x_1019; 
lean_dec(x_990);
x_1011 = lean_box(0);
x_1012 = lean_unsigned_to_nat(1u);
x_1013 = lean_nat_add(x_991, x_1012);
lean_dec(x_991);
x_1014 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1014, 0, x_995);
lean_ctor_set(x_1014, 1, x_1011);
lean_ctor_set(x_1014, 2, x_1009);
x_1015 = lean_array_uset(x_992, x_1008, x_1014);
x_1016 = lean_nat_mul(x_1013, x_877);
x_1017 = lean_nat_div(x_1016, x_865);
lean_dec(x_1016);
x_1018 = lean_array_get_size(x_1015);
x_1019 = lean_nat_dec_le(x_1017, x_1018);
lean_dec(x_1018);
lean_dec(x_1017);
if (x_1019 == 0)
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1020 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_1015);
x_1021 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1021, 0, x_1013);
lean_ctor_set(x_1021, 1, x_1020);
x_1022 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_988);
return x_1022;
}
else
{
lean_object* x_1023; lean_object* x_1024; 
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1013);
lean_ctor_set(x_1023, 1, x_1015);
x_1024 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1024, 0, x_1023);
lean_ctor_set(x_1024, 1, x_988);
return x_1024;
}
}
else
{
lean_object* x_1025; 
lean_dec(x_1009);
lean_dec(x_995);
lean_dec(x_992);
lean_dec(x_991);
x_1025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1025, 0, x_990);
lean_ctor_set(x_1025, 1, x_988);
return x_1025;
}
}
block_1075:
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; uint64_t x_1036; uint64_t x_1037; uint64_t x_1038; uint64_t x_1039; uint64_t x_1040; uint64_t x_1041; uint64_t x_1042; size_t x_1043; size_t x_1044; size_t x_1045; size_t x_1046; size_t x_1047; lean_object* x_1048; uint8_t x_1049; 
x_1030 = lean_ctor_get(x_1027, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1027, 1);
lean_inc(x_1031);
x_1032 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
x_1033 = l_Lean_Expr_const___override(x_1032, x_871);
lean_inc(x_1028);
x_1034 = l_Lean_Expr_app___override(x_1033, x_1028);
x_1035 = lean_array_get_size(x_1031);
x_1036 = l_Lean_Expr_hash(x_1034);
x_1037 = 32;
x_1038 = lean_uint64_shift_right(x_1036, x_1037);
x_1039 = lean_uint64_xor(x_1036, x_1038);
x_1040 = 16;
x_1041 = lean_uint64_shift_right(x_1039, x_1040);
x_1042 = lean_uint64_xor(x_1039, x_1041);
x_1043 = lean_uint64_to_usize(x_1042);
x_1044 = lean_usize_of_nat(x_1035);
lean_dec(x_1035);
x_1045 = 1;
x_1046 = lean_usize_sub(x_1044, x_1045);
x_1047 = lean_usize_land(x_1043, x_1046);
x_1048 = lean_array_uget(x_1031, x_1047);
x_1049 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1034, x_1048);
if (x_1049 == 0)
{
uint8_t x_1050; 
x_1050 = !lean_is_exclusive(x_1027);
if (x_1050 == 0)
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; 
x_1051 = lean_ctor_get(x_1027, 1);
lean_dec(x_1051);
x_1052 = lean_ctor_get(x_1027, 0);
lean_dec(x_1052);
x_1053 = lean_box(0);
x_1054 = lean_unsigned_to_nat(1u);
x_1055 = lean_nat_add(x_1030, x_1054);
lean_dec(x_1030);
x_1056 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1056, 0, x_1034);
lean_ctor_set(x_1056, 1, x_1053);
lean_ctor_set(x_1056, 2, x_1048);
x_1057 = lean_array_uset(x_1031, x_1047, x_1056);
x_1058 = lean_nat_mul(x_1055, x_877);
x_1059 = lean_nat_div(x_1058, x_865);
lean_dec(x_1058);
x_1060 = lean_array_get_size(x_1057);
x_1061 = lean_nat_dec_le(x_1059, x_1060);
lean_dec(x_1060);
lean_dec(x_1059);
if (x_1061 == 0)
{
lean_object* x_1062; 
x_1062 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_1057);
lean_inc(x_1062);
lean_inc(x_1055);
lean_ctor_set(x_1027, 1, x_1062);
lean_ctor_set(x_1027, 0, x_1055);
x_988 = x_1029;
x_989 = x_1028;
x_990 = x_1027;
x_991 = x_1055;
x_992 = x_1062;
goto block_1026;
}
else
{
lean_inc(x_1057);
lean_inc(x_1055);
lean_ctor_set(x_1027, 1, x_1057);
lean_ctor_set(x_1027, 0, x_1055);
x_988 = x_1029;
x_989 = x_1028;
x_990 = x_1027;
x_991 = x_1055;
x_992 = x_1057;
goto block_1026;
}
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; uint8_t x_1071; 
lean_dec(x_1027);
x_1063 = lean_box(0);
x_1064 = lean_unsigned_to_nat(1u);
x_1065 = lean_nat_add(x_1030, x_1064);
lean_dec(x_1030);
x_1066 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1066, 0, x_1034);
lean_ctor_set(x_1066, 1, x_1063);
lean_ctor_set(x_1066, 2, x_1048);
x_1067 = lean_array_uset(x_1031, x_1047, x_1066);
x_1068 = lean_nat_mul(x_1065, x_877);
x_1069 = lean_nat_div(x_1068, x_865);
lean_dec(x_1068);
x_1070 = lean_array_get_size(x_1067);
x_1071 = lean_nat_dec_le(x_1069, x_1070);
lean_dec(x_1070);
lean_dec(x_1069);
if (x_1071 == 0)
{
lean_object* x_1072; lean_object* x_1073; 
x_1072 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_1067);
lean_inc(x_1072);
lean_inc(x_1065);
x_1073 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1073, 0, x_1065);
lean_ctor_set(x_1073, 1, x_1072);
x_988 = x_1029;
x_989 = x_1028;
x_990 = x_1073;
x_991 = x_1065;
x_992 = x_1072;
goto block_1026;
}
else
{
lean_object* x_1074; 
lean_inc(x_1067);
lean_inc(x_1065);
x_1074 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1074, 0, x_1065);
lean_ctor_set(x_1074, 1, x_1067);
x_988 = x_1029;
x_989 = x_1028;
x_990 = x_1074;
x_991 = x_1065;
x_992 = x_1067;
goto block_1026;
}
}
}
else
{
lean_dec(x_1048);
lean_dec(x_1034);
x_988 = x_1029;
x_989 = x_1028;
x_990 = x_1027;
x_991 = x_1030;
x_992 = x_1031;
goto block_1026;
}
}
block_1343:
{
uint8_t x_1077; 
x_1077 = lean_ctor_get_uint8(x_2, 1);
if (x_1077 == 0)
{
lean_object* x_1078; lean_object* x_1079; 
x_1078 = l_Lean_Expr_getAppFnArgs(x_876);
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
if (lean_obj_tag(x_1079) == 1)
{
lean_object* x_1080; 
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc(x_1080);
if (lean_obj_tag(x_1080) == 1)
{
lean_object* x_1081; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
if (lean_obj_tag(x_1081) == 0)
{
uint8_t x_1082; 
x_1082 = !lean_is_exclusive(x_1078);
if (x_1082 == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; uint8_t x_1087; 
x_1083 = lean_ctor_get(x_1078, 1);
x_1084 = lean_ctor_get(x_1078, 0);
lean_dec(x_1084);
x_1085 = lean_ctor_get(x_1079, 1);
lean_inc(x_1085);
lean_dec(x_1079);
x_1086 = lean_ctor_get(x_1080, 1);
lean_inc(x_1086);
lean_dec(x_1080);
x_1087 = lean_string_dec_eq(x_1086, x_873);
if (x_1087 == 0)
{
lean_object* x_1088; uint8_t x_1089; 
x_1088 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
x_1089 = lean_string_dec_eq(x_1086, x_1088);
if (x_1089 == 0)
{
lean_object* x_1090; uint8_t x_1091; 
x_1090 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
x_1091 = lean_string_dec_eq(x_1086, x_1090);
lean_dec(x_1086);
if (x_1091 == 0)
{
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_133);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1092; uint8_t x_1093; 
x_1092 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92;
x_1093 = lean_string_dec_eq(x_1085, x_1092);
lean_dec(x_1085);
if (x_1093 == 0)
{
lean_dec(x_1083);
lean_dec(x_133);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1094; uint8_t x_1095; 
x_1094 = lean_array_get_size(x_1083);
x_1095 = lean_nat_dec_eq(x_1094, x_875);
lean_dec(x_1094);
if (x_1095 == 0)
{
lean_dec(x_1083);
lean_dec(x_133);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
lean_free_object(x_1078);
x_1096 = lean_array_fget(x_1083, x_867);
x_1097 = lean_unsigned_to_nat(1u);
x_1098 = lean_array_fget(x_1083, x_1097);
lean_dec(x_1083);
x_878 = x_1076;
x_879 = x_1096;
x_880 = x_1098;
x_881 = x_7;
goto block_932;
}
}
}
}
else
{
lean_object* x_1099; uint8_t x_1100; 
lean_dec(x_1086);
lean_dec(x_133);
x_1099 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
x_1100 = lean_string_dec_eq(x_1085, x_1099);
lean_dec(x_1085);
if (x_1100 == 0)
{
lean_dec(x_1083);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1101; uint8_t x_1102; 
x_1101 = lean_array_get_size(x_1083);
x_1102 = lean_nat_dec_eq(x_1101, x_875);
lean_dec(x_1101);
if (x_1102 == 0)
{
lean_dec(x_1083);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_free_object(x_1078);
x_1103 = lean_array_fget(x_1083, x_867);
x_1104 = lean_unsigned_to_nat(1u);
x_1105 = lean_array_fget(x_1083, x_1104);
lean_dec(x_1083);
x_933 = x_1076;
x_934 = x_1103;
x_935 = x_1105;
x_936 = x_7;
goto block_987;
}
}
}
}
else
{
lean_object* x_1106; uint8_t x_1107; 
lean_dec(x_1086);
lean_dec(x_133);
x_1106 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94;
x_1107 = lean_string_dec_eq(x_1085, x_1106);
lean_dec(x_1085);
if (x_1107 == 0)
{
lean_dec(x_1083);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1108; lean_object* x_1109; uint8_t x_1110; 
x_1108 = lean_array_get_size(x_1083);
x_1109 = lean_unsigned_to_nat(1u);
x_1110 = lean_nat_dec_eq(x_1108, x_1109);
lean_dec(x_1108);
if (x_1110 == 0)
{
lean_dec(x_1083);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1111; 
lean_free_object(x_1078);
x_1111 = lean_array_fget(x_1083, x_867);
lean_dec(x_1083);
x_1027 = x_1076;
x_1028 = x_1111;
x_1029 = x_7;
goto block_1075;
}
}
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; uint8_t x_1115; 
x_1112 = lean_ctor_get(x_1078, 1);
lean_inc(x_1112);
lean_dec(x_1078);
x_1113 = lean_ctor_get(x_1079, 1);
lean_inc(x_1113);
lean_dec(x_1079);
x_1114 = lean_ctor_get(x_1080, 1);
lean_inc(x_1114);
lean_dec(x_1080);
x_1115 = lean_string_dec_eq(x_1114, x_873);
if (x_1115 == 0)
{
lean_object* x_1116; uint8_t x_1117; 
x_1116 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
x_1117 = lean_string_dec_eq(x_1114, x_1116);
if (x_1117 == 0)
{
lean_object* x_1118; uint8_t x_1119; 
x_1118 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
x_1119 = lean_string_dec_eq(x_1114, x_1118);
lean_dec(x_1114);
if (x_1119 == 0)
{
lean_object* x_1120; 
lean_dec(x_1113);
lean_dec(x_1112);
lean_dec(x_133);
x_1120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1120, 0, x_1076);
lean_ctor_set(x_1120, 1, x_7);
return x_1120;
}
else
{
lean_object* x_1121; uint8_t x_1122; 
x_1121 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92;
x_1122 = lean_string_dec_eq(x_1113, x_1121);
lean_dec(x_1113);
if (x_1122 == 0)
{
lean_object* x_1123; 
lean_dec(x_1112);
lean_dec(x_133);
x_1123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1123, 0, x_1076);
lean_ctor_set(x_1123, 1, x_7);
return x_1123;
}
else
{
lean_object* x_1124; uint8_t x_1125; 
x_1124 = lean_array_get_size(x_1112);
x_1125 = lean_nat_dec_eq(x_1124, x_875);
lean_dec(x_1124);
if (x_1125 == 0)
{
lean_object* x_1126; 
lean_dec(x_1112);
lean_dec(x_133);
x_1126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1126, 0, x_1076);
lean_ctor_set(x_1126, 1, x_7);
return x_1126;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1127 = lean_array_fget(x_1112, x_867);
x_1128 = lean_unsigned_to_nat(1u);
x_1129 = lean_array_fget(x_1112, x_1128);
lean_dec(x_1112);
x_878 = x_1076;
x_879 = x_1127;
x_880 = x_1129;
x_881 = x_7;
goto block_932;
}
}
}
}
else
{
lean_object* x_1130; uint8_t x_1131; 
lean_dec(x_1114);
lean_dec(x_133);
x_1130 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
x_1131 = lean_string_dec_eq(x_1113, x_1130);
lean_dec(x_1113);
if (x_1131 == 0)
{
lean_object* x_1132; 
lean_dec(x_1112);
x_1132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1132, 0, x_1076);
lean_ctor_set(x_1132, 1, x_7);
return x_1132;
}
else
{
lean_object* x_1133; uint8_t x_1134; 
x_1133 = lean_array_get_size(x_1112);
x_1134 = lean_nat_dec_eq(x_1133, x_875);
lean_dec(x_1133);
if (x_1134 == 0)
{
lean_object* x_1135; 
lean_dec(x_1112);
x_1135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1135, 0, x_1076);
lean_ctor_set(x_1135, 1, x_7);
return x_1135;
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1136 = lean_array_fget(x_1112, x_867);
x_1137 = lean_unsigned_to_nat(1u);
x_1138 = lean_array_fget(x_1112, x_1137);
lean_dec(x_1112);
x_933 = x_1076;
x_934 = x_1136;
x_935 = x_1138;
x_936 = x_7;
goto block_987;
}
}
}
}
else
{
lean_object* x_1139; uint8_t x_1140; 
lean_dec(x_1114);
lean_dec(x_133);
x_1139 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94;
x_1140 = lean_string_dec_eq(x_1113, x_1139);
lean_dec(x_1113);
if (x_1140 == 0)
{
lean_object* x_1141; 
lean_dec(x_1112);
x_1141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1141, 0, x_1076);
lean_ctor_set(x_1141, 1, x_7);
return x_1141;
}
else
{
lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; 
x_1142 = lean_array_get_size(x_1112);
x_1143 = lean_unsigned_to_nat(1u);
x_1144 = lean_nat_dec_eq(x_1142, x_1143);
lean_dec(x_1142);
if (x_1144 == 0)
{
lean_object* x_1145; 
lean_dec(x_1112);
x_1145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1145, 0, x_1076);
lean_ctor_set(x_1145, 1, x_7);
return x_1145;
}
else
{
lean_object* x_1146; 
x_1146 = lean_array_fget(x_1112, x_867);
lean_dec(x_1112);
x_1027 = x_1076;
x_1028 = x_1146;
x_1029 = x_7;
goto block_1075;
}
}
}
}
}
else
{
uint8_t x_1147; 
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_133);
x_1147 = !lean_is_exclusive(x_1078);
if (x_1147 == 0)
{
lean_object* x_1148; lean_object* x_1149; 
x_1148 = lean_ctor_get(x_1078, 1);
lean_dec(x_1148);
x_1149 = lean_ctor_get(x_1078, 0);
lean_dec(x_1149);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1150; 
lean_dec(x_1078);
x_1150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1150, 0, x_1076);
lean_ctor_set(x_1150, 1, x_7);
return x_1150;
}
}
}
else
{
uint8_t x_1151; 
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_133);
x_1151 = !lean_is_exclusive(x_1078);
if (x_1151 == 0)
{
lean_object* x_1152; lean_object* x_1153; 
x_1152 = lean_ctor_get(x_1078, 1);
lean_dec(x_1152);
x_1153 = lean_ctor_get(x_1078, 0);
lean_dec(x_1153);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1154; 
lean_dec(x_1078);
x_1154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1154, 0, x_1076);
lean_ctor_set(x_1154, 1, x_7);
return x_1154;
}
}
}
else
{
uint8_t x_1155; 
lean_dec(x_1079);
lean_dec(x_133);
x_1155 = !lean_is_exclusive(x_1078);
if (x_1155 == 0)
{
lean_object* x_1156; lean_object* x_1157; 
x_1156 = lean_ctor_get(x_1078, 1);
lean_dec(x_1156);
x_1157 = lean_ctor_get(x_1078, 0);
lean_dec(x_1157);
lean_ctor_set(x_1078, 1, x_7);
lean_ctor_set(x_1078, 0, x_1076);
return x_1078;
}
else
{
lean_object* x_1158; 
lean_dec(x_1078);
x_1158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1158, 0, x_1076);
lean_ctor_set(x_1158, 1, x_7);
return x_1158;
}
}
}
else
{
lean_object* x_1159; lean_object* x_1160; 
x_1159 = l_Lean_Expr_getAppFnArgs(x_876);
x_1160 = lean_ctor_get(x_1159, 0);
lean_inc(x_1160);
if (lean_obj_tag(x_1160) == 1)
{
lean_object* x_1161; 
x_1161 = lean_ctor_get(x_1160, 0);
lean_inc(x_1161);
if (lean_obj_tag(x_1161) == 1)
{
lean_object* x_1162; 
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
if (lean_obj_tag(x_1162) == 0)
{
uint8_t x_1163; 
x_1163 = !lean_is_exclusive(x_1159);
if (x_1163 == 0)
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; uint8_t x_1169; 
x_1164 = lean_ctor_get(x_1159, 1);
x_1165 = lean_ctor_get(x_1159, 0);
lean_dec(x_1165);
x_1166 = lean_ctor_get(x_1160, 1);
lean_inc(x_1166);
lean_dec(x_1160);
x_1167 = lean_ctor_get(x_1161, 1);
lean_inc(x_1167);
lean_dec(x_1161);
x_1168 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_1169 = lean_string_dec_eq(x_1167, x_1168);
if (x_1169 == 0)
{
uint8_t x_1170; 
x_1170 = lean_string_dec_eq(x_1167, x_873);
if (x_1170 == 0)
{
lean_object* x_1171; uint8_t x_1172; 
x_1171 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
x_1172 = lean_string_dec_eq(x_1167, x_1171);
if (x_1172 == 0)
{
lean_object* x_1173; uint8_t x_1174; 
x_1173 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
x_1174 = lean_string_dec_eq(x_1167, x_1173);
lean_dec(x_1167);
if (x_1174 == 0)
{
lean_dec(x_1166);
lean_dec(x_1164);
lean_dec(x_133);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1175; uint8_t x_1176; 
x_1175 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92;
x_1176 = lean_string_dec_eq(x_1166, x_1175);
lean_dec(x_1166);
if (x_1176 == 0)
{
lean_dec(x_1164);
lean_dec(x_133);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1177; uint8_t x_1178; 
x_1177 = lean_array_get_size(x_1164);
x_1178 = lean_nat_dec_eq(x_1177, x_875);
lean_dec(x_1177);
if (x_1178 == 0)
{
lean_dec(x_1164);
lean_dec(x_133);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
lean_free_object(x_1159);
x_1179 = lean_array_fget(x_1164, x_867);
x_1180 = lean_unsigned_to_nat(1u);
x_1181 = lean_array_fget(x_1164, x_1180);
lean_dec(x_1164);
x_878 = x_1076;
x_879 = x_1179;
x_880 = x_1181;
x_881 = x_7;
goto block_932;
}
}
}
}
else
{
lean_object* x_1182; uint8_t x_1183; 
lean_dec(x_1167);
lean_dec(x_133);
x_1182 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
x_1183 = lean_string_dec_eq(x_1166, x_1182);
lean_dec(x_1166);
if (x_1183 == 0)
{
lean_dec(x_1164);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1184; uint8_t x_1185; 
x_1184 = lean_array_get_size(x_1164);
x_1185 = lean_nat_dec_eq(x_1184, x_875);
lean_dec(x_1184);
if (x_1185 == 0)
{
lean_dec(x_1164);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
lean_free_object(x_1159);
x_1186 = lean_array_fget(x_1164, x_867);
x_1187 = lean_unsigned_to_nat(1u);
x_1188 = lean_array_fget(x_1164, x_1187);
lean_dec(x_1164);
x_933 = x_1076;
x_934 = x_1186;
x_935 = x_1188;
x_936 = x_7;
goto block_987;
}
}
}
}
else
{
lean_object* x_1189; uint8_t x_1190; 
lean_dec(x_1167);
lean_dec(x_133);
x_1189 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94;
x_1190 = lean_string_dec_eq(x_1166, x_1189);
lean_dec(x_1166);
if (x_1190 == 0)
{
lean_dec(x_1164);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1191; lean_object* x_1192; uint8_t x_1193; 
x_1191 = lean_array_get_size(x_1164);
x_1192 = lean_unsigned_to_nat(1u);
x_1193 = lean_nat_dec_eq(x_1191, x_1192);
lean_dec(x_1191);
if (x_1193 == 0)
{
lean_dec(x_1164);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1194; 
lean_free_object(x_1159);
x_1194 = lean_array_fget(x_1164, x_867);
lean_dec(x_1164);
x_1027 = x_1076;
x_1028 = x_1194;
x_1029 = x_7;
goto block_1075;
}
}
}
}
else
{
lean_object* x_1195; uint8_t x_1196; 
lean_dec(x_1167);
lean_dec(x_133);
x_1195 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_1196 = lean_string_dec_eq(x_1166, x_1195);
lean_dec(x_1166);
if (x_1196 == 0)
{
lean_dec(x_1164);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1197; lean_object* x_1198; uint8_t x_1199; 
x_1197 = lean_array_get_size(x_1164);
x_1198 = lean_unsigned_to_nat(6u);
x_1199 = lean_nat_dec_eq(x_1197, x_1198);
lean_dec(x_1197);
if (x_1199 == 0)
{
lean_dec(x_1164);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; uint64_t x_1209; uint64_t x_1210; uint64_t x_1211; uint64_t x_1212; uint64_t x_1213; uint64_t x_1214; uint64_t x_1215; size_t x_1216; size_t x_1217; size_t x_1218; size_t x_1219; size_t x_1220; lean_object* x_1221; uint8_t x_1222; 
x_1200 = lean_ctor_get(x_1076, 0);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1076, 1);
lean_inc(x_1201);
x_1202 = lean_array_fget(x_1164, x_877);
x_1203 = lean_unsigned_to_nat(5u);
x_1204 = lean_array_fget(x_1164, x_1203);
lean_dec(x_1164);
x_1205 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__96;
x_1206 = l_Lean_Expr_const___override(x_1205, x_871);
x_1207 = l_Lean_mkAppB(x_1206, x_1202, x_1204);
x_1208 = lean_array_get_size(x_1201);
x_1209 = l_Lean_Expr_hash(x_1207);
x_1210 = 32;
x_1211 = lean_uint64_shift_right(x_1209, x_1210);
x_1212 = lean_uint64_xor(x_1209, x_1211);
x_1213 = 16;
x_1214 = lean_uint64_shift_right(x_1212, x_1213);
x_1215 = lean_uint64_xor(x_1212, x_1214);
x_1216 = lean_uint64_to_usize(x_1215);
x_1217 = lean_usize_of_nat(x_1208);
lean_dec(x_1208);
x_1218 = 1;
x_1219 = lean_usize_sub(x_1217, x_1218);
x_1220 = lean_usize_land(x_1216, x_1219);
x_1221 = lean_array_uget(x_1201, x_1220);
x_1222 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1207, x_1221);
if (x_1222 == 0)
{
uint8_t x_1223; 
x_1223 = !lean_is_exclusive(x_1076);
if (x_1223 == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; 
x_1224 = lean_ctor_get(x_1076, 1);
lean_dec(x_1224);
x_1225 = lean_ctor_get(x_1076, 0);
lean_dec(x_1225);
x_1226 = lean_box(0);
x_1227 = lean_unsigned_to_nat(1u);
x_1228 = lean_nat_add(x_1200, x_1227);
lean_dec(x_1200);
x_1229 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1229, 0, x_1207);
lean_ctor_set(x_1229, 1, x_1226);
lean_ctor_set(x_1229, 2, x_1221);
x_1230 = lean_array_uset(x_1201, x_1220, x_1229);
x_1231 = lean_nat_mul(x_1228, x_877);
x_1232 = lean_nat_div(x_1231, x_865);
lean_dec(x_1231);
x_1233 = lean_array_get_size(x_1230);
x_1234 = lean_nat_dec_le(x_1232, x_1233);
lean_dec(x_1233);
lean_dec(x_1232);
if (x_1234 == 0)
{
lean_object* x_1235; 
x_1235 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_1230);
lean_ctor_set(x_1076, 1, x_1235);
lean_ctor_set(x_1076, 0, x_1228);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_ctor_set(x_1076, 1, x_1230);
lean_ctor_set(x_1076, 0, x_1228);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; uint8_t x_1244; 
lean_dec(x_1076);
x_1236 = lean_box(0);
x_1237 = lean_unsigned_to_nat(1u);
x_1238 = lean_nat_add(x_1200, x_1237);
lean_dec(x_1200);
x_1239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1239, 0, x_1207);
lean_ctor_set(x_1239, 1, x_1236);
lean_ctor_set(x_1239, 2, x_1221);
x_1240 = lean_array_uset(x_1201, x_1220, x_1239);
x_1241 = lean_nat_mul(x_1238, x_877);
x_1242 = lean_nat_div(x_1241, x_865);
lean_dec(x_1241);
x_1243 = lean_array_get_size(x_1240);
x_1244 = lean_nat_dec_le(x_1242, x_1243);
lean_dec(x_1243);
lean_dec(x_1242);
if (x_1244 == 0)
{
lean_object* x_1245; lean_object* x_1246; 
x_1245 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_1240);
x_1246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1246, 0, x_1238);
lean_ctor_set(x_1246, 1, x_1245);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1246);
return x_1159;
}
else
{
lean_object* x_1247; 
x_1247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1247, 0, x_1238);
lean_ctor_set(x_1247, 1, x_1240);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1247);
return x_1159;
}
}
}
else
{
lean_dec(x_1221);
lean_dec(x_1207);
lean_dec(x_1201);
lean_dec(x_1200);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
}
}
}
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; uint8_t x_1252; 
x_1248 = lean_ctor_get(x_1159, 1);
lean_inc(x_1248);
lean_dec(x_1159);
x_1249 = lean_ctor_get(x_1160, 1);
lean_inc(x_1249);
lean_dec(x_1160);
x_1250 = lean_ctor_get(x_1161, 1);
lean_inc(x_1250);
lean_dec(x_1161);
x_1251 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_1252 = lean_string_dec_eq(x_1250, x_1251);
if (x_1252 == 0)
{
uint8_t x_1253; 
x_1253 = lean_string_dec_eq(x_1250, x_873);
if (x_1253 == 0)
{
lean_object* x_1254; uint8_t x_1255; 
x_1254 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
x_1255 = lean_string_dec_eq(x_1250, x_1254);
if (x_1255 == 0)
{
lean_object* x_1256; uint8_t x_1257; 
x_1256 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
x_1257 = lean_string_dec_eq(x_1250, x_1256);
lean_dec(x_1250);
if (x_1257 == 0)
{
lean_object* x_1258; 
lean_dec(x_1249);
lean_dec(x_1248);
lean_dec(x_133);
x_1258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1258, 0, x_1076);
lean_ctor_set(x_1258, 1, x_7);
return x_1258;
}
else
{
lean_object* x_1259; uint8_t x_1260; 
x_1259 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92;
x_1260 = lean_string_dec_eq(x_1249, x_1259);
lean_dec(x_1249);
if (x_1260 == 0)
{
lean_object* x_1261; 
lean_dec(x_1248);
lean_dec(x_133);
x_1261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1261, 0, x_1076);
lean_ctor_set(x_1261, 1, x_7);
return x_1261;
}
else
{
lean_object* x_1262; uint8_t x_1263; 
x_1262 = lean_array_get_size(x_1248);
x_1263 = lean_nat_dec_eq(x_1262, x_875);
lean_dec(x_1262);
if (x_1263 == 0)
{
lean_object* x_1264; 
lean_dec(x_1248);
lean_dec(x_133);
x_1264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1264, 0, x_1076);
lean_ctor_set(x_1264, 1, x_7);
return x_1264;
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1265 = lean_array_fget(x_1248, x_867);
x_1266 = lean_unsigned_to_nat(1u);
x_1267 = lean_array_fget(x_1248, x_1266);
lean_dec(x_1248);
x_878 = x_1076;
x_879 = x_1265;
x_880 = x_1267;
x_881 = x_7;
goto block_932;
}
}
}
}
else
{
lean_object* x_1268; uint8_t x_1269; 
lean_dec(x_1250);
lean_dec(x_133);
x_1268 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
x_1269 = lean_string_dec_eq(x_1249, x_1268);
lean_dec(x_1249);
if (x_1269 == 0)
{
lean_object* x_1270; 
lean_dec(x_1248);
x_1270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1270, 0, x_1076);
lean_ctor_set(x_1270, 1, x_7);
return x_1270;
}
else
{
lean_object* x_1271; uint8_t x_1272; 
x_1271 = lean_array_get_size(x_1248);
x_1272 = lean_nat_dec_eq(x_1271, x_875);
lean_dec(x_1271);
if (x_1272 == 0)
{
lean_object* x_1273; 
lean_dec(x_1248);
x_1273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1273, 0, x_1076);
lean_ctor_set(x_1273, 1, x_7);
return x_1273;
}
else
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
x_1274 = lean_array_fget(x_1248, x_867);
x_1275 = lean_unsigned_to_nat(1u);
x_1276 = lean_array_fget(x_1248, x_1275);
lean_dec(x_1248);
x_933 = x_1076;
x_934 = x_1274;
x_935 = x_1276;
x_936 = x_7;
goto block_987;
}
}
}
}
else
{
lean_object* x_1277; uint8_t x_1278; 
lean_dec(x_1250);
lean_dec(x_133);
x_1277 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94;
x_1278 = lean_string_dec_eq(x_1249, x_1277);
lean_dec(x_1249);
if (x_1278 == 0)
{
lean_object* x_1279; 
lean_dec(x_1248);
x_1279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1279, 0, x_1076);
lean_ctor_set(x_1279, 1, x_7);
return x_1279;
}
else
{
lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; 
x_1280 = lean_array_get_size(x_1248);
x_1281 = lean_unsigned_to_nat(1u);
x_1282 = lean_nat_dec_eq(x_1280, x_1281);
lean_dec(x_1280);
if (x_1282 == 0)
{
lean_object* x_1283; 
lean_dec(x_1248);
x_1283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1283, 0, x_1076);
lean_ctor_set(x_1283, 1, x_7);
return x_1283;
}
else
{
lean_object* x_1284; 
x_1284 = lean_array_fget(x_1248, x_867);
lean_dec(x_1248);
x_1027 = x_1076;
x_1028 = x_1284;
x_1029 = x_7;
goto block_1075;
}
}
}
}
else
{
lean_object* x_1285; uint8_t x_1286; 
lean_dec(x_1250);
lean_dec(x_133);
x_1285 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_1286 = lean_string_dec_eq(x_1249, x_1285);
lean_dec(x_1249);
if (x_1286 == 0)
{
lean_object* x_1287; 
lean_dec(x_1248);
x_1287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1287, 0, x_1076);
lean_ctor_set(x_1287, 1, x_7);
return x_1287;
}
else
{
lean_object* x_1288; lean_object* x_1289; uint8_t x_1290; 
x_1288 = lean_array_get_size(x_1248);
x_1289 = lean_unsigned_to_nat(6u);
x_1290 = lean_nat_dec_eq(x_1288, x_1289);
lean_dec(x_1288);
if (x_1290 == 0)
{
lean_object* x_1291; 
lean_dec(x_1248);
x_1291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1291, 0, x_1076);
lean_ctor_set(x_1291, 1, x_7);
return x_1291;
}
else
{
lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; uint64_t x_1301; uint64_t x_1302; uint64_t x_1303; uint64_t x_1304; uint64_t x_1305; uint64_t x_1306; uint64_t x_1307; size_t x_1308; size_t x_1309; size_t x_1310; size_t x_1311; size_t x_1312; lean_object* x_1313; uint8_t x_1314; 
x_1292 = lean_ctor_get(x_1076, 0);
lean_inc(x_1292);
x_1293 = lean_ctor_get(x_1076, 1);
lean_inc(x_1293);
x_1294 = lean_array_fget(x_1248, x_877);
x_1295 = lean_unsigned_to_nat(5u);
x_1296 = lean_array_fget(x_1248, x_1295);
lean_dec(x_1248);
x_1297 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__96;
x_1298 = l_Lean_Expr_const___override(x_1297, x_871);
x_1299 = l_Lean_mkAppB(x_1298, x_1294, x_1296);
x_1300 = lean_array_get_size(x_1293);
x_1301 = l_Lean_Expr_hash(x_1299);
x_1302 = 32;
x_1303 = lean_uint64_shift_right(x_1301, x_1302);
x_1304 = lean_uint64_xor(x_1301, x_1303);
x_1305 = 16;
x_1306 = lean_uint64_shift_right(x_1304, x_1305);
x_1307 = lean_uint64_xor(x_1304, x_1306);
x_1308 = lean_uint64_to_usize(x_1307);
x_1309 = lean_usize_of_nat(x_1300);
lean_dec(x_1300);
x_1310 = 1;
x_1311 = lean_usize_sub(x_1309, x_1310);
x_1312 = lean_usize_land(x_1308, x_1311);
x_1313 = lean_array_uget(x_1293, x_1312);
x_1314 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1299, x_1313);
if (x_1314 == 0)
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; uint8_t x_1324; 
if (lean_is_exclusive(x_1076)) {
 lean_ctor_release(x_1076, 0);
 lean_ctor_release(x_1076, 1);
 x_1315 = x_1076;
} else {
 lean_dec_ref(x_1076);
 x_1315 = lean_box(0);
}
x_1316 = lean_box(0);
x_1317 = lean_unsigned_to_nat(1u);
x_1318 = lean_nat_add(x_1292, x_1317);
lean_dec(x_1292);
x_1319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1319, 0, x_1299);
lean_ctor_set(x_1319, 1, x_1316);
lean_ctor_set(x_1319, 2, x_1313);
x_1320 = lean_array_uset(x_1293, x_1312, x_1319);
x_1321 = lean_nat_mul(x_1318, x_877);
x_1322 = lean_nat_div(x_1321, x_865);
lean_dec(x_1321);
x_1323 = lean_array_get_size(x_1320);
x_1324 = lean_nat_dec_le(x_1322, x_1323);
lean_dec(x_1323);
lean_dec(x_1322);
if (x_1324 == 0)
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; 
x_1325 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_1320);
if (lean_is_scalar(x_1315)) {
 x_1326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1326 = x_1315;
}
lean_ctor_set(x_1326, 0, x_1318);
lean_ctor_set(x_1326, 1, x_1325);
x_1327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1327, 0, x_1326);
lean_ctor_set(x_1327, 1, x_7);
return x_1327;
}
else
{
lean_object* x_1328; lean_object* x_1329; 
if (lean_is_scalar(x_1315)) {
 x_1328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1328 = x_1315;
}
lean_ctor_set(x_1328, 0, x_1318);
lean_ctor_set(x_1328, 1, x_1320);
x_1329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1329, 0, x_1328);
lean_ctor_set(x_1329, 1, x_7);
return x_1329;
}
}
else
{
lean_object* x_1330; 
lean_dec(x_1313);
lean_dec(x_1299);
lean_dec(x_1293);
lean_dec(x_1292);
x_1330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1330, 0, x_1076);
lean_ctor_set(x_1330, 1, x_7);
return x_1330;
}
}
}
}
}
}
else
{
uint8_t x_1331; 
lean_dec(x_1162);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_133);
x_1331 = !lean_is_exclusive(x_1159);
if (x_1331 == 0)
{
lean_object* x_1332; lean_object* x_1333; 
x_1332 = lean_ctor_get(x_1159, 1);
lean_dec(x_1332);
x_1333 = lean_ctor_get(x_1159, 0);
lean_dec(x_1333);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1334; 
lean_dec(x_1159);
x_1334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1334, 0, x_1076);
lean_ctor_set(x_1334, 1, x_7);
return x_1334;
}
}
}
else
{
uint8_t x_1335; 
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_133);
x_1335 = !lean_is_exclusive(x_1159);
if (x_1335 == 0)
{
lean_object* x_1336; lean_object* x_1337; 
x_1336 = lean_ctor_get(x_1159, 1);
lean_dec(x_1336);
x_1337 = lean_ctor_get(x_1159, 0);
lean_dec(x_1337);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1338; 
lean_dec(x_1159);
x_1338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1338, 0, x_1076);
lean_ctor_set(x_1338, 1, x_7);
return x_1338;
}
}
}
else
{
uint8_t x_1339; 
lean_dec(x_1160);
lean_dec(x_133);
x_1339 = !lean_is_exclusive(x_1159);
if (x_1339 == 0)
{
lean_object* x_1340; lean_object* x_1341; 
x_1340 = lean_ctor_get(x_1159, 1);
lean_dec(x_1340);
x_1341 = lean_ctor_get(x_1159, 0);
lean_dec(x_1341);
lean_ctor_set(x_1159, 1, x_7);
lean_ctor_set(x_1159, 0, x_1076);
return x_1159;
}
else
{
lean_object* x_1342; 
lean_dec(x_1159);
x_1342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1342, 0, x_1076);
lean_ctor_set(x_1342, 1, x_7);
return x_1342;
}
}
}
}
}
else
{
lean_dec(x_871);
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
}
}
else
{
lean_dec(x_870);
lean_dec(x_869);
lean_dec(x_868);
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
}
else
{
lean_dec(x_869);
lean_dec(x_868);
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
}
else
{
lean_dec(x_868);
lean_dec(x_133);
lean_dec(x_132);
x_12 = x_7;
goto block_15;
}
}
}
}
}
else
{
lean_dec(x_131);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = x_7;
goto block_15;
}
}
default: 
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = x_7;
goto block_15;
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = x_7;
goto block_15;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_analyzeAtom(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_1, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_infer_type(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = lean_infer_type(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static double _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
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
lean_object* x_21; double x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0;
x_23 = lean_box(0);
x_24 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_26);
x_27 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2;
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_28);
lean_ctor_set(x_12, 0, x_8);
x_29 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_29);
x_30 = lean_st_ref_set(x_6, x_13, x_16);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint64_t x_37; lean_object* x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
lean_dec(x_14);
x_39 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0;
x_40 = lean_box(0);
x_41 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1;
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_39);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_39);
x_43 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_43);
x_44 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2;
x_45 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_45);
lean_ctor_set(x_12, 0, x_8);
x_46 = l_Lean_PersistentArray_push___redArg(x_38, x_12);
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_37);
lean_ctor_set(x_13, 4, x_47);
x_48 = lean_st_ref_set(x_6, x_13, x_16);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; double x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
x_55 = lean_ctor_get(x_13, 2);
x_56 = lean_ctor_get(x_13, 3);
x_57 = lean_ctor_get(x_13, 5);
x_58 = lean_ctor_get(x_13, 6);
x_59 = lean_ctor_get(x_13, 7);
x_60 = lean_ctor_get(x_13, 8);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_61 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_62 = lean_ctor_get(x_14, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_63 = x_14;
} else {
 lean_dec_ref(x_14);
 x_63 = lean_box(0);
}
x_64 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0;
x_65 = lean_box(0);
x_66 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1;
x_67 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_float(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_float(x_67, sizeof(void*)*2 + 8, x_64);
x_68 = lean_unbox(x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 16, x_68);
x_69 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2;
x_70 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_10);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_70);
lean_ctor_set(x_12, 0, x_8);
x_71 = l_Lean_PersistentArray_push___redArg(x_62, x_12);
if (lean_is_scalar(x_63)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_63;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_61);
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_54);
lean_ctor_set(x_73, 2, x_55);
lean_ctor_set(x_73, 3, x_56);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_57);
lean_ctor_set(x_73, 6, x_58);
lean_ctor_set(x_73, 7, x_59);
lean_ctor_set(x_73, 8, x_60);
x_74 = lean_st_ref_set(x_6, x_73, x_16);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; double x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_dec(x_12);
x_80 = lean_ctor_get(x_13, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_13, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_13, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_13, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_13, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_13, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_13, 7);
lean_inc(x_86);
x_87 = lean_ctor_get(x_13, 8);
lean_inc(x_87);
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
 x_88 = x_13;
} else {
 lean_dec_ref(x_13);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_90 = lean_ctor_get(x_14, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_91 = x_14;
} else {
 lean_dec_ref(x_14);
 x_91 = lean_box(0);
}
x_92 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0;
x_93 = lean_box(0);
x_94 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1;
x_95 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_float(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_float(x_95, sizeof(void*)*2 + 8, x_92);
x_96 = lean_unbox(x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 16, x_96);
x_97 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2;
x_98 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_10);
lean_ctor_set(x_98, 2, x_97);
lean_inc(x_8);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_8);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_PersistentArray_push___redArg(x_90, x_99);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 1, 8);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_uint64(x_101, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_88)) {
 x_102 = lean_alloc_ctor(0, 9, 0);
} else {
 x_102 = x_88;
}
lean_ctor_set(x_102, 0, x_80);
lean_ctor_set(x_102, 1, x_81);
lean_ctor_set(x_102, 2, x_82);
lean_ctor_set(x_102, 3, x_83);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set(x_102, 5, x_84);
lean_ctor_set(x_102, 6, x_85);
lean_ctor_set(x_102, 7, x_86);
lean_ctor_set(x_102, 8, x_87);
x_103 = lean_st_ref_set(x_6, x_102, x_79);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
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
x_1 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_st_ref_get(x_3, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Meta_Canonicalizer_canon(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_36 = x_28;
} else {
 lean_dec_ref(x_28);
 x_36 = lean_box(0);
}
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
lean_dec(x_35);
x_108 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_33, x_107);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_free_object(x_31);
x_109 = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
x_178 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_109, x_9, x_34);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_unbox(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_140 = x_2;
x_141 = x_3;
x_142 = x_4;
x_143 = x_5;
x_144 = x_6;
x_145 = x_7;
x_146 = x_8;
x_147 = x_9;
x_148 = x_10;
x_149 = x_181;
goto block_177;
}
else
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_178);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_ctor_get(x_178, 1);
x_184 = lean_ctor_get(x_178, 0);
lean_dec(x_184);
x_185 = l_Lean_Elab_Tactic_Omega_lookup___closed__6;
lean_inc(x_33);
x_186 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_178, 7);
lean_ctor_set(x_178, 1, x_186);
lean_ctor_set(x_178, 0, x_185);
x_187 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_178);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_109, x_188, x_7, x_8, x_9, x_10, x_183);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_140 = x_2;
x_141 = x_3;
x_142 = x_4;
x_143 = x_5;
x_144 = x_6;
x_145 = x_7;
x_146 = x_8;
x_147 = x_9;
x_148 = x_10;
x_149 = x_190;
goto block_177;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_191 = lean_ctor_get(x_178, 1);
lean_inc(x_191);
lean_dec(x_178);
x_192 = l_Lean_Elab_Tactic_Omega_lookup___closed__6;
lean_inc(x_33);
x_193 = l_Lean_MessageData_ofExpr(x_33);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_109, x_196, x_7, x_8, x_9, x_10, x_191);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_140 = x_2;
x_141 = x_3;
x_142 = x_4;
x_143 = x_5;
x_144 = x_6;
x_145 = x_7;
x_146 = x_8;
x_147 = x_9;
x_148 = x_10;
x_149 = x_198;
goto block_177;
}
}
block_139:
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_box(0);
lean_inc(x_114);
lean_inc(x_115);
lean_inc(x_120);
lean_inc(x_118);
x_123 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_121, x_122, x_118, x_120, x_115, x_114, x_117);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_127 = lean_box(0);
x_128 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_124, x_127);
x_129 = l_Lean_MessageData_ofList(x_128);
if (lean_is_scalar(x_36)) {
 x_130 = lean_alloc_ctor(7, 2, 0);
} else {
 x_130 = x_36;
 lean_ctor_set_tag(x_130, 7);
}
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_30)) {
 x_132 = lean_alloc_ctor(7, 2, 0);
} else {
 x_132 = x_30;
 lean_ctor_set_tag(x_132, 7);
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_109, x_132, x_118, x_120, x_115, x_114, x_125);
lean_dec(x_114);
lean_dec(x_115);
lean_dec(x_120);
lean_dec(x_118);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_48 = x_119;
x_49 = x_113;
x_50 = x_134;
goto block_104;
}
else
{
uint8_t x_135; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_123);
if (x_135 == 0)
{
return x_123;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_123, 0);
x_137 = lean_ctor_get(x_123, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_123);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
block_177:
{
lean_object* x_150; 
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_33);
x_150 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_33, x_142, x_145, x_146, x_147, x_148, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_109, x_147, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_36);
lean_dec(x_30);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_48 = x_151;
x_49 = x_141;
x_50 = x_156;
goto block_104;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
x_158 = lean_ctor_get(x_151, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_151, 1);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_nat_dec_eq(x_158, x_160);
lean_dec(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_109, x_147, x_157);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_159);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_36);
lean_dec(x_30);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_48 = x_151;
x_49 = x_141;
x_50 = x_165;
goto block_104;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_box(0);
x_168 = lean_array_get_size(x_159);
x_169 = lean_nat_dec_lt(x_160, x_168);
if (x_169 == 0)
{
lean_dec(x_168);
lean_dec(x_159);
x_110 = x_144;
x_111 = x_143;
x_112 = x_140;
x_113 = x_141;
x_114 = x_148;
x_115 = x_147;
x_116 = x_142;
x_117 = x_166;
x_118 = x_145;
x_119 = x_151;
x_120 = x_146;
x_121 = x_167;
goto block_139;
}
else
{
size_t x_170; size_t x_171; lean_object* x_172; 
x_170 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_171 = 0;
x_172 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(x_159, x_170, x_171, x_167);
lean_dec(x_159);
x_110 = x_144;
x_111 = x_143;
x_112 = x_140;
x_113 = x_141;
x_114 = x_148;
x_115 = x_147;
x_116 = x_142;
x_117 = x_166;
x_118 = x_145;
x_119 = x_151;
x_120 = x_146;
x_121 = x_172;
goto block_139;
}
}
}
else
{
lean_dec(x_159);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_36);
lean_dec(x_30);
x_48 = x_151;
x_49 = x_141;
x_50 = x_157;
goto block_104;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_30);
x_173 = !lean_is_exclusive(x_150);
if (x_173 == 0)
{
return x_150;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_150, 0);
x_175 = lean_ctor_get(x_150, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_150);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_199 = lean_ctor_get(x_108, 0);
lean_inc(x_199);
lean_dec(x_108);
x_200 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_36;
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_31, 0, x_201);
return x_31;
}
block_104:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_take(x_49, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
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
x_62 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_33, x_61);
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
x_73 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_66);
lean_ctor_set(x_52, 1, x_73);
lean_ctor_set(x_52, 0, x_64);
x_12 = x_55;
x_13 = x_53;
x_14 = x_48;
x_15 = x_49;
x_16 = x_52;
goto block_26;
}
else
{
lean_ctor_set(x_52, 1, x_66);
lean_ctor_set(x_52, 0, x_64);
x_12 = x_55;
x_13 = x_53;
x_14 = x_48;
x_15 = x_49;
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
x_76 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_33, x_55, x_61);
x_77 = lean_array_uset(x_75, x_60, x_76);
lean_inc(x_55);
lean_ctor_set(x_52, 1, x_77);
x_12 = x_55;
x_13 = x_53;
x_14 = x_48;
x_15 = x_49;
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
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_33, x_84);
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
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_12 = x_78;
x_13 = x_53;
x_14 = x_48;
x_15 = x_49;
x_16 = x_97;
goto block_26;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
x_12 = x_78;
x_13 = x_53;
x_14 = x_48;
x_15 = x_49;
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
x_101 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_33, x_78, x_84);
x_102 = lean_array_uset(x_100, x_83, x_101);
lean_inc(x_78);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_78);
lean_ctor_set(x_103, 1, x_102);
x_12 = x_78;
x_13 = x_53;
x_14 = x_48;
x_15 = x_49;
x_16 = x_103;
goto block_26;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; size_t x_214; size_t x_215; size_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; size_t x_251; size_t x_252; lean_object* x_253; lean_object* x_254; 
x_202 = lean_ctor_get(x_31, 0);
x_203 = lean_ctor_get(x_31, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_31);
x_204 = lean_ctor_get(x_28, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_205 = x_28;
} else {
 lean_dec_ref(x_28);
 x_205 = lean_box(0);
}
x_206 = lean_array_get_size(x_204);
x_207 = l_Lean_Expr_hash(x_202);
x_208 = 32;
x_209 = lean_uint64_shift_right(x_207, x_208);
x_210 = lean_uint64_xor(x_207, x_209);
x_211 = 16;
x_212 = lean_uint64_shift_right(x_210, x_211);
x_213 = lean_uint64_xor(x_210, x_212);
x_214 = lean_uint64_to_usize(x_213);
x_215 = lean_usize_of_nat(x_206);
lean_dec(x_206);
x_216 = 1;
x_251 = lean_usize_sub(x_215, x_216);
x_252 = lean_usize_land(x_214, x_251);
x_253 = lean_array_uget(x_204, x_252);
lean_dec(x_204);
x_254 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_202, x_253);
lean_dec(x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_255 = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
x_324 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_255, x_9, x_203);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_unbox(x_325);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_dec(x_324);
x_286 = x_2;
x_287 = x_3;
x_288 = x_4;
x_289 = x_5;
x_290 = x_6;
x_291 = x_7;
x_292 = x_8;
x_293 = x_9;
x_294 = x_10;
x_295 = x_327;
goto block_323;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_329 = x_324;
} else {
 lean_dec_ref(x_324);
 x_329 = lean_box(0);
}
x_330 = l_Lean_Elab_Tactic_Omega_lookup___closed__6;
lean_inc(x_202);
x_331 = l_Lean_MessageData_ofExpr(x_202);
if (lean_is_scalar(x_329)) {
 x_332 = lean_alloc_ctor(7, 2, 0);
} else {
 x_332 = x_329;
 lean_ctor_set_tag(x_332, 7);
}
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_334 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_255, x_334, x_7, x_8, x_9, x_10, x_328);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
lean_dec(x_335);
x_286 = x_2;
x_287 = x_3;
x_288 = x_4;
x_289 = x_5;
x_290 = x_6;
x_291 = x_7;
x_292 = x_8;
x_293 = x_9;
x_294 = x_10;
x_295 = x_336;
goto block_323;
}
block_285:
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_box(0);
lean_inc(x_260);
lean_inc(x_261);
lean_inc(x_266);
lean_inc(x_264);
x_269 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(x_267, x_268, x_264, x_266, x_261, x_260, x_263);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_273 = lean_box(0);
x_274 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_270, x_273);
x_275 = l_Lean_MessageData_ofList(x_274);
if (lean_is_scalar(x_205)) {
 x_276 = lean_alloc_ctor(7, 2, 0);
} else {
 x_276 = x_205;
 lean_ctor_set_tag(x_276, 7);
}
lean_ctor_set(x_276, 0, x_272);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_30)) {
 x_278 = lean_alloc_ctor(7, 2, 0);
} else {
 x_278 = x_30;
 lean_ctor_set_tag(x_278, 7);
}
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_255, x_278, x_264, x_266, x_261, x_260, x_271);
lean_dec(x_260);
lean_dec(x_261);
lean_dec(x_266);
lean_dec(x_264);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_217 = x_265;
x_218 = x_259;
x_219 = x_280;
goto block_250;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_205);
lean_dec(x_202);
lean_dec(x_30);
x_281 = lean_ctor_get(x_269, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_269, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_283 = x_269;
} else {
 lean_dec_ref(x_269);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
block_323:
{
lean_object* x_296; 
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_202);
x_296 = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(x_202, x_288, x_291, x_292, x_293, x_294, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_255, x_293, x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_unbox(x_300);
lean_dec(x_300);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_205);
lean_dec(x_30);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_217 = x_297;
x_218 = x_287;
x_219 = x_302;
goto block_250;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_303 = lean_ctor_get(x_299, 1);
lean_inc(x_303);
lean_dec(x_299);
x_304 = lean_ctor_get(x_297, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_297, 1);
lean_inc(x_305);
x_306 = lean_unsigned_to_nat(0u);
x_307 = lean_nat_dec_eq(x_304, x_306);
lean_dec(x_304);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_308 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_255, x_293, x_303);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_unbox(x_309);
lean_dec(x_309);
if (x_310 == 0)
{
lean_object* x_311; 
lean_dec(x_305);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_205);
lean_dec(x_30);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
x_217 = x_297;
x_218 = x_287;
x_219 = x_311;
goto block_250;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_312 = lean_ctor_get(x_308, 1);
lean_inc(x_312);
lean_dec(x_308);
x_313 = lean_box(0);
x_314 = lean_array_get_size(x_305);
x_315 = lean_nat_dec_lt(x_306, x_314);
if (x_315 == 0)
{
lean_dec(x_314);
lean_dec(x_305);
x_256 = x_290;
x_257 = x_289;
x_258 = x_286;
x_259 = x_287;
x_260 = x_294;
x_261 = x_293;
x_262 = x_288;
x_263 = x_312;
x_264 = x_291;
x_265 = x_297;
x_266 = x_292;
x_267 = x_313;
goto block_285;
}
else
{
size_t x_316; size_t x_317; lean_object* x_318; 
x_316 = lean_usize_of_nat(x_314);
lean_dec(x_314);
x_317 = 0;
x_318 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(x_305, x_316, x_317, x_313);
lean_dec(x_305);
x_256 = x_290;
x_257 = x_289;
x_258 = x_286;
x_259 = x_287;
x_260 = x_294;
x_261 = x_293;
x_262 = x_288;
x_263 = x_312;
x_264 = x_291;
x_265 = x_297;
x_266 = x_292;
x_267 = x_318;
goto block_285;
}
}
}
else
{
lean_dec(x_305);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_205);
lean_dec(x_30);
x_217 = x_297;
x_218 = x_287;
x_219 = x_303;
goto block_250;
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_205);
lean_dec(x_202);
lean_dec(x_30);
x_319 = lean_ctor_get(x_296, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_296, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_321 = x_296;
} else {
 lean_dec_ref(x_296);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_202);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_337 = lean_ctor_get(x_254, 0);
lean_inc(x_337);
lean_dec(x_254);
x_338 = lean_box(0);
if (lean_is_scalar(x_205)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_205;
}
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_203);
return x_340;
}
block_250:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; size_t x_227; size_t x_228; size_t x_229; lean_object* x_230; uint8_t x_231; 
x_220 = lean_st_ref_take(x_218, x_219);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
x_226 = lean_array_get_size(x_224);
x_227 = lean_usize_of_nat(x_226);
lean_dec(x_226);
x_228 = lean_usize_sub(x_227, x_216);
x_229 = lean_usize_land(x_214, x_228);
x_230 = lean_array_uget(x_224, x_229);
x_231 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_202, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_add(x_223, x_232);
lean_inc(x_223);
x_234 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_234, 0, x_202);
lean_ctor_set(x_234, 1, x_223);
lean_ctor_set(x_234, 2, x_230);
x_235 = lean_array_uset(x_224, x_229, x_234);
x_236 = lean_unsigned_to_nat(4u);
x_237 = lean_nat_mul(x_233, x_236);
x_238 = lean_unsigned_to_nat(3u);
x_239 = lean_nat_div(x_237, x_238);
lean_dec(x_237);
x_240 = lean_array_get_size(x_235);
x_241 = lean_nat_dec_le(x_239, x_240);
lean_dec(x_240);
lean_dec(x_239);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_235);
if (lean_is_scalar(x_225)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_225;
}
lean_ctor_set(x_243, 0, x_233);
lean_ctor_set(x_243, 1, x_242);
x_12 = x_223;
x_13 = x_222;
x_14 = x_217;
x_15 = x_218;
x_16 = x_243;
goto block_26;
}
else
{
lean_object* x_244; 
if (lean_is_scalar(x_225)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_225;
}
lean_ctor_set(x_244, 0, x_233);
lean_ctor_set(x_244, 1, x_235);
x_12 = x_223;
x_13 = x_222;
x_14 = x_217;
x_15 = x_218;
x_16 = x_244;
goto block_26;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_box(0);
x_246 = lean_array_uset(x_224, x_229, x_245);
lean_inc(x_223);
x_247 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_202, x_223, x_230);
x_248 = lean_array_uset(x_246, x_229, x_247);
lean_inc(x_223);
if (lean_is_scalar(x_225)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_225;
}
lean_ctor_set(x_249, 0, x_223);
lean_ctor_set(x_249, 1, x_248);
x_12 = x_223;
x_13 = x_222;
x_14 = x_217;
x_15 = x_218;
x_16 = x_249;
goto block_26;
}
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_341 = !lean_is_exclusive(x_31);
if (x_341 == 0)
{
return x_31;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_31, 0);
x_343 = lean_ctor_get(x_31, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_31);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
block_26:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_set(x_15, x_16, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
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
lean_ctor_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_Omega_lookup_spec__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_List_mapM_loop___at___Lean_Elab_Tactic_Omega_lookup_spec__1(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_Omega_lookup_spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Omega_lookup_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_lookup(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
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
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__6 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__6);
l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__7 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__7);
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
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8();
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
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49();
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
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__95 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__95();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__95);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__96 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__96();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__96);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__97 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__97();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__97);
l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__98 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__98();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__98);
l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__0();
l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__1);
l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___closed__2);
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

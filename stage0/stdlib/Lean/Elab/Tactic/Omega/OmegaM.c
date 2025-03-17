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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83;
static double l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__114;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3;
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__3;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87;
static lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__4;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76;
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__4;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14;
static uint8_t l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80;
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__113;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_Lean_Elab_Tactic_Omega_lookup___spec__8___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84;
static lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__4(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1;
static lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___closed__1;
lean_object* l_Int_pow(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25;
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
static lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21;
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Elab_Tactic_Omega_lookup___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47;
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
lean_object* l___private_Init_Data_Array_QSort_0__Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object*);
lean_object* l_Lean_Expr_int_x3f(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(lean_object*, lean_object*);
static size_t l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___lambda__1___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16;
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43;
lean_object* l_Nat_pow___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_apply_7(x_1, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(x_3);
x_15 = lean_apply_8(x_2, x_12, x_14, x_4, x_5, x_6, x_7, x_8, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg___boxed), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_mk_ref(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_st_mk_ref(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_16 = lean_apply_10(x_2, x_13, x_4, x_3, x_15, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_13, x_18);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_st_ref_get(x_4, x_21);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_st_ref_get(x_4, x_29);
lean_dec(x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2___boxed), 11, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg___boxed), 9, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__4;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg___boxed), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = 3;
x_15 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__5;
x_16 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg(x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_cfg___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Elab_Tactic_Omega_cfg___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Omega_cfg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___closed__1;
lean_inc(x_3);
x_9 = l___private_Init_Data_Array_QSort_0__Array_qpartition___rarg(x_1, x_2, x_8, x_3, x_4, lean_box(0), lean_box(0));
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_le(x_4, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2(x_1, x_11, x_3, x_10, lean_box(0), lean_box(0));
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_10, x_14);
lean_dec(x_10);
x_2 = x_13;
x_3 = x_15;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__1(x_4, x_6);
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
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
x_18 = 0;
if (x_17 == 0)
{
lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_14);
x_37 = l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
x_19 = x_37;
goto block_36;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_15, x_15);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_15);
lean_dec(x_14);
x_39 = l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
x_19 = x_39;
goto block_36;
}
else
{
size_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_41 = l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
x_42 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__4(x_14, x_18, x_40, x_41);
lean_dec(x_14);
x_19 = x_42;
goto block_36;
}
}
block_36:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
x_23 = lean_nat_dec_eq(x_20, x_16);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_16, x_22);
if (x_24 == 0)
{
lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_22);
x_25 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2(x_20, x_19, x_22, x_22, lean_box(0), lean_box(0));
lean_dec(x_22);
lean_dec(x_20);
x_26 = lean_array_size(x_25);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3(x_26, x_18, x_25);
if (lean_is_scalar(x_13)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_13;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
else
{
lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2(x_20, x_19, x_16, x_22, lean_box(0), lean_box(0));
lean_dec(x_22);
lean_dec(x_20);
x_30 = lean_array_size(x_29);
x_31 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3(x_30, x_18, x_29);
if (lean_is_scalar(x_13)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_13;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_12);
return x_32;
}
}
else
{
size_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_22);
lean_dec(x_20);
x_33 = lean_array_size(x_19);
x_34 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3(x_33, x_18, x_19);
if (lean_is_scalar(x_13)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_13;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_12);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_atoms___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Elab_Tactic_Omega_atoms___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Omega_atoms(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Elab_Tactic_Omega_atoms___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_to_list(x_11);
x_14 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3;
x_15 = l_Lean_Meta_mkListLit(x_14, x_13, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_atomsList___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Elab_Tactic_Omega_atomsList___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Omega_atomsList(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Omega", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Coeffs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofList", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__3;
x_4 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Omega_atomsList___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6;
x_14 = l_Lean_Expr_app___override(x_13, x_12);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6;
x_18 = l_Lean_Expr_app___override(x_17, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_commitWhen___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Elab_Tactic_Omega_commitWhen___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_commitWhen___rarg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_apply_10(x_1, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(x_6);
x_18 = lean_apply_11(x_2, x_15, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg___boxed), 12, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1___boxed), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg___boxed), 12, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_Omega_commitWhen___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2() {
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
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
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
x_12 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
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
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
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
x_12 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
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
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_2(x_1, x_6, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_2(x_1, x_6, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_add___boxed), 2, 0);
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
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_14 = lean_string_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_16 = lean_string_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_18 = lean_string_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
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
x_22 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
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
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_array_fget(x_6, x_29);
x_31 = lean_unsigned_to_nat(5u);
x_32 = lean_array_fget(x_6, x_31);
lean_dec(x_6);
x_33 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
x_34 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_33, x_30, x_32);
return x_34;
}
}
}
}
else
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_8);
x_35 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
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
x_42 = lean_unsigned_to_nat(4u);
x_43 = lean_array_fget(x_6, x_42);
x_44 = lean_unsigned_to_nat(5u);
x_45 = lean_array_fget(x_6, x_44);
lean_dec(x_6);
x_46 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
x_47 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_46, x_43, x_45);
return x_47;
}
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_8);
x_48 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
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
x_55 = lean_unsigned_to_nat(4u);
x_56 = lean_array_fget(x_6, x_55);
x_57 = lean_unsigned_to_nat(5u);
x_58 = lean_array_fget(x_6, x_57);
lean_dec(x_6);
x_59 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
x_60 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_59, x_56, x_58);
return x_60;
}
}
}
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_8);
x_61 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12;
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
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_array_fget(x_6, x_68);
x_70 = lean_unsigned_to_nat(5u);
x_71 = lean_array_fget(x_6, x_70);
lean_dec(x_6);
x_72 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
x_73 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_72, x_69, x_71);
return x_73;
}
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_8);
x_74 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14;
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
x_81 = lean_unsigned_to_nat(4u);
x_82 = lean_array_fget(x_6, x_81);
x_83 = lean_unsigned_to_nat(5u);
x_84 = lean_array_fget(x_6, x_83);
lean_dec(x_6);
x_85 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15;
x_86 = l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(x_85, x_82, x_84);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_8);
x_87 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_2(x_1, x_6, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_2(x_1, x_6, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_ediv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
return x_1;
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
x_9 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
x_14 = lean_string_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_16 = lean_string_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_18 = lean_string_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
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
x_22 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_array_fget(x_6, x_29);
x_31 = lean_unsigned_to_nat(5u);
x_32 = lean_array_fget(x_6, x_31);
lean_dec(x_6);
x_33 = l_Lean_Elab_Tactic_Omega_groundInt_x3f(x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_32);
x_34 = lean_box(0);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_35);
x_37 = lean_box(0);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = l_Int_pow(x_35, x_39);
lean_dec(x_39);
lean_dec(x_35);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = l_Int_pow(x_35, x_41);
lean_dec(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
}
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_8);
x_44 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_45 = lean_string_dec_eq(x_7, x_44);
lean_dec(x_7);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_6);
x_46 = l_Lean_Expr_int_x3f(x_1);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_array_get_size(x_6);
x_48 = lean_unsigned_to_nat(6u);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_6);
x_50 = l_Lean_Expr_int_x3f(x_1);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_array_fget(x_6, x_51);
x_53 = lean_unsigned_to_nat(5u);
x_54 = lean_array_fget(x_6, x_53);
lean_dec(x_6);
x_55 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1;
x_56 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_55, x_52, x_54);
return x_56;
}
}
}
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_8);
x_57 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
x_58 = lean_string_dec_eq(x_7, x_57);
lean_dec(x_7);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_6);
x_59 = l_Lean_Expr_int_x3f(x_1);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_array_get_size(x_6);
x_61 = lean_unsigned_to_nat(6u);
x_62 = lean_nat_dec_eq(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_6);
x_63 = l_Lean_Expr_int_x3f(x_1);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_array_fget(x_6, x_64);
x_66 = lean_unsigned_to_nat(5u);
x_67 = lean_array_fget(x_6, x_66);
lean_dec(x_6);
x_68 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2;
x_69 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_68, x_65, x_67);
return x_69;
}
}
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_8);
x_70 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12;
x_71 = lean_string_dec_eq(x_7, x_70);
lean_dec(x_7);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_6);
x_72 = l_Lean_Expr_int_x3f(x_1);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_array_get_size(x_6);
x_74 = lean_unsigned_to_nat(6u);
x_75 = lean_nat_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_6);
x_76 = l_Lean_Expr_int_x3f(x_1);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_1);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_array_fget(x_6, x_77);
x_79 = lean_unsigned_to_nat(5u);
x_80 = lean_array_fget(x_6, x_79);
lean_dec(x_6);
x_81 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3;
x_82 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_81, x_78, x_80);
return x_82;
}
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_8);
x_83 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14;
x_84 = lean_string_dec_eq(x_7, x_83);
lean_dec(x_7);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_6);
x_85 = l_Lean_Expr_int_x3f(x_1);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_array_get_size(x_6);
x_87 = lean_unsigned_to_nat(6u);
x_88 = lean_nat_dec_eq(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_6);
x_89 = l_Lean_Expr_int_x3f(x_1);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_90 = lean_unsigned_to_nat(4u);
x_91 = lean_array_fget(x_6, x_90);
x_92 = lean_unsigned_to_nat(5u);
x_93 = lean_array_fget(x_6, x_92);
lean_dec(x_6);
x_94 = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__4;
x_95 = l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(x_94, x_91, x_93);
return x_95;
}
}
}
}
else
{
lean_object* x_96; uint8_t x_97; 
lean_dec(x_8);
x_96 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_97 = lean_string_dec_eq(x_7, x_96);
lean_dec(x_7);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_6);
x_98 = l_Lean_Expr_int_x3f(x_1);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_array_get_size(x_6);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_dec_eq(x_99, x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_6);
x_102 = l_Lean_Expr_int_x3f(x_1);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_1);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_array_fget(x_6, x_103);
lean_dec(x_6);
x_105 = l_Lean_Elab_Tactic_Omega_groundNat_x3f(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_box(0);
return x_106;
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_nat_to_int(x_108);
lean_ctor_set(x_105, 0, x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_nat_to_int(x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_5);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = l_Lean_Expr_int_x3f(x_1);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_dec(x_3);
lean_dec(x_2);
x_115 = l_Lean_Expr_int_x3f(x_1);
return x_115;
}
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_mkEq(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkExpectedTypeHint(x_9, x_12, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_disjunction", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_right", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_right", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_ofNat_nonneg", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTNat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_pos_of_pos", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54;
x_2 = lean_int_dec_le(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTInt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul_ediv_self_le", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_mul_ediv_self_add", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_nonneg", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isLt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("val", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natAbs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_natAbs", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg_le_natAbs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_sub_dichotomy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__113() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__114() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_getAppFnArgs(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_array_get_size(x_16);
x_23 = lean_unsigned_to_nat(5u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
x_25 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_fget(x_16, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_array_fget(x_16, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_array_fget(x_16, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_array_fget(x_16, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_array_fget(x_16, x_34);
lean_dec(x_16);
x_36 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3;
x_37 = lean_expr_eqv(x_27, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_38 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_39 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
x_40 = l_Lean_mkApp5(x_39, x_27, x_29, x_31, x_33, x_35);
x_41 = l_Lean_Expr_hash(x_40);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_50 = lean_usize_land(x_48, x_49);
x_51 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_52 = lean_array_uget(x_51, x_50);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_40, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_52);
x_56 = lean_array_uset(x_51, x_50, x_55);
x_57 = lean_array_get_size(x_56);
x_58 = lean_nat_dec_le(x_28, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_56);
lean_ctor_set(x_12, 1, x_59);
lean_ctor_set(x_12, 0, x_28);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_12);
lean_ctor_set(x_60, 1, x_11);
return x_60;
}
else
{
lean_object* x_61; 
lean_ctor_set(x_12, 1, x_56);
lean_ctor_set(x_12, 0, x_28);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_12);
lean_ctor_set(x_61, 1, x_11);
return x_61;
}
}
else
{
lean_object* x_62; 
lean_dec(x_52);
lean_dec(x_40);
x_62 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_62);
return x_12;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_dec(x_12);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_dec(x_13);
x_65 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_66 = lean_string_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_67 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_11);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_array_get_size(x_63);
x_70 = lean_unsigned_to_nat(5u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
x_72 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_11);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_fget(x_63, x_74);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_array_fget(x_63, x_76);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_array_fget(x_63, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_array_fget(x_63, x_80);
x_82 = lean_unsigned_to_nat(4u);
x_83 = lean_array_fget(x_63, x_82);
lean_dec(x_63);
x_84 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3;
x_85 = lean_expr_eqv(x_75, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_75);
x_86 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_11);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_88 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
x_89 = l_Lean_mkApp5(x_88, x_75, x_77, x_79, x_81, x_83);
x_90 = l_Lean_Expr_hash(x_89);
x_91 = 32;
x_92 = lean_uint64_shift_right(x_90, x_91);
x_93 = lean_uint64_xor(x_90, x_92);
x_94 = 16;
x_95 = lean_uint64_shift_right(x_93, x_94);
x_96 = lean_uint64_xor(x_93, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_99 = lean_usize_land(x_97, x_98);
x_100 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_101 = lean_array_uget(x_100, x_99);
x_102 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_89, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_101);
x_105 = lean_array_uset(x_100, x_99, x_104);
x_106 = lean_array_get_size(x_105);
x_107 = lean_nat_dec_le(x_76, x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_105);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_76);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_11);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_76);
lean_ctor_set(x_111, 1, x_105);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_11);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_101);
lean_dec(x_89);
x_113 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_11);
return x_114;
}
}
}
}
}
}
case 1:
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_14, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_ctor_get(x_12, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_117 = x_12;
} else {
 lean_dec_ref(x_12);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_13, 1);
lean_inc(x_118);
lean_dec(x_13);
x_119 = lean_ctor_get(x_14, 1);
lean_inc(x_119);
lean_dec(x_14);
x_120 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_121 = lean_string_dec_eq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_123 = lean_string_dec_eq(x_119, x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10;
x_125 = lean_string_dec_eq(x_119, x_124);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_126 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11;
x_127 = lean_string_dec_eq(x_119, x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12;
x_129 = lean_string_dec_eq(x_119, x_128);
lean_dec(x_119);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_118);
lean_dec(x_116);
x_130 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_117;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_11);
return x_131;
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13;
x_133 = lean_string_dec_eq(x_118, x_132);
lean_dec(x_118);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_116);
x_134 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_117;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_11);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_array_get_size(x_116);
x_137 = lean_unsigned_to_nat(4u);
x_138 = lean_nat_dec_eq(x_136, x_137);
lean_dec(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_116);
x_139 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_117;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_11);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; size_t x_154; size_t x_155; size_t x_156; size_t x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_141 = lean_unsigned_to_nat(2u);
x_142 = lean_array_fget(x_116, x_141);
x_143 = lean_unsigned_to_nat(3u);
x_144 = lean_array_fget(x_116, x_143);
lean_dec(x_116);
x_145 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16;
lean_inc(x_144);
lean_inc(x_142);
x_146 = l_Lean_mkAppB(x_145, x_142, x_144);
x_147 = l_Lean_Expr_hash(x_146);
x_148 = 32;
x_149 = lean_uint64_shift_right(x_147, x_148);
x_150 = lean_uint64_xor(x_147, x_149);
x_151 = 16;
x_152 = lean_uint64_shift_right(x_150, x_151);
x_153 = lean_uint64_xor(x_150, x_152);
x_154 = lean_uint64_to_usize(x_153);
x_155 = 1;
x_156 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_157 = lean_usize_land(x_154, x_156);
x_158 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_159 = lean_array_uget(x_158, x_157);
x_160 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_146, x_159);
x_161 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19;
x_162 = l_Lean_mkAppB(x_161, x_142, x_144);
if (x_160 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_224, 0, x_146);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_224, 2, x_159);
x_225 = lean_array_uset(x_158, x_157, x_224);
x_226 = lean_array_get_size(x_225);
x_227 = lean_unsigned_to_nat(1u);
x_228 = lean_nat_dec_le(x_227, x_226);
lean_dec(x_226);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_225);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
x_163 = x_230;
goto block_222;
}
else
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set(x_231, 1, x_225);
x_163 = x_231;
goto block_222;
}
}
else
{
lean_object* x_232; 
lean_dec(x_159);
lean_dec(x_146);
x_232 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_163 = x_232;
goto block_222;
}
block_222:
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; size_t x_173; size_t x_174; size_t x_175; size_t x_176; lean_object* x_177; uint8_t x_178; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
x_167 = lean_array_get_size(x_166);
x_168 = l_Lean_Expr_hash(x_162);
x_169 = lean_uint64_shift_right(x_168, x_148);
x_170 = lean_uint64_xor(x_168, x_169);
x_171 = lean_uint64_shift_right(x_170, x_151);
x_172 = lean_uint64_xor(x_170, x_171);
x_173 = lean_uint64_to_usize(x_172);
x_174 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_175 = lean_usize_sub(x_174, x_155);
x_176 = lean_usize_land(x_173, x_175);
x_177 = lean_array_uget(x_166, x_176);
x_178 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_162, x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_nat_add(x_165, x_179);
lean_dec(x_165);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_162);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_177);
x_183 = lean_array_uset(x_166, x_176, x_182);
x_184 = lean_nat_mul(x_180, x_137);
x_185 = lean_nat_div(x_184, x_143);
lean_dec(x_184);
x_186 = lean_array_get_size(x_183);
x_187 = lean_nat_dec_le(x_185, x_186);
lean_dec(x_186);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_183);
lean_ctor_set(x_163, 1, x_188);
lean_ctor_set(x_163, 0, x_180);
if (lean_is_scalar(x_117)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_117;
}
lean_ctor_set(x_189, 0, x_163);
lean_ctor_set(x_189, 1, x_11);
return x_189;
}
else
{
lean_object* x_190; 
lean_ctor_set(x_163, 1, x_183);
lean_ctor_set(x_163, 0, x_180);
if (lean_is_scalar(x_117)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_117;
}
lean_ctor_set(x_190, 0, x_163);
lean_ctor_set(x_190, 1, x_11);
return x_190;
}
}
else
{
lean_object* x_191; 
lean_dec(x_177);
lean_dec(x_162);
if (lean_is_scalar(x_117)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_117;
}
lean_ctor_set(x_191, 0, x_163);
lean_ctor_set(x_191, 1, x_11);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint64_t x_195; uint64_t x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; size_t x_200; size_t x_201; size_t x_202; size_t x_203; lean_object* x_204; uint8_t x_205; 
x_192 = lean_ctor_get(x_163, 0);
x_193 = lean_ctor_get(x_163, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_163);
x_194 = lean_array_get_size(x_193);
x_195 = l_Lean_Expr_hash(x_162);
x_196 = lean_uint64_shift_right(x_195, x_148);
x_197 = lean_uint64_xor(x_195, x_196);
x_198 = lean_uint64_shift_right(x_197, x_151);
x_199 = lean_uint64_xor(x_197, x_198);
x_200 = lean_uint64_to_usize(x_199);
x_201 = lean_usize_of_nat(x_194);
lean_dec(x_194);
x_202 = lean_usize_sub(x_201, x_155);
x_203 = lean_usize_land(x_200, x_202);
x_204 = lean_array_uget(x_193, x_203);
x_205 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_162, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_add(x_192, x_206);
lean_dec(x_192);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_162);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_204);
x_210 = lean_array_uset(x_193, x_203, x_209);
x_211 = lean_nat_mul(x_207, x_137);
x_212 = lean_nat_div(x_211, x_143);
lean_dec(x_211);
x_213 = lean_array_get_size(x_210);
x_214 = lean_nat_dec_le(x_212, x_213);
lean_dec(x_213);
lean_dec(x_212);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_210);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_207);
lean_ctor_set(x_216, 1, x_215);
if (lean_is_scalar(x_117)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_117;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_11);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_207);
lean_ctor_set(x_218, 1, x_210);
if (lean_is_scalar(x_117)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_117;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_11);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_204);
lean_dec(x_162);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_192);
lean_ctor_set(x_220, 1, x_193);
if (lean_is_scalar(x_117)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_117;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_11);
return x_221;
}
}
}
}
}
}
}
else
{
lean_object* x_233; uint8_t x_234; 
lean_dec(x_119);
x_233 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20;
x_234 = lean_string_dec_eq(x_118, x_233);
lean_dec(x_118);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_116);
x_235 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_117;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_11);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_237 = lean_array_get_size(x_116);
x_238 = lean_unsigned_to_nat(4u);
x_239 = lean_nat_dec_eq(x_237, x_238);
lean_dec(x_237);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_116);
x_240 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_117;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_11);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint64_t x_248; uint64_t x_249; uint64_t x_250; uint64_t x_251; uint64_t x_252; uint64_t x_253; uint64_t x_254; size_t x_255; size_t x_256; size_t x_257; size_t x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_242 = lean_unsigned_to_nat(2u);
x_243 = lean_array_fget(x_116, x_242);
x_244 = lean_unsigned_to_nat(3u);
x_245 = lean_array_fget(x_116, x_244);
lean_dec(x_116);
x_246 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23;
lean_inc(x_245);
lean_inc(x_243);
x_247 = l_Lean_mkAppB(x_246, x_243, x_245);
x_248 = l_Lean_Expr_hash(x_247);
x_249 = 32;
x_250 = lean_uint64_shift_right(x_248, x_249);
x_251 = lean_uint64_xor(x_248, x_250);
x_252 = 16;
x_253 = lean_uint64_shift_right(x_251, x_252);
x_254 = lean_uint64_xor(x_251, x_253);
x_255 = lean_uint64_to_usize(x_254);
x_256 = 1;
x_257 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_258 = lean_usize_land(x_255, x_257);
x_259 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_260 = lean_array_uget(x_259, x_258);
x_261 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_247, x_260);
x_262 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26;
x_263 = l_Lean_mkAppB(x_262, x_243, x_245);
if (x_261 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_324 = lean_box(0);
x_325 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_325, 0, x_247);
lean_ctor_set(x_325, 1, x_324);
lean_ctor_set(x_325, 2, x_260);
x_326 = lean_array_uset(x_259, x_258, x_325);
x_327 = lean_array_get_size(x_326);
x_328 = lean_unsigned_to_nat(1u);
x_329 = lean_nat_dec_le(x_328, x_327);
lean_dec(x_327);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
x_330 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_326);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_330);
x_264 = x_331;
goto block_323;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_328);
lean_ctor_set(x_332, 1, x_326);
x_264 = x_332;
goto block_323;
}
}
else
{
lean_object* x_333; 
lean_dec(x_260);
lean_dec(x_247);
x_333 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_264 = x_333;
goto block_323;
}
block_323:
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint64_t x_269; uint64_t x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; size_t x_274; size_t x_275; size_t x_276; size_t x_277; lean_object* x_278; uint8_t x_279; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_ctor_get(x_264, 1);
x_268 = lean_array_get_size(x_267);
x_269 = l_Lean_Expr_hash(x_263);
x_270 = lean_uint64_shift_right(x_269, x_249);
x_271 = lean_uint64_xor(x_269, x_270);
x_272 = lean_uint64_shift_right(x_271, x_252);
x_273 = lean_uint64_xor(x_271, x_272);
x_274 = lean_uint64_to_usize(x_273);
x_275 = lean_usize_of_nat(x_268);
lean_dec(x_268);
x_276 = lean_usize_sub(x_275, x_256);
x_277 = lean_usize_land(x_274, x_276);
x_278 = lean_array_uget(x_267, x_277);
x_279 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_263, x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_280 = lean_unsigned_to_nat(1u);
x_281 = lean_nat_add(x_266, x_280);
lean_dec(x_266);
x_282 = lean_box(0);
x_283 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_283, 0, x_263);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set(x_283, 2, x_278);
x_284 = lean_array_uset(x_267, x_277, x_283);
x_285 = lean_nat_mul(x_281, x_238);
x_286 = lean_nat_div(x_285, x_244);
lean_dec(x_285);
x_287 = lean_array_get_size(x_284);
x_288 = lean_nat_dec_le(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_284);
lean_ctor_set(x_264, 1, x_289);
lean_ctor_set(x_264, 0, x_281);
if (lean_is_scalar(x_117)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_117;
}
lean_ctor_set(x_290, 0, x_264);
lean_ctor_set(x_290, 1, x_11);
return x_290;
}
else
{
lean_object* x_291; 
lean_ctor_set(x_264, 1, x_284);
lean_ctor_set(x_264, 0, x_281);
if (lean_is_scalar(x_117)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_117;
}
lean_ctor_set(x_291, 0, x_264);
lean_ctor_set(x_291, 1, x_11);
return x_291;
}
}
else
{
lean_object* x_292; 
lean_dec(x_278);
lean_dec(x_263);
if (lean_is_scalar(x_117)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_117;
}
lean_ctor_set(x_292, 0, x_264);
lean_ctor_set(x_292, 1, x_11);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; uint64_t x_296; uint64_t x_297; uint64_t x_298; uint64_t x_299; uint64_t x_300; size_t x_301; size_t x_302; size_t x_303; size_t x_304; lean_object* x_305; uint8_t x_306; 
x_293 = lean_ctor_get(x_264, 0);
x_294 = lean_ctor_get(x_264, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_264);
x_295 = lean_array_get_size(x_294);
x_296 = l_Lean_Expr_hash(x_263);
x_297 = lean_uint64_shift_right(x_296, x_249);
x_298 = lean_uint64_xor(x_296, x_297);
x_299 = lean_uint64_shift_right(x_298, x_252);
x_300 = lean_uint64_xor(x_298, x_299);
x_301 = lean_uint64_to_usize(x_300);
x_302 = lean_usize_of_nat(x_295);
lean_dec(x_295);
x_303 = lean_usize_sub(x_302, x_256);
x_304 = lean_usize_land(x_301, x_303);
x_305 = lean_array_uget(x_294, x_304);
x_306 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_263, x_305);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_307 = lean_unsigned_to_nat(1u);
x_308 = lean_nat_add(x_293, x_307);
lean_dec(x_293);
x_309 = lean_box(0);
x_310 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_310, 0, x_263);
lean_ctor_set(x_310, 1, x_309);
lean_ctor_set(x_310, 2, x_305);
x_311 = lean_array_uset(x_294, x_304, x_310);
x_312 = lean_nat_mul(x_308, x_238);
x_313 = lean_nat_div(x_312, x_244);
lean_dec(x_312);
x_314 = lean_array_get_size(x_311);
x_315 = lean_nat_dec_le(x_313, x_314);
lean_dec(x_314);
lean_dec(x_313);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_311);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_308);
lean_ctor_set(x_317, 1, x_316);
if (lean_is_scalar(x_117)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_117;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_11);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_308);
lean_ctor_set(x_319, 1, x_311);
if (lean_is_scalar(x_117)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_117;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_11);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; 
lean_dec(x_305);
lean_dec(x_263);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_293);
lean_ctor_set(x_321, 1, x_294);
if (lean_is_scalar(x_117)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_117;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_11);
return x_322;
}
}
}
}
}
}
}
else
{
lean_object* x_334; uint8_t x_335; 
lean_dec(x_119);
x_334 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27;
x_335 = lean_string_dec_eq(x_118, x_334);
lean_dec(x_118);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_116);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_336 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_117;
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_11);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_array_get_size(x_116);
x_339 = lean_unsigned_to_nat(6u);
x_340 = lean_nat_dec_eq(x_338, x_339);
lean_dec(x_338);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_116);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_341 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_117;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_11);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_117);
x_343 = lean_unsigned_to_nat(4u);
x_344 = lean_array_fget(x_116, x_343);
x_345 = lean_unsigned_to_nat(5u);
x_346 = lean_array_fget(x_116, x_345);
lean_dec(x_116);
lean_inc(x_346);
x_347 = l_Lean_Expr_getAppFnArgs(x_346);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 1)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 1)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_352 = x_347;
} else {
 lean_dec_ref(x_347);
 x_352 = lean_box(0);
}
x_353 = lean_ctor_get(x_348, 1);
lean_inc(x_353);
lean_dec(x_348);
x_354 = lean_ctor_get(x_349, 1);
lean_inc(x_354);
lean_dec(x_349);
x_355 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_356 = lean_string_dec_eq(x_354, x_355);
if (x_356 == 0)
{
uint8_t x_357; 
x_357 = lean_string_dec_eq(x_354, x_120);
lean_dec(x_354);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_358 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_352;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_11);
return x_359;
}
else
{
lean_object* x_360; uint8_t x_361; 
x_360 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_361 = lean_string_dec_eq(x_353, x_360);
lean_dec(x_353);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_362 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_352;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_11);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_364 = lean_array_get_size(x_351);
x_365 = lean_unsigned_to_nat(3u);
x_366 = lean_nat_dec_eq(x_364, x_365);
lean_dec(x_364);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_367 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_352;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_11);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_unsigned_to_nat(0u);
x_370 = lean_array_fget(x_351, x_369);
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
x_375 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_376 = lean_string_dec_eq(x_374, x_375);
lean_dec(x_374);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_373);
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_377 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_352;
}
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_11);
return x_378;
}
else
{
lean_dec(x_352);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_379 = lean_unsigned_to_nat(2u);
x_380 = lean_array_fget(x_351, x_379);
lean_dec(x_351);
lean_inc(x_380);
x_381 = l_Lean_Expr_getAppFnArgs(x_380);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
if (lean_obj_tag(x_382) == 1)
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
if (lean_obj_tag(x_383) == 1)
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_385 = lean_ctor_get(x_381, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_386 = x_381;
} else {
 lean_dec_ref(x_381);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_382, 1);
lean_inc(x_387);
lean_dec(x_382);
x_388 = lean_ctor_get(x_383, 1);
lean_inc(x_388);
lean_dec(x_383);
x_389 = lean_string_dec_eq(x_388, x_355);
lean_dec(x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_380);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_390 = l_Lean_Expr_getAppFnArgs(x_344);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_obj_tag(x_391) == 1)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 1)
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
uint8_t x_394; 
x_394 = !lean_is_exclusive(x_390);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_395 = lean_ctor_get(x_390, 1);
x_396 = lean_ctor_get(x_390, 0);
lean_dec(x_396);
x_397 = lean_ctor_get(x_391, 1);
lean_inc(x_397);
lean_dec(x_391);
x_398 = lean_ctor_get(x_392, 1);
lean_inc(x_398);
lean_dec(x_392);
x_399 = lean_string_dec_eq(x_398, x_120);
lean_dec(x_398);
if (x_399 == 0)
{
lean_object* x_400; 
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_400 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_400);
return x_390;
}
else
{
uint8_t x_401; 
x_401 = lean_string_dec_eq(x_397, x_360);
lean_dec(x_397);
if (x_401 == 0)
{
lean_object* x_402; 
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_402 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_402);
return x_390;
}
else
{
lean_object* x_403; uint8_t x_404; 
x_403 = lean_array_get_size(x_395);
x_404 = lean_nat_dec_eq(x_403, x_365);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; 
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_405 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_405);
return x_390;
}
else
{
lean_object* x_406; 
x_406 = lean_array_fget(x_395, x_369);
if (lean_obj_tag(x_406) == 4)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_obj_tag(x_407) == 1)
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; uint8_t x_411; 
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_411 = lean_string_dec_eq(x_410, x_375);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; 
lean_dec(x_409);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_412 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_412);
return x_390;
}
else
{
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; uint64_t x_416; uint64_t x_417; uint64_t x_418; uint64_t x_419; uint64_t x_420; uint64_t x_421; uint64_t x_422; size_t x_423; size_t x_424; size_t x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_413 = lean_array_fget(x_395, x_379);
lean_dec(x_395);
x_414 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_415 = l_Lean_mkAppB(x_414, x_413, x_346);
x_416 = l_Lean_Expr_hash(x_415);
x_417 = 32;
x_418 = lean_uint64_shift_right(x_416, x_417);
x_419 = lean_uint64_xor(x_416, x_418);
x_420 = 16;
x_421 = lean_uint64_shift_right(x_419, x_420);
x_422 = lean_uint64_xor(x_419, x_421);
x_423 = lean_uint64_to_usize(x_422);
x_424 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_425 = lean_usize_land(x_423, x_424);
x_426 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_427 = lean_array_uget(x_426, x_425);
x_428 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_415, x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_429 = lean_box(0);
x_430 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_430, 0, x_415);
lean_ctor_set(x_430, 1, x_429);
lean_ctor_set(x_430, 2, x_427);
x_431 = lean_array_uset(x_426, x_425, x_430);
x_432 = lean_array_get_size(x_431);
x_433 = lean_unsigned_to_nat(1u);
x_434 = lean_nat_dec_le(x_433, x_432);
lean_dec(x_432);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; 
x_435 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_431);
lean_ctor_set(x_390, 1, x_435);
lean_ctor_set(x_390, 0, x_433);
if (lean_is_scalar(x_386)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_386;
}
lean_ctor_set(x_436, 0, x_390);
lean_ctor_set(x_436, 1, x_11);
return x_436;
}
else
{
lean_object* x_437; 
lean_ctor_set(x_390, 1, x_431);
lean_ctor_set(x_390, 0, x_433);
if (lean_is_scalar(x_386)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_386;
}
lean_ctor_set(x_437, 0, x_390);
lean_ctor_set(x_437, 1, x_11);
return x_437;
}
}
else
{
lean_object* x_438; 
lean_dec(x_427);
lean_dec(x_415);
lean_dec(x_386);
x_438 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_438);
return x_390;
}
}
else
{
uint8_t x_439; 
lean_free_object(x_390);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_439 = !lean_is_exclusive(x_409);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_409, 1);
lean_dec(x_440);
x_441 = lean_ctor_get(x_409, 0);
lean_dec(x_441);
x_442 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_409, 0);
lean_ctor_set(x_409, 1, x_11);
lean_ctor_set(x_409, 0, x_442);
return x_409;
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_409);
x_443 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_11);
return x_444;
}
}
}
}
else
{
lean_object* x_445; 
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_445 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_445);
return x_390;
}
}
else
{
lean_object* x_446; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_446 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_446);
return x_390;
}
}
else
{
lean_object* x_447; 
lean_dec(x_406);
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_346);
x_447 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_447);
return x_390;
}
}
}
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_448 = lean_ctor_get(x_390, 1);
lean_inc(x_448);
lean_dec(x_390);
x_449 = lean_ctor_get(x_391, 1);
lean_inc(x_449);
lean_dec(x_391);
x_450 = lean_ctor_get(x_392, 1);
lean_inc(x_450);
lean_dec(x_392);
x_451 = lean_string_dec_eq(x_450, x_120);
lean_dec(x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
x_452 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_11);
return x_453;
}
else
{
uint8_t x_454; 
x_454 = lean_string_dec_eq(x_449, x_360);
lean_dec(x_449);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
x_455 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_11);
return x_456;
}
else
{
lean_object* x_457; uint8_t x_458; 
x_457 = lean_array_get_size(x_448);
x_458 = lean_nat_dec_eq(x_457, x_365);
lean_dec(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; 
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
x_459 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_11);
return x_460;
}
else
{
lean_object* x_461; 
x_461 = lean_array_fget(x_448, x_369);
if (lean_obj_tag(x_461) == 4)
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
if (lean_obj_tag(x_462) == 1)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_464 = lean_ctor_get(x_461, 1);
lean_inc(x_464);
lean_dec(x_461);
x_465 = lean_ctor_get(x_462, 1);
lean_inc(x_465);
lean_dec(x_462);
x_466 = lean_string_dec_eq(x_465, x_375);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; 
lean_dec(x_464);
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
x_467 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_11);
return x_468;
}
else
{
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; uint64_t x_472; uint64_t x_473; uint64_t x_474; uint64_t x_475; uint64_t x_476; uint64_t x_477; uint64_t x_478; size_t x_479; size_t x_480; size_t x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_469 = lean_array_fget(x_448, x_379);
lean_dec(x_448);
x_470 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_471 = l_Lean_mkAppB(x_470, x_469, x_346);
x_472 = l_Lean_Expr_hash(x_471);
x_473 = 32;
x_474 = lean_uint64_shift_right(x_472, x_473);
x_475 = lean_uint64_xor(x_472, x_474);
x_476 = 16;
x_477 = lean_uint64_shift_right(x_475, x_476);
x_478 = lean_uint64_xor(x_475, x_477);
x_479 = lean_uint64_to_usize(x_478);
x_480 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_481 = lean_usize_land(x_479, x_480);
x_482 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_483 = lean_array_uget(x_482, x_481);
x_484 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_471, x_483);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; 
x_485 = lean_box(0);
x_486 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_486, 0, x_471);
lean_ctor_set(x_486, 1, x_485);
lean_ctor_set(x_486, 2, x_483);
x_487 = lean_array_uset(x_482, x_481, x_486);
x_488 = lean_array_get_size(x_487);
x_489 = lean_unsigned_to_nat(1u);
x_490 = lean_nat_dec_le(x_489, x_488);
lean_dec(x_488);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_487);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_491);
if (lean_is_scalar(x_386)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_386;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_11);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_489);
lean_ctor_set(x_494, 1, x_487);
if (lean_is_scalar(x_386)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_386;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_11);
return x_495;
}
}
else
{
lean_object* x_496; lean_object* x_497; 
lean_dec(x_483);
lean_dec(x_471);
lean_dec(x_386);
x_496 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_11);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_498 = x_464;
} else {
 lean_dec_ref(x_464);
 x_498 = lean_box(0);
}
x_499 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_498)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_498;
 lean_ctor_set_tag(x_500, 0);
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_11);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
x_501 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_11);
return x_502;
}
}
else
{
lean_object* x_503; lean_object* x_504; 
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
x_503 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_11);
return x_504;
}
}
else
{
lean_object* x_505; lean_object* x_506; 
lean_dec(x_461);
lean_dec(x_448);
lean_dec(x_386);
lean_dec(x_346);
x_505 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_11);
return x_506;
}
}
}
}
}
}
else
{
uint8_t x_507; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_386);
lean_dec(x_346);
x_507 = !lean_is_exclusive(x_390);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_390, 1);
lean_dec(x_508);
x_509 = lean_ctor_get(x_390, 0);
lean_dec(x_509);
x_510 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_510);
return x_390;
}
else
{
lean_object* x_511; lean_object* x_512; 
lean_dec(x_390);
x_511 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_11);
return x_512;
}
}
}
else
{
uint8_t x_513; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_386);
lean_dec(x_346);
x_513 = !lean_is_exclusive(x_390);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_390, 1);
lean_dec(x_514);
x_515 = lean_ctor_get(x_390, 0);
lean_dec(x_515);
x_516 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_516);
return x_390;
}
else
{
lean_object* x_517; lean_object* x_518; 
lean_dec(x_390);
x_517 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_11);
return x_518;
}
}
}
else
{
uint8_t x_519; 
lean_dec(x_391);
lean_dec(x_386);
lean_dec(x_346);
x_519 = !lean_is_exclusive(x_390);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_390, 1);
lean_dec(x_520);
x_521 = lean_ctor_get(x_390, 0);
lean_dec(x_521);
x_522 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_390, 1, x_11);
lean_ctor_set(x_390, 0, x_522);
return x_390;
}
else
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_390);
x_523 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_11);
return x_524;
}
}
}
else
{
lean_object* x_525; uint8_t x_526; 
x_525 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_526 = lean_string_dec_eq(x_387, x_525);
lean_dec(x_387);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; 
lean_dec(x_385);
lean_dec(x_380);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_527 = l_Lean_Expr_getAppFnArgs(x_344);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
if (lean_obj_tag(x_528) == 1)
{
lean_object* x_529; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
if (lean_obj_tag(x_529) == 1)
{
lean_object* x_530; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
if (lean_obj_tag(x_530) == 0)
{
uint8_t x_531; 
x_531 = !lean_is_exclusive(x_527);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; 
x_532 = lean_ctor_get(x_527, 1);
x_533 = lean_ctor_get(x_527, 0);
lean_dec(x_533);
x_534 = lean_ctor_get(x_528, 1);
lean_inc(x_534);
lean_dec(x_528);
x_535 = lean_ctor_get(x_529, 1);
lean_inc(x_535);
lean_dec(x_529);
x_536 = lean_string_dec_eq(x_535, x_120);
lean_dec(x_535);
if (x_536 == 0)
{
lean_object* x_537; 
lean_dec(x_534);
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_537 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_537);
return x_527;
}
else
{
uint8_t x_538; 
x_538 = lean_string_dec_eq(x_534, x_360);
lean_dec(x_534);
if (x_538 == 0)
{
lean_object* x_539; 
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_539 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_539);
return x_527;
}
else
{
lean_object* x_540; uint8_t x_541; 
x_540 = lean_array_get_size(x_532);
x_541 = lean_nat_dec_eq(x_540, x_365);
lean_dec(x_540);
if (x_541 == 0)
{
lean_object* x_542; 
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_542 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_542);
return x_527;
}
else
{
lean_object* x_543; 
x_543 = lean_array_fget(x_532, x_369);
if (lean_obj_tag(x_543) == 4)
{
lean_object* x_544; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
if (lean_obj_tag(x_544) == 1)
{
lean_object* x_545; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_546 = lean_ctor_get(x_543, 1);
lean_inc(x_546);
lean_dec(x_543);
x_547 = lean_ctor_get(x_544, 1);
lean_inc(x_547);
lean_dec(x_544);
x_548 = lean_string_dec_eq(x_547, x_375);
lean_dec(x_547);
if (x_548 == 0)
{
lean_object* x_549; 
lean_dec(x_546);
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_549 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_549);
return x_527;
}
else
{
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; uint64_t x_553; uint64_t x_554; uint64_t x_555; uint64_t x_556; uint64_t x_557; uint64_t x_558; uint64_t x_559; size_t x_560; size_t x_561; size_t x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; 
x_550 = lean_array_fget(x_532, x_379);
lean_dec(x_532);
x_551 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_552 = l_Lean_mkAppB(x_551, x_550, x_346);
x_553 = l_Lean_Expr_hash(x_552);
x_554 = 32;
x_555 = lean_uint64_shift_right(x_553, x_554);
x_556 = lean_uint64_xor(x_553, x_555);
x_557 = 16;
x_558 = lean_uint64_shift_right(x_556, x_557);
x_559 = lean_uint64_xor(x_556, x_558);
x_560 = lean_uint64_to_usize(x_559);
x_561 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_562 = lean_usize_land(x_560, x_561);
x_563 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_564 = lean_array_uget(x_563, x_562);
x_565 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_552, x_564);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; 
x_566 = lean_box(0);
x_567 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_567, 0, x_552);
lean_ctor_set(x_567, 1, x_566);
lean_ctor_set(x_567, 2, x_564);
x_568 = lean_array_uset(x_563, x_562, x_567);
x_569 = lean_array_get_size(x_568);
x_570 = lean_unsigned_to_nat(1u);
x_571 = lean_nat_dec_le(x_570, x_569);
lean_dec(x_569);
if (x_571 == 0)
{
lean_object* x_572; lean_object* x_573; 
x_572 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_568);
lean_ctor_set(x_527, 1, x_572);
lean_ctor_set(x_527, 0, x_570);
if (lean_is_scalar(x_386)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_386;
}
lean_ctor_set(x_573, 0, x_527);
lean_ctor_set(x_573, 1, x_11);
return x_573;
}
else
{
lean_object* x_574; 
lean_ctor_set(x_527, 1, x_568);
lean_ctor_set(x_527, 0, x_570);
if (lean_is_scalar(x_386)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_386;
}
lean_ctor_set(x_574, 0, x_527);
lean_ctor_set(x_574, 1, x_11);
return x_574;
}
}
else
{
lean_object* x_575; 
lean_dec(x_564);
lean_dec(x_552);
lean_dec(x_386);
x_575 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_575);
return x_527;
}
}
else
{
uint8_t x_576; 
lean_free_object(x_527);
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_576 = !lean_is_exclusive(x_546);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_546, 1);
lean_dec(x_577);
x_578 = lean_ctor_get(x_546, 0);
lean_dec(x_578);
x_579 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_546, 0);
lean_ctor_set(x_546, 1, x_11);
lean_ctor_set(x_546, 0, x_579);
return x_546;
}
else
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_546);
x_580 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_11);
return x_581;
}
}
}
}
else
{
lean_object* x_582; 
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_582 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_582);
return x_527;
}
}
else
{
lean_object* x_583; 
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_583 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_583);
return x_527;
}
}
else
{
lean_object* x_584; 
lean_dec(x_543);
lean_dec(x_532);
lean_dec(x_386);
lean_dec(x_346);
x_584 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_584);
return x_527;
}
}
}
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; 
x_585 = lean_ctor_get(x_527, 1);
lean_inc(x_585);
lean_dec(x_527);
x_586 = lean_ctor_get(x_528, 1);
lean_inc(x_586);
lean_dec(x_528);
x_587 = lean_ctor_get(x_529, 1);
lean_inc(x_587);
lean_dec(x_529);
x_588 = lean_string_dec_eq(x_587, x_120);
lean_dec(x_587);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
x_589 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_11);
return x_590;
}
else
{
uint8_t x_591; 
x_591 = lean_string_dec_eq(x_586, x_360);
lean_dec(x_586);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; 
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
x_592 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_593 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_11);
return x_593;
}
else
{
lean_object* x_594; uint8_t x_595; 
x_594 = lean_array_get_size(x_585);
x_595 = lean_nat_dec_eq(x_594, x_365);
lean_dec(x_594);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; 
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
x_596 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_11);
return x_597;
}
else
{
lean_object* x_598; 
x_598 = lean_array_fget(x_585, x_369);
if (lean_obj_tag(x_598) == 4)
{
lean_object* x_599; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
if (lean_obj_tag(x_599) == 1)
{
lean_object* x_600; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; uint8_t x_603; 
x_601 = lean_ctor_get(x_598, 1);
lean_inc(x_601);
lean_dec(x_598);
x_602 = lean_ctor_get(x_599, 1);
lean_inc(x_602);
lean_dec(x_599);
x_603 = lean_string_dec_eq(x_602, x_375);
lean_dec(x_602);
if (x_603 == 0)
{
lean_object* x_604; lean_object* x_605; 
lean_dec(x_601);
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
x_604 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_11);
return x_605;
}
else
{
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; uint64_t x_609; uint64_t x_610; uint64_t x_611; uint64_t x_612; uint64_t x_613; uint64_t x_614; uint64_t x_615; size_t x_616; size_t x_617; size_t x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; 
x_606 = lean_array_fget(x_585, x_379);
lean_dec(x_585);
x_607 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_608 = l_Lean_mkAppB(x_607, x_606, x_346);
x_609 = l_Lean_Expr_hash(x_608);
x_610 = 32;
x_611 = lean_uint64_shift_right(x_609, x_610);
x_612 = lean_uint64_xor(x_609, x_611);
x_613 = 16;
x_614 = lean_uint64_shift_right(x_612, x_613);
x_615 = lean_uint64_xor(x_612, x_614);
x_616 = lean_uint64_to_usize(x_615);
x_617 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_618 = lean_usize_land(x_616, x_617);
x_619 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_620 = lean_array_uget(x_619, x_618);
x_621 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_608, x_620);
if (x_621 == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
x_622 = lean_box(0);
x_623 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_623, 0, x_608);
lean_ctor_set(x_623, 1, x_622);
lean_ctor_set(x_623, 2, x_620);
x_624 = lean_array_uset(x_619, x_618, x_623);
x_625 = lean_array_get_size(x_624);
x_626 = lean_unsigned_to_nat(1u);
x_627 = lean_nat_dec_le(x_626, x_625);
lean_dec(x_625);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_624);
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_628);
if (lean_is_scalar(x_386)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_386;
}
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_11);
return x_630;
}
else
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_626);
lean_ctor_set(x_631, 1, x_624);
if (lean_is_scalar(x_386)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_386;
}
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_11);
return x_632;
}
}
else
{
lean_object* x_633; lean_object* x_634; 
lean_dec(x_620);
lean_dec(x_608);
lean_dec(x_386);
x_633 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_11);
return x_634;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_635 = x_601;
} else {
 lean_dec_ref(x_601);
 x_635 = lean_box(0);
}
x_636 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_635)) {
 x_637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_637 = x_635;
 lean_ctor_set_tag(x_637, 0);
}
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_11);
return x_637;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
x_638 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_11);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; 
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
x_640 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_11);
return x_641;
}
}
else
{
lean_object* x_642; lean_object* x_643; 
lean_dec(x_598);
lean_dec(x_585);
lean_dec(x_386);
lean_dec(x_346);
x_642 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_11);
return x_643;
}
}
}
}
}
}
else
{
uint8_t x_644; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_386);
lean_dec(x_346);
x_644 = !lean_is_exclusive(x_527);
if (x_644 == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_527, 1);
lean_dec(x_645);
x_646 = lean_ctor_get(x_527, 0);
lean_dec(x_646);
x_647 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_647);
return x_527;
}
else
{
lean_object* x_648; lean_object* x_649; 
lean_dec(x_527);
x_648 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_11);
return x_649;
}
}
}
else
{
uint8_t x_650; 
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_386);
lean_dec(x_346);
x_650 = !lean_is_exclusive(x_527);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_527, 1);
lean_dec(x_651);
x_652 = lean_ctor_get(x_527, 0);
lean_dec(x_652);
x_653 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_653);
return x_527;
}
else
{
lean_object* x_654; lean_object* x_655; 
lean_dec(x_527);
x_654 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_11);
return x_655;
}
}
}
else
{
uint8_t x_656; 
lean_dec(x_528);
lean_dec(x_386);
lean_dec(x_346);
x_656 = !lean_is_exclusive(x_527);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_527, 1);
lean_dec(x_657);
x_658 = lean_ctor_get(x_527, 0);
lean_dec(x_658);
x_659 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_527, 1, x_11);
lean_ctor_set(x_527, 0, x_659);
return x_527;
}
else
{
lean_object* x_660; lean_object* x_661; 
lean_dec(x_527);
x_660 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_11);
return x_661;
}
}
}
else
{
lean_object* x_662; uint8_t x_663; 
x_662 = lean_array_get_size(x_385);
x_663 = lean_nat_dec_eq(x_662, x_339);
lean_dec(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; 
lean_dec(x_385);
lean_dec(x_380);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_664 = l_Lean_Expr_getAppFnArgs(x_344);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
if (lean_obj_tag(x_665) == 1)
{
lean_object* x_666; 
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
if (lean_obj_tag(x_666) == 1)
{
lean_object* x_667; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
if (lean_obj_tag(x_667) == 0)
{
uint8_t x_668; 
x_668 = !lean_is_exclusive(x_664);
if (x_668 == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_669 = lean_ctor_get(x_664, 1);
x_670 = lean_ctor_get(x_664, 0);
lean_dec(x_670);
x_671 = lean_ctor_get(x_665, 1);
lean_inc(x_671);
lean_dec(x_665);
x_672 = lean_ctor_get(x_666, 1);
lean_inc(x_672);
lean_dec(x_666);
x_673 = lean_string_dec_eq(x_672, x_120);
lean_dec(x_672);
if (x_673 == 0)
{
lean_object* x_674; 
lean_dec(x_671);
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_674 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_674);
return x_664;
}
else
{
uint8_t x_675; 
x_675 = lean_string_dec_eq(x_671, x_360);
lean_dec(x_671);
if (x_675 == 0)
{
lean_object* x_676; 
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_676 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_676);
return x_664;
}
else
{
lean_object* x_677; uint8_t x_678; 
x_677 = lean_array_get_size(x_669);
x_678 = lean_nat_dec_eq(x_677, x_365);
lean_dec(x_677);
if (x_678 == 0)
{
lean_object* x_679; 
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_679 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_679);
return x_664;
}
else
{
lean_object* x_680; 
x_680 = lean_array_fget(x_669, x_369);
if (lean_obj_tag(x_680) == 4)
{
lean_object* x_681; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
if (lean_obj_tag(x_681) == 1)
{
lean_object* x_682; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; uint8_t x_685; 
x_683 = lean_ctor_get(x_680, 1);
lean_inc(x_683);
lean_dec(x_680);
x_684 = lean_ctor_get(x_681, 1);
lean_inc(x_684);
lean_dec(x_681);
x_685 = lean_string_dec_eq(x_684, x_375);
lean_dec(x_684);
if (x_685 == 0)
{
lean_object* x_686; 
lean_dec(x_683);
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_686 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_686);
return x_664;
}
else
{
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; uint64_t x_690; uint64_t x_691; uint64_t x_692; uint64_t x_693; uint64_t x_694; uint64_t x_695; uint64_t x_696; size_t x_697; size_t x_698; size_t x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_687 = lean_array_fget(x_669, x_379);
lean_dec(x_669);
x_688 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_689 = l_Lean_mkAppB(x_688, x_687, x_346);
x_690 = l_Lean_Expr_hash(x_689);
x_691 = 32;
x_692 = lean_uint64_shift_right(x_690, x_691);
x_693 = lean_uint64_xor(x_690, x_692);
x_694 = 16;
x_695 = lean_uint64_shift_right(x_693, x_694);
x_696 = lean_uint64_xor(x_693, x_695);
x_697 = lean_uint64_to_usize(x_696);
x_698 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_699 = lean_usize_land(x_697, x_698);
x_700 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_701 = lean_array_uget(x_700, x_699);
x_702 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_689, x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; 
x_703 = lean_box(0);
x_704 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_704, 0, x_689);
lean_ctor_set(x_704, 1, x_703);
lean_ctor_set(x_704, 2, x_701);
x_705 = lean_array_uset(x_700, x_699, x_704);
x_706 = lean_array_get_size(x_705);
x_707 = lean_unsigned_to_nat(1u);
x_708 = lean_nat_dec_le(x_707, x_706);
lean_dec(x_706);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_705);
lean_ctor_set(x_664, 1, x_709);
lean_ctor_set(x_664, 0, x_707);
if (lean_is_scalar(x_386)) {
 x_710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_710 = x_386;
}
lean_ctor_set(x_710, 0, x_664);
lean_ctor_set(x_710, 1, x_11);
return x_710;
}
else
{
lean_object* x_711; 
lean_ctor_set(x_664, 1, x_705);
lean_ctor_set(x_664, 0, x_707);
if (lean_is_scalar(x_386)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_386;
}
lean_ctor_set(x_711, 0, x_664);
lean_ctor_set(x_711, 1, x_11);
return x_711;
}
}
else
{
lean_object* x_712; 
lean_dec(x_701);
lean_dec(x_689);
lean_dec(x_386);
x_712 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_712);
return x_664;
}
}
else
{
uint8_t x_713; 
lean_free_object(x_664);
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_713 = !lean_is_exclusive(x_683);
if (x_713 == 0)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_683, 1);
lean_dec(x_714);
x_715 = lean_ctor_get(x_683, 0);
lean_dec(x_715);
x_716 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_683, 0);
lean_ctor_set(x_683, 1, x_11);
lean_ctor_set(x_683, 0, x_716);
return x_683;
}
else
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_683);
x_717 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_11);
return x_718;
}
}
}
}
else
{
lean_object* x_719; 
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_719 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_719);
return x_664;
}
}
else
{
lean_object* x_720; 
lean_dec(x_681);
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_720 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_720);
return x_664;
}
}
else
{
lean_object* x_721; 
lean_dec(x_680);
lean_dec(x_669);
lean_dec(x_386);
lean_dec(x_346);
x_721 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_721);
return x_664;
}
}
}
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; 
x_722 = lean_ctor_get(x_664, 1);
lean_inc(x_722);
lean_dec(x_664);
x_723 = lean_ctor_get(x_665, 1);
lean_inc(x_723);
lean_dec(x_665);
x_724 = lean_ctor_get(x_666, 1);
lean_inc(x_724);
lean_dec(x_666);
x_725 = lean_string_dec_eq(x_724, x_120);
lean_dec(x_724);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; 
lean_dec(x_723);
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
x_726 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_11);
return x_727;
}
else
{
uint8_t x_728; 
x_728 = lean_string_dec_eq(x_723, x_360);
lean_dec(x_723);
if (x_728 == 0)
{
lean_object* x_729; lean_object* x_730; 
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
x_729 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_730 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_11);
return x_730;
}
else
{
lean_object* x_731; uint8_t x_732; 
x_731 = lean_array_get_size(x_722);
x_732 = lean_nat_dec_eq(x_731, x_365);
lean_dec(x_731);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; 
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
x_733 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_11);
return x_734;
}
else
{
lean_object* x_735; 
x_735 = lean_array_fget(x_722, x_369);
if (lean_obj_tag(x_735) == 4)
{
lean_object* x_736; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
if (lean_obj_tag(x_736) == 1)
{
lean_object* x_737; 
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; uint8_t x_740; 
x_738 = lean_ctor_get(x_735, 1);
lean_inc(x_738);
lean_dec(x_735);
x_739 = lean_ctor_get(x_736, 1);
lean_inc(x_739);
lean_dec(x_736);
x_740 = lean_string_dec_eq(x_739, x_375);
lean_dec(x_739);
if (x_740 == 0)
{
lean_object* x_741; lean_object* x_742; 
lean_dec(x_738);
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
x_741 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_11);
return x_742;
}
else
{
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; uint64_t x_746; uint64_t x_747; uint64_t x_748; uint64_t x_749; uint64_t x_750; uint64_t x_751; uint64_t x_752; size_t x_753; size_t x_754; size_t x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; 
x_743 = lean_array_fget(x_722, x_379);
lean_dec(x_722);
x_744 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_745 = l_Lean_mkAppB(x_744, x_743, x_346);
x_746 = l_Lean_Expr_hash(x_745);
x_747 = 32;
x_748 = lean_uint64_shift_right(x_746, x_747);
x_749 = lean_uint64_xor(x_746, x_748);
x_750 = 16;
x_751 = lean_uint64_shift_right(x_749, x_750);
x_752 = lean_uint64_xor(x_749, x_751);
x_753 = lean_uint64_to_usize(x_752);
x_754 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_755 = lean_usize_land(x_753, x_754);
x_756 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_757 = lean_array_uget(x_756, x_755);
x_758 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_745, x_757);
if (x_758 == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; 
x_759 = lean_box(0);
x_760 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_760, 0, x_745);
lean_ctor_set(x_760, 1, x_759);
lean_ctor_set(x_760, 2, x_757);
x_761 = lean_array_uset(x_756, x_755, x_760);
x_762 = lean_array_get_size(x_761);
x_763 = lean_unsigned_to_nat(1u);
x_764 = lean_nat_dec_le(x_763, x_762);
lean_dec(x_762);
if (x_764 == 0)
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_765 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_761);
x_766 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_765);
if (lean_is_scalar(x_386)) {
 x_767 = lean_alloc_ctor(0, 2, 0);
} else {
 x_767 = x_386;
}
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_11);
return x_767;
}
else
{
lean_object* x_768; lean_object* x_769; 
x_768 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_768, 0, x_763);
lean_ctor_set(x_768, 1, x_761);
if (lean_is_scalar(x_386)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_386;
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_11);
return x_769;
}
}
else
{
lean_object* x_770; lean_object* x_771; 
lean_dec(x_757);
lean_dec(x_745);
lean_dec(x_386);
x_770 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_771 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set(x_771, 1, x_11);
return x_771;
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_772 = x_738;
} else {
 lean_dec_ref(x_738);
 x_772 = lean_box(0);
}
x_773 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_772)) {
 x_774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_774 = x_772;
 lean_ctor_set_tag(x_774, 0);
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_11);
return x_774;
}
}
}
else
{
lean_object* x_775; lean_object* x_776; 
lean_dec(x_737);
lean_dec(x_736);
lean_dec(x_735);
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
x_775 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_776 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_11);
return x_776;
}
}
else
{
lean_object* x_777; lean_object* x_778; 
lean_dec(x_736);
lean_dec(x_735);
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
x_777 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_11);
return x_778;
}
}
else
{
lean_object* x_779; lean_object* x_780; 
lean_dec(x_735);
lean_dec(x_722);
lean_dec(x_386);
lean_dec(x_346);
x_779 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_780 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_11);
return x_780;
}
}
}
}
}
}
else
{
uint8_t x_781; 
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_386);
lean_dec(x_346);
x_781 = !lean_is_exclusive(x_664);
if (x_781 == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_664, 1);
lean_dec(x_782);
x_783 = lean_ctor_get(x_664, 0);
lean_dec(x_783);
x_784 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_784);
return x_664;
}
else
{
lean_object* x_785; lean_object* x_786; 
lean_dec(x_664);
x_785 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_786 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_11);
return x_786;
}
}
}
else
{
uint8_t x_787; 
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_386);
lean_dec(x_346);
x_787 = !lean_is_exclusive(x_664);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_664, 1);
lean_dec(x_788);
x_789 = lean_ctor_get(x_664, 0);
lean_dec(x_789);
x_790 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_790);
return x_664;
}
else
{
lean_object* x_791; lean_object* x_792; 
lean_dec(x_664);
x_791 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_11);
return x_792;
}
}
}
else
{
uint8_t x_793; 
lean_dec(x_665);
lean_dec(x_386);
lean_dec(x_346);
x_793 = !lean_is_exclusive(x_664);
if (x_793 == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = lean_ctor_get(x_664, 1);
lean_dec(x_794);
x_795 = lean_ctor_get(x_664, 0);
lean_dec(x_795);
x_796 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_664, 1, x_11);
lean_ctor_set(x_664, 0, x_796);
return x_664;
}
else
{
lean_object* x_797; lean_object* x_798; 
lean_dec(x_664);
x_797 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_798 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_11);
return x_798;
}
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_array_fget(x_385, x_343);
x_800 = lean_array_fget(x_385, x_345);
lean_dec(x_385);
lean_inc(x_799);
x_801 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_799);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; 
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_380);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_802 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_386)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_386;
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_11);
return x_803;
}
else
{
lean_object* x_804; uint8_t x_805; 
x_804 = lean_ctor_get(x_801, 0);
lean_inc(x_804);
lean_dec(x_801);
x_805 = lean_nat_dec_eq(x_804, x_369);
lean_dec(x_804);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_806 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_807 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37;
x_808 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40;
x_809 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41;
lean_inc(x_799);
x_810 = l_Lean_mkApp4(x_806, x_807, x_808, x_809, x_799);
x_811 = l_Lean_Meta_mkDecideProof(x_810, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; uint64_t x_819; uint64_t x_820; size_t x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_884; uint8_t x_911; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_814 = x_811;
} else {
 lean_dec_ref(x_811);
 x_814 = lean_box(0);
}
x_815 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44;
x_816 = l_Lean_mkApp3(x_815, x_799, x_800, x_812);
x_817 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47;
x_818 = l_Lean_mkAppB(x_817, x_380, x_816);
x_819 = 32;
x_820 = 16;
x_821 = 1;
x_822 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
lean_inc(x_818);
lean_inc(x_346);
lean_inc(x_344);
x_823 = l_Lean_mkApp3(x_822, x_344, x_346, x_818);
x_911 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55;
if (x_911 == 0)
{
lean_object* x_912; 
x_912 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_884 = x_912;
goto block_910;
}
else
{
lean_object* x_913; 
x_913 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
x_884 = x_913;
goto block_910;
}
block_883:
{
uint8_t x_825; 
x_825 = !lean_is_exclusive(x_824);
if (x_825 == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; uint64_t x_829; uint64_t x_830; uint64_t x_831; uint64_t x_832; uint64_t x_833; size_t x_834; size_t x_835; size_t x_836; size_t x_837; lean_object* x_838; uint8_t x_839; 
x_826 = lean_ctor_get(x_824, 0);
x_827 = lean_ctor_get(x_824, 1);
x_828 = lean_array_get_size(x_827);
x_829 = l_Lean_Expr_hash(x_823);
x_830 = lean_uint64_shift_right(x_829, x_819);
x_831 = lean_uint64_xor(x_829, x_830);
x_832 = lean_uint64_shift_right(x_831, x_820);
x_833 = lean_uint64_xor(x_831, x_832);
x_834 = lean_uint64_to_usize(x_833);
x_835 = lean_usize_of_nat(x_828);
lean_dec(x_828);
x_836 = lean_usize_sub(x_835, x_821);
x_837 = lean_usize_land(x_834, x_836);
x_838 = lean_array_uget(x_827, x_837);
x_839 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_823, x_838);
if (x_839 == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; 
x_840 = lean_unsigned_to_nat(1u);
x_841 = lean_nat_add(x_826, x_840);
lean_dec(x_826);
x_842 = lean_box(0);
x_843 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_843, 0, x_823);
lean_ctor_set(x_843, 1, x_842);
lean_ctor_set(x_843, 2, x_838);
x_844 = lean_array_uset(x_827, x_837, x_843);
x_845 = lean_nat_mul(x_841, x_343);
x_846 = lean_nat_div(x_845, x_365);
lean_dec(x_845);
x_847 = lean_array_get_size(x_844);
x_848 = lean_nat_dec_le(x_846, x_847);
lean_dec(x_847);
lean_dec(x_846);
if (x_848 == 0)
{
lean_object* x_849; lean_object* x_850; 
x_849 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_844);
lean_ctor_set(x_824, 1, x_849);
lean_ctor_set(x_824, 0, x_841);
if (lean_is_scalar(x_814)) {
 x_850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_850 = x_814;
}
lean_ctor_set(x_850, 0, x_824);
lean_ctor_set(x_850, 1, x_813);
return x_850;
}
else
{
lean_object* x_851; 
lean_ctor_set(x_824, 1, x_844);
lean_ctor_set(x_824, 0, x_841);
if (lean_is_scalar(x_814)) {
 x_851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_851 = x_814;
}
lean_ctor_set(x_851, 0, x_824);
lean_ctor_set(x_851, 1, x_813);
return x_851;
}
}
else
{
lean_object* x_852; 
lean_dec(x_838);
lean_dec(x_823);
if (lean_is_scalar(x_814)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_814;
}
lean_ctor_set(x_852, 0, x_824);
lean_ctor_set(x_852, 1, x_813);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; uint64_t x_856; uint64_t x_857; uint64_t x_858; uint64_t x_859; uint64_t x_860; size_t x_861; size_t x_862; size_t x_863; size_t x_864; lean_object* x_865; uint8_t x_866; 
x_853 = lean_ctor_get(x_824, 0);
x_854 = lean_ctor_get(x_824, 1);
lean_inc(x_854);
lean_inc(x_853);
lean_dec(x_824);
x_855 = lean_array_get_size(x_854);
x_856 = l_Lean_Expr_hash(x_823);
x_857 = lean_uint64_shift_right(x_856, x_819);
x_858 = lean_uint64_xor(x_856, x_857);
x_859 = lean_uint64_shift_right(x_858, x_820);
x_860 = lean_uint64_xor(x_858, x_859);
x_861 = lean_uint64_to_usize(x_860);
x_862 = lean_usize_of_nat(x_855);
lean_dec(x_855);
x_863 = lean_usize_sub(x_862, x_821);
x_864 = lean_usize_land(x_861, x_863);
x_865 = lean_array_uget(x_854, x_864);
x_866 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_823, x_865);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; 
x_867 = lean_unsigned_to_nat(1u);
x_868 = lean_nat_add(x_853, x_867);
lean_dec(x_853);
x_869 = lean_box(0);
x_870 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_870, 0, x_823);
lean_ctor_set(x_870, 1, x_869);
lean_ctor_set(x_870, 2, x_865);
x_871 = lean_array_uset(x_854, x_864, x_870);
x_872 = lean_nat_mul(x_868, x_343);
x_873 = lean_nat_div(x_872, x_365);
lean_dec(x_872);
x_874 = lean_array_get_size(x_871);
x_875 = lean_nat_dec_le(x_873, x_874);
lean_dec(x_874);
lean_dec(x_873);
if (x_875 == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_871);
x_877 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_877, 0, x_868);
lean_ctor_set(x_877, 1, x_876);
if (lean_is_scalar(x_814)) {
 x_878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_878 = x_814;
}
lean_ctor_set(x_878, 0, x_877);
lean_ctor_set(x_878, 1, x_813);
return x_878;
}
else
{
lean_object* x_879; lean_object* x_880; 
x_879 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_879, 0, x_868);
lean_ctor_set(x_879, 1, x_871);
if (lean_is_scalar(x_814)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_814;
}
lean_ctor_set(x_880, 0, x_879);
lean_ctor_set(x_880, 1, x_813);
return x_880;
}
}
else
{
lean_object* x_881; lean_object* x_882; 
lean_dec(x_865);
lean_dec(x_823);
x_881 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_881, 0, x_853);
lean_ctor_set(x_881, 1, x_854);
if (lean_is_scalar(x_814)) {
 x_882 = lean_alloc_ctor(0, 2, 0);
} else {
 x_882 = x_814;
}
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_813);
return x_882;
}
}
}
block_910:
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; uint64_t x_889; uint64_t x_890; uint64_t x_891; uint64_t x_892; uint64_t x_893; size_t x_894; size_t x_895; size_t x_896; lean_object* x_897; lean_object* x_898; uint8_t x_899; 
x_885 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
lean_inc(x_346);
x_886 = l_Lean_mkApp3(x_885, x_346, x_884, x_818);
x_887 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
x_888 = l_Lean_mkApp3(x_887, x_344, x_346, x_886);
x_889 = l_Lean_Expr_hash(x_888);
x_890 = lean_uint64_shift_right(x_889, x_819);
x_891 = lean_uint64_xor(x_889, x_890);
x_892 = lean_uint64_shift_right(x_891, x_820);
x_893 = lean_uint64_xor(x_891, x_892);
x_894 = lean_uint64_to_usize(x_893);
x_895 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_896 = lean_usize_land(x_894, x_895);
x_897 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_898 = lean_array_uget(x_897, x_896);
x_899 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_888, x_898);
if (x_899 == 0)
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; uint8_t x_905; 
x_900 = lean_box(0);
x_901 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_901, 0, x_888);
lean_ctor_set(x_901, 1, x_900);
lean_ctor_set(x_901, 2, x_898);
x_902 = lean_array_uset(x_897, x_896, x_901);
x_903 = lean_array_get_size(x_902);
x_904 = lean_unsigned_to_nat(1u);
x_905 = lean_nat_dec_le(x_904, x_903);
lean_dec(x_903);
if (x_905 == 0)
{
lean_object* x_906; lean_object* x_907; 
x_906 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_902);
if (lean_is_scalar(x_386)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_386;
}
lean_ctor_set(x_907, 0, x_904);
lean_ctor_set(x_907, 1, x_906);
x_824 = x_907;
goto block_883;
}
else
{
lean_object* x_908; 
if (lean_is_scalar(x_386)) {
 x_908 = lean_alloc_ctor(0, 2, 0);
} else {
 x_908 = x_386;
}
lean_ctor_set(x_908, 0, x_904);
lean_ctor_set(x_908, 1, x_902);
x_824 = x_908;
goto block_883;
}
}
else
{
lean_object* x_909; 
lean_dec(x_898);
lean_dec(x_888);
lean_dec(x_386);
x_909 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_824 = x_909;
goto block_883;
}
}
}
else
{
uint8_t x_914; 
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_386);
lean_dec(x_380);
lean_dec(x_346);
lean_dec(x_344);
x_914 = !lean_is_exclusive(x_811);
if (x_914 == 0)
{
return x_811;
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_915 = lean_ctor_get(x_811, 0);
x_916 = lean_ctor_get(x_811, 1);
lean_inc(x_916);
lean_inc(x_915);
lean_dec(x_811);
x_917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_917, 0, x_915);
lean_ctor_set(x_917, 1, x_916);
return x_917;
}
}
}
else
{
lean_object* x_918; lean_object* x_919; 
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_380);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_918 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_386)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_386;
}
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_11);
return x_919;
}
}
}
}
}
}
else
{
uint8_t x_920; 
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_380);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_920 = !lean_is_exclusive(x_381);
if (x_920 == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_921 = lean_ctor_get(x_381, 1);
lean_dec(x_921);
x_922 = lean_ctor_get(x_381, 0);
lean_dec(x_922);
x_923 = l_Lean_Expr_getAppFnArgs(x_344);
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
if (lean_obj_tag(x_924) == 1)
{
lean_object* x_925; 
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
if (lean_obj_tag(x_925) == 1)
{
lean_object* x_926; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
if (lean_obj_tag(x_926) == 0)
{
uint8_t x_927; 
x_927 = !lean_is_exclusive(x_923);
if (x_927 == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; 
x_928 = lean_ctor_get(x_923, 1);
x_929 = lean_ctor_get(x_923, 0);
lean_dec(x_929);
x_930 = lean_ctor_get(x_924, 1);
lean_inc(x_930);
lean_dec(x_924);
x_931 = lean_ctor_get(x_925, 1);
lean_inc(x_931);
lean_dec(x_925);
x_932 = lean_string_dec_eq(x_931, x_120);
lean_dec(x_931);
if (x_932 == 0)
{
lean_object* x_933; 
lean_dec(x_930);
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_933 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_933);
return x_923;
}
else
{
uint8_t x_934; 
x_934 = lean_string_dec_eq(x_930, x_360);
lean_dec(x_930);
if (x_934 == 0)
{
lean_object* x_935; 
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_935 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_935);
return x_923;
}
else
{
lean_object* x_936; uint8_t x_937; 
x_936 = lean_array_get_size(x_928);
x_937 = lean_nat_dec_eq(x_936, x_365);
lean_dec(x_936);
if (x_937 == 0)
{
lean_object* x_938; 
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_938 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_938);
return x_923;
}
else
{
lean_object* x_939; 
x_939 = lean_array_fget(x_928, x_369);
if (lean_obj_tag(x_939) == 4)
{
lean_object* x_940; 
x_940 = lean_ctor_get(x_939, 0);
lean_inc(x_940);
if (lean_obj_tag(x_940) == 1)
{
lean_object* x_941; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; uint8_t x_944; 
x_942 = lean_ctor_get(x_939, 1);
lean_inc(x_942);
lean_dec(x_939);
x_943 = lean_ctor_get(x_940, 1);
lean_inc(x_943);
lean_dec(x_940);
x_944 = lean_string_dec_eq(x_943, x_375);
lean_dec(x_943);
if (x_944 == 0)
{
lean_object* x_945; 
lean_dec(x_942);
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_945 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_945);
return x_923;
}
else
{
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; uint64_t x_949; uint64_t x_950; uint64_t x_951; uint64_t x_952; uint64_t x_953; uint64_t x_954; uint64_t x_955; size_t x_956; size_t x_957; size_t x_958; lean_object* x_959; lean_object* x_960; uint8_t x_961; 
x_946 = lean_array_fget(x_928, x_379);
lean_dec(x_928);
x_947 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_948 = l_Lean_mkAppB(x_947, x_946, x_346);
x_949 = l_Lean_Expr_hash(x_948);
x_950 = 32;
x_951 = lean_uint64_shift_right(x_949, x_950);
x_952 = lean_uint64_xor(x_949, x_951);
x_953 = 16;
x_954 = lean_uint64_shift_right(x_952, x_953);
x_955 = lean_uint64_xor(x_952, x_954);
x_956 = lean_uint64_to_usize(x_955);
x_957 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_958 = lean_usize_land(x_956, x_957);
x_959 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_960 = lean_array_uget(x_959, x_958);
x_961 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_948, x_960);
if (x_961 == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; uint8_t x_967; 
x_962 = lean_box(0);
x_963 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_963, 0, x_948);
lean_ctor_set(x_963, 1, x_962);
lean_ctor_set(x_963, 2, x_960);
x_964 = lean_array_uset(x_959, x_958, x_963);
x_965 = lean_array_get_size(x_964);
x_966 = lean_unsigned_to_nat(1u);
x_967 = lean_nat_dec_le(x_966, x_965);
lean_dec(x_965);
if (x_967 == 0)
{
lean_object* x_968; 
x_968 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_964);
lean_ctor_set(x_923, 1, x_968);
lean_ctor_set(x_923, 0, x_966);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_923);
return x_381;
}
else
{
lean_ctor_set(x_923, 1, x_964);
lean_ctor_set(x_923, 0, x_966);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_923);
return x_381;
}
}
else
{
lean_object* x_969; 
lean_dec(x_960);
lean_dec(x_948);
lean_free_object(x_381);
x_969 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_969);
return x_923;
}
}
else
{
uint8_t x_970; 
lean_free_object(x_923);
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_970 = !lean_is_exclusive(x_942);
if (x_970 == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_942, 1);
lean_dec(x_971);
x_972 = lean_ctor_get(x_942, 0);
lean_dec(x_972);
x_973 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_942, 0);
lean_ctor_set(x_942, 1, x_11);
lean_ctor_set(x_942, 0, x_973);
return x_942;
}
else
{
lean_object* x_974; lean_object* x_975; 
lean_dec(x_942);
x_974 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_975 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_975, 0, x_974);
lean_ctor_set(x_975, 1, x_11);
return x_975;
}
}
}
}
else
{
lean_object* x_976; 
lean_dec(x_941);
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_976 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_976);
return x_923;
}
}
else
{
lean_object* x_977; 
lean_dec(x_940);
lean_dec(x_939);
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_977 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_977);
return x_923;
}
}
else
{
lean_object* x_978; 
lean_dec(x_939);
lean_dec(x_928);
lean_free_object(x_381);
lean_dec(x_346);
x_978 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_978);
return x_923;
}
}
}
}
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; uint8_t x_982; 
x_979 = lean_ctor_get(x_923, 1);
lean_inc(x_979);
lean_dec(x_923);
x_980 = lean_ctor_get(x_924, 1);
lean_inc(x_980);
lean_dec(x_924);
x_981 = lean_ctor_get(x_925, 1);
lean_inc(x_981);
lean_dec(x_925);
x_982 = lean_string_dec_eq(x_981, x_120);
lean_dec(x_981);
if (x_982 == 0)
{
lean_object* x_983; lean_object* x_984; 
lean_dec(x_980);
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
x_983 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_984 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set(x_984, 1, x_11);
return x_984;
}
else
{
uint8_t x_985; 
x_985 = lean_string_dec_eq(x_980, x_360);
lean_dec(x_980);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; 
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
x_986 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_987 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_11);
return x_987;
}
else
{
lean_object* x_988; uint8_t x_989; 
x_988 = lean_array_get_size(x_979);
x_989 = lean_nat_dec_eq(x_988, x_365);
lean_dec(x_988);
if (x_989 == 0)
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
x_990 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_990);
lean_ctor_set(x_991, 1, x_11);
return x_991;
}
else
{
lean_object* x_992; 
x_992 = lean_array_fget(x_979, x_369);
if (lean_obj_tag(x_992) == 4)
{
lean_object* x_993; 
x_993 = lean_ctor_get(x_992, 0);
lean_inc(x_993);
if (lean_obj_tag(x_993) == 1)
{
lean_object* x_994; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; uint8_t x_997; 
x_995 = lean_ctor_get(x_992, 1);
lean_inc(x_995);
lean_dec(x_992);
x_996 = lean_ctor_get(x_993, 1);
lean_inc(x_996);
lean_dec(x_993);
x_997 = lean_string_dec_eq(x_996, x_375);
lean_dec(x_996);
if (x_997 == 0)
{
lean_object* x_998; lean_object* x_999; 
lean_dec(x_995);
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
x_998 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_999, 0, x_998);
lean_ctor_set(x_999, 1, x_11);
return x_999;
}
else
{
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint64_t x_1003; uint64_t x_1004; uint64_t x_1005; uint64_t x_1006; uint64_t x_1007; uint64_t x_1008; uint64_t x_1009; size_t x_1010; size_t x_1011; size_t x_1012; lean_object* x_1013; lean_object* x_1014; uint8_t x_1015; 
x_1000 = lean_array_fget(x_979, x_379);
lean_dec(x_979);
x_1001 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1002 = l_Lean_mkAppB(x_1001, x_1000, x_346);
x_1003 = l_Lean_Expr_hash(x_1002);
x_1004 = 32;
x_1005 = lean_uint64_shift_right(x_1003, x_1004);
x_1006 = lean_uint64_xor(x_1003, x_1005);
x_1007 = 16;
x_1008 = lean_uint64_shift_right(x_1006, x_1007);
x_1009 = lean_uint64_xor(x_1006, x_1008);
x_1010 = lean_uint64_to_usize(x_1009);
x_1011 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1012 = lean_usize_land(x_1010, x_1011);
x_1013 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1014 = lean_array_uget(x_1013, x_1012);
x_1015 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1002, x_1014);
if (x_1015 == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; 
x_1016 = lean_box(0);
x_1017 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1017, 0, x_1002);
lean_ctor_set(x_1017, 1, x_1016);
lean_ctor_set(x_1017, 2, x_1014);
x_1018 = lean_array_uset(x_1013, x_1012, x_1017);
x_1019 = lean_array_get_size(x_1018);
x_1020 = lean_unsigned_to_nat(1u);
x_1021 = lean_nat_dec_le(x_1020, x_1019);
lean_dec(x_1019);
if (x_1021 == 0)
{
lean_object* x_1022; lean_object* x_1023; 
x_1022 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1018);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1020);
lean_ctor_set(x_1023, 1, x_1022);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1023);
return x_381;
}
else
{
lean_object* x_1024; 
x_1024 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1024, 0, x_1020);
lean_ctor_set(x_1024, 1, x_1018);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1024);
return x_381;
}
}
else
{
lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_1014);
lean_dec(x_1002);
lean_free_object(x_381);
x_1025 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1026 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1026, 0, x_1025);
lean_ctor_set(x_1026, 1, x_11);
return x_1026;
}
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_1027 = x_995;
} else {
 lean_dec_ref(x_995);
 x_1027 = lean_box(0);
}
x_1028 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1027)) {
 x_1029 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1029 = x_1027;
 lean_ctor_set_tag(x_1029, 0);
}
lean_ctor_set(x_1029, 0, x_1028);
lean_ctor_set(x_1029, 1, x_11);
return x_1029;
}
}
}
else
{
lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_994);
lean_dec(x_993);
lean_dec(x_992);
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
x_1030 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1031 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1031, 0, x_1030);
lean_ctor_set(x_1031, 1, x_11);
return x_1031;
}
}
else
{
lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_993);
lean_dec(x_992);
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
x_1032 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1033 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1033, 0, x_1032);
lean_ctor_set(x_1033, 1, x_11);
return x_1033;
}
}
else
{
lean_object* x_1034; lean_object* x_1035; 
lean_dec(x_992);
lean_dec(x_979);
lean_free_object(x_381);
lean_dec(x_346);
x_1034 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1035 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1035, 0, x_1034);
lean_ctor_set(x_1035, 1, x_11);
return x_1035;
}
}
}
}
}
}
else
{
uint8_t x_1036; 
lean_dec(x_926);
lean_dec(x_925);
lean_dec(x_924);
lean_free_object(x_381);
lean_dec(x_346);
x_1036 = !lean_is_exclusive(x_923);
if (x_1036 == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1037 = lean_ctor_get(x_923, 1);
lean_dec(x_1037);
x_1038 = lean_ctor_get(x_923, 0);
lean_dec(x_1038);
x_1039 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_1039);
return x_923;
}
else
{
lean_object* x_1040; lean_object* x_1041; 
lean_dec(x_923);
x_1040 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1041 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1041, 0, x_1040);
lean_ctor_set(x_1041, 1, x_11);
return x_1041;
}
}
}
else
{
uint8_t x_1042; 
lean_dec(x_925);
lean_dec(x_924);
lean_free_object(x_381);
lean_dec(x_346);
x_1042 = !lean_is_exclusive(x_923);
if (x_1042 == 0)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1043 = lean_ctor_get(x_923, 1);
lean_dec(x_1043);
x_1044 = lean_ctor_get(x_923, 0);
lean_dec(x_1044);
x_1045 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_1045);
return x_923;
}
else
{
lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_923);
x_1046 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1047 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_11);
return x_1047;
}
}
}
else
{
uint8_t x_1048; 
lean_dec(x_924);
lean_free_object(x_381);
lean_dec(x_346);
x_1048 = !lean_is_exclusive(x_923);
if (x_1048 == 0)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1049 = lean_ctor_get(x_923, 1);
lean_dec(x_1049);
x_1050 = lean_ctor_get(x_923, 0);
lean_dec(x_1050);
x_1051 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_923, 1, x_11);
lean_ctor_set(x_923, 0, x_1051);
return x_923;
}
else
{
lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_923);
x_1052 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1053 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_11);
return x_1053;
}
}
}
else
{
lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_381);
x_1054 = l_Lean_Expr_getAppFnArgs(x_344);
x_1055 = lean_ctor_get(x_1054, 0);
lean_inc(x_1055);
if (lean_obj_tag(x_1055) == 1)
{
lean_object* x_1056; 
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
if (lean_obj_tag(x_1056) == 1)
{
lean_object* x_1057; 
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; uint8_t x_1062; 
x_1058 = lean_ctor_get(x_1054, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 lean_ctor_release(x_1054, 1);
 x_1059 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1059 = lean_box(0);
}
x_1060 = lean_ctor_get(x_1055, 1);
lean_inc(x_1060);
lean_dec(x_1055);
x_1061 = lean_ctor_get(x_1056, 1);
lean_inc(x_1061);
lean_dec(x_1056);
x_1062 = lean_string_dec_eq(x_1061, x_120);
lean_dec(x_1061);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; 
lean_dec(x_1060);
lean_dec(x_1058);
lean_dec(x_346);
x_1063 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1064 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1064 = x_1059;
}
lean_ctor_set(x_1064, 0, x_1063);
lean_ctor_set(x_1064, 1, x_11);
return x_1064;
}
else
{
uint8_t x_1065; 
x_1065 = lean_string_dec_eq(x_1060, x_360);
lean_dec(x_1060);
if (x_1065 == 0)
{
lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_1058);
lean_dec(x_346);
x_1066 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1067 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1067 = x_1059;
}
lean_ctor_set(x_1067, 0, x_1066);
lean_ctor_set(x_1067, 1, x_11);
return x_1067;
}
else
{
lean_object* x_1068; uint8_t x_1069; 
x_1068 = lean_array_get_size(x_1058);
x_1069 = lean_nat_dec_eq(x_1068, x_365);
lean_dec(x_1068);
if (x_1069 == 0)
{
lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_1058);
lean_dec(x_346);
x_1070 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1071 = x_1059;
}
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_11);
return x_1071;
}
else
{
lean_object* x_1072; 
x_1072 = lean_array_fget(x_1058, x_369);
if (lean_obj_tag(x_1072) == 4)
{
lean_object* x_1073; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
if (lean_obj_tag(x_1073) == 1)
{
lean_object* x_1074; 
x_1074 = lean_ctor_get(x_1073, 0);
lean_inc(x_1074);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; uint8_t x_1077; 
x_1075 = lean_ctor_get(x_1072, 1);
lean_inc(x_1075);
lean_dec(x_1072);
x_1076 = lean_ctor_get(x_1073, 1);
lean_inc(x_1076);
lean_dec(x_1073);
x_1077 = lean_string_dec_eq(x_1076, x_375);
lean_dec(x_1076);
if (x_1077 == 0)
{
lean_object* x_1078; lean_object* x_1079; 
lean_dec(x_1075);
lean_dec(x_1058);
lean_dec(x_346);
x_1078 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1079 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1079 = x_1059;
}
lean_ctor_set(x_1079, 0, x_1078);
lean_ctor_set(x_1079, 1, x_11);
return x_1079;
}
else
{
if (lean_obj_tag(x_1075) == 0)
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; uint64_t x_1083; uint64_t x_1084; uint64_t x_1085; uint64_t x_1086; uint64_t x_1087; uint64_t x_1088; uint64_t x_1089; size_t x_1090; size_t x_1091; size_t x_1092; lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; 
x_1080 = lean_array_fget(x_1058, x_379);
lean_dec(x_1058);
x_1081 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1082 = l_Lean_mkAppB(x_1081, x_1080, x_346);
x_1083 = l_Lean_Expr_hash(x_1082);
x_1084 = 32;
x_1085 = lean_uint64_shift_right(x_1083, x_1084);
x_1086 = lean_uint64_xor(x_1083, x_1085);
x_1087 = 16;
x_1088 = lean_uint64_shift_right(x_1086, x_1087);
x_1089 = lean_uint64_xor(x_1086, x_1088);
x_1090 = lean_uint64_to_usize(x_1089);
x_1091 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1092 = lean_usize_land(x_1090, x_1091);
x_1093 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1094 = lean_array_uget(x_1093, x_1092);
x_1095 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1082, x_1094);
if (x_1095 == 0)
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; uint8_t x_1101; 
x_1096 = lean_box(0);
x_1097 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1097, 0, x_1082);
lean_ctor_set(x_1097, 1, x_1096);
lean_ctor_set(x_1097, 2, x_1094);
x_1098 = lean_array_uset(x_1093, x_1092, x_1097);
x_1099 = lean_array_get_size(x_1098);
x_1100 = lean_unsigned_to_nat(1u);
x_1101 = lean_nat_dec_le(x_1100, x_1099);
lean_dec(x_1099);
if (x_1101 == 0)
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1102 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1098);
if (lean_is_scalar(x_1059)) {
 x_1103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1103 = x_1059;
}
lean_ctor_set(x_1103, 0, x_1100);
lean_ctor_set(x_1103, 1, x_1102);
x_1104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1104, 0, x_1103);
lean_ctor_set(x_1104, 1, x_11);
return x_1104;
}
else
{
lean_object* x_1105; lean_object* x_1106; 
if (lean_is_scalar(x_1059)) {
 x_1105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1105 = x_1059;
}
lean_ctor_set(x_1105, 0, x_1100);
lean_ctor_set(x_1105, 1, x_1098);
x_1106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1106, 0, x_1105);
lean_ctor_set(x_1106, 1, x_11);
return x_1106;
}
}
else
{
lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_1094);
lean_dec(x_1082);
x_1107 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1108 = x_1059;
}
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_11);
return x_1108;
}
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_1059);
lean_dec(x_1058);
lean_dec(x_346);
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 lean_ctor_release(x_1075, 1);
 x_1109 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1109 = lean_box(0);
}
x_1110 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1109)) {
 x_1111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1111 = x_1109;
 lean_ctor_set_tag(x_1111, 0);
}
lean_ctor_set(x_1111, 0, x_1110);
lean_ctor_set(x_1111, 1, x_11);
return x_1111;
}
}
}
else
{
lean_object* x_1112; lean_object* x_1113; 
lean_dec(x_1074);
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_1058);
lean_dec(x_346);
x_1112 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1113 = x_1059;
}
lean_ctor_set(x_1113, 0, x_1112);
lean_ctor_set(x_1113, 1, x_11);
return x_1113;
}
}
else
{
lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_1058);
lean_dec(x_346);
x_1114 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1115 = x_1059;
}
lean_ctor_set(x_1115, 0, x_1114);
lean_ctor_set(x_1115, 1, x_11);
return x_1115;
}
}
else
{
lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_1072);
lean_dec(x_1058);
lean_dec(x_346);
x_1116 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1059)) {
 x_1117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1117 = x_1059;
}
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_11);
return x_1117;
}
}
}
}
}
else
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
lean_dec(x_1057);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_346);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 lean_ctor_release(x_1054, 1);
 x_1118 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1118 = lean_box(0);
}
x_1119 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1118)) {
 x_1120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1120 = x_1118;
}
lean_ctor_set(x_1120, 0, x_1119);
lean_ctor_set(x_1120, 1, x_11);
return x_1120;
}
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_346);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 lean_ctor_release(x_1054, 1);
 x_1121 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1121 = lean_box(0);
}
x_1122 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1121)) {
 x_1123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1123 = x_1121;
}
lean_ctor_set(x_1123, 0, x_1122);
lean_ctor_set(x_1123, 1, x_11);
return x_1123;
}
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_1055);
lean_dec(x_346);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 lean_ctor_release(x_1054, 1);
 x_1124 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1124 = lean_box(0);
}
x_1125 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1124)) {
 x_1126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1126 = x_1124;
}
lean_ctor_set(x_1126, 0, x_1125);
lean_ctor_set(x_1126, 1, x_11);
return x_1126;
}
}
}
}
else
{
uint8_t x_1127; 
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_380);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1127 = !lean_is_exclusive(x_381);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1128 = lean_ctor_get(x_381, 1);
lean_dec(x_1128);
x_1129 = lean_ctor_get(x_381, 0);
lean_dec(x_1129);
x_1130 = l_Lean_Expr_getAppFnArgs(x_344);
x_1131 = lean_ctor_get(x_1130, 0);
lean_inc(x_1131);
if (lean_obj_tag(x_1131) == 1)
{
lean_object* x_1132; 
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
if (lean_obj_tag(x_1132) == 1)
{
lean_object* x_1133; 
x_1133 = lean_ctor_get(x_1132, 0);
lean_inc(x_1133);
if (lean_obj_tag(x_1133) == 0)
{
uint8_t x_1134; 
x_1134 = !lean_is_exclusive(x_1130);
if (x_1134 == 0)
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; 
x_1135 = lean_ctor_get(x_1130, 1);
x_1136 = lean_ctor_get(x_1130, 0);
lean_dec(x_1136);
x_1137 = lean_ctor_get(x_1131, 1);
lean_inc(x_1137);
lean_dec(x_1131);
x_1138 = lean_ctor_get(x_1132, 1);
lean_inc(x_1138);
lean_dec(x_1132);
x_1139 = lean_string_dec_eq(x_1138, x_120);
lean_dec(x_1138);
if (x_1139 == 0)
{
lean_object* x_1140; 
lean_dec(x_1137);
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1140 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1140);
return x_1130;
}
else
{
uint8_t x_1141; 
x_1141 = lean_string_dec_eq(x_1137, x_360);
lean_dec(x_1137);
if (x_1141 == 0)
{
lean_object* x_1142; 
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1142 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1142);
return x_1130;
}
else
{
lean_object* x_1143; uint8_t x_1144; 
x_1143 = lean_array_get_size(x_1135);
x_1144 = lean_nat_dec_eq(x_1143, x_365);
lean_dec(x_1143);
if (x_1144 == 0)
{
lean_object* x_1145; 
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1145 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1145);
return x_1130;
}
else
{
lean_object* x_1146; 
x_1146 = lean_array_fget(x_1135, x_369);
if (lean_obj_tag(x_1146) == 4)
{
lean_object* x_1147; 
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
if (lean_obj_tag(x_1147) == 1)
{
lean_object* x_1148; 
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; lean_object* x_1150; uint8_t x_1151; 
x_1149 = lean_ctor_get(x_1146, 1);
lean_inc(x_1149);
lean_dec(x_1146);
x_1150 = lean_ctor_get(x_1147, 1);
lean_inc(x_1150);
lean_dec(x_1147);
x_1151 = lean_string_dec_eq(x_1150, x_375);
lean_dec(x_1150);
if (x_1151 == 0)
{
lean_object* x_1152; 
lean_dec(x_1149);
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1152 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1152);
return x_1130;
}
else
{
if (lean_obj_tag(x_1149) == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint64_t x_1156; uint64_t x_1157; uint64_t x_1158; uint64_t x_1159; uint64_t x_1160; uint64_t x_1161; uint64_t x_1162; size_t x_1163; size_t x_1164; size_t x_1165; lean_object* x_1166; lean_object* x_1167; uint8_t x_1168; 
x_1153 = lean_array_fget(x_1135, x_379);
lean_dec(x_1135);
x_1154 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1155 = l_Lean_mkAppB(x_1154, x_1153, x_346);
x_1156 = l_Lean_Expr_hash(x_1155);
x_1157 = 32;
x_1158 = lean_uint64_shift_right(x_1156, x_1157);
x_1159 = lean_uint64_xor(x_1156, x_1158);
x_1160 = 16;
x_1161 = lean_uint64_shift_right(x_1159, x_1160);
x_1162 = lean_uint64_xor(x_1159, x_1161);
x_1163 = lean_uint64_to_usize(x_1162);
x_1164 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1165 = lean_usize_land(x_1163, x_1164);
x_1166 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1167 = lean_array_uget(x_1166, x_1165);
x_1168 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1155, x_1167);
if (x_1168 == 0)
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; uint8_t x_1174; 
x_1169 = lean_box(0);
x_1170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1170, 0, x_1155);
lean_ctor_set(x_1170, 1, x_1169);
lean_ctor_set(x_1170, 2, x_1167);
x_1171 = lean_array_uset(x_1166, x_1165, x_1170);
x_1172 = lean_array_get_size(x_1171);
x_1173 = lean_unsigned_to_nat(1u);
x_1174 = lean_nat_dec_le(x_1173, x_1172);
lean_dec(x_1172);
if (x_1174 == 0)
{
lean_object* x_1175; 
x_1175 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1171);
lean_ctor_set(x_1130, 1, x_1175);
lean_ctor_set(x_1130, 0, x_1173);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1130);
return x_381;
}
else
{
lean_ctor_set(x_1130, 1, x_1171);
lean_ctor_set(x_1130, 0, x_1173);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1130);
return x_381;
}
}
else
{
lean_object* x_1176; 
lean_dec(x_1167);
lean_dec(x_1155);
lean_free_object(x_381);
x_1176 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1176);
return x_1130;
}
}
else
{
uint8_t x_1177; 
lean_free_object(x_1130);
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1177 = !lean_is_exclusive(x_1149);
if (x_1177 == 0)
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
x_1178 = lean_ctor_get(x_1149, 1);
lean_dec(x_1178);
x_1179 = lean_ctor_get(x_1149, 0);
lean_dec(x_1179);
x_1180 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_1149, 0);
lean_ctor_set(x_1149, 1, x_11);
lean_ctor_set(x_1149, 0, x_1180);
return x_1149;
}
else
{
lean_object* x_1181; lean_object* x_1182; 
lean_dec(x_1149);
x_1181 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1182, 0, x_1181);
lean_ctor_set(x_1182, 1, x_11);
return x_1182;
}
}
}
}
else
{
lean_object* x_1183; 
lean_dec(x_1148);
lean_dec(x_1147);
lean_dec(x_1146);
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1183 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1183);
return x_1130;
}
}
else
{
lean_object* x_1184; 
lean_dec(x_1147);
lean_dec(x_1146);
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1184 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1184);
return x_1130;
}
}
else
{
lean_object* x_1185; 
lean_dec(x_1146);
lean_dec(x_1135);
lean_free_object(x_381);
lean_dec(x_346);
x_1185 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1185);
return x_1130;
}
}
}
}
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; uint8_t x_1189; 
x_1186 = lean_ctor_get(x_1130, 1);
lean_inc(x_1186);
lean_dec(x_1130);
x_1187 = lean_ctor_get(x_1131, 1);
lean_inc(x_1187);
lean_dec(x_1131);
x_1188 = lean_ctor_get(x_1132, 1);
lean_inc(x_1188);
lean_dec(x_1132);
x_1189 = lean_string_dec_eq(x_1188, x_120);
lean_dec(x_1188);
if (x_1189 == 0)
{
lean_object* x_1190; lean_object* x_1191; 
lean_dec(x_1187);
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
x_1190 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1191, 0, x_1190);
lean_ctor_set(x_1191, 1, x_11);
return x_1191;
}
else
{
uint8_t x_1192; 
x_1192 = lean_string_dec_eq(x_1187, x_360);
lean_dec(x_1187);
if (x_1192 == 0)
{
lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
x_1193 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1194, 0, x_1193);
lean_ctor_set(x_1194, 1, x_11);
return x_1194;
}
else
{
lean_object* x_1195; uint8_t x_1196; 
x_1195 = lean_array_get_size(x_1186);
x_1196 = lean_nat_dec_eq(x_1195, x_365);
lean_dec(x_1195);
if (x_1196 == 0)
{
lean_object* x_1197; lean_object* x_1198; 
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
x_1197 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1198, 0, x_1197);
lean_ctor_set(x_1198, 1, x_11);
return x_1198;
}
else
{
lean_object* x_1199; 
x_1199 = lean_array_fget(x_1186, x_369);
if (lean_obj_tag(x_1199) == 4)
{
lean_object* x_1200; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
if (lean_obj_tag(x_1200) == 1)
{
lean_object* x_1201; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
if (lean_obj_tag(x_1201) == 0)
{
lean_object* x_1202; lean_object* x_1203; uint8_t x_1204; 
x_1202 = lean_ctor_get(x_1199, 1);
lean_inc(x_1202);
lean_dec(x_1199);
x_1203 = lean_ctor_get(x_1200, 1);
lean_inc(x_1203);
lean_dec(x_1200);
x_1204 = lean_string_dec_eq(x_1203, x_375);
lean_dec(x_1203);
if (x_1204 == 0)
{
lean_object* x_1205; lean_object* x_1206; 
lean_dec(x_1202);
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
x_1205 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1206, 0, x_1205);
lean_ctor_set(x_1206, 1, x_11);
return x_1206;
}
else
{
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; uint64_t x_1210; uint64_t x_1211; uint64_t x_1212; uint64_t x_1213; uint64_t x_1214; uint64_t x_1215; uint64_t x_1216; size_t x_1217; size_t x_1218; size_t x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; 
x_1207 = lean_array_fget(x_1186, x_379);
lean_dec(x_1186);
x_1208 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1209 = l_Lean_mkAppB(x_1208, x_1207, x_346);
x_1210 = l_Lean_Expr_hash(x_1209);
x_1211 = 32;
x_1212 = lean_uint64_shift_right(x_1210, x_1211);
x_1213 = lean_uint64_xor(x_1210, x_1212);
x_1214 = 16;
x_1215 = lean_uint64_shift_right(x_1213, x_1214);
x_1216 = lean_uint64_xor(x_1213, x_1215);
x_1217 = lean_uint64_to_usize(x_1216);
x_1218 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1219 = lean_usize_land(x_1217, x_1218);
x_1220 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1221 = lean_array_uget(x_1220, x_1219);
x_1222 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1209, x_1221);
if (x_1222 == 0)
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; uint8_t x_1228; 
x_1223 = lean_box(0);
x_1224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1224, 0, x_1209);
lean_ctor_set(x_1224, 1, x_1223);
lean_ctor_set(x_1224, 2, x_1221);
x_1225 = lean_array_uset(x_1220, x_1219, x_1224);
x_1226 = lean_array_get_size(x_1225);
x_1227 = lean_unsigned_to_nat(1u);
x_1228 = lean_nat_dec_le(x_1227, x_1226);
lean_dec(x_1226);
if (x_1228 == 0)
{
lean_object* x_1229; lean_object* x_1230; 
x_1229 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1225);
x_1230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1230, 0, x_1227);
lean_ctor_set(x_1230, 1, x_1229);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1230);
return x_381;
}
else
{
lean_object* x_1231; 
x_1231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1231, 0, x_1227);
lean_ctor_set(x_1231, 1, x_1225);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1231);
return x_381;
}
}
else
{
lean_object* x_1232; lean_object* x_1233; 
lean_dec(x_1221);
lean_dec(x_1209);
lean_free_object(x_381);
x_1232 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_1232);
lean_ctor_set(x_1233, 1, x_11);
return x_1233;
}
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
if (lean_is_exclusive(x_1202)) {
 lean_ctor_release(x_1202, 0);
 lean_ctor_release(x_1202, 1);
 x_1234 = x_1202;
} else {
 lean_dec_ref(x_1202);
 x_1234 = lean_box(0);
}
x_1235 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1234)) {
 x_1236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1236 = x_1234;
 lean_ctor_set_tag(x_1236, 0);
}
lean_ctor_set(x_1236, 0, x_1235);
lean_ctor_set(x_1236, 1, x_11);
return x_1236;
}
}
}
else
{
lean_object* x_1237; lean_object* x_1238; 
lean_dec(x_1201);
lean_dec(x_1200);
lean_dec(x_1199);
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
x_1237 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1238, 0, x_1237);
lean_ctor_set(x_1238, 1, x_11);
return x_1238;
}
}
else
{
lean_object* x_1239; lean_object* x_1240; 
lean_dec(x_1200);
lean_dec(x_1199);
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
x_1239 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1240, 0, x_1239);
lean_ctor_set(x_1240, 1, x_11);
return x_1240;
}
}
else
{
lean_object* x_1241; lean_object* x_1242; 
lean_dec(x_1199);
lean_dec(x_1186);
lean_free_object(x_381);
lean_dec(x_346);
x_1241 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1242, 0, x_1241);
lean_ctor_set(x_1242, 1, x_11);
return x_1242;
}
}
}
}
}
}
else
{
uint8_t x_1243; 
lean_dec(x_1133);
lean_dec(x_1132);
lean_dec(x_1131);
lean_free_object(x_381);
lean_dec(x_346);
x_1243 = !lean_is_exclusive(x_1130);
if (x_1243 == 0)
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1244 = lean_ctor_get(x_1130, 1);
lean_dec(x_1244);
x_1245 = lean_ctor_get(x_1130, 0);
lean_dec(x_1245);
x_1246 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1246);
return x_1130;
}
else
{
lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_1130);
x_1247 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1248, 0, x_1247);
lean_ctor_set(x_1248, 1, x_11);
return x_1248;
}
}
}
else
{
uint8_t x_1249; 
lean_dec(x_1132);
lean_dec(x_1131);
lean_free_object(x_381);
lean_dec(x_346);
x_1249 = !lean_is_exclusive(x_1130);
if (x_1249 == 0)
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
x_1250 = lean_ctor_get(x_1130, 1);
lean_dec(x_1250);
x_1251 = lean_ctor_get(x_1130, 0);
lean_dec(x_1251);
x_1252 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1252);
return x_1130;
}
else
{
lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1130);
x_1253 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1254, 0, x_1253);
lean_ctor_set(x_1254, 1, x_11);
return x_1254;
}
}
}
else
{
uint8_t x_1255; 
lean_dec(x_1131);
lean_free_object(x_381);
lean_dec(x_346);
x_1255 = !lean_is_exclusive(x_1130);
if (x_1255 == 0)
{
lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
x_1256 = lean_ctor_get(x_1130, 1);
lean_dec(x_1256);
x_1257 = lean_ctor_get(x_1130, 0);
lean_dec(x_1257);
x_1258 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1130, 1, x_11);
lean_ctor_set(x_1130, 0, x_1258);
return x_1130;
}
else
{
lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_1130);
x_1259 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1260, 0, x_1259);
lean_ctor_set(x_1260, 1, x_11);
return x_1260;
}
}
}
else
{
lean_object* x_1261; lean_object* x_1262; 
lean_dec(x_381);
x_1261 = l_Lean_Expr_getAppFnArgs(x_344);
x_1262 = lean_ctor_get(x_1261, 0);
lean_inc(x_1262);
if (lean_obj_tag(x_1262) == 1)
{
lean_object* x_1263; 
x_1263 = lean_ctor_get(x_1262, 0);
lean_inc(x_1263);
if (lean_obj_tag(x_1263) == 1)
{
lean_object* x_1264; 
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
if (lean_obj_tag(x_1264) == 0)
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; 
x_1265 = lean_ctor_get(x_1261, 1);
lean_inc(x_1265);
if (lean_is_exclusive(x_1261)) {
 lean_ctor_release(x_1261, 0);
 lean_ctor_release(x_1261, 1);
 x_1266 = x_1261;
} else {
 lean_dec_ref(x_1261);
 x_1266 = lean_box(0);
}
x_1267 = lean_ctor_get(x_1262, 1);
lean_inc(x_1267);
lean_dec(x_1262);
x_1268 = lean_ctor_get(x_1263, 1);
lean_inc(x_1268);
lean_dec(x_1263);
x_1269 = lean_string_dec_eq(x_1268, x_120);
lean_dec(x_1268);
if (x_1269 == 0)
{
lean_object* x_1270; lean_object* x_1271; 
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_346);
x_1270 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1271 = x_1266;
}
lean_ctor_set(x_1271, 0, x_1270);
lean_ctor_set(x_1271, 1, x_11);
return x_1271;
}
else
{
uint8_t x_1272; 
x_1272 = lean_string_dec_eq(x_1267, x_360);
lean_dec(x_1267);
if (x_1272 == 0)
{
lean_object* x_1273; lean_object* x_1274; 
lean_dec(x_1265);
lean_dec(x_346);
x_1273 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1274 = x_1266;
}
lean_ctor_set(x_1274, 0, x_1273);
lean_ctor_set(x_1274, 1, x_11);
return x_1274;
}
else
{
lean_object* x_1275; uint8_t x_1276; 
x_1275 = lean_array_get_size(x_1265);
x_1276 = lean_nat_dec_eq(x_1275, x_365);
lean_dec(x_1275);
if (x_1276 == 0)
{
lean_object* x_1277; lean_object* x_1278; 
lean_dec(x_1265);
lean_dec(x_346);
x_1277 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1278 = x_1266;
}
lean_ctor_set(x_1278, 0, x_1277);
lean_ctor_set(x_1278, 1, x_11);
return x_1278;
}
else
{
lean_object* x_1279; 
x_1279 = lean_array_fget(x_1265, x_369);
if (lean_obj_tag(x_1279) == 4)
{
lean_object* x_1280; 
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
if (lean_obj_tag(x_1280) == 1)
{
lean_object* x_1281; 
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
if (lean_obj_tag(x_1281) == 0)
{
lean_object* x_1282; lean_object* x_1283; uint8_t x_1284; 
x_1282 = lean_ctor_get(x_1279, 1);
lean_inc(x_1282);
lean_dec(x_1279);
x_1283 = lean_ctor_get(x_1280, 1);
lean_inc(x_1283);
lean_dec(x_1280);
x_1284 = lean_string_dec_eq(x_1283, x_375);
lean_dec(x_1283);
if (x_1284 == 0)
{
lean_object* x_1285; lean_object* x_1286; 
lean_dec(x_1282);
lean_dec(x_1265);
lean_dec(x_346);
x_1285 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1286 = x_1266;
}
lean_ctor_set(x_1286, 0, x_1285);
lean_ctor_set(x_1286, 1, x_11);
return x_1286;
}
else
{
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; uint64_t x_1290; uint64_t x_1291; uint64_t x_1292; uint64_t x_1293; uint64_t x_1294; uint64_t x_1295; uint64_t x_1296; size_t x_1297; size_t x_1298; size_t x_1299; lean_object* x_1300; lean_object* x_1301; uint8_t x_1302; 
x_1287 = lean_array_fget(x_1265, x_379);
lean_dec(x_1265);
x_1288 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1289 = l_Lean_mkAppB(x_1288, x_1287, x_346);
x_1290 = l_Lean_Expr_hash(x_1289);
x_1291 = 32;
x_1292 = lean_uint64_shift_right(x_1290, x_1291);
x_1293 = lean_uint64_xor(x_1290, x_1292);
x_1294 = 16;
x_1295 = lean_uint64_shift_right(x_1293, x_1294);
x_1296 = lean_uint64_xor(x_1293, x_1295);
x_1297 = lean_uint64_to_usize(x_1296);
x_1298 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1299 = lean_usize_land(x_1297, x_1298);
x_1300 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1301 = lean_array_uget(x_1300, x_1299);
x_1302 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1289, x_1301);
if (x_1302 == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; 
x_1303 = lean_box(0);
x_1304 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1304, 0, x_1289);
lean_ctor_set(x_1304, 1, x_1303);
lean_ctor_set(x_1304, 2, x_1301);
x_1305 = lean_array_uset(x_1300, x_1299, x_1304);
x_1306 = lean_array_get_size(x_1305);
x_1307 = lean_unsigned_to_nat(1u);
x_1308 = lean_nat_dec_le(x_1307, x_1306);
lean_dec(x_1306);
if (x_1308 == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
x_1309 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1305);
if (lean_is_scalar(x_1266)) {
 x_1310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1310 = x_1266;
}
lean_ctor_set(x_1310, 0, x_1307);
lean_ctor_set(x_1310, 1, x_1309);
x_1311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1311, 0, x_1310);
lean_ctor_set(x_1311, 1, x_11);
return x_1311;
}
else
{
lean_object* x_1312; lean_object* x_1313; 
if (lean_is_scalar(x_1266)) {
 x_1312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1312 = x_1266;
}
lean_ctor_set(x_1312, 0, x_1307);
lean_ctor_set(x_1312, 1, x_1305);
x_1313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1313, 0, x_1312);
lean_ctor_set(x_1313, 1, x_11);
return x_1313;
}
}
else
{
lean_object* x_1314; lean_object* x_1315; 
lean_dec(x_1301);
lean_dec(x_1289);
x_1314 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1315 = x_1266;
}
lean_ctor_set(x_1315, 0, x_1314);
lean_ctor_set(x_1315, 1, x_11);
return x_1315;
}
}
else
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_1266);
lean_dec(x_1265);
lean_dec(x_346);
if (lean_is_exclusive(x_1282)) {
 lean_ctor_release(x_1282, 0);
 lean_ctor_release(x_1282, 1);
 x_1316 = x_1282;
} else {
 lean_dec_ref(x_1282);
 x_1316 = lean_box(0);
}
x_1317 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1316)) {
 x_1318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1318 = x_1316;
 lean_ctor_set_tag(x_1318, 0);
}
lean_ctor_set(x_1318, 0, x_1317);
lean_ctor_set(x_1318, 1, x_11);
return x_1318;
}
}
}
else
{
lean_object* x_1319; lean_object* x_1320; 
lean_dec(x_1281);
lean_dec(x_1280);
lean_dec(x_1279);
lean_dec(x_1265);
lean_dec(x_346);
x_1319 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1320 = x_1266;
}
lean_ctor_set(x_1320, 0, x_1319);
lean_ctor_set(x_1320, 1, x_11);
return x_1320;
}
}
else
{
lean_object* x_1321; lean_object* x_1322; 
lean_dec(x_1280);
lean_dec(x_1279);
lean_dec(x_1265);
lean_dec(x_346);
x_1321 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1322 = x_1266;
}
lean_ctor_set(x_1322, 0, x_1321);
lean_ctor_set(x_1322, 1, x_11);
return x_1322;
}
}
else
{
lean_object* x_1323; lean_object* x_1324; 
lean_dec(x_1279);
lean_dec(x_1265);
lean_dec(x_346);
x_1323 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1266)) {
 x_1324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1324 = x_1266;
}
lean_ctor_set(x_1324, 0, x_1323);
lean_ctor_set(x_1324, 1, x_11);
return x_1324;
}
}
}
}
}
else
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; 
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_346);
if (lean_is_exclusive(x_1261)) {
 lean_ctor_release(x_1261, 0);
 lean_ctor_release(x_1261, 1);
 x_1325 = x_1261;
} else {
 lean_dec_ref(x_1261);
 x_1325 = lean_box(0);
}
x_1326 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1325)) {
 x_1327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1327 = x_1325;
}
lean_ctor_set(x_1327, 0, x_1326);
lean_ctor_set(x_1327, 1, x_11);
return x_1327;
}
}
else
{
lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_346);
if (lean_is_exclusive(x_1261)) {
 lean_ctor_release(x_1261, 0);
 lean_ctor_release(x_1261, 1);
 x_1328 = x_1261;
} else {
 lean_dec_ref(x_1261);
 x_1328 = lean_box(0);
}
x_1329 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1328)) {
 x_1330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1330 = x_1328;
}
lean_ctor_set(x_1330, 0, x_1329);
lean_ctor_set(x_1330, 1, x_11);
return x_1330;
}
}
else
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; 
lean_dec(x_1262);
lean_dec(x_346);
if (lean_is_exclusive(x_1261)) {
 lean_ctor_release(x_1261, 0);
 lean_ctor_release(x_1261, 1);
 x_1331 = x_1261;
} else {
 lean_dec_ref(x_1261);
 x_1331 = lean_box(0);
}
x_1332 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1331)) {
 x_1333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1333 = x_1331;
}
lean_ctor_set(x_1333, 0, x_1332);
lean_ctor_set(x_1333, 1, x_11);
return x_1333;
}
}
}
}
else
{
uint8_t x_1334; 
lean_dec(x_382);
lean_dec(x_380);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1334 = !lean_is_exclusive(x_381);
if (x_1334 == 0)
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
x_1335 = lean_ctor_get(x_381, 1);
lean_dec(x_1335);
x_1336 = lean_ctor_get(x_381, 0);
lean_dec(x_1336);
x_1337 = l_Lean_Expr_getAppFnArgs(x_344);
x_1338 = lean_ctor_get(x_1337, 0);
lean_inc(x_1338);
if (lean_obj_tag(x_1338) == 1)
{
lean_object* x_1339; 
x_1339 = lean_ctor_get(x_1338, 0);
lean_inc(x_1339);
if (lean_obj_tag(x_1339) == 1)
{
lean_object* x_1340; 
x_1340 = lean_ctor_get(x_1339, 0);
lean_inc(x_1340);
if (lean_obj_tag(x_1340) == 0)
{
uint8_t x_1341; 
x_1341 = !lean_is_exclusive(x_1337);
if (x_1341 == 0)
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; uint8_t x_1346; 
x_1342 = lean_ctor_get(x_1337, 1);
x_1343 = lean_ctor_get(x_1337, 0);
lean_dec(x_1343);
x_1344 = lean_ctor_get(x_1338, 1);
lean_inc(x_1344);
lean_dec(x_1338);
x_1345 = lean_ctor_get(x_1339, 1);
lean_inc(x_1345);
lean_dec(x_1339);
x_1346 = lean_string_dec_eq(x_1345, x_120);
lean_dec(x_1345);
if (x_1346 == 0)
{
lean_object* x_1347; 
lean_dec(x_1344);
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1347 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1347);
return x_1337;
}
else
{
uint8_t x_1348; 
x_1348 = lean_string_dec_eq(x_1344, x_360);
lean_dec(x_1344);
if (x_1348 == 0)
{
lean_object* x_1349; 
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1349 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1349);
return x_1337;
}
else
{
lean_object* x_1350; uint8_t x_1351; 
x_1350 = lean_array_get_size(x_1342);
x_1351 = lean_nat_dec_eq(x_1350, x_365);
lean_dec(x_1350);
if (x_1351 == 0)
{
lean_object* x_1352; 
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1352 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1352);
return x_1337;
}
else
{
lean_object* x_1353; 
x_1353 = lean_array_fget(x_1342, x_369);
if (lean_obj_tag(x_1353) == 4)
{
lean_object* x_1354; 
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc(x_1354);
if (lean_obj_tag(x_1354) == 1)
{
lean_object* x_1355; 
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
if (lean_obj_tag(x_1355) == 0)
{
lean_object* x_1356; lean_object* x_1357; uint8_t x_1358; 
x_1356 = lean_ctor_get(x_1353, 1);
lean_inc(x_1356);
lean_dec(x_1353);
x_1357 = lean_ctor_get(x_1354, 1);
lean_inc(x_1357);
lean_dec(x_1354);
x_1358 = lean_string_dec_eq(x_1357, x_375);
lean_dec(x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; 
lean_dec(x_1356);
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1359 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1359);
return x_1337;
}
else
{
if (lean_obj_tag(x_1356) == 0)
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; uint64_t x_1363; uint64_t x_1364; uint64_t x_1365; uint64_t x_1366; uint64_t x_1367; uint64_t x_1368; uint64_t x_1369; size_t x_1370; size_t x_1371; size_t x_1372; lean_object* x_1373; lean_object* x_1374; uint8_t x_1375; 
x_1360 = lean_array_fget(x_1342, x_379);
lean_dec(x_1342);
x_1361 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1362 = l_Lean_mkAppB(x_1361, x_1360, x_346);
x_1363 = l_Lean_Expr_hash(x_1362);
x_1364 = 32;
x_1365 = lean_uint64_shift_right(x_1363, x_1364);
x_1366 = lean_uint64_xor(x_1363, x_1365);
x_1367 = 16;
x_1368 = lean_uint64_shift_right(x_1366, x_1367);
x_1369 = lean_uint64_xor(x_1366, x_1368);
x_1370 = lean_uint64_to_usize(x_1369);
x_1371 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1372 = lean_usize_land(x_1370, x_1371);
x_1373 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1374 = lean_array_uget(x_1373, x_1372);
x_1375 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1362, x_1374);
if (x_1375 == 0)
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; uint8_t x_1381; 
x_1376 = lean_box(0);
x_1377 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1377, 0, x_1362);
lean_ctor_set(x_1377, 1, x_1376);
lean_ctor_set(x_1377, 2, x_1374);
x_1378 = lean_array_uset(x_1373, x_1372, x_1377);
x_1379 = lean_array_get_size(x_1378);
x_1380 = lean_unsigned_to_nat(1u);
x_1381 = lean_nat_dec_le(x_1380, x_1379);
lean_dec(x_1379);
if (x_1381 == 0)
{
lean_object* x_1382; 
x_1382 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1378);
lean_ctor_set(x_1337, 1, x_1382);
lean_ctor_set(x_1337, 0, x_1380);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1337);
return x_381;
}
else
{
lean_ctor_set(x_1337, 1, x_1378);
lean_ctor_set(x_1337, 0, x_1380);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1337);
return x_381;
}
}
else
{
lean_object* x_1383; 
lean_dec(x_1374);
lean_dec(x_1362);
lean_free_object(x_381);
x_1383 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1383);
return x_1337;
}
}
else
{
uint8_t x_1384; 
lean_free_object(x_1337);
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1384 = !lean_is_exclusive(x_1356);
if (x_1384 == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1356, 1);
lean_dec(x_1385);
x_1386 = lean_ctor_get(x_1356, 0);
lean_dec(x_1386);
x_1387 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_1356, 0);
lean_ctor_set(x_1356, 1, x_11);
lean_ctor_set(x_1356, 0, x_1387);
return x_1356;
}
else
{
lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_1356);
x_1388 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1389, 0, x_1388);
lean_ctor_set(x_1389, 1, x_11);
return x_1389;
}
}
}
}
else
{
lean_object* x_1390; 
lean_dec(x_1355);
lean_dec(x_1354);
lean_dec(x_1353);
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1390 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1390);
return x_1337;
}
}
else
{
lean_object* x_1391; 
lean_dec(x_1354);
lean_dec(x_1353);
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1391 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1391);
return x_1337;
}
}
else
{
lean_object* x_1392; 
lean_dec(x_1353);
lean_dec(x_1342);
lean_free_object(x_381);
lean_dec(x_346);
x_1392 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1392);
return x_1337;
}
}
}
}
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; uint8_t x_1396; 
x_1393 = lean_ctor_get(x_1337, 1);
lean_inc(x_1393);
lean_dec(x_1337);
x_1394 = lean_ctor_get(x_1338, 1);
lean_inc(x_1394);
lean_dec(x_1338);
x_1395 = lean_ctor_get(x_1339, 1);
lean_inc(x_1395);
lean_dec(x_1339);
x_1396 = lean_string_dec_eq(x_1395, x_120);
lean_dec(x_1395);
if (x_1396 == 0)
{
lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1394);
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
x_1397 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_11);
return x_1398;
}
else
{
uint8_t x_1399; 
x_1399 = lean_string_dec_eq(x_1394, x_360);
lean_dec(x_1394);
if (x_1399 == 0)
{
lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
x_1400 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1401, 0, x_1400);
lean_ctor_set(x_1401, 1, x_11);
return x_1401;
}
else
{
lean_object* x_1402; uint8_t x_1403; 
x_1402 = lean_array_get_size(x_1393);
x_1403 = lean_nat_dec_eq(x_1402, x_365);
lean_dec(x_1402);
if (x_1403 == 0)
{
lean_object* x_1404; lean_object* x_1405; 
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
x_1404 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1405, 0, x_1404);
lean_ctor_set(x_1405, 1, x_11);
return x_1405;
}
else
{
lean_object* x_1406; 
x_1406 = lean_array_fget(x_1393, x_369);
if (lean_obj_tag(x_1406) == 4)
{
lean_object* x_1407; 
x_1407 = lean_ctor_get(x_1406, 0);
lean_inc(x_1407);
if (lean_obj_tag(x_1407) == 1)
{
lean_object* x_1408; 
x_1408 = lean_ctor_get(x_1407, 0);
lean_inc(x_1408);
if (lean_obj_tag(x_1408) == 0)
{
lean_object* x_1409; lean_object* x_1410; uint8_t x_1411; 
x_1409 = lean_ctor_get(x_1406, 1);
lean_inc(x_1409);
lean_dec(x_1406);
x_1410 = lean_ctor_get(x_1407, 1);
lean_inc(x_1410);
lean_dec(x_1407);
x_1411 = lean_string_dec_eq(x_1410, x_375);
lean_dec(x_1410);
if (x_1411 == 0)
{
lean_object* x_1412; lean_object* x_1413; 
lean_dec(x_1409);
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
x_1412 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1413, 0, x_1412);
lean_ctor_set(x_1413, 1, x_11);
return x_1413;
}
else
{
if (lean_obj_tag(x_1409) == 0)
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; uint64_t x_1417; uint64_t x_1418; uint64_t x_1419; uint64_t x_1420; uint64_t x_1421; uint64_t x_1422; uint64_t x_1423; size_t x_1424; size_t x_1425; size_t x_1426; lean_object* x_1427; lean_object* x_1428; uint8_t x_1429; 
x_1414 = lean_array_fget(x_1393, x_379);
lean_dec(x_1393);
x_1415 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1416 = l_Lean_mkAppB(x_1415, x_1414, x_346);
x_1417 = l_Lean_Expr_hash(x_1416);
x_1418 = 32;
x_1419 = lean_uint64_shift_right(x_1417, x_1418);
x_1420 = lean_uint64_xor(x_1417, x_1419);
x_1421 = 16;
x_1422 = lean_uint64_shift_right(x_1420, x_1421);
x_1423 = lean_uint64_xor(x_1420, x_1422);
x_1424 = lean_uint64_to_usize(x_1423);
x_1425 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1426 = lean_usize_land(x_1424, x_1425);
x_1427 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1428 = lean_array_uget(x_1427, x_1426);
x_1429 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1416, x_1428);
if (x_1429 == 0)
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; uint8_t x_1435; 
x_1430 = lean_box(0);
x_1431 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1431, 0, x_1416);
lean_ctor_set(x_1431, 1, x_1430);
lean_ctor_set(x_1431, 2, x_1428);
x_1432 = lean_array_uset(x_1427, x_1426, x_1431);
x_1433 = lean_array_get_size(x_1432);
x_1434 = lean_unsigned_to_nat(1u);
x_1435 = lean_nat_dec_le(x_1434, x_1433);
lean_dec(x_1433);
if (x_1435 == 0)
{
lean_object* x_1436; lean_object* x_1437; 
x_1436 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1432);
x_1437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1437, 0, x_1434);
lean_ctor_set(x_1437, 1, x_1436);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1437);
return x_381;
}
else
{
lean_object* x_1438; 
x_1438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1438, 0, x_1434);
lean_ctor_set(x_1438, 1, x_1432);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 0, x_1438);
return x_381;
}
}
else
{
lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_1428);
lean_dec(x_1416);
lean_free_object(x_381);
x_1439 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1440, 0, x_1439);
lean_ctor_set(x_1440, 1, x_11);
return x_1440;
}
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; 
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
if (lean_is_exclusive(x_1409)) {
 lean_ctor_release(x_1409, 0);
 lean_ctor_release(x_1409, 1);
 x_1441 = x_1409;
} else {
 lean_dec_ref(x_1409);
 x_1441 = lean_box(0);
}
x_1442 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1441)) {
 x_1443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1443 = x_1441;
 lean_ctor_set_tag(x_1443, 0);
}
lean_ctor_set(x_1443, 0, x_1442);
lean_ctor_set(x_1443, 1, x_11);
return x_1443;
}
}
}
else
{
lean_object* x_1444; lean_object* x_1445; 
lean_dec(x_1408);
lean_dec(x_1407);
lean_dec(x_1406);
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
x_1444 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1445, 0, x_1444);
lean_ctor_set(x_1445, 1, x_11);
return x_1445;
}
}
else
{
lean_object* x_1446; lean_object* x_1447; 
lean_dec(x_1407);
lean_dec(x_1406);
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
x_1446 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1447, 0, x_1446);
lean_ctor_set(x_1447, 1, x_11);
return x_1447;
}
}
else
{
lean_object* x_1448; lean_object* x_1449; 
lean_dec(x_1406);
lean_dec(x_1393);
lean_free_object(x_381);
lean_dec(x_346);
x_1448 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1449, 0, x_1448);
lean_ctor_set(x_1449, 1, x_11);
return x_1449;
}
}
}
}
}
}
else
{
uint8_t x_1450; 
lean_dec(x_1340);
lean_dec(x_1339);
lean_dec(x_1338);
lean_free_object(x_381);
lean_dec(x_346);
x_1450 = !lean_is_exclusive(x_1337);
if (x_1450 == 0)
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
x_1451 = lean_ctor_get(x_1337, 1);
lean_dec(x_1451);
x_1452 = lean_ctor_get(x_1337, 0);
lean_dec(x_1452);
x_1453 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1453);
return x_1337;
}
else
{
lean_object* x_1454; lean_object* x_1455; 
lean_dec(x_1337);
x_1454 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1455, 0, x_1454);
lean_ctor_set(x_1455, 1, x_11);
return x_1455;
}
}
}
else
{
uint8_t x_1456; 
lean_dec(x_1339);
lean_dec(x_1338);
lean_free_object(x_381);
lean_dec(x_346);
x_1456 = !lean_is_exclusive(x_1337);
if (x_1456 == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; 
x_1457 = lean_ctor_get(x_1337, 1);
lean_dec(x_1457);
x_1458 = lean_ctor_get(x_1337, 0);
lean_dec(x_1458);
x_1459 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1459);
return x_1337;
}
else
{
lean_object* x_1460; lean_object* x_1461; 
lean_dec(x_1337);
x_1460 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1461, 0, x_1460);
lean_ctor_set(x_1461, 1, x_11);
return x_1461;
}
}
}
else
{
uint8_t x_1462; 
lean_dec(x_1338);
lean_free_object(x_381);
lean_dec(x_346);
x_1462 = !lean_is_exclusive(x_1337);
if (x_1462 == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
x_1463 = lean_ctor_get(x_1337, 1);
lean_dec(x_1463);
x_1464 = lean_ctor_get(x_1337, 0);
lean_dec(x_1464);
x_1465 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_1337, 1, x_11);
lean_ctor_set(x_1337, 0, x_1465);
return x_1337;
}
else
{
lean_object* x_1466; lean_object* x_1467; 
lean_dec(x_1337);
x_1466 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1467, 0, x_1466);
lean_ctor_set(x_1467, 1, x_11);
return x_1467;
}
}
}
else
{
lean_object* x_1468; lean_object* x_1469; 
lean_dec(x_381);
x_1468 = l_Lean_Expr_getAppFnArgs(x_344);
x_1469 = lean_ctor_get(x_1468, 0);
lean_inc(x_1469);
if (lean_obj_tag(x_1469) == 1)
{
lean_object* x_1470; 
x_1470 = lean_ctor_get(x_1469, 0);
lean_inc(x_1470);
if (lean_obj_tag(x_1470) == 1)
{
lean_object* x_1471; 
x_1471 = lean_ctor_get(x_1470, 0);
lean_inc(x_1471);
if (lean_obj_tag(x_1471) == 0)
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; uint8_t x_1476; 
x_1472 = lean_ctor_get(x_1468, 1);
lean_inc(x_1472);
if (lean_is_exclusive(x_1468)) {
 lean_ctor_release(x_1468, 0);
 lean_ctor_release(x_1468, 1);
 x_1473 = x_1468;
} else {
 lean_dec_ref(x_1468);
 x_1473 = lean_box(0);
}
x_1474 = lean_ctor_get(x_1469, 1);
lean_inc(x_1474);
lean_dec(x_1469);
x_1475 = lean_ctor_get(x_1470, 1);
lean_inc(x_1475);
lean_dec(x_1470);
x_1476 = lean_string_dec_eq(x_1475, x_120);
lean_dec(x_1475);
if (x_1476 == 0)
{
lean_object* x_1477; lean_object* x_1478; 
lean_dec(x_1474);
lean_dec(x_1472);
lean_dec(x_346);
x_1477 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1478 = x_1473;
}
lean_ctor_set(x_1478, 0, x_1477);
lean_ctor_set(x_1478, 1, x_11);
return x_1478;
}
else
{
uint8_t x_1479; 
x_1479 = lean_string_dec_eq(x_1474, x_360);
lean_dec(x_1474);
if (x_1479 == 0)
{
lean_object* x_1480; lean_object* x_1481; 
lean_dec(x_1472);
lean_dec(x_346);
x_1480 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1481 = x_1473;
}
lean_ctor_set(x_1481, 0, x_1480);
lean_ctor_set(x_1481, 1, x_11);
return x_1481;
}
else
{
lean_object* x_1482; uint8_t x_1483; 
x_1482 = lean_array_get_size(x_1472);
x_1483 = lean_nat_dec_eq(x_1482, x_365);
lean_dec(x_1482);
if (x_1483 == 0)
{
lean_object* x_1484; lean_object* x_1485; 
lean_dec(x_1472);
lean_dec(x_346);
x_1484 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1485 = x_1473;
}
lean_ctor_set(x_1485, 0, x_1484);
lean_ctor_set(x_1485, 1, x_11);
return x_1485;
}
else
{
lean_object* x_1486; 
x_1486 = lean_array_fget(x_1472, x_369);
if (lean_obj_tag(x_1486) == 4)
{
lean_object* x_1487; 
x_1487 = lean_ctor_get(x_1486, 0);
lean_inc(x_1487);
if (lean_obj_tag(x_1487) == 1)
{
lean_object* x_1488; 
x_1488 = lean_ctor_get(x_1487, 0);
lean_inc(x_1488);
if (lean_obj_tag(x_1488) == 0)
{
lean_object* x_1489; lean_object* x_1490; uint8_t x_1491; 
x_1489 = lean_ctor_get(x_1486, 1);
lean_inc(x_1489);
lean_dec(x_1486);
x_1490 = lean_ctor_get(x_1487, 1);
lean_inc(x_1490);
lean_dec(x_1487);
x_1491 = lean_string_dec_eq(x_1490, x_375);
lean_dec(x_1490);
if (x_1491 == 0)
{
lean_object* x_1492; lean_object* x_1493; 
lean_dec(x_1489);
lean_dec(x_1472);
lean_dec(x_346);
x_1492 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1493 = x_1473;
}
lean_ctor_set(x_1493, 0, x_1492);
lean_ctor_set(x_1493, 1, x_11);
return x_1493;
}
else
{
if (lean_obj_tag(x_1489) == 0)
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; uint64_t x_1497; uint64_t x_1498; uint64_t x_1499; uint64_t x_1500; uint64_t x_1501; uint64_t x_1502; uint64_t x_1503; size_t x_1504; size_t x_1505; size_t x_1506; lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; 
x_1494 = lean_array_fget(x_1472, x_379);
lean_dec(x_1472);
x_1495 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_1496 = l_Lean_mkAppB(x_1495, x_1494, x_346);
x_1497 = l_Lean_Expr_hash(x_1496);
x_1498 = 32;
x_1499 = lean_uint64_shift_right(x_1497, x_1498);
x_1500 = lean_uint64_xor(x_1497, x_1499);
x_1501 = 16;
x_1502 = lean_uint64_shift_right(x_1500, x_1501);
x_1503 = lean_uint64_xor(x_1500, x_1502);
x_1504 = lean_uint64_to_usize(x_1503);
x_1505 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1506 = lean_usize_land(x_1504, x_1505);
x_1507 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1508 = lean_array_uget(x_1507, x_1506);
x_1509 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1496, x_1508);
if (x_1509 == 0)
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; uint8_t x_1515; 
x_1510 = lean_box(0);
x_1511 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1511, 0, x_1496);
lean_ctor_set(x_1511, 1, x_1510);
lean_ctor_set(x_1511, 2, x_1508);
x_1512 = lean_array_uset(x_1507, x_1506, x_1511);
x_1513 = lean_array_get_size(x_1512);
x_1514 = lean_unsigned_to_nat(1u);
x_1515 = lean_nat_dec_le(x_1514, x_1513);
lean_dec(x_1513);
if (x_1515 == 0)
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
x_1516 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1512);
if (lean_is_scalar(x_1473)) {
 x_1517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1517 = x_1473;
}
lean_ctor_set(x_1517, 0, x_1514);
lean_ctor_set(x_1517, 1, x_1516);
x_1518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1518, 0, x_1517);
lean_ctor_set(x_1518, 1, x_11);
return x_1518;
}
else
{
lean_object* x_1519; lean_object* x_1520; 
if (lean_is_scalar(x_1473)) {
 x_1519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1519 = x_1473;
}
lean_ctor_set(x_1519, 0, x_1514);
lean_ctor_set(x_1519, 1, x_1512);
x_1520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1520, 0, x_1519);
lean_ctor_set(x_1520, 1, x_11);
return x_1520;
}
}
else
{
lean_object* x_1521; lean_object* x_1522; 
lean_dec(x_1508);
lean_dec(x_1496);
x_1521 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1522 = x_1473;
}
lean_ctor_set(x_1522, 0, x_1521);
lean_ctor_set(x_1522, 1, x_11);
return x_1522;
}
}
else
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
lean_dec(x_1473);
lean_dec(x_1472);
lean_dec(x_346);
if (lean_is_exclusive(x_1489)) {
 lean_ctor_release(x_1489, 0);
 lean_ctor_release(x_1489, 1);
 x_1523 = x_1489;
} else {
 lean_dec_ref(x_1489);
 x_1523 = lean_box(0);
}
x_1524 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1523)) {
 x_1525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1525 = x_1523;
 lean_ctor_set_tag(x_1525, 0);
}
lean_ctor_set(x_1525, 0, x_1524);
lean_ctor_set(x_1525, 1, x_11);
return x_1525;
}
}
}
else
{
lean_object* x_1526; lean_object* x_1527; 
lean_dec(x_1488);
lean_dec(x_1487);
lean_dec(x_1486);
lean_dec(x_1472);
lean_dec(x_346);
x_1526 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1527 = x_1473;
}
lean_ctor_set(x_1527, 0, x_1526);
lean_ctor_set(x_1527, 1, x_11);
return x_1527;
}
}
else
{
lean_object* x_1528; lean_object* x_1529; 
lean_dec(x_1487);
lean_dec(x_1486);
lean_dec(x_1472);
lean_dec(x_346);
x_1528 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1529 = x_1473;
}
lean_ctor_set(x_1529, 0, x_1528);
lean_ctor_set(x_1529, 1, x_11);
return x_1529;
}
}
else
{
lean_object* x_1530; lean_object* x_1531; 
lean_dec(x_1486);
lean_dec(x_1472);
lean_dec(x_346);
x_1530 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1473)) {
 x_1531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1531 = x_1473;
}
lean_ctor_set(x_1531, 0, x_1530);
lean_ctor_set(x_1531, 1, x_11);
return x_1531;
}
}
}
}
}
else
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
lean_dec(x_1471);
lean_dec(x_1470);
lean_dec(x_1469);
lean_dec(x_346);
if (lean_is_exclusive(x_1468)) {
 lean_ctor_release(x_1468, 0);
 lean_ctor_release(x_1468, 1);
 x_1532 = x_1468;
} else {
 lean_dec_ref(x_1468);
 x_1532 = lean_box(0);
}
x_1533 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1532)) {
 x_1534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1534 = x_1532;
}
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set(x_1534, 1, x_11);
return x_1534;
}
}
else
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; 
lean_dec(x_1470);
lean_dec(x_1469);
lean_dec(x_346);
if (lean_is_exclusive(x_1468)) {
 lean_ctor_release(x_1468, 0);
 lean_ctor_release(x_1468, 1);
 x_1535 = x_1468;
} else {
 lean_dec_ref(x_1468);
 x_1535 = lean_box(0);
}
x_1536 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1535)) {
 x_1537 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1537 = x_1535;
}
lean_ctor_set(x_1537, 0, x_1536);
lean_ctor_set(x_1537, 1, x_11);
return x_1537;
}
}
else
{
lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; 
lean_dec(x_1469);
lean_dec(x_346);
if (lean_is_exclusive(x_1468)) {
 lean_ctor_release(x_1468, 0);
 lean_ctor_release(x_1468, 1);
 x_1538 = x_1468;
} else {
 lean_dec_ref(x_1468);
 x_1538 = lean_box(0);
}
x_1539 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_1538)) {
 x_1540 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1540 = x_1538;
}
lean_ctor_set(x_1540, 0, x_1539);
lean_ctor_set(x_1540, 1, x_11);
return x_1540;
}
}
}
}
else
{
uint8_t x_1541; 
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1541 = !lean_is_exclusive(x_373);
if (x_1541 == 0)
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; 
x_1542 = lean_ctor_get(x_373, 1);
lean_dec(x_1542);
x_1543 = lean_ctor_get(x_373, 0);
lean_dec(x_1543);
x_1544 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_373, 0);
lean_ctor_set(x_373, 1, x_11);
lean_ctor_set(x_373, 0, x_1544);
return x_373;
}
else
{
lean_object* x_1545; lean_object* x_1546; 
lean_dec(x_373);
x_1545 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1546, 0, x_1545);
lean_ctor_set(x_1546, 1, x_11);
return x_1546;
}
}
}
}
else
{
lean_object* x_1547; lean_object* x_1548; 
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1547 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_1548 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1548 = x_352;
}
lean_ctor_set(x_1548, 0, x_1547);
lean_ctor_set(x_1548, 1, x_11);
return x_1548;
}
}
else
{
lean_object* x_1549; lean_object* x_1550; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1549 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_1550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1550 = x_352;
}
lean_ctor_set(x_1550, 0, x_1549);
lean_ctor_set(x_1550, 1, x_11);
return x_1550;
}
}
else
{
lean_object* x_1551; lean_object* x_1552; 
lean_dec(x_370);
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1551 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_1552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1552 = x_352;
}
lean_ctor_set(x_1552, 0, x_1551);
lean_ctor_set(x_1552, 1, x_11);
return x_1552;
}
}
}
}
}
else
{
lean_object* x_1553; uint8_t x_1554; 
lean_dec(x_354);
x_1553 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_1554 = lean_string_dec_eq(x_353, x_1553);
lean_dec(x_353);
if (x_1554 == 0)
{
lean_object* x_1555; lean_object* x_1556; 
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1555 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_1556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1556 = x_352;
}
lean_ctor_set(x_1556, 0, x_1555);
lean_ctor_set(x_1556, 1, x_11);
return x_1556;
}
else
{
lean_object* x_1557; uint8_t x_1558; 
x_1557 = lean_array_get_size(x_351);
x_1558 = lean_nat_dec_eq(x_1557, x_339);
lean_dec(x_1557);
if (x_1558 == 0)
{
lean_object* x_1559; lean_object* x_1560; 
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1559 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_1560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1560 = x_352;
}
lean_ctor_set(x_1560, 0, x_1559);
lean_ctor_set(x_1560, 1, x_11);
return x_1560;
}
else
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
x_1561 = lean_array_fget(x_351, x_343);
x_1562 = lean_array_fget(x_351, x_345);
lean_dec(x_351);
lean_inc(x_1561);
x_1563 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1561);
if (lean_obj_tag(x_1563) == 0)
{
lean_object* x_1564; lean_object* x_1565; 
lean_dec(x_1562);
lean_dec(x_1561);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1564 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_1565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1565 = x_352;
}
lean_ctor_set(x_1565, 0, x_1564);
lean_ctor_set(x_1565, 1, x_11);
return x_1565;
}
else
{
lean_object* x_1566; lean_object* x_1567; uint8_t x_1568; 
x_1566 = lean_ctor_get(x_1563, 0);
lean_inc(x_1566);
lean_dec(x_1563);
x_1567 = lean_unsigned_to_nat(0u);
x_1568 = lean_nat_dec_eq(x_1566, x_1567);
lean_dec(x_1566);
if (x_1568 == 0)
{
lean_object* x_1569; uint8_t x_1677; 
x_1677 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55;
if (x_1677 == 0)
{
lean_object* x_1678; 
x_1678 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78;
x_1569 = x_1678;
goto block_1676;
}
else
{
lean_object* x_1679; 
x_1679 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
x_1569 = x_1679;
goto block_1676;
}
block_1676:
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; 
x_1570 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_1571 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
x_1572 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
lean_inc(x_1561);
lean_inc(x_1569);
x_1573 = l_Lean_mkApp4(x_1570, x_1571, x_1572, x_1569, x_1561);
x_1574 = l_Lean_Meta_mkDecideProof(x_1573, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1574) == 0)
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; uint64_t x_1584; uint64_t x_1585; uint64_t x_1586; uint64_t x_1587; uint64_t x_1588; uint64_t x_1589; uint64_t x_1590; size_t x_1591; size_t x_1592; size_t x_1593; size_t x_1594; lean_object* x_1595; lean_object* x_1596; uint8_t x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
x_1575 = lean_ctor_get(x_1574, 0);
lean_inc(x_1575);
x_1576 = lean_ctor_get(x_1574, 1);
lean_inc(x_1576);
if (lean_is_exclusive(x_1574)) {
 lean_ctor_release(x_1574, 0);
 lean_ctor_release(x_1574, 1);
 x_1577 = x_1574;
} else {
 lean_dec_ref(x_1574);
 x_1577 = lean_box(0);
}
x_1578 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77;
x_1579 = l_Lean_mkApp3(x_1578, x_1561, x_1562, x_1575);
x_1580 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
lean_inc(x_1579);
lean_inc(x_346);
x_1581 = l_Lean_mkApp3(x_1580, x_346, x_1569, x_1579);
x_1582 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
lean_inc(x_346);
lean_inc(x_344);
x_1583 = l_Lean_mkApp3(x_1582, x_344, x_346, x_1581);
x_1584 = l_Lean_Expr_hash(x_1583);
x_1585 = 32;
x_1586 = lean_uint64_shift_right(x_1584, x_1585);
x_1587 = lean_uint64_xor(x_1584, x_1586);
x_1588 = 16;
x_1589 = lean_uint64_shift_right(x_1587, x_1588);
x_1590 = lean_uint64_xor(x_1587, x_1589);
x_1591 = lean_uint64_to_usize(x_1590);
x_1592 = 1;
x_1593 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1594 = lean_usize_land(x_1591, x_1593);
x_1595 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1596 = lean_array_uget(x_1595, x_1594);
x_1597 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1583, x_1596);
x_1598 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
x_1599 = l_Lean_mkApp3(x_1598, x_344, x_346, x_1579);
if (x_1597 == 0)
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; uint8_t x_1667; 
x_1662 = lean_box(0);
x_1663 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1663, 0, x_1583);
lean_ctor_set(x_1663, 1, x_1662);
lean_ctor_set(x_1663, 2, x_1596);
x_1664 = lean_array_uset(x_1595, x_1594, x_1663);
x_1665 = lean_array_get_size(x_1664);
x_1666 = lean_unsigned_to_nat(1u);
x_1667 = lean_nat_dec_le(x_1666, x_1665);
lean_dec(x_1665);
if (x_1667 == 0)
{
lean_object* x_1668; lean_object* x_1669; 
x_1668 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1664);
if (lean_is_scalar(x_352)) {
 x_1669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1669 = x_352;
}
lean_ctor_set(x_1669, 0, x_1666);
lean_ctor_set(x_1669, 1, x_1668);
x_1600 = x_1669;
goto block_1661;
}
else
{
lean_object* x_1670; 
if (lean_is_scalar(x_352)) {
 x_1670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1670 = x_352;
}
lean_ctor_set(x_1670, 0, x_1666);
lean_ctor_set(x_1670, 1, x_1664);
x_1600 = x_1670;
goto block_1661;
}
}
else
{
lean_object* x_1671; 
lean_dec(x_1596);
lean_dec(x_1583);
lean_dec(x_352);
x_1671 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1600 = x_1671;
goto block_1661;
}
block_1661:
{
uint8_t x_1601; 
x_1601 = !lean_is_exclusive(x_1600);
if (x_1601 == 0)
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; uint64_t x_1605; uint64_t x_1606; uint64_t x_1607; uint64_t x_1608; uint64_t x_1609; size_t x_1610; size_t x_1611; size_t x_1612; size_t x_1613; lean_object* x_1614; uint8_t x_1615; 
x_1602 = lean_ctor_get(x_1600, 0);
x_1603 = lean_ctor_get(x_1600, 1);
x_1604 = lean_array_get_size(x_1603);
x_1605 = l_Lean_Expr_hash(x_1599);
x_1606 = lean_uint64_shift_right(x_1605, x_1585);
x_1607 = lean_uint64_xor(x_1605, x_1606);
x_1608 = lean_uint64_shift_right(x_1607, x_1588);
x_1609 = lean_uint64_xor(x_1607, x_1608);
x_1610 = lean_uint64_to_usize(x_1609);
x_1611 = lean_usize_of_nat(x_1604);
lean_dec(x_1604);
x_1612 = lean_usize_sub(x_1611, x_1592);
x_1613 = lean_usize_land(x_1610, x_1612);
x_1614 = lean_array_uget(x_1603, x_1613);
x_1615 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1599, x_1614);
if (x_1615 == 0)
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; uint8_t x_1625; 
x_1616 = lean_unsigned_to_nat(1u);
x_1617 = lean_nat_add(x_1602, x_1616);
lean_dec(x_1602);
x_1618 = lean_box(0);
x_1619 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1619, 0, x_1599);
lean_ctor_set(x_1619, 1, x_1618);
lean_ctor_set(x_1619, 2, x_1614);
x_1620 = lean_array_uset(x_1603, x_1613, x_1619);
x_1621 = lean_nat_mul(x_1617, x_343);
x_1622 = lean_unsigned_to_nat(3u);
x_1623 = lean_nat_div(x_1621, x_1622);
lean_dec(x_1621);
x_1624 = lean_array_get_size(x_1620);
x_1625 = lean_nat_dec_le(x_1623, x_1624);
lean_dec(x_1624);
lean_dec(x_1623);
if (x_1625 == 0)
{
lean_object* x_1626; lean_object* x_1627; 
x_1626 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1620);
lean_ctor_set(x_1600, 1, x_1626);
lean_ctor_set(x_1600, 0, x_1617);
if (lean_is_scalar(x_1577)) {
 x_1627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1627 = x_1577;
}
lean_ctor_set(x_1627, 0, x_1600);
lean_ctor_set(x_1627, 1, x_1576);
return x_1627;
}
else
{
lean_object* x_1628; 
lean_ctor_set(x_1600, 1, x_1620);
lean_ctor_set(x_1600, 0, x_1617);
if (lean_is_scalar(x_1577)) {
 x_1628 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1628 = x_1577;
}
lean_ctor_set(x_1628, 0, x_1600);
lean_ctor_set(x_1628, 1, x_1576);
return x_1628;
}
}
else
{
lean_object* x_1629; 
lean_dec(x_1614);
lean_dec(x_1599);
if (lean_is_scalar(x_1577)) {
 x_1629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1629 = x_1577;
}
lean_ctor_set(x_1629, 0, x_1600);
lean_ctor_set(x_1629, 1, x_1576);
return x_1629;
}
}
else
{
lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; uint64_t x_1633; uint64_t x_1634; uint64_t x_1635; uint64_t x_1636; uint64_t x_1637; size_t x_1638; size_t x_1639; size_t x_1640; size_t x_1641; lean_object* x_1642; uint8_t x_1643; 
x_1630 = lean_ctor_get(x_1600, 0);
x_1631 = lean_ctor_get(x_1600, 1);
lean_inc(x_1631);
lean_inc(x_1630);
lean_dec(x_1600);
x_1632 = lean_array_get_size(x_1631);
x_1633 = l_Lean_Expr_hash(x_1599);
x_1634 = lean_uint64_shift_right(x_1633, x_1585);
x_1635 = lean_uint64_xor(x_1633, x_1634);
x_1636 = lean_uint64_shift_right(x_1635, x_1588);
x_1637 = lean_uint64_xor(x_1635, x_1636);
x_1638 = lean_uint64_to_usize(x_1637);
x_1639 = lean_usize_of_nat(x_1632);
lean_dec(x_1632);
x_1640 = lean_usize_sub(x_1639, x_1592);
x_1641 = lean_usize_land(x_1638, x_1640);
x_1642 = lean_array_uget(x_1631, x_1641);
x_1643 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1599, x_1642);
if (x_1643 == 0)
{
lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; uint8_t x_1653; 
x_1644 = lean_unsigned_to_nat(1u);
x_1645 = lean_nat_add(x_1630, x_1644);
lean_dec(x_1630);
x_1646 = lean_box(0);
x_1647 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1647, 0, x_1599);
lean_ctor_set(x_1647, 1, x_1646);
lean_ctor_set(x_1647, 2, x_1642);
x_1648 = lean_array_uset(x_1631, x_1641, x_1647);
x_1649 = lean_nat_mul(x_1645, x_343);
x_1650 = lean_unsigned_to_nat(3u);
x_1651 = lean_nat_div(x_1649, x_1650);
lean_dec(x_1649);
x_1652 = lean_array_get_size(x_1648);
x_1653 = lean_nat_dec_le(x_1651, x_1652);
lean_dec(x_1652);
lean_dec(x_1651);
if (x_1653 == 0)
{
lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; 
x_1654 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1648);
x_1655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1655, 0, x_1645);
lean_ctor_set(x_1655, 1, x_1654);
if (lean_is_scalar(x_1577)) {
 x_1656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1656 = x_1577;
}
lean_ctor_set(x_1656, 0, x_1655);
lean_ctor_set(x_1656, 1, x_1576);
return x_1656;
}
else
{
lean_object* x_1657; lean_object* x_1658; 
x_1657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1657, 0, x_1645);
lean_ctor_set(x_1657, 1, x_1648);
if (lean_is_scalar(x_1577)) {
 x_1658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1658 = x_1577;
}
lean_ctor_set(x_1658, 0, x_1657);
lean_ctor_set(x_1658, 1, x_1576);
return x_1658;
}
}
else
{
lean_object* x_1659; lean_object* x_1660; 
lean_dec(x_1642);
lean_dec(x_1599);
x_1659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1659, 0, x_1630);
lean_ctor_set(x_1659, 1, x_1631);
if (lean_is_scalar(x_1577)) {
 x_1660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1660 = x_1577;
}
lean_ctor_set(x_1660, 0, x_1659);
lean_ctor_set(x_1660, 1, x_1576);
return x_1660;
}
}
}
}
else
{
uint8_t x_1672; 
lean_dec(x_1569);
lean_dec(x_1562);
lean_dec(x_1561);
lean_dec(x_352);
lean_dec(x_346);
lean_dec(x_344);
x_1672 = !lean_is_exclusive(x_1574);
if (x_1672 == 0)
{
return x_1574;
}
else
{
lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
x_1673 = lean_ctor_get(x_1574, 0);
x_1674 = lean_ctor_get(x_1574, 1);
lean_inc(x_1674);
lean_inc(x_1673);
lean_dec(x_1574);
x_1675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1675, 0, x_1673);
lean_ctor_set(x_1675, 1, x_1674);
return x_1675;
}
}
}
}
else
{
lean_object* x_1680; lean_object* x_1681; 
lean_dec(x_1562);
lean_dec(x_1561);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1680 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_352)) {
 x_1681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1681 = x_352;
}
lean_ctor_set(x_1681, 0, x_1680);
lean_ctor_set(x_1681, 1, x_11);
return x_1681;
}
}
}
}
}
}
else
{
uint8_t x_1682; 
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1682 = !lean_is_exclusive(x_347);
if (x_1682 == 0)
{
lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
x_1683 = lean_ctor_get(x_347, 1);
lean_dec(x_1683);
x_1684 = lean_ctor_get(x_347, 0);
lean_dec(x_1684);
x_1685 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_347, 1, x_11);
lean_ctor_set(x_347, 0, x_1685);
return x_347;
}
else
{
lean_object* x_1686; lean_object* x_1687; 
lean_dec(x_347);
x_1686 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1687, 0, x_1686);
lean_ctor_set(x_1687, 1, x_11);
return x_1687;
}
}
}
else
{
uint8_t x_1688; 
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1688 = !lean_is_exclusive(x_347);
if (x_1688 == 0)
{
lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; 
x_1689 = lean_ctor_get(x_347, 1);
lean_dec(x_1689);
x_1690 = lean_ctor_get(x_347, 0);
lean_dec(x_1690);
x_1691 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_347, 1, x_11);
lean_ctor_set(x_347, 0, x_1691);
return x_347;
}
else
{
lean_object* x_1692; lean_object* x_1693; 
lean_dec(x_347);
x_1692 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1693 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1693, 0, x_1692);
lean_ctor_set(x_1693, 1, x_11);
return x_1693;
}
}
}
else
{
uint8_t x_1694; 
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_344);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1694 = !lean_is_exclusive(x_347);
if (x_1694 == 0)
{
lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; 
x_1695 = lean_ctor_get(x_347, 1);
lean_dec(x_1695);
x_1696 = lean_ctor_get(x_347, 0);
lean_dec(x_1696);
x_1697 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_347, 1, x_11);
lean_ctor_set(x_347, 0, x_1697);
return x_347;
}
else
{
lean_object* x_1698; lean_object* x_1699; 
lean_dec(x_347);
x_1698 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1699 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1699, 0, x_1698);
lean_ctor_set(x_1699, 1, x_11);
return x_1699;
}
}
}
}
}
}
else
{
lean_object* x_1700; uint8_t x_1701; 
lean_dec(x_119);
x_1700 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_1701 = lean_string_dec_eq(x_118, x_1700);
lean_dec(x_118);
if (x_1701 == 0)
{
lean_object* x_1702; lean_object* x_1703; 
lean_dec(x_116);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1702 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_1703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1703 = x_117;
}
lean_ctor_set(x_1703, 0, x_1702);
lean_ctor_set(x_1703, 1, x_11);
return x_1703;
}
else
{
lean_object* x_1704; lean_object* x_1705; uint8_t x_1706; 
x_1704 = lean_array_get_size(x_116);
x_1705 = lean_unsigned_to_nat(6u);
x_1706 = lean_nat_dec_eq(x_1704, x_1705);
lean_dec(x_1704);
if (x_1706 == 0)
{
lean_object* x_1707; lean_object* x_1708; 
lean_dec(x_116);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1707 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_1708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1708 = x_117;
}
lean_ctor_set(x_1708, 0, x_1707);
lean_ctor_set(x_1708, 1, x_11);
return x_1708;
}
else
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; 
x_1709 = lean_unsigned_to_nat(4u);
x_1710 = lean_array_fget(x_116, x_1709);
x_1711 = lean_unsigned_to_nat(5u);
x_1712 = lean_array_fget(x_116, x_1711);
lean_dec(x_116);
lean_inc(x_1712);
x_1713 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1712);
if (lean_obj_tag(x_1713) == 0)
{
lean_object* x_1714; lean_object* x_1715; 
lean_dec(x_1712);
lean_dec(x_1710);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1714 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_1715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1715 = x_117;
}
lean_ctor_set(x_1715, 0, x_1714);
lean_ctor_set(x_1715, 1, x_11);
return x_1715;
}
else
{
lean_object* x_1716; lean_object* x_1717; uint8_t x_1718; 
x_1716 = lean_ctor_get(x_1713, 0);
lean_inc(x_1716);
lean_dec(x_1713);
x_1717 = lean_unsigned_to_nat(0u);
x_1718 = lean_nat_dec_eq(x_1716, x_1717);
lean_dec(x_1716);
if (x_1718 == 0)
{
lean_object* x_1719; uint8_t x_1832; 
x_1832 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55;
if (x_1832 == 0)
{
lean_object* x_1833; 
x_1833 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92;
x_1719 = x_1833;
goto block_1831;
}
else
{
lean_object* x_1834; 
x_1834 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
x_1719 = x_1834;
goto block_1831;
}
block_1831:
{
lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; 
x_1720 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83;
x_1721 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
lean_inc(x_1719);
lean_inc(x_1712);
x_1722 = l_Lean_mkApp3(x_1720, x_1721, x_1712, x_1719);
x_1723 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84;
x_1724 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
lean_inc(x_1712);
x_1725 = l_Lean_mkApp4(x_1723, x_1721, x_1724, x_1719, x_1712);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_1726 = l_Lean_Meta_mkDecideProof(x_1722, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1726) == 0)
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; 
x_1727 = lean_ctor_get(x_1726, 0);
lean_inc(x_1727);
x_1728 = lean_ctor_get(x_1726, 1);
lean_inc(x_1728);
lean_dec(x_1726);
x_1729 = l_Lean_Meta_mkDecideProof(x_1725, x_7, x_8, x_9, x_10, x_1728);
if (lean_obj_tag(x_1729) == 0)
{
lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; uint64_t x_1735; uint64_t x_1736; uint64_t x_1737; uint64_t x_1738; uint64_t x_1739; uint64_t x_1740; uint64_t x_1741; size_t x_1742; size_t x_1743; size_t x_1744; size_t x_1745; lean_object* x_1746; lean_object* x_1747; uint8_t x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; 
x_1730 = lean_ctor_get(x_1729, 0);
lean_inc(x_1730);
x_1731 = lean_ctor_get(x_1729, 1);
lean_inc(x_1731);
if (lean_is_exclusive(x_1729)) {
 lean_ctor_release(x_1729, 0);
 lean_ctor_release(x_1729, 1);
 x_1732 = x_1729;
} else {
 lean_dec_ref(x_1729);
 x_1732 = lean_box(0);
}
x_1733 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87;
lean_inc(x_1712);
lean_inc(x_1710);
x_1734 = l_Lean_mkApp3(x_1733, x_1710, x_1712, x_1727);
x_1735 = l_Lean_Expr_hash(x_1734);
x_1736 = 32;
x_1737 = lean_uint64_shift_right(x_1735, x_1736);
x_1738 = lean_uint64_xor(x_1735, x_1737);
x_1739 = 16;
x_1740 = lean_uint64_shift_right(x_1738, x_1739);
x_1741 = lean_uint64_xor(x_1738, x_1740);
x_1742 = lean_uint64_to_usize(x_1741);
x_1743 = 1;
x_1744 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1745 = lean_usize_land(x_1742, x_1744);
x_1746 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_1747 = lean_array_uget(x_1746, x_1745);
x_1748 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1734, x_1747);
x_1749 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90;
x_1750 = l_Lean_mkApp3(x_1749, x_1710, x_1712, x_1730);
if (x_1748 == 0)
{
lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; uint8_t x_1818; 
x_1813 = lean_box(0);
x_1814 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1814, 0, x_1734);
lean_ctor_set(x_1814, 1, x_1813);
lean_ctor_set(x_1814, 2, x_1747);
x_1815 = lean_array_uset(x_1746, x_1745, x_1814);
x_1816 = lean_array_get_size(x_1815);
x_1817 = lean_unsigned_to_nat(1u);
x_1818 = lean_nat_dec_le(x_1817, x_1816);
lean_dec(x_1816);
if (x_1818 == 0)
{
lean_object* x_1819; lean_object* x_1820; 
x_1819 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1815);
if (lean_is_scalar(x_117)) {
 x_1820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1820 = x_117;
}
lean_ctor_set(x_1820, 0, x_1817);
lean_ctor_set(x_1820, 1, x_1819);
x_1751 = x_1820;
goto block_1812;
}
else
{
lean_object* x_1821; 
if (lean_is_scalar(x_117)) {
 x_1821 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1821 = x_117;
}
lean_ctor_set(x_1821, 0, x_1817);
lean_ctor_set(x_1821, 1, x_1815);
x_1751 = x_1821;
goto block_1812;
}
}
else
{
lean_object* x_1822; 
lean_dec(x_1747);
lean_dec(x_1734);
lean_dec(x_117);
x_1822 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1751 = x_1822;
goto block_1812;
}
block_1812:
{
uint8_t x_1752; 
x_1752 = !lean_is_exclusive(x_1751);
if (x_1752 == 0)
{
lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; uint64_t x_1756; uint64_t x_1757; uint64_t x_1758; uint64_t x_1759; uint64_t x_1760; size_t x_1761; size_t x_1762; size_t x_1763; size_t x_1764; lean_object* x_1765; uint8_t x_1766; 
x_1753 = lean_ctor_get(x_1751, 0);
x_1754 = lean_ctor_get(x_1751, 1);
x_1755 = lean_array_get_size(x_1754);
x_1756 = l_Lean_Expr_hash(x_1750);
x_1757 = lean_uint64_shift_right(x_1756, x_1736);
x_1758 = lean_uint64_xor(x_1756, x_1757);
x_1759 = lean_uint64_shift_right(x_1758, x_1739);
x_1760 = lean_uint64_xor(x_1758, x_1759);
x_1761 = lean_uint64_to_usize(x_1760);
x_1762 = lean_usize_of_nat(x_1755);
lean_dec(x_1755);
x_1763 = lean_usize_sub(x_1762, x_1743);
x_1764 = lean_usize_land(x_1761, x_1763);
x_1765 = lean_array_uget(x_1754, x_1764);
x_1766 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1750, x_1765);
if (x_1766 == 0)
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; uint8_t x_1776; 
x_1767 = lean_unsigned_to_nat(1u);
x_1768 = lean_nat_add(x_1753, x_1767);
lean_dec(x_1753);
x_1769 = lean_box(0);
x_1770 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1770, 0, x_1750);
lean_ctor_set(x_1770, 1, x_1769);
lean_ctor_set(x_1770, 2, x_1765);
x_1771 = lean_array_uset(x_1754, x_1764, x_1770);
x_1772 = lean_nat_mul(x_1768, x_1709);
x_1773 = lean_unsigned_to_nat(3u);
x_1774 = lean_nat_div(x_1772, x_1773);
lean_dec(x_1772);
x_1775 = lean_array_get_size(x_1771);
x_1776 = lean_nat_dec_le(x_1774, x_1775);
lean_dec(x_1775);
lean_dec(x_1774);
if (x_1776 == 0)
{
lean_object* x_1777; lean_object* x_1778; 
x_1777 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1771);
lean_ctor_set(x_1751, 1, x_1777);
lean_ctor_set(x_1751, 0, x_1768);
if (lean_is_scalar(x_1732)) {
 x_1778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1778 = x_1732;
}
lean_ctor_set(x_1778, 0, x_1751);
lean_ctor_set(x_1778, 1, x_1731);
return x_1778;
}
else
{
lean_object* x_1779; 
lean_ctor_set(x_1751, 1, x_1771);
lean_ctor_set(x_1751, 0, x_1768);
if (lean_is_scalar(x_1732)) {
 x_1779 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1779 = x_1732;
}
lean_ctor_set(x_1779, 0, x_1751);
lean_ctor_set(x_1779, 1, x_1731);
return x_1779;
}
}
else
{
lean_object* x_1780; 
lean_dec(x_1765);
lean_dec(x_1750);
if (lean_is_scalar(x_1732)) {
 x_1780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1780 = x_1732;
}
lean_ctor_set(x_1780, 0, x_1751);
lean_ctor_set(x_1780, 1, x_1731);
return x_1780;
}
}
else
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; uint64_t x_1784; uint64_t x_1785; uint64_t x_1786; uint64_t x_1787; uint64_t x_1788; size_t x_1789; size_t x_1790; size_t x_1791; size_t x_1792; lean_object* x_1793; uint8_t x_1794; 
x_1781 = lean_ctor_get(x_1751, 0);
x_1782 = lean_ctor_get(x_1751, 1);
lean_inc(x_1782);
lean_inc(x_1781);
lean_dec(x_1751);
x_1783 = lean_array_get_size(x_1782);
x_1784 = l_Lean_Expr_hash(x_1750);
x_1785 = lean_uint64_shift_right(x_1784, x_1736);
x_1786 = lean_uint64_xor(x_1784, x_1785);
x_1787 = lean_uint64_shift_right(x_1786, x_1739);
x_1788 = lean_uint64_xor(x_1786, x_1787);
x_1789 = lean_uint64_to_usize(x_1788);
x_1790 = lean_usize_of_nat(x_1783);
lean_dec(x_1783);
x_1791 = lean_usize_sub(x_1790, x_1743);
x_1792 = lean_usize_land(x_1789, x_1791);
x_1793 = lean_array_uget(x_1782, x_1792);
x_1794 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1750, x_1793);
if (x_1794 == 0)
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; uint8_t x_1804; 
x_1795 = lean_unsigned_to_nat(1u);
x_1796 = lean_nat_add(x_1781, x_1795);
lean_dec(x_1781);
x_1797 = lean_box(0);
x_1798 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1798, 0, x_1750);
lean_ctor_set(x_1798, 1, x_1797);
lean_ctor_set(x_1798, 2, x_1793);
x_1799 = lean_array_uset(x_1782, x_1792, x_1798);
x_1800 = lean_nat_mul(x_1796, x_1709);
x_1801 = lean_unsigned_to_nat(3u);
x_1802 = lean_nat_div(x_1800, x_1801);
lean_dec(x_1800);
x_1803 = lean_array_get_size(x_1799);
x_1804 = lean_nat_dec_le(x_1802, x_1803);
lean_dec(x_1803);
lean_dec(x_1802);
if (x_1804 == 0)
{
lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; 
x_1805 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1799);
x_1806 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1806, 0, x_1796);
lean_ctor_set(x_1806, 1, x_1805);
if (lean_is_scalar(x_1732)) {
 x_1807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1807 = x_1732;
}
lean_ctor_set(x_1807, 0, x_1806);
lean_ctor_set(x_1807, 1, x_1731);
return x_1807;
}
else
{
lean_object* x_1808; lean_object* x_1809; 
x_1808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1808, 0, x_1796);
lean_ctor_set(x_1808, 1, x_1799);
if (lean_is_scalar(x_1732)) {
 x_1809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1809 = x_1732;
}
lean_ctor_set(x_1809, 0, x_1808);
lean_ctor_set(x_1809, 1, x_1731);
return x_1809;
}
}
else
{
lean_object* x_1810; lean_object* x_1811; 
lean_dec(x_1793);
lean_dec(x_1750);
x_1810 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1810, 0, x_1781);
lean_ctor_set(x_1810, 1, x_1782);
if (lean_is_scalar(x_1732)) {
 x_1811 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1811 = x_1732;
}
lean_ctor_set(x_1811, 0, x_1810);
lean_ctor_set(x_1811, 1, x_1731);
return x_1811;
}
}
}
}
else
{
uint8_t x_1823; 
lean_dec(x_1727);
lean_dec(x_1712);
lean_dec(x_1710);
lean_dec(x_117);
x_1823 = !lean_is_exclusive(x_1729);
if (x_1823 == 0)
{
return x_1729;
}
else
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; 
x_1824 = lean_ctor_get(x_1729, 0);
x_1825 = lean_ctor_get(x_1729, 1);
lean_inc(x_1825);
lean_inc(x_1824);
lean_dec(x_1729);
x_1826 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1826, 0, x_1824);
lean_ctor_set(x_1826, 1, x_1825);
return x_1826;
}
}
}
else
{
uint8_t x_1827; 
lean_dec(x_1725);
lean_dec(x_1712);
lean_dec(x_1710);
lean_dec(x_117);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1827 = !lean_is_exclusive(x_1726);
if (x_1827 == 0)
{
return x_1726;
}
else
{
lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; 
x_1828 = lean_ctor_get(x_1726, 0);
x_1829 = lean_ctor_get(x_1726, 1);
lean_inc(x_1829);
lean_inc(x_1828);
lean_dec(x_1726);
x_1830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1830, 0, x_1828);
lean_ctor_set(x_1830, 1, x_1829);
return x_1830;
}
}
}
}
else
{
lean_object* x_1835; lean_object* x_1836; 
lean_dec(x_1712);
lean_dec(x_1710);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1835 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_1836 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1836 = x_117;
}
lean_ctor_set(x_1836, 0, x_1835);
lean_ctor_set(x_1836, 1, x_11);
return x_1836;
}
}
}
}
}
}
else
{
lean_object* x_1837; uint8_t x_1838; 
lean_dec(x_119);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1837 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_1838 = lean_string_dec_eq(x_118, x_1837);
lean_dec(x_118);
if (x_1838 == 0)
{
lean_object* x_1839; lean_object* x_1840; 
lean_dec(x_116);
x_1839 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_1840 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1840 = x_117;
}
lean_ctor_set(x_1840, 0, x_1839);
lean_ctor_set(x_1840, 1, x_11);
return x_1840;
}
else
{
lean_object* x_1841; lean_object* x_1842; uint8_t x_1843; 
x_1841 = lean_array_get_size(x_116);
x_1842 = lean_unsigned_to_nat(3u);
x_1843 = lean_nat_dec_eq(x_1841, x_1842);
lean_dec(x_1841);
if (x_1843 == 0)
{
lean_object* x_1844; lean_object* x_1845; 
lean_dec(x_116);
x_1844 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_1845 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1845 = x_117;
}
lean_ctor_set(x_1845, 0, x_1844);
lean_ctor_set(x_1845, 1, x_11);
return x_1845;
}
else
{
lean_object* x_1846; lean_object* x_1847; 
x_1846 = lean_unsigned_to_nat(0u);
x_1847 = lean_array_fget(x_116, x_1846);
if (lean_obj_tag(x_1847) == 4)
{
lean_object* x_1848; 
x_1848 = lean_ctor_get(x_1847, 0);
lean_inc(x_1848);
if (lean_obj_tag(x_1848) == 1)
{
lean_object* x_1849; 
x_1849 = lean_ctor_get(x_1848, 0);
lean_inc(x_1849);
if (lean_obj_tag(x_1849) == 0)
{
lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; uint8_t x_1853; 
x_1850 = lean_ctor_get(x_1847, 1);
lean_inc(x_1850);
lean_dec(x_1847);
x_1851 = lean_ctor_get(x_1848, 1);
lean_inc(x_1851);
lean_dec(x_1848);
x_1852 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_1853 = lean_string_dec_eq(x_1851, x_1852);
lean_dec(x_1851);
if (x_1853 == 0)
{
lean_object* x_1854; lean_object* x_1855; 
lean_dec(x_1850);
lean_dec(x_116);
x_1854 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_1855 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1855 = x_117;
}
lean_ctor_set(x_1855, 0, x_1854);
lean_ctor_set(x_1855, 1, x_11);
return x_1855;
}
else
{
if (lean_obj_tag(x_1850) == 0)
{
lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_2563; lean_object* x_2564; uint64_t x_2565; uint64_t x_2566; uint64_t x_2567; uint64_t x_2568; uint64_t x_2569; uint64_t x_2570; uint64_t x_2571; size_t x_2572; size_t x_2573; size_t x_2574; lean_object* x_2575; lean_object* x_2576; uint8_t x_2577; 
x_1856 = lean_unsigned_to_nat(2u);
x_1857 = lean_array_fget(x_116, x_1856);
lean_dec(x_116);
x_2563 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__114;
lean_inc(x_1857);
x_2564 = l_Lean_Expr_app___override(x_2563, x_1857);
x_2565 = l_Lean_Expr_hash(x_2564);
x_2566 = 32;
x_2567 = lean_uint64_shift_right(x_2565, x_2566);
x_2568 = lean_uint64_xor(x_2565, x_2567);
x_2569 = 16;
x_2570 = lean_uint64_shift_right(x_2568, x_2569);
x_2571 = lean_uint64_xor(x_2568, x_2570);
x_2572 = lean_uint64_to_usize(x_2571);
x_2573 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_2574 = lean_usize_land(x_2572, x_2573);
x_2575 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_2576 = lean_array_uget(x_2575, x_2574);
x_2577 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2564, x_2576);
if (x_2577 == 0)
{
lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; uint8_t x_2583; 
x_2578 = lean_box(0);
x_2579 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2579, 0, x_2564);
lean_ctor_set(x_2579, 1, x_2578);
lean_ctor_set(x_2579, 2, x_2576);
x_2580 = lean_array_uset(x_2575, x_2574, x_2579);
x_2581 = lean_array_get_size(x_2580);
x_2582 = lean_unsigned_to_nat(1u);
x_2583 = lean_nat_dec_le(x_2582, x_2581);
lean_dec(x_2581);
if (x_2583 == 0)
{
lean_object* x_2584; lean_object* x_2585; 
x_2584 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2580);
if (lean_is_scalar(x_117)) {
 x_2585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2585 = x_117;
}
lean_ctor_set(x_2585, 0, x_2582);
lean_ctor_set(x_2585, 1, x_2584);
x_1858 = x_2585;
goto block_2562;
}
else
{
lean_object* x_2586; 
if (lean_is_scalar(x_117)) {
 x_2586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2586 = x_117;
}
lean_ctor_set(x_2586, 0, x_2582);
lean_ctor_set(x_2586, 1, x_2580);
x_1858 = x_2586;
goto block_2562;
}
}
else
{
lean_object* x_2587; 
lean_dec(x_2576);
lean_dec(x_2564);
lean_dec(x_117);
x_2587 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_1858 = x_2587;
goto block_2562;
}
block_2562:
{
uint8_t x_1859; lean_object* x_1860; 
x_1859 = lean_ctor_get_uint8(x_4, 1);
x_1860 = l_Lean_Expr_getAppFnArgs(x_1857);
if (x_1859 == 0)
{
lean_object* x_1861; 
x_1861 = lean_ctor_get(x_1860, 0);
lean_inc(x_1861);
if (lean_obj_tag(x_1861) == 1)
{
lean_object* x_1862; 
x_1862 = lean_ctor_get(x_1861, 0);
lean_inc(x_1862);
if (lean_obj_tag(x_1862) == 1)
{
lean_object* x_1863; 
x_1863 = lean_ctor_get(x_1862, 0);
lean_inc(x_1863);
if (lean_obj_tag(x_1863) == 0)
{
lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; uint8_t x_1868; 
x_1864 = lean_ctor_get(x_1860, 1);
lean_inc(x_1864);
if (lean_is_exclusive(x_1860)) {
 lean_ctor_release(x_1860, 0);
 lean_ctor_release(x_1860, 1);
 x_1865 = x_1860;
} else {
 lean_dec_ref(x_1860);
 x_1865 = lean_box(0);
}
x_1866 = lean_ctor_get(x_1861, 1);
lean_inc(x_1866);
lean_dec(x_1861);
x_1867 = lean_ctor_get(x_1862, 1);
lean_inc(x_1867);
lean_dec(x_1862);
x_1868 = lean_string_dec_eq(x_1867, x_1852);
if (x_1868 == 0)
{
lean_object* x_1869; uint8_t x_1870; 
x_1869 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_1870 = lean_string_dec_eq(x_1867, x_1869);
if (x_1870 == 0)
{
lean_object* x_1871; uint8_t x_1872; 
x_1871 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_1872 = lean_string_dec_eq(x_1867, x_1871);
lean_dec(x_1867);
if (x_1872 == 0)
{
lean_object* x_1873; 
lean_dec(x_1866);
lean_dec(x_1864);
if (lean_is_scalar(x_1865)) {
 x_1873 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1873 = x_1865;
}
lean_ctor_set(x_1873, 0, x_1858);
lean_ctor_set(x_1873, 1, x_11);
return x_1873;
}
else
{
lean_object* x_1874; uint8_t x_1875; 
x_1874 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97;
x_1875 = lean_string_dec_eq(x_1866, x_1874);
lean_dec(x_1866);
if (x_1875 == 0)
{
lean_object* x_1876; 
lean_dec(x_1864);
if (lean_is_scalar(x_1865)) {
 x_1876 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1876 = x_1865;
}
lean_ctor_set(x_1876, 0, x_1858);
lean_ctor_set(x_1876, 1, x_11);
return x_1876;
}
else
{
lean_object* x_1877; uint8_t x_1878; 
x_1877 = lean_array_get_size(x_1864);
x_1878 = lean_nat_dec_eq(x_1877, x_1856);
lean_dec(x_1877);
if (x_1878 == 0)
{
lean_object* x_1879; 
lean_dec(x_1864);
if (lean_is_scalar(x_1865)) {
 x_1879 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1879 = x_1865;
}
lean_ctor_set(x_1879, 0, x_1858);
lean_ctor_set(x_1879, 1, x_11);
return x_1879;
}
else
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; uint8_t x_1885; 
x_1880 = lean_array_fget(x_1864, x_1846);
x_1881 = lean_unsigned_to_nat(1u);
x_1882 = lean_array_fget(x_1864, x_1881);
lean_dec(x_1864);
x_1883 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_1884 = l_Lean_mkAppB(x_1883, x_1880, x_1882);
x_1885 = !lean_is_exclusive(x_1858);
if (x_1885 == 0)
{
lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; uint64_t x_1889; uint64_t x_1890; uint64_t x_1891; uint64_t x_1892; uint64_t x_1893; uint64_t x_1894; uint64_t x_1895; size_t x_1896; size_t x_1897; size_t x_1898; size_t x_1899; size_t x_1900; lean_object* x_1901; uint8_t x_1902; 
x_1886 = lean_ctor_get(x_1858, 0);
x_1887 = lean_ctor_get(x_1858, 1);
x_1888 = lean_array_get_size(x_1887);
x_1889 = l_Lean_Expr_hash(x_1884);
x_1890 = 32;
x_1891 = lean_uint64_shift_right(x_1889, x_1890);
x_1892 = lean_uint64_xor(x_1889, x_1891);
x_1893 = 16;
x_1894 = lean_uint64_shift_right(x_1892, x_1893);
x_1895 = lean_uint64_xor(x_1892, x_1894);
x_1896 = lean_uint64_to_usize(x_1895);
x_1897 = lean_usize_of_nat(x_1888);
lean_dec(x_1888);
x_1898 = 1;
x_1899 = lean_usize_sub(x_1897, x_1898);
x_1900 = lean_usize_land(x_1896, x_1899);
x_1901 = lean_array_uget(x_1887, x_1900);
x_1902 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1884, x_1901);
if (x_1902 == 0)
{
lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; uint8_t x_1911; 
x_1903 = lean_nat_add(x_1886, x_1881);
lean_dec(x_1886);
x_1904 = lean_box(0);
x_1905 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1905, 0, x_1884);
lean_ctor_set(x_1905, 1, x_1904);
lean_ctor_set(x_1905, 2, x_1901);
x_1906 = lean_array_uset(x_1887, x_1900, x_1905);
x_1907 = lean_unsigned_to_nat(4u);
x_1908 = lean_nat_mul(x_1903, x_1907);
x_1909 = lean_nat_div(x_1908, x_1842);
lean_dec(x_1908);
x_1910 = lean_array_get_size(x_1906);
x_1911 = lean_nat_dec_le(x_1909, x_1910);
lean_dec(x_1910);
lean_dec(x_1909);
if (x_1911 == 0)
{
lean_object* x_1912; lean_object* x_1913; 
x_1912 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1906);
lean_ctor_set(x_1858, 1, x_1912);
lean_ctor_set(x_1858, 0, x_1903);
if (lean_is_scalar(x_1865)) {
 x_1913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1913 = x_1865;
}
lean_ctor_set(x_1913, 0, x_1858);
lean_ctor_set(x_1913, 1, x_11);
return x_1913;
}
else
{
lean_object* x_1914; 
lean_ctor_set(x_1858, 1, x_1906);
lean_ctor_set(x_1858, 0, x_1903);
if (lean_is_scalar(x_1865)) {
 x_1914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1914 = x_1865;
}
lean_ctor_set(x_1914, 0, x_1858);
lean_ctor_set(x_1914, 1, x_11);
return x_1914;
}
}
else
{
lean_object* x_1915; 
lean_dec(x_1901);
lean_dec(x_1884);
if (lean_is_scalar(x_1865)) {
 x_1915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1915 = x_1865;
}
lean_ctor_set(x_1915, 0, x_1858);
lean_ctor_set(x_1915, 1, x_11);
return x_1915;
}
}
else
{
lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; uint64_t x_1919; uint64_t x_1920; uint64_t x_1921; uint64_t x_1922; uint64_t x_1923; uint64_t x_1924; uint64_t x_1925; size_t x_1926; size_t x_1927; size_t x_1928; size_t x_1929; size_t x_1930; lean_object* x_1931; uint8_t x_1932; 
x_1916 = lean_ctor_get(x_1858, 0);
x_1917 = lean_ctor_get(x_1858, 1);
lean_inc(x_1917);
lean_inc(x_1916);
lean_dec(x_1858);
x_1918 = lean_array_get_size(x_1917);
x_1919 = l_Lean_Expr_hash(x_1884);
x_1920 = 32;
x_1921 = lean_uint64_shift_right(x_1919, x_1920);
x_1922 = lean_uint64_xor(x_1919, x_1921);
x_1923 = 16;
x_1924 = lean_uint64_shift_right(x_1922, x_1923);
x_1925 = lean_uint64_xor(x_1922, x_1924);
x_1926 = lean_uint64_to_usize(x_1925);
x_1927 = lean_usize_of_nat(x_1918);
lean_dec(x_1918);
x_1928 = 1;
x_1929 = lean_usize_sub(x_1927, x_1928);
x_1930 = lean_usize_land(x_1926, x_1929);
x_1931 = lean_array_uget(x_1917, x_1930);
x_1932 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1884, x_1931);
if (x_1932 == 0)
{
lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; uint8_t x_1941; 
x_1933 = lean_nat_add(x_1916, x_1881);
lean_dec(x_1916);
x_1934 = lean_box(0);
x_1935 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1935, 0, x_1884);
lean_ctor_set(x_1935, 1, x_1934);
lean_ctor_set(x_1935, 2, x_1931);
x_1936 = lean_array_uset(x_1917, x_1930, x_1935);
x_1937 = lean_unsigned_to_nat(4u);
x_1938 = lean_nat_mul(x_1933, x_1937);
x_1939 = lean_nat_div(x_1938, x_1842);
lean_dec(x_1938);
x_1940 = lean_array_get_size(x_1936);
x_1941 = lean_nat_dec_le(x_1939, x_1940);
lean_dec(x_1940);
lean_dec(x_1939);
if (x_1941 == 0)
{
lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; 
x_1942 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1936);
x_1943 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1943, 0, x_1933);
lean_ctor_set(x_1943, 1, x_1942);
if (lean_is_scalar(x_1865)) {
 x_1944 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1944 = x_1865;
}
lean_ctor_set(x_1944, 0, x_1943);
lean_ctor_set(x_1944, 1, x_11);
return x_1944;
}
else
{
lean_object* x_1945; lean_object* x_1946; 
x_1945 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1945, 0, x_1933);
lean_ctor_set(x_1945, 1, x_1936);
if (lean_is_scalar(x_1865)) {
 x_1946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1946 = x_1865;
}
lean_ctor_set(x_1946, 0, x_1945);
lean_ctor_set(x_1946, 1, x_11);
return x_1946;
}
}
else
{
lean_object* x_1947; lean_object* x_1948; 
lean_dec(x_1931);
lean_dec(x_1884);
x_1947 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1947, 0, x_1916);
lean_ctor_set(x_1947, 1, x_1917);
if (lean_is_scalar(x_1865)) {
 x_1948 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1948 = x_1865;
}
lean_ctor_set(x_1948, 0, x_1947);
lean_ctor_set(x_1948, 1, x_11);
return x_1948;
}
}
}
}
}
}
else
{
lean_object* x_1949; uint8_t x_1950; 
lean_dec(x_1867);
x_1949 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101;
x_1950 = lean_string_dec_eq(x_1866, x_1949);
lean_dec(x_1866);
if (x_1950 == 0)
{
lean_object* x_1951; 
lean_dec(x_1864);
if (lean_is_scalar(x_1865)) {
 x_1951 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1951 = x_1865;
}
lean_ctor_set(x_1951, 0, x_1858);
lean_ctor_set(x_1951, 1, x_11);
return x_1951;
}
else
{
lean_object* x_1952; uint8_t x_1953; 
x_1952 = lean_array_get_size(x_1864);
x_1953 = lean_nat_dec_eq(x_1952, x_1856);
lean_dec(x_1952);
if (x_1953 == 0)
{
lean_object* x_1954; 
lean_dec(x_1864);
if (lean_is_scalar(x_1865)) {
 x_1954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1954 = x_1865;
}
lean_ctor_set(x_1954, 0, x_1858);
lean_ctor_set(x_1954, 1, x_11);
return x_1954;
}
else
{
lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; uint8_t x_1960; 
x_1955 = lean_array_fget(x_1864, x_1846);
x_1956 = lean_unsigned_to_nat(1u);
x_1957 = lean_array_fget(x_1864, x_1956);
lean_dec(x_1864);
x_1958 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_1959 = l_Lean_mkAppB(x_1958, x_1955, x_1957);
x_1960 = !lean_is_exclusive(x_1858);
if (x_1960 == 0)
{
lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; uint64_t x_1964; uint64_t x_1965; uint64_t x_1966; uint64_t x_1967; uint64_t x_1968; uint64_t x_1969; uint64_t x_1970; size_t x_1971; size_t x_1972; size_t x_1973; size_t x_1974; size_t x_1975; lean_object* x_1976; uint8_t x_1977; 
x_1961 = lean_ctor_get(x_1858, 0);
x_1962 = lean_ctor_get(x_1858, 1);
x_1963 = lean_array_get_size(x_1962);
x_1964 = l_Lean_Expr_hash(x_1959);
x_1965 = 32;
x_1966 = lean_uint64_shift_right(x_1964, x_1965);
x_1967 = lean_uint64_xor(x_1964, x_1966);
x_1968 = 16;
x_1969 = lean_uint64_shift_right(x_1967, x_1968);
x_1970 = lean_uint64_xor(x_1967, x_1969);
x_1971 = lean_uint64_to_usize(x_1970);
x_1972 = lean_usize_of_nat(x_1963);
lean_dec(x_1963);
x_1973 = 1;
x_1974 = lean_usize_sub(x_1972, x_1973);
x_1975 = lean_usize_land(x_1971, x_1974);
x_1976 = lean_array_uget(x_1962, x_1975);
x_1977 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1959, x_1976);
if (x_1977 == 0)
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; uint8_t x_1986; 
x_1978 = lean_nat_add(x_1961, x_1956);
lean_dec(x_1961);
x_1979 = lean_box(0);
x_1980 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1980, 0, x_1959);
lean_ctor_set(x_1980, 1, x_1979);
lean_ctor_set(x_1980, 2, x_1976);
x_1981 = lean_array_uset(x_1962, x_1975, x_1980);
x_1982 = lean_unsigned_to_nat(4u);
x_1983 = lean_nat_mul(x_1978, x_1982);
x_1984 = lean_nat_div(x_1983, x_1842);
lean_dec(x_1983);
x_1985 = lean_array_get_size(x_1981);
x_1986 = lean_nat_dec_le(x_1984, x_1985);
lean_dec(x_1985);
lean_dec(x_1984);
if (x_1986 == 0)
{
lean_object* x_1987; lean_object* x_1988; 
x_1987 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_1981);
lean_ctor_set(x_1858, 1, x_1987);
lean_ctor_set(x_1858, 0, x_1978);
if (lean_is_scalar(x_1865)) {
 x_1988 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1988 = x_1865;
}
lean_ctor_set(x_1988, 0, x_1858);
lean_ctor_set(x_1988, 1, x_11);
return x_1988;
}
else
{
lean_object* x_1989; 
lean_ctor_set(x_1858, 1, x_1981);
lean_ctor_set(x_1858, 0, x_1978);
if (lean_is_scalar(x_1865)) {
 x_1989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1989 = x_1865;
}
lean_ctor_set(x_1989, 0, x_1858);
lean_ctor_set(x_1989, 1, x_11);
return x_1989;
}
}
else
{
lean_object* x_1990; 
lean_dec(x_1976);
lean_dec(x_1959);
if (lean_is_scalar(x_1865)) {
 x_1990 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1990 = x_1865;
}
lean_ctor_set(x_1990, 0, x_1858);
lean_ctor_set(x_1990, 1, x_11);
return x_1990;
}
}
else
{
lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; uint64_t x_1994; uint64_t x_1995; uint64_t x_1996; uint64_t x_1997; uint64_t x_1998; uint64_t x_1999; uint64_t x_2000; size_t x_2001; size_t x_2002; size_t x_2003; size_t x_2004; size_t x_2005; lean_object* x_2006; uint8_t x_2007; 
x_1991 = lean_ctor_get(x_1858, 0);
x_1992 = lean_ctor_get(x_1858, 1);
lean_inc(x_1992);
lean_inc(x_1991);
lean_dec(x_1858);
x_1993 = lean_array_get_size(x_1992);
x_1994 = l_Lean_Expr_hash(x_1959);
x_1995 = 32;
x_1996 = lean_uint64_shift_right(x_1994, x_1995);
x_1997 = lean_uint64_xor(x_1994, x_1996);
x_1998 = 16;
x_1999 = lean_uint64_shift_right(x_1997, x_1998);
x_2000 = lean_uint64_xor(x_1997, x_1999);
x_2001 = lean_uint64_to_usize(x_2000);
x_2002 = lean_usize_of_nat(x_1993);
lean_dec(x_1993);
x_2003 = 1;
x_2004 = lean_usize_sub(x_2002, x_2003);
x_2005 = lean_usize_land(x_2001, x_2004);
x_2006 = lean_array_uget(x_1992, x_2005);
x_2007 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_1959, x_2006);
if (x_2007 == 0)
{
lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; uint8_t x_2016; 
x_2008 = lean_nat_add(x_1991, x_1956);
lean_dec(x_1991);
x_2009 = lean_box(0);
x_2010 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2010, 0, x_1959);
lean_ctor_set(x_2010, 1, x_2009);
lean_ctor_set(x_2010, 2, x_2006);
x_2011 = lean_array_uset(x_1992, x_2005, x_2010);
x_2012 = lean_unsigned_to_nat(4u);
x_2013 = lean_nat_mul(x_2008, x_2012);
x_2014 = lean_nat_div(x_2013, x_1842);
lean_dec(x_2013);
x_2015 = lean_array_get_size(x_2011);
x_2016 = lean_nat_dec_le(x_2014, x_2015);
lean_dec(x_2015);
lean_dec(x_2014);
if (x_2016 == 0)
{
lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; 
x_2017 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2011);
x_2018 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2018, 0, x_2008);
lean_ctor_set(x_2018, 1, x_2017);
if (lean_is_scalar(x_1865)) {
 x_2019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2019 = x_1865;
}
lean_ctor_set(x_2019, 0, x_2018);
lean_ctor_set(x_2019, 1, x_11);
return x_2019;
}
else
{
lean_object* x_2020; lean_object* x_2021; 
x_2020 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2020, 0, x_2008);
lean_ctor_set(x_2020, 1, x_2011);
if (lean_is_scalar(x_1865)) {
 x_2021 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2021 = x_1865;
}
lean_ctor_set(x_2021, 0, x_2020);
lean_ctor_set(x_2021, 1, x_11);
return x_2021;
}
}
else
{
lean_object* x_2022; lean_object* x_2023; 
lean_dec(x_2006);
lean_dec(x_1959);
x_2022 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2022, 0, x_1991);
lean_ctor_set(x_2022, 1, x_1992);
if (lean_is_scalar(x_1865)) {
 x_2023 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2023 = x_1865;
}
lean_ctor_set(x_2023, 0, x_2022);
lean_ctor_set(x_2023, 1, x_11);
return x_2023;
}
}
}
}
}
}
else
{
lean_object* x_2024; uint8_t x_2025; 
lean_dec(x_1867);
x_2024 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104;
x_2025 = lean_string_dec_eq(x_1866, x_2024);
lean_dec(x_1866);
if (x_2025 == 0)
{
lean_object* x_2026; 
lean_dec(x_1864);
if (lean_is_scalar(x_1865)) {
 x_2026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2026 = x_1865;
}
lean_ctor_set(x_2026, 0, x_1858);
lean_ctor_set(x_2026, 1, x_11);
return x_2026;
}
else
{
lean_object* x_2027; lean_object* x_2028; uint8_t x_2029; 
x_2027 = lean_array_get_size(x_1864);
x_2028 = lean_unsigned_to_nat(1u);
x_2029 = lean_nat_dec_eq(x_2027, x_2028);
lean_dec(x_2027);
if (x_2029 == 0)
{
lean_object* x_2030; 
lean_dec(x_1864);
if (lean_is_scalar(x_1865)) {
 x_2030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2030 = x_1865;
}
lean_ctor_set(x_2030, 0, x_1858);
lean_ctor_set(x_2030, 1, x_11);
return x_2030;
}
else
{
lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; uint8_t x_2102; 
x_2031 = lean_array_fget(x_1864, x_1846);
lean_dec(x_1864);
x_2032 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107;
lean_inc(x_2031);
x_2033 = l_Lean_Expr_app___override(x_2032, x_2031);
x_2034 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110;
x_2035 = l_Lean_Expr_app___override(x_2034, x_2031);
x_2102 = !lean_is_exclusive(x_1858);
if (x_2102 == 0)
{
lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; uint64_t x_2106; uint64_t x_2107; uint64_t x_2108; uint64_t x_2109; uint64_t x_2110; uint64_t x_2111; uint64_t x_2112; size_t x_2113; size_t x_2114; size_t x_2115; size_t x_2116; size_t x_2117; lean_object* x_2118; uint8_t x_2119; 
x_2103 = lean_ctor_get(x_1858, 0);
x_2104 = lean_ctor_get(x_1858, 1);
x_2105 = lean_array_get_size(x_2104);
x_2106 = l_Lean_Expr_hash(x_2033);
x_2107 = 32;
x_2108 = lean_uint64_shift_right(x_2106, x_2107);
x_2109 = lean_uint64_xor(x_2106, x_2108);
x_2110 = 16;
x_2111 = lean_uint64_shift_right(x_2109, x_2110);
x_2112 = lean_uint64_xor(x_2109, x_2111);
x_2113 = lean_uint64_to_usize(x_2112);
x_2114 = lean_usize_of_nat(x_2105);
lean_dec(x_2105);
x_2115 = 1;
x_2116 = lean_usize_sub(x_2114, x_2115);
x_2117 = lean_usize_land(x_2113, x_2116);
x_2118 = lean_array_uget(x_2104, x_2117);
x_2119 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2033, x_2118);
if (x_2119 == 0)
{
lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; uint8_t x_2128; 
x_2120 = lean_nat_add(x_2103, x_2028);
lean_dec(x_2103);
x_2121 = lean_box(0);
x_2122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2122, 0, x_2033);
lean_ctor_set(x_2122, 1, x_2121);
lean_ctor_set(x_2122, 2, x_2118);
x_2123 = lean_array_uset(x_2104, x_2117, x_2122);
x_2124 = lean_unsigned_to_nat(4u);
x_2125 = lean_nat_mul(x_2120, x_2124);
x_2126 = lean_nat_div(x_2125, x_1842);
lean_dec(x_2125);
x_2127 = lean_array_get_size(x_2123);
x_2128 = lean_nat_dec_le(x_2126, x_2127);
lean_dec(x_2127);
lean_dec(x_2126);
if (x_2128 == 0)
{
lean_object* x_2129; 
x_2129 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2123);
lean_ctor_set(x_1858, 1, x_2129);
lean_ctor_set(x_1858, 0, x_2120);
x_2036 = x_1858;
goto block_2101;
}
else
{
lean_ctor_set(x_1858, 1, x_2123);
lean_ctor_set(x_1858, 0, x_2120);
x_2036 = x_1858;
goto block_2101;
}
}
else
{
lean_dec(x_2118);
lean_dec(x_2033);
x_2036 = x_1858;
goto block_2101;
}
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; uint64_t x_2133; uint64_t x_2134; uint64_t x_2135; uint64_t x_2136; uint64_t x_2137; uint64_t x_2138; uint64_t x_2139; size_t x_2140; size_t x_2141; size_t x_2142; size_t x_2143; size_t x_2144; lean_object* x_2145; uint8_t x_2146; 
x_2130 = lean_ctor_get(x_1858, 0);
x_2131 = lean_ctor_get(x_1858, 1);
lean_inc(x_2131);
lean_inc(x_2130);
lean_dec(x_1858);
x_2132 = lean_array_get_size(x_2131);
x_2133 = l_Lean_Expr_hash(x_2033);
x_2134 = 32;
x_2135 = lean_uint64_shift_right(x_2133, x_2134);
x_2136 = lean_uint64_xor(x_2133, x_2135);
x_2137 = 16;
x_2138 = lean_uint64_shift_right(x_2136, x_2137);
x_2139 = lean_uint64_xor(x_2136, x_2138);
x_2140 = lean_uint64_to_usize(x_2139);
x_2141 = lean_usize_of_nat(x_2132);
lean_dec(x_2132);
x_2142 = 1;
x_2143 = lean_usize_sub(x_2141, x_2142);
x_2144 = lean_usize_land(x_2140, x_2143);
x_2145 = lean_array_uget(x_2131, x_2144);
x_2146 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2033, x_2145);
if (x_2146 == 0)
{
lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; uint8_t x_2155; 
x_2147 = lean_nat_add(x_2130, x_2028);
lean_dec(x_2130);
x_2148 = lean_box(0);
x_2149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2149, 0, x_2033);
lean_ctor_set(x_2149, 1, x_2148);
lean_ctor_set(x_2149, 2, x_2145);
x_2150 = lean_array_uset(x_2131, x_2144, x_2149);
x_2151 = lean_unsigned_to_nat(4u);
x_2152 = lean_nat_mul(x_2147, x_2151);
x_2153 = lean_nat_div(x_2152, x_1842);
lean_dec(x_2152);
x_2154 = lean_array_get_size(x_2150);
x_2155 = lean_nat_dec_le(x_2153, x_2154);
lean_dec(x_2154);
lean_dec(x_2153);
if (x_2155 == 0)
{
lean_object* x_2156; lean_object* x_2157; 
x_2156 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2150);
x_2157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2157, 0, x_2147);
lean_ctor_set(x_2157, 1, x_2156);
x_2036 = x_2157;
goto block_2101;
}
else
{
lean_object* x_2158; 
x_2158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2158, 0, x_2147);
lean_ctor_set(x_2158, 1, x_2150);
x_2036 = x_2158;
goto block_2101;
}
}
else
{
lean_object* x_2159; 
lean_dec(x_2145);
lean_dec(x_2033);
x_2159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2159, 0, x_2130);
lean_ctor_set(x_2159, 1, x_2131);
x_2036 = x_2159;
goto block_2101;
}
}
block_2101:
{
uint8_t x_2037; 
x_2037 = !lean_is_exclusive(x_2036);
if (x_2037 == 0)
{
lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; uint64_t x_2041; uint64_t x_2042; uint64_t x_2043; uint64_t x_2044; uint64_t x_2045; uint64_t x_2046; uint64_t x_2047; size_t x_2048; size_t x_2049; size_t x_2050; size_t x_2051; size_t x_2052; lean_object* x_2053; uint8_t x_2054; 
x_2038 = lean_ctor_get(x_2036, 0);
x_2039 = lean_ctor_get(x_2036, 1);
x_2040 = lean_array_get_size(x_2039);
x_2041 = l_Lean_Expr_hash(x_2035);
x_2042 = 32;
x_2043 = lean_uint64_shift_right(x_2041, x_2042);
x_2044 = lean_uint64_xor(x_2041, x_2043);
x_2045 = 16;
x_2046 = lean_uint64_shift_right(x_2044, x_2045);
x_2047 = lean_uint64_xor(x_2044, x_2046);
x_2048 = lean_uint64_to_usize(x_2047);
x_2049 = lean_usize_of_nat(x_2040);
lean_dec(x_2040);
x_2050 = 1;
x_2051 = lean_usize_sub(x_2049, x_2050);
x_2052 = lean_usize_land(x_2048, x_2051);
x_2053 = lean_array_uget(x_2039, x_2052);
x_2054 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2035, x_2053);
if (x_2054 == 0)
{
lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; uint8_t x_2063; 
x_2055 = lean_nat_add(x_2038, x_2028);
lean_dec(x_2038);
x_2056 = lean_box(0);
x_2057 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2057, 0, x_2035);
lean_ctor_set(x_2057, 1, x_2056);
lean_ctor_set(x_2057, 2, x_2053);
x_2058 = lean_array_uset(x_2039, x_2052, x_2057);
x_2059 = lean_unsigned_to_nat(4u);
x_2060 = lean_nat_mul(x_2055, x_2059);
x_2061 = lean_nat_div(x_2060, x_1842);
lean_dec(x_2060);
x_2062 = lean_array_get_size(x_2058);
x_2063 = lean_nat_dec_le(x_2061, x_2062);
lean_dec(x_2062);
lean_dec(x_2061);
if (x_2063 == 0)
{
lean_object* x_2064; lean_object* x_2065; 
x_2064 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2058);
lean_ctor_set(x_2036, 1, x_2064);
lean_ctor_set(x_2036, 0, x_2055);
if (lean_is_scalar(x_1865)) {
 x_2065 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2065 = x_1865;
}
lean_ctor_set(x_2065, 0, x_2036);
lean_ctor_set(x_2065, 1, x_11);
return x_2065;
}
else
{
lean_object* x_2066; 
lean_ctor_set(x_2036, 1, x_2058);
lean_ctor_set(x_2036, 0, x_2055);
if (lean_is_scalar(x_1865)) {
 x_2066 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2066 = x_1865;
}
lean_ctor_set(x_2066, 0, x_2036);
lean_ctor_set(x_2066, 1, x_11);
return x_2066;
}
}
else
{
lean_object* x_2067; 
lean_dec(x_2053);
lean_dec(x_2035);
if (lean_is_scalar(x_1865)) {
 x_2067 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2067 = x_1865;
}
lean_ctor_set(x_2067, 0, x_2036);
lean_ctor_set(x_2067, 1, x_11);
return x_2067;
}
}
else
{
lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; uint64_t x_2071; uint64_t x_2072; uint64_t x_2073; uint64_t x_2074; uint64_t x_2075; uint64_t x_2076; uint64_t x_2077; size_t x_2078; size_t x_2079; size_t x_2080; size_t x_2081; size_t x_2082; lean_object* x_2083; uint8_t x_2084; 
x_2068 = lean_ctor_get(x_2036, 0);
x_2069 = lean_ctor_get(x_2036, 1);
lean_inc(x_2069);
lean_inc(x_2068);
lean_dec(x_2036);
x_2070 = lean_array_get_size(x_2069);
x_2071 = l_Lean_Expr_hash(x_2035);
x_2072 = 32;
x_2073 = lean_uint64_shift_right(x_2071, x_2072);
x_2074 = lean_uint64_xor(x_2071, x_2073);
x_2075 = 16;
x_2076 = lean_uint64_shift_right(x_2074, x_2075);
x_2077 = lean_uint64_xor(x_2074, x_2076);
x_2078 = lean_uint64_to_usize(x_2077);
x_2079 = lean_usize_of_nat(x_2070);
lean_dec(x_2070);
x_2080 = 1;
x_2081 = lean_usize_sub(x_2079, x_2080);
x_2082 = lean_usize_land(x_2078, x_2081);
x_2083 = lean_array_uget(x_2069, x_2082);
x_2084 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2035, x_2083);
if (x_2084 == 0)
{
lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; uint8_t x_2093; 
x_2085 = lean_nat_add(x_2068, x_2028);
lean_dec(x_2068);
x_2086 = lean_box(0);
x_2087 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2087, 0, x_2035);
lean_ctor_set(x_2087, 1, x_2086);
lean_ctor_set(x_2087, 2, x_2083);
x_2088 = lean_array_uset(x_2069, x_2082, x_2087);
x_2089 = lean_unsigned_to_nat(4u);
x_2090 = lean_nat_mul(x_2085, x_2089);
x_2091 = lean_nat_div(x_2090, x_1842);
lean_dec(x_2090);
x_2092 = lean_array_get_size(x_2088);
x_2093 = lean_nat_dec_le(x_2091, x_2092);
lean_dec(x_2092);
lean_dec(x_2091);
if (x_2093 == 0)
{
lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; 
x_2094 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2088);
x_2095 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2095, 0, x_2085);
lean_ctor_set(x_2095, 1, x_2094);
if (lean_is_scalar(x_1865)) {
 x_2096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2096 = x_1865;
}
lean_ctor_set(x_2096, 0, x_2095);
lean_ctor_set(x_2096, 1, x_11);
return x_2096;
}
else
{
lean_object* x_2097; lean_object* x_2098; 
x_2097 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2097, 0, x_2085);
lean_ctor_set(x_2097, 1, x_2088);
if (lean_is_scalar(x_1865)) {
 x_2098 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2098 = x_1865;
}
lean_ctor_set(x_2098, 0, x_2097);
lean_ctor_set(x_2098, 1, x_11);
return x_2098;
}
}
else
{
lean_object* x_2099; lean_object* x_2100; 
lean_dec(x_2083);
lean_dec(x_2035);
x_2099 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2099, 0, x_2068);
lean_ctor_set(x_2099, 1, x_2069);
if (lean_is_scalar(x_1865)) {
 x_2100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2100 = x_1865;
}
lean_ctor_set(x_2100, 0, x_2099);
lean_ctor_set(x_2100, 1, x_11);
return x_2100;
}
}
}
}
}
}
}
else
{
uint8_t x_2160; 
lean_dec(x_1863);
lean_dec(x_1862);
lean_dec(x_1861);
x_2160 = !lean_is_exclusive(x_1860);
if (x_2160 == 0)
{
lean_object* x_2161; lean_object* x_2162; 
x_2161 = lean_ctor_get(x_1860, 1);
lean_dec(x_2161);
x_2162 = lean_ctor_get(x_1860, 0);
lean_dec(x_2162);
lean_ctor_set(x_1860, 1, x_11);
lean_ctor_set(x_1860, 0, x_1858);
return x_1860;
}
else
{
lean_object* x_2163; 
lean_dec(x_1860);
x_2163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2163, 0, x_1858);
lean_ctor_set(x_2163, 1, x_11);
return x_2163;
}
}
}
else
{
uint8_t x_2164; 
lean_dec(x_1862);
lean_dec(x_1861);
x_2164 = !lean_is_exclusive(x_1860);
if (x_2164 == 0)
{
lean_object* x_2165; lean_object* x_2166; 
x_2165 = lean_ctor_get(x_1860, 1);
lean_dec(x_2165);
x_2166 = lean_ctor_get(x_1860, 0);
lean_dec(x_2166);
lean_ctor_set(x_1860, 1, x_11);
lean_ctor_set(x_1860, 0, x_1858);
return x_1860;
}
else
{
lean_object* x_2167; 
lean_dec(x_1860);
x_2167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2167, 0, x_1858);
lean_ctor_set(x_2167, 1, x_11);
return x_2167;
}
}
}
else
{
uint8_t x_2168; 
lean_dec(x_1861);
x_2168 = !lean_is_exclusive(x_1860);
if (x_2168 == 0)
{
lean_object* x_2169; lean_object* x_2170; 
x_2169 = lean_ctor_get(x_1860, 1);
lean_dec(x_2169);
x_2170 = lean_ctor_get(x_1860, 0);
lean_dec(x_2170);
lean_ctor_set(x_1860, 1, x_11);
lean_ctor_set(x_1860, 0, x_1858);
return x_1860;
}
else
{
lean_object* x_2171; 
lean_dec(x_1860);
x_2171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2171, 0, x_1858);
lean_ctor_set(x_2171, 1, x_11);
return x_2171;
}
}
}
else
{
lean_object* x_2172; 
x_2172 = lean_ctor_get(x_1860, 0);
lean_inc(x_2172);
if (lean_obj_tag(x_2172) == 1)
{
lean_object* x_2173; 
x_2173 = lean_ctor_get(x_2172, 0);
lean_inc(x_2173);
if (lean_obj_tag(x_2173) == 1)
{
lean_object* x_2174; 
x_2174 = lean_ctor_get(x_2173, 0);
lean_inc(x_2174);
if (lean_obj_tag(x_2174) == 0)
{
lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; uint8_t x_2180; 
x_2175 = lean_ctor_get(x_1860, 1);
lean_inc(x_2175);
if (lean_is_exclusive(x_1860)) {
 lean_ctor_release(x_1860, 0);
 lean_ctor_release(x_1860, 1);
 x_2176 = x_1860;
} else {
 lean_dec_ref(x_1860);
 x_2176 = lean_box(0);
}
x_2177 = lean_ctor_get(x_2172, 1);
lean_inc(x_2177);
lean_dec(x_2172);
x_2178 = lean_ctor_get(x_2173, 1);
lean_inc(x_2178);
lean_dec(x_2173);
x_2179 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_2180 = lean_string_dec_eq(x_2178, x_2179);
if (x_2180 == 0)
{
uint8_t x_2181; 
x_2181 = lean_string_dec_eq(x_2178, x_1852);
if (x_2181 == 0)
{
lean_object* x_2182; uint8_t x_2183; 
x_2182 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_2183 = lean_string_dec_eq(x_2178, x_2182);
if (x_2183 == 0)
{
lean_object* x_2184; uint8_t x_2185; 
x_2184 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_2185 = lean_string_dec_eq(x_2178, x_2184);
lean_dec(x_2178);
if (x_2185 == 0)
{
lean_object* x_2186; 
lean_dec(x_2177);
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2186 = x_2176;
}
lean_ctor_set(x_2186, 0, x_1858);
lean_ctor_set(x_2186, 1, x_11);
return x_2186;
}
else
{
lean_object* x_2187; uint8_t x_2188; 
x_2187 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97;
x_2188 = lean_string_dec_eq(x_2177, x_2187);
lean_dec(x_2177);
if (x_2188 == 0)
{
lean_object* x_2189; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2189 = x_2176;
}
lean_ctor_set(x_2189, 0, x_1858);
lean_ctor_set(x_2189, 1, x_11);
return x_2189;
}
else
{
lean_object* x_2190; uint8_t x_2191; 
x_2190 = lean_array_get_size(x_2175);
x_2191 = lean_nat_dec_eq(x_2190, x_1856);
lean_dec(x_2190);
if (x_2191 == 0)
{
lean_object* x_2192; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2192 = x_2176;
}
lean_ctor_set(x_2192, 0, x_1858);
lean_ctor_set(x_2192, 1, x_11);
return x_2192;
}
else
{
lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; uint8_t x_2198; 
x_2193 = lean_array_fget(x_2175, x_1846);
x_2194 = lean_unsigned_to_nat(1u);
x_2195 = lean_array_fget(x_2175, x_2194);
lean_dec(x_2175);
x_2196 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_2197 = l_Lean_mkAppB(x_2196, x_2193, x_2195);
x_2198 = !lean_is_exclusive(x_1858);
if (x_2198 == 0)
{
lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; uint64_t x_2202; uint64_t x_2203; uint64_t x_2204; uint64_t x_2205; uint64_t x_2206; uint64_t x_2207; uint64_t x_2208; size_t x_2209; size_t x_2210; size_t x_2211; size_t x_2212; size_t x_2213; lean_object* x_2214; uint8_t x_2215; 
x_2199 = lean_ctor_get(x_1858, 0);
x_2200 = lean_ctor_get(x_1858, 1);
x_2201 = lean_array_get_size(x_2200);
x_2202 = l_Lean_Expr_hash(x_2197);
x_2203 = 32;
x_2204 = lean_uint64_shift_right(x_2202, x_2203);
x_2205 = lean_uint64_xor(x_2202, x_2204);
x_2206 = 16;
x_2207 = lean_uint64_shift_right(x_2205, x_2206);
x_2208 = lean_uint64_xor(x_2205, x_2207);
x_2209 = lean_uint64_to_usize(x_2208);
x_2210 = lean_usize_of_nat(x_2201);
lean_dec(x_2201);
x_2211 = 1;
x_2212 = lean_usize_sub(x_2210, x_2211);
x_2213 = lean_usize_land(x_2209, x_2212);
x_2214 = lean_array_uget(x_2200, x_2213);
x_2215 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2197, x_2214);
if (x_2215 == 0)
{
lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; uint8_t x_2224; 
x_2216 = lean_nat_add(x_2199, x_2194);
lean_dec(x_2199);
x_2217 = lean_box(0);
x_2218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2218, 0, x_2197);
lean_ctor_set(x_2218, 1, x_2217);
lean_ctor_set(x_2218, 2, x_2214);
x_2219 = lean_array_uset(x_2200, x_2213, x_2218);
x_2220 = lean_unsigned_to_nat(4u);
x_2221 = lean_nat_mul(x_2216, x_2220);
x_2222 = lean_nat_div(x_2221, x_1842);
lean_dec(x_2221);
x_2223 = lean_array_get_size(x_2219);
x_2224 = lean_nat_dec_le(x_2222, x_2223);
lean_dec(x_2223);
lean_dec(x_2222);
if (x_2224 == 0)
{
lean_object* x_2225; lean_object* x_2226; 
x_2225 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2219);
lean_ctor_set(x_1858, 1, x_2225);
lean_ctor_set(x_1858, 0, x_2216);
if (lean_is_scalar(x_2176)) {
 x_2226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2226 = x_2176;
}
lean_ctor_set(x_2226, 0, x_1858);
lean_ctor_set(x_2226, 1, x_11);
return x_2226;
}
else
{
lean_object* x_2227; 
lean_ctor_set(x_1858, 1, x_2219);
lean_ctor_set(x_1858, 0, x_2216);
if (lean_is_scalar(x_2176)) {
 x_2227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2227 = x_2176;
}
lean_ctor_set(x_2227, 0, x_1858);
lean_ctor_set(x_2227, 1, x_11);
return x_2227;
}
}
else
{
lean_object* x_2228; 
lean_dec(x_2214);
lean_dec(x_2197);
if (lean_is_scalar(x_2176)) {
 x_2228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2228 = x_2176;
}
lean_ctor_set(x_2228, 0, x_1858);
lean_ctor_set(x_2228, 1, x_11);
return x_2228;
}
}
else
{
lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; uint64_t x_2232; uint64_t x_2233; uint64_t x_2234; uint64_t x_2235; uint64_t x_2236; uint64_t x_2237; uint64_t x_2238; size_t x_2239; size_t x_2240; size_t x_2241; size_t x_2242; size_t x_2243; lean_object* x_2244; uint8_t x_2245; 
x_2229 = lean_ctor_get(x_1858, 0);
x_2230 = lean_ctor_get(x_1858, 1);
lean_inc(x_2230);
lean_inc(x_2229);
lean_dec(x_1858);
x_2231 = lean_array_get_size(x_2230);
x_2232 = l_Lean_Expr_hash(x_2197);
x_2233 = 32;
x_2234 = lean_uint64_shift_right(x_2232, x_2233);
x_2235 = lean_uint64_xor(x_2232, x_2234);
x_2236 = 16;
x_2237 = lean_uint64_shift_right(x_2235, x_2236);
x_2238 = lean_uint64_xor(x_2235, x_2237);
x_2239 = lean_uint64_to_usize(x_2238);
x_2240 = lean_usize_of_nat(x_2231);
lean_dec(x_2231);
x_2241 = 1;
x_2242 = lean_usize_sub(x_2240, x_2241);
x_2243 = lean_usize_land(x_2239, x_2242);
x_2244 = lean_array_uget(x_2230, x_2243);
x_2245 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2197, x_2244);
if (x_2245 == 0)
{
lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; uint8_t x_2254; 
x_2246 = lean_nat_add(x_2229, x_2194);
lean_dec(x_2229);
x_2247 = lean_box(0);
x_2248 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2248, 0, x_2197);
lean_ctor_set(x_2248, 1, x_2247);
lean_ctor_set(x_2248, 2, x_2244);
x_2249 = lean_array_uset(x_2230, x_2243, x_2248);
x_2250 = lean_unsigned_to_nat(4u);
x_2251 = lean_nat_mul(x_2246, x_2250);
x_2252 = lean_nat_div(x_2251, x_1842);
lean_dec(x_2251);
x_2253 = lean_array_get_size(x_2249);
x_2254 = lean_nat_dec_le(x_2252, x_2253);
lean_dec(x_2253);
lean_dec(x_2252);
if (x_2254 == 0)
{
lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; 
x_2255 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2249);
x_2256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2256, 0, x_2246);
lean_ctor_set(x_2256, 1, x_2255);
if (lean_is_scalar(x_2176)) {
 x_2257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2257 = x_2176;
}
lean_ctor_set(x_2257, 0, x_2256);
lean_ctor_set(x_2257, 1, x_11);
return x_2257;
}
else
{
lean_object* x_2258; lean_object* x_2259; 
x_2258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2258, 0, x_2246);
lean_ctor_set(x_2258, 1, x_2249);
if (lean_is_scalar(x_2176)) {
 x_2259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2259 = x_2176;
}
lean_ctor_set(x_2259, 0, x_2258);
lean_ctor_set(x_2259, 1, x_11);
return x_2259;
}
}
else
{
lean_object* x_2260; lean_object* x_2261; 
lean_dec(x_2244);
lean_dec(x_2197);
x_2260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2260, 0, x_2229);
lean_ctor_set(x_2260, 1, x_2230);
if (lean_is_scalar(x_2176)) {
 x_2261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2261 = x_2176;
}
lean_ctor_set(x_2261, 0, x_2260);
lean_ctor_set(x_2261, 1, x_11);
return x_2261;
}
}
}
}
}
}
else
{
lean_object* x_2262; uint8_t x_2263; 
lean_dec(x_2178);
x_2262 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101;
x_2263 = lean_string_dec_eq(x_2177, x_2262);
lean_dec(x_2177);
if (x_2263 == 0)
{
lean_object* x_2264; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2264 = x_2176;
}
lean_ctor_set(x_2264, 0, x_1858);
lean_ctor_set(x_2264, 1, x_11);
return x_2264;
}
else
{
lean_object* x_2265; uint8_t x_2266; 
x_2265 = lean_array_get_size(x_2175);
x_2266 = lean_nat_dec_eq(x_2265, x_1856);
lean_dec(x_2265);
if (x_2266 == 0)
{
lean_object* x_2267; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2267 = x_2176;
}
lean_ctor_set(x_2267, 0, x_1858);
lean_ctor_set(x_2267, 1, x_11);
return x_2267;
}
else
{
lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; uint8_t x_2273; 
x_2268 = lean_array_fget(x_2175, x_1846);
x_2269 = lean_unsigned_to_nat(1u);
x_2270 = lean_array_fget(x_2175, x_2269);
lean_dec(x_2175);
x_2271 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_2272 = l_Lean_mkAppB(x_2271, x_2268, x_2270);
x_2273 = !lean_is_exclusive(x_1858);
if (x_2273 == 0)
{
lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; uint64_t x_2277; uint64_t x_2278; uint64_t x_2279; uint64_t x_2280; uint64_t x_2281; uint64_t x_2282; uint64_t x_2283; size_t x_2284; size_t x_2285; size_t x_2286; size_t x_2287; size_t x_2288; lean_object* x_2289; uint8_t x_2290; 
x_2274 = lean_ctor_get(x_1858, 0);
x_2275 = lean_ctor_get(x_1858, 1);
x_2276 = lean_array_get_size(x_2275);
x_2277 = l_Lean_Expr_hash(x_2272);
x_2278 = 32;
x_2279 = lean_uint64_shift_right(x_2277, x_2278);
x_2280 = lean_uint64_xor(x_2277, x_2279);
x_2281 = 16;
x_2282 = lean_uint64_shift_right(x_2280, x_2281);
x_2283 = lean_uint64_xor(x_2280, x_2282);
x_2284 = lean_uint64_to_usize(x_2283);
x_2285 = lean_usize_of_nat(x_2276);
lean_dec(x_2276);
x_2286 = 1;
x_2287 = lean_usize_sub(x_2285, x_2286);
x_2288 = lean_usize_land(x_2284, x_2287);
x_2289 = lean_array_uget(x_2275, x_2288);
x_2290 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2272, x_2289);
if (x_2290 == 0)
{
lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; uint8_t x_2299; 
x_2291 = lean_nat_add(x_2274, x_2269);
lean_dec(x_2274);
x_2292 = lean_box(0);
x_2293 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2293, 0, x_2272);
lean_ctor_set(x_2293, 1, x_2292);
lean_ctor_set(x_2293, 2, x_2289);
x_2294 = lean_array_uset(x_2275, x_2288, x_2293);
x_2295 = lean_unsigned_to_nat(4u);
x_2296 = lean_nat_mul(x_2291, x_2295);
x_2297 = lean_nat_div(x_2296, x_1842);
lean_dec(x_2296);
x_2298 = lean_array_get_size(x_2294);
x_2299 = lean_nat_dec_le(x_2297, x_2298);
lean_dec(x_2298);
lean_dec(x_2297);
if (x_2299 == 0)
{
lean_object* x_2300; lean_object* x_2301; 
x_2300 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2294);
lean_ctor_set(x_1858, 1, x_2300);
lean_ctor_set(x_1858, 0, x_2291);
if (lean_is_scalar(x_2176)) {
 x_2301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2301 = x_2176;
}
lean_ctor_set(x_2301, 0, x_1858);
lean_ctor_set(x_2301, 1, x_11);
return x_2301;
}
else
{
lean_object* x_2302; 
lean_ctor_set(x_1858, 1, x_2294);
lean_ctor_set(x_1858, 0, x_2291);
if (lean_is_scalar(x_2176)) {
 x_2302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2302 = x_2176;
}
lean_ctor_set(x_2302, 0, x_1858);
lean_ctor_set(x_2302, 1, x_11);
return x_2302;
}
}
else
{
lean_object* x_2303; 
lean_dec(x_2289);
lean_dec(x_2272);
if (lean_is_scalar(x_2176)) {
 x_2303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2303 = x_2176;
}
lean_ctor_set(x_2303, 0, x_1858);
lean_ctor_set(x_2303, 1, x_11);
return x_2303;
}
}
else
{
lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; uint64_t x_2307; uint64_t x_2308; uint64_t x_2309; uint64_t x_2310; uint64_t x_2311; uint64_t x_2312; uint64_t x_2313; size_t x_2314; size_t x_2315; size_t x_2316; size_t x_2317; size_t x_2318; lean_object* x_2319; uint8_t x_2320; 
x_2304 = lean_ctor_get(x_1858, 0);
x_2305 = lean_ctor_get(x_1858, 1);
lean_inc(x_2305);
lean_inc(x_2304);
lean_dec(x_1858);
x_2306 = lean_array_get_size(x_2305);
x_2307 = l_Lean_Expr_hash(x_2272);
x_2308 = 32;
x_2309 = lean_uint64_shift_right(x_2307, x_2308);
x_2310 = lean_uint64_xor(x_2307, x_2309);
x_2311 = 16;
x_2312 = lean_uint64_shift_right(x_2310, x_2311);
x_2313 = lean_uint64_xor(x_2310, x_2312);
x_2314 = lean_uint64_to_usize(x_2313);
x_2315 = lean_usize_of_nat(x_2306);
lean_dec(x_2306);
x_2316 = 1;
x_2317 = lean_usize_sub(x_2315, x_2316);
x_2318 = lean_usize_land(x_2314, x_2317);
x_2319 = lean_array_uget(x_2305, x_2318);
x_2320 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2272, x_2319);
if (x_2320 == 0)
{
lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; uint8_t x_2329; 
x_2321 = lean_nat_add(x_2304, x_2269);
lean_dec(x_2304);
x_2322 = lean_box(0);
x_2323 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2323, 0, x_2272);
lean_ctor_set(x_2323, 1, x_2322);
lean_ctor_set(x_2323, 2, x_2319);
x_2324 = lean_array_uset(x_2305, x_2318, x_2323);
x_2325 = lean_unsigned_to_nat(4u);
x_2326 = lean_nat_mul(x_2321, x_2325);
x_2327 = lean_nat_div(x_2326, x_1842);
lean_dec(x_2326);
x_2328 = lean_array_get_size(x_2324);
x_2329 = lean_nat_dec_le(x_2327, x_2328);
lean_dec(x_2328);
lean_dec(x_2327);
if (x_2329 == 0)
{
lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; 
x_2330 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2324);
x_2331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2331, 0, x_2321);
lean_ctor_set(x_2331, 1, x_2330);
if (lean_is_scalar(x_2176)) {
 x_2332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2332 = x_2176;
}
lean_ctor_set(x_2332, 0, x_2331);
lean_ctor_set(x_2332, 1, x_11);
return x_2332;
}
else
{
lean_object* x_2333; lean_object* x_2334; 
x_2333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2333, 0, x_2321);
lean_ctor_set(x_2333, 1, x_2324);
if (lean_is_scalar(x_2176)) {
 x_2334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2334 = x_2176;
}
lean_ctor_set(x_2334, 0, x_2333);
lean_ctor_set(x_2334, 1, x_11);
return x_2334;
}
}
else
{
lean_object* x_2335; lean_object* x_2336; 
lean_dec(x_2319);
lean_dec(x_2272);
x_2335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2335, 0, x_2304);
lean_ctor_set(x_2335, 1, x_2305);
if (lean_is_scalar(x_2176)) {
 x_2336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2336 = x_2176;
}
lean_ctor_set(x_2336, 0, x_2335);
lean_ctor_set(x_2336, 1, x_11);
return x_2336;
}
}
}
}
}
}
else
{
lean_object* x_2337; uint8_t x_2338; 
lean_dec(x_2178);
x_2337 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104;
x_2338 = lean_string_dec_eq(x_2177, x_2337);
lean_dec(x_2177);
if (x_2338 == 0)
{
lean_object* x_2339; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2339 = x_2176;
}
lean_ctor_set(x_2339, 0, x_1858);
lean_ctor_set(x_2339, 1, x_11);
return x_2339;
}
else
{
lean_object* x_2340; lean_object* x_2341; uint8_t x_2342; 
x_2340 = lean_array_get_size(x_2175);
x_2341 = lean_unsigned_to_nat(1u);
x_2342 = lean_nat_dec_eq(x_2340, x_2341);
lean_dec(x_2340);
if (x_2342 == 0)
{
lean_object* x_2343; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2343 = x_2176;
}
lean_ctor_set(x_2343, 0, x_1858);
lean_ctor_set(x_2343, 1, x_11);
return x_2343;
}
else
{
lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; uint8_t x_2415; 
x_2344 = lean_array_fget(x_2175, x_1846);
lean_dec(x_2175);
x_2345 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107;
lean_inc(x_2344);
x_2346 = l_Lean_Expr_app___override(x_2345, x_2344);
x_2347 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110;
x_2348 = l_Lean_Expr_app___override(x_2347, x_2344);
x_2415 = !lean_is_exclusive(x_1858);
if (x_2415 == 0)
{
lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; uint64_t x_2419; uint64_t x_2420; uint64_t x_2421; uint64_t x_2422; uint64_t x_2423; uint64_t x_2424; uint64_t x_2425; size_t x_2426; size_t x_2427; size_t x_2428; size_t x_2429; size_t x_2430; lean_object* x_2431; uint8_t x_2432; 
x_2416 = lean_ctor_get(x_1858, 0);
x_2417 = lean_ctor_get(x_1858, 1);
x_2418 = lean_array_get_size(x_2417);
x_2419 = l_Lean_Expr_hash(x_2346);
x_2420 = 32;
x_2421 = lean_uint64_shift_right(x_2419, x_2420);
x_2422 = lean_uint64_xor(x_2419, x_2421);
x_2423 = 16;
x_2424 = lean_uint64_shift_right(x_2422, x_2423);
x_2425 = lean_uint64_xor(x_2422, x_2424);
x_2426 = lean_uint64_to_usize(x_2425);
x_2427 = lean_usize_of_nat(x_2418);
lean_dec(x_2418);
x_2428 = 1;
x_2429 = lean_usize_sub(x_2427, x_2428);
x_2430 = lean_usize_land(x_2426, x_2429);
x_2431 = lean_array_uget(x_2417, x_2430);
x_2432 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2346, x_2431);
if (x_2432 == 0)
{
lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; uint8_t x_2441; 
x_2433 = lean_nat_add(x_2416, x_2341);
lean_dec(x_2416);
x_2434 = lean_box(0);
x_2435 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2435, 0, x_2346);
lean_ctor_set(x_2435, 1, x_2434);
lean_ctor_set(x_2435, 2, x_2431);
x_2436 = lean_array_uset(x_2417, x_2430, x_2435);
x_2437 = lean_unsigned_to_nat(4u);
x_2438 = lean_nat_mul(x_2433, x_2437);
x_2439 = lean_nat_div(x_2438, x_1842);
lean_dec(x_2438);
x_2440 = lean_array_get_size(x_2436);
x_2441 = lean_nat_dec_le(x_2439, x_2440);
lean_dec(x_2440);
lean_dec(x_2439);
if (x_2441 == 0)
{
lean_object* x_2442; 
x_2442 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2436);
lean_ctor_set(x_1858, 1, x_2442);
lean_ctor_set(x_1858, 0, x_2433);
x_2349 = x_1858;
goto block_2414;
}
else
{
lean_ctor_set(x_1858, 1, x_2436);
lean_ctor_set(x_1858, 0, x_2433);
x_2349 = x_1858;
goto block_2414;
}
}
else
{
lean_dec(x_2431);
lean_dec(x_2346);
x_2349 = x_1858;
goto block_2414;
}
}
else
{
lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; uint64_t x_2446; uint64_t x_2447; uint64_t x_2448; uint64_t x_2449; uint64_t x_2450; uint64_t x_2451; uint64_t x_2452; size_t x_2453; size_t x_2454; size_t x_2455; size_t x_2456; size_t x_2457; lean_object* x_2458; uint8_t x_2459; 
x_2443 = lean_ctor_get(x_1858, 0);
x_2444 = lean_ctor_get(x_1858, 1);
lean_inc(x_2444);
lean_inc(x_2443);
lean_dec(x_1858);
x_2445 = lean_array_get_size(x_2444);
x_2446 = l_Lean_Expr_hash(x_2346);
x_2447 = 32;
x_2448 = lean_uint64_shift_right(x_2446, x_2447);
x_2449 = lean_uint64_xor(x_2446, x_2448);
x_2450 = 16;
x_2451 = lean_uint64_shift_right(x_2449, x_2450);
x_2452 = lean_uint64_xor(x_2449, x_2451);
x_2453 = lean_uint64_to_usize(x_2452);
x_2454 = lean_usize_of_nat(x_2445);
lean_dec(x_2445);
x_2455 = 1;
x_2456 = lean_usize_sub(x_2454, x_2455);
x_2457 = lean_usize_land(x_2453, x_2456);
x_2458 = lean_array_uget(x_2444, x_2457);
x_2459 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2346, x_2458);
if (x_2459 == 0)
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; uint8_t x_2468; 
x_2460 = lean_nat_add(x_2443, x_2341);
lean_dec(x_2443);
x_2461 = lean_box(0);
x_2462 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2462, 0, x_2346);
lean_ctor_set(x_2462, 1, x_2461);
lean_ctor_set(x_2462, 2, x_2458);
x_2463 = lean_array_uset(x_2444, x_2457, x_2462);
x_2464 = lean_unsigned_to_nat(4u);
x_2465 = lean_nat_mul(x_2460, x_2464);
x_2466 = lean_nat_div(x_2465, x_1842);
lean_dec(x_2465);
x_2467 = lean_array_get_size(x_2463);
x_2468 = lean_nat_dec_le(x_2466, x_2467);
lean_dec(x_2467);
lean_dec(x_2466);
if (x_2468 == 0)
{
lean_object* x_2469; lean_object* x_2470; 
x_2469 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2463);
x_2470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2470, 0, x_2460);
lean_ctor_set(x_2470, 1, x_2469);
x_2349 = x_2470;
goto block_2414;
}
else
{
lean_object* x_2471; 
x_2471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2471, 0, x_2460);
lean_ctor_set(x_2471, 1, x_2463);
x_2349 = x_2471;
goto block_2414;
}
}
else
{
lean_object* x_2472; 
lean_dec(x_2458);
lean_dec(x_2346);
x_2472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2472, 0, x_2443);
lean_ctor_set(x_2472, 1, x_2444);
x_2349 = x_2472;
goto block_2414;
}
}
block_2414:
{
uint8_t x_2350; 
x_2350 = !lean_is_exclusive(x_2349);
if (x_2350 == 0)
{
lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; uint64_t x_2354; uint64_t x_2355; uint64_t x_2356; uint64_t x_2357; uint64_t x_2358; uint64_t x_2359; uint64_t x_2360; size_t x_2361; size_t x_2362; size_t x_2363; size_t x_2364; size_t x_2365; lean_object* x_2366; uint8_t x_2367; 
x_2351 = lean_ctor_get(x_2349, 0);
x_2352 = lean_ctor_get(x_2349, 1);
x_2353 = lean_array_get_size(x_2352);
x_2354 = l_Lean_Expr_hash(x_2348);
x_2355 = 32;
x_2356 = lean_uint64_shift_right(x_2354, x_2355);
x_2357 = lean_uint64_xor(x_2354, x_2356);
x_2358 = 16;
x_2359 = lean_uint64_shift_right(x_2357, x_2358);
x_2360 = lean_uint64_xor(x_2357, x_2359);
x_2361 = lean_uint64_to_usize(x_2360);
x_2362 = lean_usize_of_nat(x_2353);
lean_dec(x_2353);
x_2363 = 1;
x_2364 = lean_usize_sub(x_2362, x_2363);
x_2365 = lean_usize_land(x_2361, x_2364);
x_2366 = lean_array_uget(x_2352, x_2365);
x_2367 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2348, x_2366);
if (x_2367 == 0)
{
lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; uint8_t x_2376; 
x_2368 = lean_nat_add(x_2351, x_2341);
lean_dec(x_2351);
x_2369 = lean_box(0);
x_2370 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2370, 0, x_2348);
lean_ctor_set(x_2370, 1, x_2369);
lean_ctor_set(x_2370, 2, x_2366);
x_2371 = lean_array_uset(x_2352, x_2365, x_2370);
x_2372 = lean_unsigned_to_nat(4u);
x_2373 = lean_nat_mul(x_2368, x_2372);
x_2374 = lean_nat_div(x_2373, x_1842);
lean_dec(x_2373);
x_2375 = lean_array_get_size(x_2371);
x_2376 = lean_nat_dec_le(x_2374, x_2375);
lean_dec(x_2375);
lean_dec(x_2374);
if (x_2376 == 0)
{
lean_object* x_2377; lean_object* x_2378; 
x_2377 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2371);
lean_ctor_set(x_2349, 1, x_2377);
lean_ctor_set(x_2349, 0, x_2368);
if (lean_is_scalar(x_2176)) {
 x_2378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2378 = x_2176;
}
lean_ctor_set(x_2378, 0, x_2349);
lean_ctor_set(x_2378, 1, x_11);
return x_2378;
}
else
{
lean_object* x_2379; 
lean_ctor_set(x_2349, 1, x_2371);
lean_ctor_set(x_2349, 0, x_2368);
if (lean_is_scalar(x_2176)) {
 x_2379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2379 = x_2176;
}
lean_ctor_set(x_2379, 0, x_2349);
lean_ctor_set(x_2379, 1, x_11);
return x_2379;
}
}
else
{
lean_object* x_2380; 
lean_dec(x_2366);
lean_dec(x_2348);
if (lean_is_scalar(x_2176)) {
 x_2380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2380 = x_2176;
}
lean_ctor_set(x_2380, 0, x_2349);
lean_ctor_set(x_2380, 1, x_11);
return x_2380;
}
}
else
{
lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; uint64_t x_2384; uint64_t x_2385; uint64_t x_2386; uint64_t x_2387; uint64_t x_2388; uint64_t x_2389; uint64_t x_2390; size_t x_2391; size_t x_2392; size_t x_2393; size_t x_2394; size_t x_2395; lean_object* x_2396; uint8_t x_2397; 
x_2381 = lean_ctor_get(x_2349, 0);
x_2382 = lean_ctor_get(x_2349, 1);
lean_inc(x_2382);
lean_inc(x_2381);
lean_dec(x_2349);
x_2383 = lean_array_get_size(x_2382);
x_2384 = l_Lean_Expr_hash(x_2348);
x_2385 = 32;
x_2386 = lean_uint64_shift_right(x_2384, x_2385);
x_2387 = lean_uint64_xor(x_2384, x_2386);
x_2388 = 16;
x_2389 = lean_uint64_shift_right(x_2387, x_2388);
x_2390 = lean_uint64_xor(x_2387, x_2389);
x_2391 = lean_uint64_to_usize(x_2390);
x_2392 = lean_usize_of_nat(x_2383);
lean_dec(x_2383);
x_2393 = 1;
x_2394 = lean_usize_sub(x_2392, x_2393);
x_2395 = lean_usize_land(x_2391, x_2394);
x_2396 = lean_array_uget(x_2382, x_2395);
x_2397 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2348, x_2396);
if (x_2397 == 0)
{
lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; uint8_t x_2406; 
x_2398 = lean_nat_add(x_2381, x_2341);
lean_dec(x_2381);
x_2399 = lean_box(0);
x_2400 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2400, 0, x_2348);
lean_ctor_set(x_2400, 1, x_2399);
lean_ctor_set(x_2400, 2, x_2396);
x_2401 = lean_array_uset(x_2382, x_2395, x_2400);
x_2402 = lean_unsigned_to_nat(4u);
x_2403 = lean_nat_mul(x_2398, x_2402);
x_2404 = lean_nat_div(x_2403, x_1842);
lean_dec(x_2403);
x_2405 = lean_array_get_size(x_2401);
x_2406 = lean_nat_dec_le(x_2404, x_2405);
lean_dec(x_2405);
lean_dec(x_2404);
if (x_2406 == 0)
{
lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; 
x_2407 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2401);
x_2408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2408, 0, x_2398);
lean_ctor_set(x_2408, 1, x_2407);
if (lean_is_scalar(x_2176)) {
 x_2409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2409 = x_2176;
}
lean_ctor_set(x_2409, 0, x_2408);
lean_ctor_set(x_2409, 1, x_11);
return x_2409;
}
else
{
lean_object* x_2410; lean_object* x_2411; 
x_2410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2410, 0, x_2398);
lean_ctor_set(x_2410, 1, x_2401);
if (lean_is_scalar(x_2176)) {
 x_2411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2411 = x_2176;
}
lean_ctor_set(x_2411, 0, x_2410);
lean_ctor_set(x_2411, 1, x_11);
return x_2411;
}
}
else
{
lean_object* x_2412; lean_object* x_2413; 
lean_dec(x_2396);
lean_dec(x_2348);
x_2412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2412, 0, x_2381);
lean_ctor_set(x_2412, 1, x_2382);
if (lean_is_scalar(x_2176)) {
 x_2413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2413 = x_2176;
}
lean_ctor_set(x_2413, 0, x_2412);
lean_ctor_set(x_2413, 1, x_11);
return x_2413;
}
}
}
}
}
}
}
else
{
lean_object* x_2473; uint8_t x_2474; 
lean_dec(x_2178);
x_2473 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
x_2474 = lean_string_dec_eq(x_2177, x_2473);
lean_dec(x_2177);
if (x_2474 == 0)
{
lean_object* x_2475; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2475 = x_2176;
}
lean_ctor_set(x_2475, 0, x_1858);
lean_ctor_set(x_2475, 1, x_11);
return x_2475;
}
else
{
lean_object* x_2476; lean_object* x_2477; uint8_t x_2478; 
x_2476 = lean_array_get_size(x_2175);
x_2477 = lean_unsigned_to_nat(6u);
x_2478 = lean_nat_dec_eq(x_2476, x_2477);
lean_dec(x_2476);
if (x_2478 == 0)
{
lean_object* x_2479; 
lean_dec(x_2175);
if (lean_is_scalar(x_2176)) {
 x_2479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2479 = x_2176;
}
lean_ctor_set(x_2479, 0, x_1858);
lean_ctor_set(x_2479, 1, x_11);
return x_2479;
}
else
{
lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; uint8_t x_2486; 
x_2480 = lean_unsigned_to_nat(4u);
x_2481 = lean_array_fget(x_2175, x_2480);
x_2482 = lean_unsigned_to_nat(5u);
x_2483 = lean_array_fget(x_2175, x_2482);
lean_dec(x_2175);
x_2484 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__113;
x_2485 = l_Lean_mkAppB(x_2484, x_2481, x_2483);
x_2486 = !lean_is_exclusive(x_1858);
if (x_2486 == 0)
{
lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; uint64_t x_2490; uint64_t x_2491; uint64_t x_2492; uint64_t x_2493; uint64_t x_2494; uint64_t x_2495; uint64_t x_2496; size_t x_2497; size_t x_2498; size_t x_2499; size_t x_2500; size_t x_2501; lean_object* x_2502; uint8_t x_2503; 
x_2487 = lean_ctor_get(x_1858, 0);
x_2488 = lean_ctor_get(x_1858, 1);
x_2489 = lean_array_get_size(x_2488);
x_2490 = l_Lean_Expr_hash(x_2485);
x_2491 = 32;
x_2492 = lean_uint64_shift_right(x_2490, x_2491);
x_2493 = lean_uint64_xor(x_2490, x_2492);
x_2494 = 16;
x_2495 = lean_uint64_shift_right(x_2493, x_2494);
x_2496 = lean_uint64_xor(x_2493, x_2495);
x_2497 = lean_uint64_to_usize(x_2496);
x_2498 = lean_usize_of_nat(x_2489);
lean_dec(x_2489);
x_2499 = 1;
x_2500 = lean_usize_sub(x_2498, x_2499);
x_2501 = lean_usize_land(x_2497, x_2500);
x_2502 = lean_array_uget(x_2488, x_2501);
x_2503 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2485, x_2502);
if (x_2503 == 0)
{
lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; uint8_t x_2512; 
x_2504 = lean_unsigned_to_nat(1u);
x_2505 = lean_nat_add(x_2487, x_2504);
lean_dec(x_2487);
x_2506 = lean_box(0);
x_2507 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2507, 0, x_2485);
lean_ctor_set(x_2507, 1, x_2506);
lean_ctor_set(x_2507, 2, x_2502);
x_2508 = lean_array_uset(x_2488, x_2501, x_2507);
x_2509 = lean_nat_mul(x_2505, x_2480);
x_2510 = lean_nat_div(x_2509, x_1842);
lean_dec(x_2509);
x_2511 = lean_array_get_size(x_2508);
x_2512 = lean_nat_dec_le(x_2510, x_2511);
lean_dec(x_2511);
lean_dec(x_2510);
if (x_2512 == 0)
{
lean_object* x_2513; lean_object* x_2514; 
x_2513 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2508);
lean_ctor_set(x_1858, 1, x_2513);
lean_ctor_set(x_1858, 0, x_2505);
if (lean_is_scalar(x_2176)) {
 x_2514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2514 = x_2176;
}
lean_ctor_set(x_2514, 0, x_1858);
lean_ctor_set(x_2514, 1, x_11);
return x_2514;
}
else
{
lean_object* x_2515; 
lean_ctor_set(x_1858, 1, x_2508);
lean_ctor_set(x_1858, 0, x_2505);
if (lean_is_scalar(x_2176)) {
 x_2515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2515 = x_2176;
}
lean_ctor_set(x_2515, 0, x_1858);
lean_ctor_set(x_2515, 1, x_11);
return x_2515;
}
}
else
{
lean_object* x_2516; 
lean_dec(x_2502);
lean_dec(x_2485);
if (lean_is_scalar(x_2176)) {
 x_2516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2516 = x_2176;
}
lean_ctor_set(x_2516, 0, x_1858);
lean_ctor_set(x_2516, 1, x_11);
return x_2516;
}
}
else
{
lean_object* x_2517; lean_object* x_2518; lean_object* x_2519; uint64_t x_2520; uint64_t x_2521; uint64_t x_2522; uint64_t x_2523; uint64_t x_2524; uint64_t x_2525; uint64_t x_2526; size_t x_2527; size_t x_2528; size_t x_2529; size_t x_2530; size_t x_2531; lean_object* x_2532; uint8_t x_2533; 
x_2517 = lean_ctor_get(x_1858, 0);
x_2518 = lean_ctor_get(x_1858, 1);
lean_inc(x_2518);
lean_inc(x_2517);
lean_dec(x_1858);
x_2519 = lean_array_get_size(x_2518);
x_2520 = l_Lean_Expr_hash(x_2485);
x_2521 = 32;
x_2522 = lean_uint64_shift_right(x_2520, x_2521);
x_2523 = lean_uint64_xor(x_2520, x_2522);
x_2524 = 16;
x_2525 = lean_uint64_shift_right(x_2523, x_2524);
x_2526 = lean_uint64_xor(x_2523, x_2525);
x_2527 = lean_uint64_to_usize(x_2526);
x_2528 = lean_usize_of_nat(x_2519);
lean_dec(x_2519);
x_2529 = 1;
x_2530 = lean_usize_sub(x_2528, x_2529);
x_2531 = lean_usize_land(x_2527, x_2530);
x_2532 = lean_array_uget(x_2518, x_2531);
x_2533 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectMVars_visit___spec__1(x_2485, x_2532);
if (x_2533 == 0)
{
lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; uint8_t x_2542; 
x_2534 = lean_unsigned_to_nat(1u);
x_2535 = lean_nat_add(x_2517, x_2534);
lean_dec(x_2517);
x_2536 = lean_box(0);
x_2537 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_2537, 0, x_2485);
lean_ctor_set(x_2537, 1, x_2536);
lean_ctor_set(x_2537, 2, x_2532);
x_2538 = lean_array_uset(x_2518, x_2531, x_2537);
x_2539 = lean_nat_mul(x_2535, x_2480);
x_2540 = lean_nat_div(x_2539, x_1842);
lean_dec(x_2539);
x_2541 = lean_array_get_size(x_2538);
x_2542 = lean_nat_dec_le(x_2540, x_2541);
lean_dec(x_2541);
lean_dec(x_2540);
if (x_2542 == 0)
{
lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; 
x_2543 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectMVars_visit___spec__2(x_2538);
x_2544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2544, 0, x_2535);
lean_ctor_set(x_2544, 1, x_2543);
if (lean_is_scalar(x_2176)) {
 x_2545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2545 = x_2176;
}
lean_ctor_set(x_2545, 0, x_2544);
lean_ctor_set(x_2545, 1, x_11);
return x_2545;
}
else
{
lean_object* x_2546; lean_object* x_2547; 
x_2546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2546, 0, x_2535);
lean_ctor_set(x_2546, 1, x_2538);
if (lean_is_scalar(x_2176)) {
 x_2547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2547 = x_2176;
}
lean_ctor_set(x_2547, 0, x_2546);
lean_ctor_set(x_2547, 1, x_11);
return x_2547;
}
}
else
{
lean_object* x_2548; lean_object* x_2549; 
lean_dec(x_2532);
lean_dec(x_2485);
x_2548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2548, 0, x_2517);
lean_ctor_set(x_2548, 1, x_2518);
if (lean_is_scalar(x_2176)) {
 x_2549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2549 = x_2176;
}
lean_ctor_set(x_2549, 0, x_2548);
lean_ctor_set(x_2549, 1, x_11);
return x_2549;
}
}
}
}
}
}
else
{
uint8_t x_2550; 
lean_dec(x_2174);
lean_dec(x_2173);
lean_dec(x_2172);
x_2550 = !lean_is_exclusive(x_1860);
if (x_2550 == 0)
{
lean_object* x_2551; lean_object* x_2552; 
x_2551 = lean_ctor_get(x_1860, 1);
lean_dec(x_2551);
x_2552 = lean_ctor_get(x_1860, 0);
lean_dec(x_2552);
lean_ctor_set(x_1860, 1, x_11);
lean_ctor_set(x_1860, 0, x_1858);
return x_1860;
}
else
{
lean_object* x_2553; 
lean_dec(x_1860);
x_2553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2553, 0, x_1858);
lean_ctor_set(x_2553, 1, x_11);
return x_2553;
}
}
}
else
{
uint8_t x_2554; 
lean_dec(x_2173);
lean_dec(x_2172);
x_2554 = !lean_is_exclusive(x_1860);
if (x_2554 == 0)
{
lean_object* x_2555; lean_object* x_2556; 
x_2555 = lean_ctor_get(x_1860, 1);
lean_dec(x_2555);
x_2556 = lean_ctor_get(x_1860, 0);
lean_dec(x_2556);
lean_ctor_set(x_1860, 1, x_11);
lean_ctor_set(x_1860, 0, x_1858);
return x_1860;
}
else
{
lean_object* x_2557; 
lean_dec(x_1860);
x_2557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2557, 0, x_1858);
lean_ctor_set(x_2557, 1, x_11);
return x_2557;
}
}
}
else
{
uint8_t x_2558; 
lean_dec(x_2172);
x_2558 = !lean_is_exclusive(x_1860);
if (x_2558 == 0)
{
lean_object* x_2559; lean_object* x_2560; 
x_2559 = lean_ctor_get(x_1860, 1);
lean_dec(x_2559);
x_2560 = lean_ctor_get(x_1860, 0);
lean_dec(x_2560);
lean_ctor_set(x_1860, 1, x_11);
lean_ctor_set(x_1860, 0, x_1858);
return x_1860;
}
else
{
lean_object* x_2561; 
lean_dec(x_1860);
x_2561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2561, 0, x_1858);
lean_ctor_set(x_2561, 1, x_11);
return x_2561;
}
}
}
}
}
else
{
uint8_t x_2588; 
lean_dec(x_117);
lean_dec(x_116);
x_2588 = !lean_is_exclusive(x_1850);
if (x_2588 == 0)
{
lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; 
x_2589 = lean_ctor_get(x_1850, 1);
lean_dec(x_2589);
x_2590 = lean_ctor_get(x_1850, 0);
lean_dec(x_2590);
x_2591 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set_tag(x_1850, 0);
lean_ctor_set(x_1850, 1, x_11);
lean_ctor_set(x_1850, 0, x_2591);
return x_1850;
}
else
{
lean_object* x_2592; lean_object* x_2593; 
lean_dec(x_1850);
x_2592 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_2593 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2593, 0, x_2592);
lean_ctor_set(x_2593, 1, x_11);
return x_2593;
}
}
}
}
else
{
lean_object* x_2594; lean_object* x_2595; 
lean_dec(x_1849);
lean_dec(x_1848);
lean_dec(x_1847);
lean_dec(x_116);
x_2594 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_2595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2595 = x_117;
}
lean_ctor_set(x_2595, 0, x_2594);
lean_ctor_set(x_2595, 1, x_11);
return x_2595;
}
}
else
{
lean_object* x_2596; lean_object* x_2597; 
lean_dec(x_1848);
lean_dec(x_1847);
lean_dec(x_116);
x_2596 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_2597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2597 = x_117;
}
lean_ctor_set(x_2597, 0, x_2596);
lean_ctor_set(x_2597, 1, x_11);
return x_2597;
}
}
else
{
lean_object* x_2598; lean_object* x_2599; 
lean_dec(x_1847);
lean_dec(x_116);
x_2598 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
if (lean_is_scalar(x_117)) {
 x_2599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2599 = x_117;
}
lean_ctor_set(x_2599, 0, x_2598);
lean_ctor_set(x_2599, 1, x_11);
return x_2599;
}
}
}
}
}
else
{
uint8_t x_2600; 
lean_dec(x_115);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2600 = !lean_is_exclusive(x_12);
if (x_2600 == 0)
{
lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; 
x_2601 = lean_ctor_get(x_12, 1);
lean_dec(x_2601);
x_2602 = lean_ctor_get(x_12, 0);
lean_dec(x_2602);
x_2603 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_2603);
return x_12;
}
else
{
lean_object* x_2604; lean_object* x_2605; 
lean_dec(x_12);
x_2604 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_2605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2605, 0, x_2604);
lean_ctor_set(x_2605, 1, x_11);
return x_2605;
}
}
}
default: 
{
uint8_t x_2606; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2606 = !lean_is_exclusive(x_12);
if (x_2606 == 0)
{
lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; 
x_2607 = lean_ctor_get(x_12, 1);
lean_dec(x_2607);
x_2608 = lean_ctor_get(x_12, 0);
lean_dec(x_2608);
x_2609 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_2609);
return x_12;
}
else
{
lean_object* x_2610; lean_object* x_2611; 
lean_dec(x_12);
x_2610 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_2611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2611, 0, x_2610);
lean_ctor_set(x_2611, 1, x_11);
return x_2611;
}
}
}
}
else
{
uint8_t x_2612; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2612 = !lean_is_exclusive(x_12);
if (x_2612 == 0)
{
lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; 
x_2613 = lean_ctor_get(x_12, 1);
lean_dec(x_2613);
x_2614 = lean_ctor_get(x_12, 0);
lean_dec(x_2614);
x_2615 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_2615);
return x_12;
}
else
{
lean_object* x_2616; lean_object* x_2617; 
lean_dec(x_12);
x_2616 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_2617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2617, 0, x_2616);
lean_ctor_set(x_2617, 1, x_11);
return x_2617;
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = l_Lean_isTracingEnabledForCore(x_1, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Elab_Tactic_Omega_lookup___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Elab_Tactic_Omega_lookup___spec__5(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_expr_eqv(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__7(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_13 = l_List_reverse___rarg(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = lean_infer_type(x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_19);
{
lean_object* _tmp_0 = x_17;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_11 = x_20;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = lean_infer_type(x_26, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_2);
x_1 = x_27;
x_2 = x_31;
x_12 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_11, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 3);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; double x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1;
x_28 = 0;
x_29 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2;
x_30 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_float(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_float(x_30, sizeof(void*)*2 + 8, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 16, x_28);
x_31 = l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_15);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_32);
lean_ctor_set(x_17, 0, x_13);
x_33 = l_Lean_PersistentArray_push___rarg(x_26, x_17);
lean_ctor_set(x_19, 0, x_33);
x_34 = lean_st_ref_set(x_11, x_18, x_21);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint64_t x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
lean_dec(x_19);
x_43 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1;
x_44 = 0;
x_45 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2;
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_48);
lean_ctor_set(x_17, 0, x_13);
x_49 = l_Lean_PersistentArray_push___rarg(x_42, x_17);
x_50 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_41);
lean_ctor_set(x_18, 3, x_50);
x_51 = lean_st_ref_set(x_11, x_18, x_21);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; double x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
x_58 = lean_ctor_get(x_18, 2);
x_59 = lean_ctor_get(x_18, 4);
x_60 = lean_ctor_get(x_18, 5);
x_61 = lean_ctor_get(x_18, 6);
x_62 = lean_ctor_get(x_18, 7);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_63 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_65 = x_19;
} else {
 lean_dec_ref(x_19);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1;
x_67 = 0;
x_68 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2;
x_69 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_float(x_69, sizeof(void*)*2, x_66);
lean_ctor_set_float(x_69, sizeof(void*)*2 + 8, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 16, x_67);
x_70 = l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
x_71 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_15);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_71);
lean_ctor_set(x_17, 0, x_13);
x_72 = l_Lean_PersistentArray_push___rarg(x_64, x_17);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 1, 8);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint64(x_73, sizeof(void*)*1, x_63);
x_74 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 4, x_59);
lean_ctor_set(x_74, 5, x_60);
lean_ctor_set(x_74, 6, x_61);
lean_ctor_set(x_74, 7, x_62);
x_75 = lean_st_ref_set(x_11, x_74, x_21);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; double x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_80 = lean_ctor_get(x_17, 1);
lean_inc(x_80);
lean_dec(x_17);
x_81 = lean_ctor_get(x_18, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_18, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_18, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_18, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_18, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_18, 7);
lean_inc(x_87);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_88 = x_18;
} else {
 lean_dec_ref(x_18);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_90 = lean_ctor_get(x_19, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_91 = x_19;
} else {
 lean_dec_ref(x_19);
 x_91 = lean_box(0);
}
x_92 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1;
x_93 = 0;
x_94 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2;
x_95 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_float(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_float(x_95, sizeof(void*)*2 + 8, x_92);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 16, x_93);
x_96 = l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1;
x_97 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_15);
lean_ctor_set(x_97, 2, x_96);
lean_inc(x_13);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_13);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_PersistentArray_push___rarg(x_90, x_98);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 1, 8);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint64(x_100, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_88)) {
 x_101 = lean_alloc_ctor(0, 8, 0);
} else {
 x_101 = x_88;
}
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_82);
lean_ctor_set(x_101, 2, x_83);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_84);
lean_ctor_set(x_101, 5, x_85);
lean_ctor_set(x_101, 6, x_86);
lean_ctor_set(x_101, 7, x_87);
x_102 = lean_st_ref_set(x_11, x_101, x_80);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldrM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(x_4, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_take(x_7, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_usize_sub(x_24, x_1);
x_26 = lean_usize_land(x_2, x_25);
x_27 = lean_array_uget(x_22, x_26);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_3, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_inc(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_27);
x_32 = lean_array_uset(x_22, x_26, x_31);
x_33 = lean_unsigned_to_nat(4u);
x_34 = lean_nat_mul(x_30, x_33);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_nat_dec_le(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__4(x_32);
lean_ctor_set(x_18, 1, x_39);
lean_ctor_set(x_18, 0, x_30);
x_40 = lean_st_ref_set(x_7, x_18, x_20);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_16, 1, x_43);
lean_ctor_set(x_16, 0, x_21);
lean_ctor_set(x_40, 0, x_16);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_16, 1, x_45);
lean_ctor_set(x_16, 0, x_21);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_ctor_set(x_18, 1, x_32);
lean_ctor_set(x_18, 0, x_30);
x_47 = lean_st_ref_set(x_7, x_18, x_20);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_16, 1, x_50);
lean_ctor_set(x_16, 0, x_21);
lean_ctor_set(x_47, 0, x_16);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_16, 1, x_52);
lean_ctor_set(x_16, 0, x_21);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_16);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_box(0);
x_55 = lean_array_uset(x_22, x_26, x_54);
lean_inc(x_21);
x_56 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__7(x_3, x_21, x_27);
x_57 = lean_array_uset(x_55, x_26, x_56);
lean_inc(x_21);
lean_ctor_set(x_18, 1, x_57);
x_58 = lean_st_ref_set(x_7, x_18, x_20);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_16, 1, x_61);
lean_ctor_set(x_16, 0, x_21);
lean_ctor_set(x_58, 0, x_16);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_16, 1, x_63);
lean_ctor_set(x_16, 0, x_21);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_16);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; size_t x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_ctor_get(x_16, 1);
x_66 = lean_ctor_get(x_18, 0);
x_67 = lean_ctor_get(x_18, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_18);
x_68 = lean_array_get_size(x_67);
x_69 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_70 = lean_usize_sub(x_69, x_1);
x_71 = lean_usize_land(x_2, x_70);
x_72 = lean_array_uget(x_67, x_71);
x_73 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_3, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_66, x_74);
lean_inc(x_66);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_3);
lean_ctor_set(x_76, 1, x_66);
lean_ctor_set(x_76, 2, x_72);
x_77 = lean_array_uset(x_67, x_71, x_76);
x_78 = lean_unsigned_to_nat(4u);
x_79 = lean_nat_mul(x_75, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = lean_array_get_size(x_77);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__4(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_st_ref_set(x_7, x_85, x_65);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_4);
lean_ctor_set(x_16, 1, x_89);
lean_ctor_set(x_16, 0, x_66);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_16);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_75);
lean_ctor_set(x_91, 1, x_77);
x_92 = lean_st_ref_set(x_7, x_91, x_65);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_4);
lean_ctor_set(x_16, 1, x_95);
lean_ctor_set(x_16, 0, x_66);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_16);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_box(0);
x_98 = lean_array_uset(x_67, x_71, x_97);
lean_inc(x_66);
x_99 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__7(x_3, x_66, x_72);
x_100 = lean_array_uset(x_98, x_71, x_99);
lean_inc(x_66);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_66);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_st_ref_set(x_7, x_101, x_65);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_4);
lean_ctor_set(x_16, 1, x_105);
lean_ctor_set(x_16, 0, x_66);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_16);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; size_t x_114; size_t x_115; lean_object* x_116; uint8_t x_117; 
x_107 = lean_ctor_get(x_16, 0);
x_108 = lean_ctor_get(x_16, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_16);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_111 = x_107;
} else {
 lean_dec_ref(x_107);
 x_111 = lean_box(0);
}
x_112 = lean_array_get_size(x_110);
x_113 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_114 = lean_usize_sub(x_113, x_1);
x_115 = lean_usize_land(x_2, x_114);
x_116 = lean_array_uget(x_110, x_115);
x_117 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_3, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_109, x_118);
lean_inc(x_109);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_3);
lean_ctor_set(x_120, 1, x_109);
lean_ctor_set(x_120, 2, x_116);
x_121 = lean_array_uset(x_110, x_115, x_120);
x_122 = lean_unsigned_to_nat(4u);
x_123 = lean_nat_mul(x_119, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = lean_array_get_size(x_121);
x_127 = lean_nat_dec_le(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_128 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__4(x_121);
if (lean_is_scalar(x_111)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_111;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_st_ref_set(x_7, x_129, x_108);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_4);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_109);
lean_ctor_set(x_134, 1, x_133);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_131);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
if (lean_is_scalar(x_111)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_111;
}
lean_ctor_set(x_136, 0, x_119);
lean_ctor_set(x_136, 1, x_121);
x_137 = lean_st_ref_set(x_7, x_136, x_108);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_4);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_109);
lean_ctor_set(x_141, 1, x_140);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_138);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_143 = lean_box(0);
x_144 = lean_array_uset(x_110, x_115, x_143);
lean_inc(x_109);
x_145 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__7(x_3, x_109, x_116);
x_146 = lean_array_uset(x_144, x_115, x_145);
lean_inc(x_109);
if (lean_is_scalar(x_111)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_111;
}
lean_ctor_set(x_147, 0, x_109);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_st_ref_set(x_7, x_147, x_108);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_4);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_109);
lean_ctor_set(x_152, 1, x_151);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_149);
return x_153;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("New facts: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1);
x_17 = l_Lean_Elab_Tactic_Omega_analyzeAtom(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_inc(x_5);
x_32 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_20);
lean_dec(x_5);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_35);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_32, 1);
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_41 = lean_box(0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_30, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_42);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_45 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_41, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_46, x_41);
x_49 = l_Lean_MessageData_ofList(x_48);
x_50 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_49);
lean_ctor_set(x_32, 0, x_50);
x_51 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_51);
lean_ctor_set(x_20, 0, x_32);
x_52 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_47);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_53, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_54);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_53);
return x_55;
}
else
{
uint8_t x_56; 
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_61 = 0;
x_62 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11(x_42, x_60, x_61, x_41);
lean_dec(x_42);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_63 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_62, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_39);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_64, x_41);
x_67 = l_Lean_MessageData_ofList(x_66);
x_68 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_67);
lean_ctor_set(x_32, 0, x_68);
x_69 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_69);
lean_ctor_set(x_20, 0, x_32);
x_70 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_65);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_71, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_72);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_71);
return x_73;
}
else
{
uint8_t x_74; 
lean_free_object(x_32);
lean_free_object(x_20);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_63);
if (x_74 == 0)
{
return x_63;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_63);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_32, 1);
lean_inc(x_78);
lean_dec(x_32);
x_79 = lean_box(0);
x_80 = lean_ctor_get(x_18, 1);
lean_inc(x_80);
x_81 = lean_array_get_size(x_80);
x_82 = lean_nat_dec_lt(x_30, x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_81);
lean_dec(x_80);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_83 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_79, x_79, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_84, x_79);
x_87 = l_Lean_MessageData_ofList(x_86);
x_88 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_90);
lean_ctor_set(x_20, 0, x_89);
x_91 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_85);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_92, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_93);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_free_object(x_20);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_83, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_97 = x_83;
} else {
 lean_dec_ref(x_83);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_100 = 0;
x_101 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11(x_80, x_99, x_100, x_79);
lean_dec(x_80);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_102 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_101, x_79, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_78);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_103, x_79);
x_106 = l_Lean_MessageData_ofList(x_105);
x_107 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_109);
lean_ctor_set(x_20, 0, x_108);
x_110 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_104);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_111, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_112);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_111);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_free_object(x_20);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_114 = lean_ctor_get(x_102, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_102, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_116 = x_102;
} else {
 lean_dec_ref(x_102);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_free_object(x_20);
lean_dec(x_5);
x_118 = lean_box(0);
x_119 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_118, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_20, 1);
lean_inc(x_120);
lean_dec(x_20);
x_121 = lean_ctor_get(x_18, 0);
lean_inc(x_121);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_nat_dec_eq(x_121, x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_inc(x_5);
x_124 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_120);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_5);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_box(0);
x_129 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_128, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_127);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_131 = x_124;
} else {
 lean_dec_ref(x_124);
 x_131 = lean_box(0);
}
x_132 = lean_box(0);
x_133 = lean_ctor_get(x_18, 1);
lean_inc(x_133);
x_134 = lean_array_get_size(x_133);
x_135 = lean_nat_dec_lt(x_122, x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_134);
lean_dec(x_133);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_136 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_132, x_132, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_130);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_137, x_132);
x_140 = l_Lean_MessageData_ofList(x_139);
x_141 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
if (lean_is_scalar(x_131)) {
 x_142 = lean_alloc_ctor(7, 2, 0);
} else {
 x_142 = x_131;
 lean_ctor_set_tag(x_142, 7);
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_5, x_144, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_138);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_146, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_147);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_131);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_149 = lean_ctor_get(x_136, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_136, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_151 = x_136;
} else {
 lean_dec_ref(x_136);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_154 = 0;
x_155 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11(x_133, x_153, x_154, x_132);
lean_dec(x_133);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_156 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_155, x_132, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_130);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_157, x_132);
x_160 = l_Lean_MessageData_ofList(x_159);
x_161 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
if (lean_is_scalar(x_131)) {
 x_162 = lean_alloc_ctor(7, 2, 0);
} else {
 x_162 = x_131;
 lean_ctor_set_tag(x_162, 7);
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_5, x_164, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_158);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_166, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_167);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_131);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_169 = lean_ctor_get(x_156, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_156, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_171 = x_156;
} else {
 lean_dec_ref(x_156);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_5);
x_173 = lean_box(0);
x_174 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_3, x_4, x_1, x_18, x_173, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_120);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_17);
if (x_175 == 0)
{
return x_17;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_17, 0);
x_177 = lean_ctor_get(x_17, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_17);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("omega", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("New atom: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_Canonicalizer_canon(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_array_get_size(x_20);
x_23 = l_Lean_Expr_hash(x_18);
x_24 = 32;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = 16;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = 1;
x_33 = lean_usize_sub(x_31, x_32);
x_34 = lean_usize_land(x_30, x_33);
x_35 = lean_array_uget(x_20, x_34);
lean_dec(x_20);
x_36 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_18, x_35);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_15);
x_37 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_38 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_13);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_18, x_37, x_32, x_30, x_37, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_38, 1);
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
lean_inc(x_18);
x_47 = l_Lean_MessageData_ofExpr(x_18);
x_48 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_47);
lean_ctor_set(x_38, 0, x_48);
x_49 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_49);
lean_ctor_set(x_13, 0, x_38);
x_50 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_37, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_18, x_37, x_32, x_30, x_37, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_dec(x_38);
lean_inc(x_18);
x_55 = l_Lean_MessageData_ofExpr(x_18);
x_56 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_58);
lean_ctor_set(x_13, 0, x_57);
x_59 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_37, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_18, x_37, x_32, x_30, x_37, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
lean_dec(x_60);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_63 = lean_ctor_get(x_36, 0);
lean_inc(x_63);
lean_dec(x_36);
x_64 = lean_box(0);
lean_ctor_set(x_13, 1, x_64);
lean_ctor_set(x_13, 0, x_63);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; size_t x_76; size_t x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_dec(x_13);
x_68 = lean_array_get_size(x_67);
x_69 = l_Lean_Expr_hash(x_65);
x_70 = 32;
x_71 = lean_uint64_shift_right(x_69, x_70);
x_72 = lean_uint64_xor(x_69, x_71);
x_73 = 16;
x_74 = lean_uint64_shift_right(x_72, x_73);
x_75 = lean_uint64_xor(x_72, x_74);
x_76 = lean_uint64_to_usize(x_75);
x_77 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_78 = 1;
x_79 = lean_usize_sub(x_77, x_78);
x_80 = lean_usize_land(x_76, x_79);
x_81 = lean_array_uget(x_67, x_80);
lean_dec(x_67);
x_82 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_65, x_81);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_free_object(x_15);
x_83 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_84 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_66);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_box(0);
x_89 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_65, x_83, x_78, x_76, x_83, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
lean_inc(x_65);
x_92 = l_Lean_MessageData_ofExpr(x_65);
x_93 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(7, 2, 0);
} else {
 x_94 = x_91;
 lean_ctor_set_tag(x_94, 7);
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_83, x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_65, x_83, x_78, x_76, x_83, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
lean_dec(x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_65);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_101 = lean_ctor_get(x_82, 0);
lean_inc(x_101);
lean_dec(x_82);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_15, 0, x_103);
return x_15;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; lean_object* x_122; 
x_104 = lean_ctor_get(x_15, 0);
x_105 = lean_ctor_get(x_15, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_15);
x_106 = lean_ctor_get(x_13, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_107 = x_13;
} else {
 lean_dec_ref(x_13);
 x_107 = lean_box(0);
}
x_108 = lean_array_get_size(x_106);
x_109 = l_Lean_Expr_hash(x_104);
x_110 = 32;
x_111 = lean_uint64_shift_right(x_109, x_110);
x_112 = lean_uint64_xor(x_109, x_111);
x_113 = 16;
x_114 = lean_uint64_shift_right(x_112, x_113);
x_115 = lean_uint64_xor(x_112, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_118 = 1;
x_119 = lean_usize_sub(x_117, x_118);
x_120 = lean_usize_land(x_116, x_119);
x_121 = lean_array_uget(x_106, x_120);
lean_dec(x_106);
x_122 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_104, x_121);
lean_dec(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_124 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_105);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_107);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_box(0);
x_129 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_104, x_123, x_118, x_116, x_123, x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_131 = x_124;
} else {
 lean_dec_ref(x_124);
 x_131 = lean_box(0);
}
lean_inc(x_104);
x_132 = l_Lean_MessageData_ofExpr(x_104);
x_133 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(7, 2, 0);
} else {
 x_134 = x_131;
 lean_ctor_set_tag(x_134, 7);
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
if (lean_is_scalar(x_107)) {
 x_136 = lean_alloc_ctor(7, 2, 0);
} else {
 x_136 = x_107;
 lean_ctor_set_tag(x_136, 7);
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_123, x_136, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_130);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_104, x_123, x_118, x_116, x_123, x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_139);
lean_dec(x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_141 = lean_ctor_get(x_122, 0);
lean_inc(x_141);
lean_dec(x_122);
x_142 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_107;
}
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_105);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_145 = !lean_is_exclusive(x_15);
if (x_145 == 0)
{
return x_15;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_15, 0);
x_147 = lean_ctor_get(x_15, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_15);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_Lean_Elab_Tactic_Omega_lookup___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__11(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_9);
lean_dec(x_9);
x_19 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox(x_10);
lean_dec(x_10);
x_20 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_19, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_20;
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
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1);
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2);
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3);
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__4 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__4);
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__5 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__5);
l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___closed__1 = _init_l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__2___closed__1);
l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atoms___rarg___closed__1);
l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1);
l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2);
l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3 = _init_l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__3 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__3);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__4 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__4);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__5 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__5);
l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6 = _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6);
l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1);
l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1 = _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1);
l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2 = _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2);
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
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14);
l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15 = _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15);
l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1 = _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1);
l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2 = _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2);
l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3 = _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3);
l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__4 = _init_l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__4);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8();
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9();
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55();
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__113 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__113();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__113);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__114 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__114();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__114);
l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__1();
l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__10___closed__2);
l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1);
l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2);
l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3);
l_Lean_Elab_Tactic_Omega_lookup___closed__1 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__1);
l_Lean_Elab_Tactic_Omega_lookup___closed__2 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__2);
l_Lean_Elab_Tactic_Omega_lookup___closed__3 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__3);
l_Lean_Elab_Tactic_Omega_lookup___closed__4 = _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

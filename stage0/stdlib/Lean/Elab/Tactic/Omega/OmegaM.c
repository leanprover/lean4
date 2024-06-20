// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: Init.Omega.LinearCombo Init.Omega.Int Init.Omega.Logic Init.Data.BitVec.Basic Lean.Meta.AppBuilder Lean.Meta.Canonicalizer
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22;
LEAN_EXPORT lean_object* l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_intCast_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3;
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__5(size_t, size_t, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
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
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80;
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f_op(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_State_atoms___default;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_State_atoms___default___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__2;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__6(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static uint8_t l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__6;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1;
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4(lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Elab_Tactic_Omega_lookup___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
static lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21;
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__12(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62;
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f_op(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91;
extern lean_object* l_Lean_inheritedTraceOptions;
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
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
static lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59;
static lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_State_atoms___default___spec__1___boxed(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__2(lean_object*, lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_commitWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_object* l_Int_toNat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList___boxed(lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atomsList(lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Elab_Tactic_Omega_lookup___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run(lean_object*);
lean_object* l_List_map___at_Lean_MessageData_instCoeListExpr___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43;
lean_object* l_Nat_pow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10(lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
lean_object* l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105;
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_withoutModifyingState___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_State_atoms___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_State_atoms___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_State_atoms___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_State_atoms___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg___boxed), 9, 0);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_unsigned_to_nat(8u);
x_9 = l_Lean_mkHashMapImp___rarg(x_8);
x_10 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1;
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1___boxed), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__2___boxed), 11, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg___boxed), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg___boxed), 9, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = 3;
x_17 = l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3;
x_18 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg(x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_ReaderT_bind___at_Lean_Elab_Tactic_Omega_OmegaM_run___spec__2___rarg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__2(x_4, x_6);
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
static lean_object* _init_l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__3(x_2, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_14, x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4(x_13, x_17, x_16);
lean_dec(x_16);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__5(x_20, x_21, x_18);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1(x_23);
lean_dec(x_23);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4(x_25, x_29, x_28);
lean_dec(x_28);
x_31 = lean_array_get_size(x_30);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = 0;
x_34 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__5(x_32, x_33, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_atoms___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_atoms___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_Omega_atoms___spec__5(x_4, x_5, x_3);
return x_6;
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
x_13 = lean_array_to_list(lean_box(0), x_11);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_disjunction", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__4;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_max_right", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__15;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_left", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__20;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("min_le_right", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__23;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_ofNat_nonneg", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTNat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pos_pow_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_pos_of_pos", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_nonneg", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__47;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ne_of_gt", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52;
x_2 = lean_int_dec_le(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_lt_of_pos", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLTInt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
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
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ne", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul_ediv_self_le", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__84;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_mul_ediv_self_add", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__89;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_nonneg", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isLt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("val", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natAbs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_natAbs", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg_le_natAbs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__107;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__108;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat_sub_dichotomy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__110;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__111;
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
x_19 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2;
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
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
x_25 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
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
x_38 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_38);
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7;
x_40 = l_Lean_mkApp5(x_39, x_27, x_29, x_31, x_33, x_35);
x_41 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_42 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_41, x_40);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_42);
return x_12;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_dec(x_12);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
x_47 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_11);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_array_get_size(x_43);
x_50 = lean_unsigned_to_nat(5u);
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
x_52 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_11);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_fget(x_43, x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_array_fget(x_43, x_56);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_array_fget(x_43, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_array_fget(x_43, x_60);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_array_fget(x_43, x_62);
lean_dec(x_43);
x_64 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3;
x_65 = lean_expr_eqv(x_55, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
x_66 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_11);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7;
x_69 = l_Lean_mkApp5(x_68, x_55, x_57, x_59, x_61, x_63);
x_70 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_71 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_70, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_11);
return x_72;
}
}
}
}
}
case 1:
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_14, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_12);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_12, 1);
x_76 = lean_ctor_get(x_12, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_13, 1);
lean_inc(x_77);
lean_dec(x_13);
x_78 = lean_ctor_get(x_14, 1);
lean_inc(x_78);
lean_dec(x_14);
x_79 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_80 = lean_string_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_82 = lean_string_dec_eq(x_78, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8;
x_84 = lean_string_dec_eq(x_78, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_85 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_86 = lean_string_dec_eq(x_78, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10;
x_88 = lean_string_dec_eq(x_78, x_87);
lean_dec(x_78);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_77);
lean_dec(x_75);
x_89 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_89);
return x_12;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11;
x_91 = lean_string_dec_eq(x_77, x_90);
lean_dec(x_77);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_75);
x_92 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_92);
return x_12;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_array_get_size(x_75);
x_94 = lean_unsigned_to_nat(4u);
x_95 = lean_nat_dec_eq(x_93, x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_75);
x_96 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_96);
return x_12;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_97 = lean_unsigned_to_nat(2u);
x_98 = lean_array_fget(x_75, x_97);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_array_fget(x_75, x_99);
lean_dec(x_75);
x_101 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14;
lean_inc(x_100);
lean_inc(x_98);
x_102 = l_Lean_mkAppB(x_101, x_98, x_100);
x_103 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17;
x_104 = l_Lean_mkAppB(x_103, x_98, x_100);
x_105 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_106 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_105, x_102);
x_107 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_106, x_104);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_107);
return x_12;
}
}
}
}
else
{
lean_object* x_108; uint8_t x_109; 
lean_dec(x_78);
x_108 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18;
x_109 = lean_string_dec_eq(x_77, x_108);
lean_dec(x_77);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_75);
x_110 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_110);
return x_12;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_array_get_size(x_75);
x_112 = lean_unsigned_to_nat(4u);
x_113 = lean_nat_dec_eq(x_111, x_112);
lean_dec(x_111);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_75);
x_114 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_114);
return x_12;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_115 = lean_unsigned_to_nat(2u);
x_116 = lean_array_fget(x_75, x_115);
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_array_fget(x_75, x_117);
lean_dec(x_75);
x_119 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21;
lean_inc(x_118);
lean_inc(x_116);
x_120 = l_Lean_mkAppB(x_119, x_116, x_118);
x_121 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24;
x_122 = l_Lean_mkAppB(x_121, x_116, x_118);
x_123 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_124 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_123, x_120);
x_125 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_124, x_122);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_125);
return x_12;
}
}
}
}
else
{
lean_object* x_126; uint8_t x_127; 
lean_dec(x_78);
x_126 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25;
x_127 = lean_string_dec_eq(x_77, x_126);
lean_dec(x_77);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_128 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_128);
return x_12;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_array_get_size(x_75);
x_130 = lean_unsigned_to_nat(6u);
x_131 = lean_nat_dec_eq(x_129, x_130);
lean_dec(x_129);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_132 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_132);
return x_12;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_free_object(x_12);
x_133 = lean_unsigned_to_nat(4u);
x_134 = lean_array_fget(x_75, x_133);
x_135 = lean_unsigned_to_nat(5u);
x_136 = lean_array_fget(x_75, x_135);
lean_dec(x_75);
lean_inc(x_136);
x_137 = l_Lean_Expr_getAppFnArgs(x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 1)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 1)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_137);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_142 = lean_ctor_get(x_137, 1);
x_143 = lean_ctor_get(x_137, 0);
lean_dec(x_143);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_dec(x_138);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
x_146 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_147 = lean_string_dec_eq(x_145, x_146);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = lean_string_dec_eq(x_145, x_79);
lean_dec(x_145);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_149 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_149);
return x_137;
}
else
{
lean_object* x_150; uint8_t x_151; 
x_150 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_151 = lean_string_dec_eq(x_144, x_150);
lean_dec(x_144);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_152 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_152);
return x_137;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_array_get_size(x_142);
x_154 = lean_unsigned_to_nat(3u);
x_155 = lean_nat_dec_eq(x_153, x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_156 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_156);
return x_137;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_array_fget(x_142, x_157);
if (lean_obj_tag(x_158) == 4)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 1)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_164 = lean_string_dec_eq(x_162, x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_161);
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_165 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_165);
return x_137;
}
else
{
lean_free_object(x_137);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_unsigned_to_nat(2u);
x_167 = lean_array_fget(x_142, x_166);
lean_dec(x_142);
lean_inc(x_167);
x_168 = l_Lean_Expr_getAppFnArgs(x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 1)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 1)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_168);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = lean_ctor_get(x_168, 1);
x_174 = lean_ctor_get(x_168, 0);
lean_dec(x_174);
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
lean_dec(x_170);
x_177 = lean_string_dec_eq(x_176, x_146);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_175);
lean_free_object(x_168);
lean_dec(x_173);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_178 = l_Lean_Expr_getAppFnArgs(x_134);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_obj_tag(x_179) == 1)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 1)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_178);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_178, 1);
x_184 = lean_ctor_get(x_178, 0);
lean_dec(x_184);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_dec(x_179);
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
lean_dec(x_180);
x_187 = lean_string_dec_eq(x_186, x_79);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_136);
x_188 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_188);
return x_178;
}
else
{
uint8_t x_189; 
x_189 = lean_string_dec_eq(x_185, x_150);
lean_dec(x_185);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_183);
lean_dec(x_136);
x_190 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_190);
return x_178;
}
else
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_array_get_size(x_183);
x_192 = lean_nat_dec_eq(x_191, x_154);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_183);
lean_dec(x_136);
x_193 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_193);
return x_178;
}
else
{
lean_object* x_194; 
x_194 = lean_array_fget(x_183, x_157);
if (lean_obj_tag(x_194) == 4)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 1)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_string_dec_eq(x_198, x_163);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; 
lean_dec(x_197);
lean_dec(x_183);
lean_dec(x_136);
x_200 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_200);
return x_178;
}
else
{
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_array_fget(x_183, x_166);
lean_dec(x_183);
x_202 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_203 = l_Lean_mkAppB(x_202, x_201, x_136);
x_204 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_205 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_204, x_203);
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_205);
return x_178;
}
else
{
uint8_t x_206; 
lean_free_object(x_178);
lean_dec(x_183);
lean_dec(x_136);
x_206 = !lean_is_exclusive(x_197);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_197, 1);
lean_dec(x_207);
x_208 = lean_ctor_get(x_197, 0);
lean_dec(x_208);
x_209 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_197, 0);
lean_ctor_set(x_197, 1, x_11);
lean_ctor_set(x_197, 0, x_209);
return x_197;
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_197);
x_210 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_11);
return x_211;
}
}
}
}
else
{
lean_object* x_212; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_183);
lean_dec(x_136);
x_212 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_212);
return x_178;
}
}
else
{
lean_object* x_213; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_183);
lean_dec(x_136);
x_213 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_213);
return x_178;
}
}
else
{
lean_object* x_214; 
lean_dec(x_194);
lean_dec(x_183);
lean_dec(x_136);
x_214 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_214);
return x_178;
}
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_178, 1);
lean_inc(x_215);
lean_dec(x_178);
x_216 = lean_ctor_get(x_179, 1);
lean_inc(x_216);
lean_dec(x_179);
x_217 = lean_ctor_get(x_180, 1);
lean_inc(x_217);
lean_dec(x_180);
x_218 = lean_string_dec_eq(x_217, x_79);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_136);
x_219 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_11);
return x_220;
}
else
{
uint8_t x_221; 
x_221 = lean_string_dec_eq(x_216, x_150);
lean_dec(x_216);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_215);
lean_dec(x_136);
x_222 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_11);
return x_223;
}
else
{
lean_object* x_224; uint8_t x_225; 
x_224 = lean_array_get_size(x_215);
x_225 = lean_nat_dec_eq(x_224, x_154);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_215);
lean_dec(x_136);
x_226 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_11);
return x_227;
}
else
{
lean_object* x_228; 
x_228 = lean_array_fget(x_215, x_157);
if (lean_obj_tag(x_228) == 4)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 1)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = lean_string_dec_eq(x_232, x_163);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_231);
lean_dec(x_215);
lean_dec(x_136);
x_234 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_11);
return x_235;
}
else
{
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_array_fget(x_215, x_166);
lean_dec(x_215);
x_237 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_238 = l_Lean_mkAppB(x_237, x_236, x_136);
x_239 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_240 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_239, x_238);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_11);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_215);
lean_dec(x_136);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_242 = x_231;
} else {
 lean_dec_ref(x_231);
 x_242 = lean_box(0);
}
x_243 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_242;
 lean_ctor_set_tag(x_244, 0);
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_11);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_215);
lean_dec(x_136);
x_245 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_11);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_215);
lean_dec(x_136);
x_247 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_11);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_228);
lean_dec(x_215);
lean_dec(x_136);
x_249 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_11);
return x_250;
}
}
}
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_136);
x_251 = !lean_is_exclusive(x_178);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_178, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_178, 0);
lean_dec(x_253);
x_254 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_254);
return x_178;
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_178);
x_255 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_11);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_136);
x_257 = !lean_is_exclusive(x_178);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_178, 1);
lean_dec(x_258);
x_259 = lean_ctor_get(x_178, 0);
lean_dec(x_259);
x_260 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_260);
return x_178;
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_178);
x_261 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_11);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_179);
lean_dec(x_136);
x_263 = !lean_is_exclusive(x_178);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_178, 1);
lean_dec(x_264);
x_265 = lean_ctor_get(x_178, 0);
lean_dec(x_265);
x_266 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_178, 1, x_11);
lean_ctor_set(x_178, 0, x_266);
return x_178;
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_178);
x_267 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_11);
return x_268;
}
}
}
else
{
lean_object* x_269; uint8_t x_270; 
x_269 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_270 = lean_string_dec_eq(x_175, x_269);
lean_dec(x_175);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
lean_free_object(x_168);
lean_dec(x_173);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_271 = l_Lean_Expr_getAppFnArgs(x_134);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 1)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 1)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_271);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_276 = lean_ctor_get(x_271, 1);
x_277 = lean_ctor_get(x_271, 0);
lean_dec(x_277);
x_278 = lean_ctor_get(x_272, 1);
lean_inc(x_278);
lean_dec(x_272);
x_279 = lean_ctor_get(x_273, 1);
lean_inc(x_279);
lean_dec(x_273);
x_280 = lean_string_dec_eq(x_279, x_79);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; 
lean_dec(x_278);
lean_dec(x_276);
lean_dec(x_136);
x_281 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_281);
return x_271;
}
else
{
uint8_t x_282; 
x_282 = lean_string_dec_eq(x_278, x_150);
lean_dec(x_278);
if (x_282 == 0)
{
lean_object* x_283; 
lean_dec(x_276);
lean_dec(x_136);
x_283 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_283);
return x_271;
}
else
{
lean_object* x_284; uint8_t x_285; 
x_284 = lean_array_get_size(x_276);
x_285 = lean_nat_dec_eq(x_284, x_154);
lean_dec(x_284);
if (x_285 == 0)
{
lean_object* x_286; 
lean_dec(x_276);
lean_dec(x_136);
x_286 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_286);
return x_271;
}
else
{
lean_object* x_287; 
x_287 = lean_array_fget(x_276, x_157);
if (lean_obj_tag(x_287) == 4)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 1)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
lean_dec(x_287);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_string_dec_eq(x_291, x_163);
lean_dec(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
lean_dec(x_290);
lean_dec(x_276);
lean_dec(x_136);
x_293 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_293);
return x_271;
}
else
{
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_array_fget(x_276, x_166);
lean_dec(x_276);
x_295 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_296 = l_Lean_mkAppB(x_295, x_294, x_136);
x_297 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_298 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_297, x_296);
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_298);
return x_271;
}
else
{
uint8_t x_299; 
lean_free_object(x_271);
lean_dec(x_276);
lean_dec(x_136);
x_299 = !lean_is_exclusive(x_290);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_290, 1);
lean_dec(x_300);
x_301 = lean_ctor_get(x_290, 0);
lean_dec(x_301);
x_302 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_290, 0);
lean_ctor_set(x_290, 1, x_11);
lean_ctor_set(x_290, 0, x_302);
return x_290;
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_290);
x_303 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_11);
return x_304;
}
}
}
}
else
{
lean_object* x_305; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_276);
lean_dec(x_136);
x_305 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_305);
return x_271;
}
}
else
{
lean_object* x_306; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_276);
lean_dec(x_136);
x_306 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_306);
return x_271;
}
}
else
{
lean_object* x_307; 
lean_dec(x_287);
lean_dec(x_276);
lean_dec(x_136);
x_307 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_307);
return x_271;
}
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_308 = lean_ctor_get(x_271, 1);
lean_inc(x_308);
lean_dec(x_271);
x_309 = lean_ctor_get(x_272, 1);
lean_inc(x_309);
lean_dec(x_272);
x_310 = lean_ctor_get(x_273, 1);
lean_inc(x_310);
lean_dec(x_273);
x_311 = lean_string_dec_eq(x_310, x_79);
lean_dec(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_136);
x_312 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_11);
return x_313;
}
else
{
uint8_t x_314; 
x_314 = lean_string_dec_eq(x_309, x_150);
lean_dec(x_309);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_308);
lean_dec(x_136);
x_315 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_11);
return x_316;
}
else
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_array_get_size(x_308);
x_318 = lean_nat_dec_eq(x_317, x_154);
lean_dec(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_308);
lean_dec(x_136);
x_319 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_11);
return x_320;
}
else
{
lean_object* x_321; 
x_321 = lean_array_fget(x_308, x_157);
if (lean_obj_tag(x_321) == 4)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 1)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
lean_dec(x_321);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_string_dec_eq(x_325, x_163);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; 
lean_dec(x_324);
lean_dec(x_308);
lean_dec(x_136);
x_327 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_11);
return x_328;
}
else
{
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_329 = lean_array_fget(x_308, x_166);
lean_dec(x_308);
x_330 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_331 = l_Lean_mkAppB(x_330, x_329, x_136);
x_332 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_333 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_332, x_331);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_11);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_308);
lean_dec(x_136);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_335 = x_324;
} else {
 lean_dec_ref(x_324);
 x_335 = lean_box(0);
}
x_336 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_335)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_335;
 lean_ctor_set_tag(x_337, 0);
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_11);
return x_337;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_308);
lean_dec(x_136);
x_338 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_11);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_308);
lean_dec(x_136);
x_340 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_11);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_321);
lean_dec(x_308);
lean_dec(x_136);
x_342 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_11);
return x_343;
}
}
}
}
}
}
else
{
uint8_t x_344; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_136);
x_344 = !lean_is_exclusive(x_271);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_271, 1);
lean_dec(x_345);
x_346 = lean_ctor_get(x_271, 0);
lean_dec(x_346);
x_347 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_347);
return x_271;
}
else
{
lean_object* x_348; lean_object* x_349; 
lean_dec(x_271);
x_348 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_11);
return x_349;
}
}
}
else
{
uint8_t x_350; 
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_136);
x_350 = !lean_is_exclusive(x_271);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_271, 1);
lean_dec(x_351);
x_352 = lean_ctor_get(x_271, 0);
lean_dec(x_352);
x_353 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_353);
return x_271;
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_271);
x_354 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_11);
return x_355;
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_272);
lean_dec(x_136);
x_356 = !lean_is_exclusive(x_271);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_271, 1);
lean_dec(x_357);
x_358 = lean_ctor_get(x_271, 0);
lean_dec(x_358);
x_359 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_271, 1, x_11);
lean_ctor_set(x_271, 0, x_359);
return x_271;
}
else
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_271);
x_360 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_11);
return x_361;
}
}
}
else
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_array_get_size(x_173);
x_363 = lean_nat_dec_eq(x_362, x_130);
lean_dec(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
lean_free_object(x_168);
lean_dec(x_173);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_364 = l_Lean_Expr_getAppFnArgs(x_134);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
if (lean_obj_tag(x_365) == 1)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 1)
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
uint8_t x_368; 
x_368 = !lean_is_exclusive(x_364);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_369 = lean_ctor_get(x_364, 1);
x_370 = lean_ctor_get(x_364, 0);
lean_dec(x_370);
x_371 = lean_ctor_get(x_365, 1);
lean_inc(x_371);
lean_dec(x_365);
x_372 = lean_ctor_get(x_366, 1);
lean_inc(x_372);
lean_dec(x_366);
x_373 = lean_string_dec_eq(x_372, x_79);
lean_dec(x_372);
if (x_373 == 0)
{
lean_object* x_374; 
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_136);
x_374 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_374);
return x_364;
}
else
{
uint8_t x_375; 
x_375 = lean_string_dec_eq(x_371, x_150);
lean_dec(x_371);
if (x_375 == 0)
{
lean_object* x_376; 
lean_dec(x_369);
lean_dec(x_136);
x_376 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_376);
return x_364;
}
else
{
lean_object* x_377; uint8_t x_378; 
x_377 = lean_array_get_size(x_369);
x_378 = lean_nat_dec_eq(x_377, x_154);
lean_dec(x_377);
if (x_378 == 0)
{
lean_object* x_379; 
lean_dec(x_369);
lean_dec(x_136);
x_379 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_379);
return x_364;
}
else
{
lean_object* x_380; 
x_380 = lean_array_fget(x_369, x_157);
if (lean_obj_tag(x_380) == 4)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 1)
{
lean_object* x_382; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_dec(x_380);
x_384 = lean_ctor_get(x_381, 1);
lean_inc(x_384);
lean_dec(x_381);
x_385 = lean_string_dec_eq(x_384, x_163);
lean_dec(x_384);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_383);
lean_dec(x_369);
lean_dec(x_136);
x_386 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_386);
return x_364;
}
else
{
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_array_fget(x_369, x_166);
lean_dec(x_369);
x_388 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_389 = l_Lean_mkAppB(x_388, x_387, x_136);
x_390 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_391 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_390, x_389);
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_391);
return x_364;
}
else
{
uint8_t x_392; 
lean_free_object(x_364);
lean_dec(x_369);
lean_dec(x_136);
x_392 = !lean_is_exclusive(x_383);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_383, 1);
lean_dec(x_393);
x_394 = lean_ctor_get(x_383, 0);
lean_dec(x_394);
x_395 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_383, 0);
lean_ctor_set(x_383, 1, x_11);
lean_ctor_set(x_383, 0, x_395);
return x_383;
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_383);
x_396 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_11);
return x_397;
}
}
}
}
else
{
lean_object* x_398; 
lean_dec(x_382);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_369);
lean_dec(x_136);
x_398 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_398);
return x_364;
}
}
else
{
lean_object* x_399; 
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_369);
lean_dec(x_136);
x_399 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_399);
return x_364;
}
}
else
{
lean_object* x_400; 
lean_dec(x_380);
lean_dec(x_369);
lean_dec(x_136);
x_400 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_400);
return x_364;
}
}
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_401 = lean_ctor_get(x_364, 1);
lean_inc(x_401);
lean_dec(x_364);
x_402 = lean_ctor_get(x_365, 1);
lean_inc(x_402);
lean_dec(x_365);
x_403 = lean_ctor_get(x_366, 1);
lean_inc(x_403);
lean_dec(x_366);
x_404 = lean_string_dec_eq(x_403, x_79);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; 
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_136);
x_405 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_11);
return x_406;
}
else
{
uint8_t x_407; 
x_407 = lean_string_dec_eq(x_402, x_150);
lean_dec(x_402);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; 
lean_dec(x_401);
lean_dec(x_136);
x_408 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_11);
return x_409;
}
else
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_array_get_size(x_401);
x_411 = lean_nat_dec_eq(x_410, x_154);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_401);
lean_dec(x_136);
x_412 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_11);
return x_413;
}
else
{
lean_object* x_414; 
x_414 = lean_array_fget(x_401, x_157);
if (lean_obj_tag(x_414) == 4)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 1)
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
lean_dec(x_414);
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
lean_dec(x_415);
x_419 = lean_string_dec_eq(x_418, x_163);
lean_dec(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; 
lean_dec(x_417);
lean_dec(x_401);
lean_dec(x_136);
x_420 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_11);
return x_421;
}
else
{
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_422 = lean_array_fget(x_401, x_166);
lean_dec(x_401);
x_423 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_424 = l_Lean_mkAppB(x_423, x_422, x_136);
x_425 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_426 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_425, x_424);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_11);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_401);
lean_dec(x_136);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_428 = x_417;
} else {
 lean_dec_ref(x_417);
 x_428 = lean_box(0);
}
x_429 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_428)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_428;
 lean_ctor_set_tag(x_430, 0);
}
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_11);
return x_430;
}
}
}
else
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_401);
lean_dec(x_136);
x_431 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_11);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; 
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_401);
lean_dec(x_136);
x_433 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_11);
return x_434;
}
}
else
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_414);
lean_dec(x_401);
lean_dec(x_136);
x_435 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_11);
return x_436;
}
}
}
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_136);
x_437 = !lean_is_exclusive(x_364);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_364, 1);
lean_dec(x_438);
x_439 = lean_ctor_get(x_364, 0);
lean_dec(x_439);
x_440 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_440);
return x_364;
}
else
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_364);
x_441 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_11);
return x_442;
}
}
}
else
{
uint8_t x_443; 
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_136);
x_443 = !lean_is_exclusive(x_364);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_364, 1);
lean_dec(x_444);
x_445 = lean_ctor_get(x_364, 0);
lean_dec(x_445);
x_446 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_446);
return x_364;
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_364);
x_447 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_11);
return x_448;
}
}
}
else
{
uint8_t x_449; 
lean_dec(x_365);
lean_dec(x_136);
x_449 = !lean_is_exclusive(x_364);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_364, 1);
lean_dec(x_450);
x_451 = lean_ctor_get(x_364, 0);
lean_dec(x_451);
x_452 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_364, 1, x_11);
lean_ctor_set(x_364, 0, x_452);
return x_364;
}
else
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_364);
x_453 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_11);
return x_454;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_array_fget(x_173, x_133);
x_456 = lean_array_fget(x_173, x_135);
lean_dec(x_173);
lean_inc(x_455);
x_457 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_455);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; 
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_167);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_458 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_168, 1, x_11);
lean_ctor_set(x_168, 0, x_458);
return x_168;
}
else
{
lean_object* x_459; uint8_t x_460; 
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
lean_dec(x_457);
x_460 = lean_nat_dec_eq(x_459, x_157);
lean_dec(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_free_object(x_168);
x_461 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_462 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_463 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
x_464 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
lean_inc(x_455);
x_465 = l_Lean_mkApp4(x_461, x_462, x_463, x_464, x_455);
x_466 = l_Lean_Meta_mkDecideProof(x_465, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_466) == 0)
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_466);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; 
x_468 = lean_ctor_get(x_466, 0);
x_469 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_470 = l_Lean_mkApp3(x_469, x_455, x_456, x_468);
x_471 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_472 = l_Lean_mkAppB(x_471, x_167, x_470);
x_473 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_inc(x_472);
lean_inc(x_136);
lean_inc(x_134);
x_474 = l_Lean_mkApp3(x_473, x_134, x_136, x_472);
x_475 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_475 == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_476 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_477 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
lean_inc(x_136);
x_478 = l_Lean_mkApp3(x_476, x_136, x_477, x_472);
x_479 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_480 = l_Lean_mkApp3(x_479, x_134, x_136, x_478);
x_481 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_482 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_481, x_480);
x_483 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_482, x_474);
lean_ctor_set(x_466, 0, x_483);
return x_466;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_484 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_485 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_136);
x_486 = l_Lean_mkApp3(x_484, x_136, x_485, x_472);
x_487 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_488 = l_Lean_mkApp3(x_487, x_134, x_136, x_486);
x_489 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_490 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_489, x_488);
x_491 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_490, x_474);
lean_ctor_set(x_466, 0, x_491);
return x_466;
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_492 = lean_ctor_get(x_466, 0);
x_493 = lean_ctor_get(x_466, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_466);
x_494 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_495 = l_Lean_mkApp3(x_494, x_455, x_456, x_492);
x_496 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_497 = l_Lean_mkAppB(x_496, x_167, x_495);
x_498 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_inc(x_497);
lean_inc(x_136);
lean_inc(x_134);
x_499 = l_Lean_mkApp3(x_498, x_134, x_136, x_497);
x_500 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_501 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_502 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
lean_inc(x_136);
x_503 = l_Lean_mkApp3(x_501, x_136, x_502, x_497);
x_504 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_505 = l_Lean_mkApp3(x_504, x_134, x_136, x_503);
x_506 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_507 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_506, x_505);
x_508 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_507, x_499);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_493);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_510 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_511 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_136);
x_512 = l_Lean_mkApp3(x_510, x_136, x_511, x_497);
x_513 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_514 = l_Lean_mkApp3(x_513, x_134, x_136, x_512);
x_515 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_516 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_515, x_514);
x_517 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_516, x_499);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_493);
return x_518;
}
}
}
else
{
uint8_t x_519; 
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_167);
lean_dec(x_136);
lean_dec(x_134);
x_519 = !lean_is_exclusive(x_466);
if (x_519 == 0)
{
return x_466;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_466, 0);
x_521 = lean_ctor_get(x_466, 1);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_466);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
return x_522;
}
}
}
else
{
lean_object* x_523; 
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_167);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_523 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_168, 1, x_11);
lean_ctor_set(x_168, 0, x_523);
return x_168;
}
}
}
}
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_524 = lean_ctor_get(x_168, 1);
lean_inc(x_524);
lean_dec(x_168);
x_525 = lean_ctor_get(x_169, 1);
lean_inc(x_525);
lean_dec(x_169);
x_526 = lean_ctor_get(x_170, 1);
lean_inc(x_526);
lean_dec(x_170);
x_527 = lean_string_dec_eq(x_526, x_146);
lean_dec(x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; 
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_528 = l_Lean_Expr_getAppFnArgs(x_134);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
if (lean_obj_tag(x_529) == 1)
{
lean_object* x_530; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
if (lean_obj_tag(x_530) == 1)
{
lean_object* x_531; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; 
x_532 = lean_ctor_get(x_528, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_533 = x_528;
} else {
 lean_dec_ref(x_528);
 x_533 = lean_box(0);
}
x_534 = lean_ctor_get(x_529, 1);
lean_inc(x_534);
lean_dec(x_529);
x_535 = lean_ctor_get(x_530, 1);
lean_inc(x_535);
lean_dec(x_530);
x_536 = lean_string_dec_eq(x_535, x_79);
lean_dec(x_535);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; 
lean_dec(x_534);
lean_dec(x_532);
lean_dec(x_136);
x_537 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_533)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_533;
}
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_11);
return x_538;
}
else
{
uint8_t x_539; 
x_539 = lean_string_dec_eq(x_534, x_150);
lean_dec(x_534);
if (x_539 == 0)
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_532);
lean_dec(x_136);
x_540 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_533)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_533;
}
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_11);
return x_541;
}
else
{
lean_object* x_542; uint8_t x_543; 
x_542 = lean_array_get_size(x_532);
x_543 = lean_nat_dec_eq(x_542, x_154);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; 
lean_dec(x_532);
lean_dec(x_136);
x_544 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_533)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_533;
}
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_11);
return x_545;
}
else
{
lean_object* x_546; 
x_546 = lean_array_fget(x_532, x_157);
if (lean_obj_tag(x_546) == 4)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
if (lean_obj_tag(x_547) == 1)
{
lean_object* x_548; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; uint8_t x_551; 
x_549 = lean_ctor_get(x_546, 1);
lean_inc(x_549);
lean_dec(x_546);
x_550 = lean_ctor_get(x_547, 1);
lean_inc(x_550);
lean_dec(x_547);
x_551 = lean_string_dec_eq(x_550, x_163);
lean_dec(x_550);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_549);
lean_dec(x_532);
lean_dec(x_136);
x_552 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_533)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_533;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_11);
return x_553;
}
else
{
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_554 = lean_array_fget(x_532, x_166);
lean_dec(x_532);
x_555 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_556 = l_Lean_mkAppB(x_555, x_554, x_136);
x_557 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_558 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_557, x_556);
if (lean_is_scalar(x_533)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_533;
}
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_11);
return x_559;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_136);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_560 = x_549;
} else {
 lean_dec_ref(x_549);
 x_560 = lean_box(0);
}
x_561 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_560)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_560;
 lean_ctor_set_tag(x_562, 0);
}
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_11);
return x_562;
}
}
}
else
{
lean_object* x_563; lean_object* x_564; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_532);
lean_dec(x_136);
x_563 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_533)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_533;
}
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_11);
return x_564;
}
}
else
{
lean_object* x_565; lean_object* x_566; 
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_532);
lean_dec(x_136);
x_565 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_533)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_533;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_11);
return x_566;
}
}
else
{
lean_object* x_567; lean_object* x_568; 
lean_dec(x_546);
lean_dec(x_532);
lean_dec(x_136);
x_567 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_533)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_533;
}
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_11);
return x_568;
}
}
}
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_531);
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_136);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_569 = x_528;
} else {
 lean_dec_ref(x_528);
 x_569 = lean_box(0);
}
x_570 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_569)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_569;
}
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_11);
return x_571;
}
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_136);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_572 = x_528;
} else {
 lean_dec_ref(x_528);
 x_572 = lean_box(0);
}
x_573 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_572)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_572;
}
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_11);
return x_574;
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_529);
lean_dec(x_136);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_575 = x_528;
} else {
 lean_dec_ref(x_528);
 x_575 = lean_box(0);
}
x_576 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_575)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_575;
}
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_11);
return x_577;
}
}
else
{
lean_object* x_578; uint8_t x_579; 
x_578 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_579 = lean_string_dec_eq(x_525, x_578);
lean_dec(x_525);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_524);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_580 = l_Lean_Expr_getAppFnArgs(x_134);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
if (lean_obj_tag(x_581) == 1)
{
lean_object* x_582; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
if (lean_obj_tag(x_582) == 1)
{
lean_object* x_583; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; 
x_584 = lean_ctor_get(x_580, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_585 = x_580;
} else {
 lean_dec_ref(x_580);
 x_585 = lean_box(0);
}
x_586 = lean_ctor_get(x_581, 1);
lean_inc(x_586);
lean_dec(x_581);
x_587 = lean_ctor_get(x_582, 1);
lean_inc(x_587);
lean_dec(x_582);
x_588 = lean_string_dec_eq(x_587, x_79);
lean_dec(x_587);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
lean_dec(x_586);
lean_dec(x_584);
lean_dec(x_136);
x_589 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_585)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_585;
}
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_11);
return x_590;
}
else
{
uint8_t x_591; 
x_591 = lean_string_dec_eq(x_586, x_150);
lean_dec(x_586);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; 
lean_dec(x_584);
lean_dec(x_136);
x_592 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_585)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_585;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_11);
return x_593;
}
else
{
lean_object* x_594; uint8_t x_595; 
x_594 = lean_array_get_size(x_584);
x_595 = lean_nat_dec_eq(x_594, x_154);
lean_dec(x_594);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; 
lean_dec(x_584);
lean_dec(x_136);
x_596 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_585)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_585;
}
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_11);
return x_597;
}
else
{
lean_object* x_598; 
x_598 = lean_array_fget(x_584, x_157);
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
x_603 = lean_string_dec_eq(x_602, x_163);
lean_dec(x_602);
if (x_603 == 0)
{
lean_object* x_604; lean_object* x_605; 
lean_dec(x_601);
lean_dec(x_584);
lean_dec(x_136);
x_604 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_585)) {
 x_605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_605 = x_585;
}
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_11);
return x_605;
}
else
{
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_606 = lean_array_fget(x_584, x_166);
lean_dec(x_584);
x_607 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_608 = l_Lean_mkAppB(x_607, x_606, x_136);
x_609 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_610 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_609, x_608);
if (lean_is_scalar(x_585)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_585;
}
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_11);
return x_611;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_136);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_612 = x_601;
} else {
 lean_dec_ref(x_601);
 x_612 = lean_box(0);
}
x_613 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_612)) {
 x_614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_614 = x_612;
 lean_ctor_set_tag(x_614, 0);
}
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_11);
return x_614;
}
}
}
else
{
lean_object* x_615; lean_object* x_616; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_584);
lean_dec(x_136);
x_615 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_585)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_585;
}
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_11);
return x_616;
}
}
else
{
lean_object* x_617; lean_object* x_618; 
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_584);
lean_dec(x_136);
x_617 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_585)) {
 x_618 = lean_alloc_ctor(0, 2, 0);
} else {
 x_618 = x_585;
}
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_11);
return x_618;
}
}
else
{
lean_object* x_619; lean_object* x_620; 
lean_dec(x_598);
lean_dec(x_584);
lean_dec(x_136);
x_619 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_585)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_585;
}
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_11);
return x_620;
}
}
}
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_136);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_621 = x_580;
} else {
 lean_dec_ref(x_580);
 x_621 = lean_box(0);
}
x_622 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_621)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_621;
}
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_11);
return x_623;
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_136);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_624 = x_580;
} else {
 lean_dec_ref(x_580);
 x_624 = lean_box(0);
}
x_625 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_624)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_624;
}
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_11);
return x_626;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_581);
lean_dec(x_136);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_627 = x_580;
} else {
 lean_dec_ref(x_580);
 x_627 = lean_box(0);
}
x_628 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_627)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_627;
}
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_11);
return x_629;
}
}
else
{
lean_object* x_630; uint8_t x_631; 
x_630 = lean_array_get_size(x_524);
x_631 = lean_nat_dec_eq(x_630, x_130);
lean_dec(x_630);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; 
lean_dec(x_524);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_632 = l_Lean_Expr_getAppFnArgs(x_134);
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
if (lean_obj_tag(x_633) == 1)
{
lean_object* x_634; 
x_634 = lean_ctor_get(x_633, 0);
lean_inc(x_634);
if (lean_obj_tag(x_634) == 1)
{
lean_object* x_635; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_636 = lean_ctor_get(x_632, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_637 = x_632;
} else {
 lean_dec_ref(x_632);
 x_637 = lean_box(0);
}
x_638 = lean_ctor_get(x_633, 1);
lean_inc(x_638);
lean_dec(x_633);
x_639 = lean_ctor_get(x_634, 1);
lean_inc(x_639);
lean_dec(x_634);
x_640 = lean_string_dec_eq(x_639, x_79);
lean_dec(x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_638);
lean_dec(x_636);
lean_dec(x_136);
x_641 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_637)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_637;
}
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_11);
return x_642;
}
else
{
uint8_t x_643; 
x_643 = lean_string_dec_eq(x_638, x_150);
lean_dec(x_638);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; 
lean_dec(x_636);
lean_dec(x_136);
x_644 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_637)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_637;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_11);
return x_645;
}
else
{
lean_object* x_646; uint8_t x_647; 
x_646 = lean_array_get_size(x_636);
x_647 = lean_nat_dec_eq(x_646, x_154);
lean_dec(x_646);
if (x_647 == 0)
{
lean_object* x_648; lean_object* x_649; 
lean_dec(x_636);
lean_dec(x_136);
x_648 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_637)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_637;
}
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_11);
return x_649;
}
else
{
lean_object* x_650; 
x_650 = lean_array_fget(x_636, x_157);
if (lean_obj_tag(x_650) == 4)
{
lean_object* x_651; 
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
if (lean_obj_tag(x_651) == 1)
{
lean_object* x_652; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_653 = lean_ctor_get(x_650, 1);
lean_inc(x_653);
lean_dec(x_650);
x_654 = lean_ctor_get(x_651, 1);
lean_inc(x_654);
lean_dec(x_651);
x_655 = lean_string_dec_eq(x_654, x_163);
lean_dec(x_654);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; 
lean_dec(x_653);
lean_dec(x_636);
lean_dec(x_136);
x_656 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_637)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_637;
}
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_11);
return x_657;
}
else
{
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_658 = lean_array_fget(x_636, x_166);
lean_dec(x_636);
x_659 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_660 = l_Lean_mkAppB(x_659, x_658, x_136);
x_661 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_662 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_661, x_660);
if (lean_is_scalar(x_637)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_637;
}
lean_ctor_set(x_663, 0, x_662);
lean_ctor_set(x_663, 1, x_11);
return x_663;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_136);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 lean_ctor_release(x_653, 1);
 x_664 = x_653;
} else {
 lean_dec_ref(x_653);
 x_664 = lean_box(0);
}
x_665 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_664)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_664;
 lean_ctor_set_tag(x_666, 0);
}
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_11);
return x_666;
}
}
}
else
{
lean_object* x_667; lean_object* x_668; 
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_636);
lean_dec(x_136);
x_667 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_637)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_637;
}
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_11);
return x_668;
}
}
else
{
lean_object* x_669; lean_object* x_670; 
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_636);
lean_dec(x_136);
x_669 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_637)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_637;
}
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_11);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; 
lean_dec(x_650);
lean_dec(x_636);
lean_dec(x_136);
x_671 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_637)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_637;
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_11);
return x_672;
}
}
}
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_136);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_673 = x_632;
} else {
 lean_dec_ref(x_632);
 x_673 = lean_box(0);
}
x_674 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_673)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_673;
}
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_11);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_136);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_676 = x_632;
} else {
 lean_dec_ref(x_632);
 x_676 = lean_box(0);
}
x_677 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_676)) {
 x_678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_678 = x_676;
}
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_11);
return x_678;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_633);
lean_dec(x_136);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_679 = x_632;
} else {
 lean_dec_ref(x_632);
 x_679 = lean_box(0);
}
x_680 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_679)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_679;
}
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_11);
return x_681;
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_array_fget(x_524, x_133);
x_683 = lean_array_fget(x_524, x_135);
lean_dec(x_524);
lean_inc(x_682);
x_684 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_682);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; 
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_167);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_685 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_686 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_11);
return x_686;
}
else
{
lean_object* x_687; uint8_t x_688; 
x_687 = lean_ctor_get(x_684, 0);
lean_inc(x_687);
lean_dec(x_684);
x_688 = lean_nat_dec_eq(x_687, x_157);
lean_dec(x_687);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_689 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_690 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_691 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
x_692 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
lean_inc(x_682);
x_693 = l_Lean_mkApp4(x_689, x_690, x_691, x_692, x_682);
x_694 = l_Lean_Meta_mkDecideProof(x_693, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 lean_ctor_release(x_694, 1);
 x_697 = x_694;
} else {
 lean_dec_ref(x_694);
 x_697 = lean_box(0);
}
x_698 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_699 = l_Lean_mkApp3(x_698, x_682, x_683, x_695);
x_700 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_701 = l_Lean_mkAppB(x_700, x_167, x_699);
x_702 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_inc(x_701);
lean_inc(x_136);
lean_inc(x_134);
x_703 = l_Lean_mkApp3(x_702, x_134, x_136, x_701);
x_704 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_705 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_706 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
lean_inc(x_136);
x_707 = l_Lean_mkApp3(x_705, x_136, x_706, x_701);
x_708 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_709 = l_Lean_mkApp3(x_708, x_134, x_136, x_707);
x_710 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_711 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_710, x_709);
x_712 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_711, x_703);
if (lean_is_scalar(x_697)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_697;
}
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_696);
return x_713;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_714 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_715 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_136);
x_716 = l_Lean_mkApp3(x_714, x_136, x_715, x_701);
x_717 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_718 = l_Lean_mkApp3(x_717, x_134, x_136, x_716);
x_719 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_720 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_719, x_718);
x_721 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_720, x_703);
if (lean_is_scalar(x_697)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_697;
}
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_696);
return x_722;
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_167);
lean_dec(x_136);
lean_dec(x_134);
x_723 = lean_ctor_get(x_694, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_694, 1);
lean_inc(x_724);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 lean_ctor_release(x_694, 1);
 x_725 = x_694;
} else {
 lean_dec_ref(x_694);
 x_725 = lean_box(0);
}
if (lean_is_scalar(x_725)) {
 x_726 = lean_alloc_ctor(1, 2, 0);
} else {
 x_726 = x_725;
}
lean_ctor_set(x_726, 0, x_723);
lean_ctor_set(x_726, 1, x_724);
return x_726;
}
}
else
{
lean_object* x_727; lean_object* x_728; 
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_167);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_727 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_728 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_11);
return x_728;
}
}
}
}
}
}
}
else
{
lean_object* x_729; lean_object* x_730; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_729 = l_Lean_Expr_getAppFnArgs(x_134);
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
if (lean_obj_tag(x_730) == 1)
{
lean_object* x_731; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
if (lean_obj_tag(x_731) == 1)
{
lean_object* x_732; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
if (lean_obj_tag(x_732) == 0)
{
uint8_t x_733; 
x_733 = !lean_is_exclusive(x_729);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; 
x_734 = lean_ctor_get(x_729, 1);
x_735 = lean_ctor_get(x_729, 0);
lean_dec(x_735);
x_736 = lean_ctor_get(x_730, 1);
lean_inc(x_736);
lean_dec(x_730);
x_737 = lean_ctor_get(x_731, 1);
lean_inc(x_737);
lean_dec(x_731);
x_738 = lean_string_dec_eq(x_737, x_79);
lean_dec(x_737);
if (x_738 == 0)
{
lean_object* x_739; 
lean_dec(x_736);
lean_dec(x_734);
lean_dec(x_136);
x_739 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_739);
return x_729;
}
else
{
uint8_t x_740; 
x_740 = lean_string_dec_eq(x_736, x_150);
lean_dec(x_736);
if (x_740 == 0)
{
lean_object* x_741; 
lean_dec(x_734);
lean_dec(x_136);
x_741 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_741);
return x_729;
}
else
{
lean_object* x_742; uint8_t x_743; 
x_742 = lean_array_get_size(x_734);
x_743 = lean_nat_dec_eq(x_742, x_154);
lean_dec(x_742);
if (x_743 == 0)
{
lean_object* x_744; 
lean_dec(x_734);
lean_dec(x_136);
x_744 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_744);
return x_729;
}
else
{
lean_object* x_745; 
x_745 = lean_array_fget(x_734, x_157);
if (lean_obj_tag(x_745) == 4)
{
lean_object* x_746; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
if (lean_obj_tag(x_746) == 1)
{
lean_object* x_747; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; uint8_t x_750; 
x_748 = lean_ctor_get(x_745, 1);
lean_inc(x_748);
lean_dec(x_745);
x_749 = lean_ctor_get(x_746, 1);
lean_inc(x_749);
lean_dec(x_746);
x_750 = lean_string_dec_eq(x_749, x_163);
lean_dec(x_749);
if (x_750 == 0)
{
lean_object* x_751; 
lean_dec(x_748);
lean_dec(x_734);
lean_dec(x_136);
x_751 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_751);
return x_729;
}
else
{
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_752 = lean_array_fget(x_734, x_166);
lean_dec(x_734);
x_753 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_754 = l_Lean_mkAppB(x_753, x_752, x_136);
x_755 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_756 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_755, x_754);
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_756);
return x_729;
}
else
{
uint8_t x_757; 
lean_free_object(x_729);
lean_dec(x_734);
lean_dec(x_136);
x_757 = !lean_is_exclusive(x_748);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_758 = lean_ctor_get(x_748, 1);
lean_dec(x_758);
x_759 = lean_ctor_get(x_748, 0);
lean_dec(x_759);
x_760 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_748, 0);
lean_ctor_set(x_748, 1, x_11);
lean_ctor_set(x_748, 0, x_760);
return x_748;
}
else
{
lean_object* x_761; lean_object* x_762; 
lean_dec(x_748);
x_761 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_762 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_11);
return x_762;
}
}
}
}
else
{
lean_object* x_763; 
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_734);
lean_dec(x_136);
x_763 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_763);
return x_729;
}
}
else
{
lean_object* x_764; 
lean_dec(x_746);
lean_dec(x_745);
lean_dec(x_734);
lean_dec(x_136);
x_764 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_764);
return x_729;
}
}
else
{
lean_object* x_765; 
lean_dec(x_745);
lean_dec(x_734);
lean_dec(x_136);
x_765 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_765);
return x_729;
}
}
}
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; uint8_t x_769; 
x_766 = lean_ctor_get(x_729, 1);
lean_inc(x_766);
lean_dec(x_729);
x_767 = lean_ctor_get(x_730, 1);
lean_inc(x_767);
lean_dec(x_730);
x_768 = lean_ctor_get(x_731, 1);
lean_inc(x_768);
lean_dec(x_731);
x_769 = lean_string_dec_eq(x_768, x_79);
lean_dec(x_768);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; 
lean_dec(x_767);
lean_dec(x_766);
lean_dec(x_136);
x_770 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_771 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set(x_771, 1, x_11);
return x_771;
}
else
{
uint8_t x_772; 
x_772 = lean_string_dec_eq(x_767, x_150);
lean_dec(x_767);
if (x_772 == 0)
{
lean_object* x_773; lean_object* x_774; 
lean_dec(x_766);
lean_dec(x_136);
x_773 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_774 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_11);
return x_774;
}
else
{
lean_object* x_775; uint8_t x_776; 
x_775 = lean_array_get_size(x_766);
x_776 = lean_nat_dec_eq(x_775, x_154);
lean_dec(x_775);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; 
lean_dec(x_766);
lean_dec(x_136);
x_777 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_11);
return x_778;
}
else
{
lean_object* x_779; 
x_779 = lean_array_fget(x_766, x_157);
if (lean_obj_tag(x_779) == 4)
{
lean_object* x_780; 
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
if (lean_obj_tag(x_780) == 1)
{
lean_object* x_781; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; uint8_t x_784; 
x_782 = lean_ctor_get(x_779, 1);
lean_inc(x_782);
lean_dec(x_779);
x_783 = lean_ctor_get(x_780, 1);
lean_inc(x_783);
lean_dec(x_780);
x_784 = lean_string_dec_eq(x_783, x_163);
lean_dec(x_783);
if (x_784 == 0)
{
lean_object* x_785; lean_object* x_786; 
lean_dec(x_782);
lean_dec(x_766);
lean_dec(x_136);
x_785 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_786 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_11);
return x_786;
}
else
{
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_787 = lean_array_fget(x_766, x_166);
lean_dec(x_766);
x_788 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_789 = l_Lean_mkAppB(x_788, x_787, x_136);
x_790 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_791 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_790, x_789);
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_11);
return x_792;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_766);
lean_dec(x_136);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_793 = x_782;
} else {
 lean_dec_ref(x_782);
 x_793 = lean_box(0);
}
x_794 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_793)) {
 x_795 = lean_alloc_ctor(0, 2, 0);
} else {
 x_795 = x_793;
 lean_ctor_set_tag(x_795, 0);
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_11);
return x_795;
}
}
}
else
{
lean_object* x_796; lean_object* x_797; 
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_766);
lean_dec(x_136);
x_796 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_797 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_11);
return x_797;
}
}
else
{
lean_object* x_798; lean_object* x_799; 
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_766);
lean_dec(x_136);
x_798 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_799 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_799, 0, x_798);
lean_ctor_set(x_799, 1, x_11);
return x_799;
}
}
else
{
lean_object* x_800; lean_object* x_801; 
lean_dec(x_779);
lean_dec(x_766);
lean_dec(x_136);
x_800 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_11);
return x_801;
}
}
}
}
}
}
else
{
uint8_t x_802; 
lean_dec(x_732);
lean_dec(x_731);
lean_dec(x_730);
lean_dec(x_136);
x_802 = !lean_is_exclusive(x_729);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_729, 1);
lean_dec(x_803);
x_804 = lean_ctor_get(x_729, 0);
lean_dec(x_804);
x_805 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_805);
return x_729;
}
else
{
lean_object* x_806; lean_object* x_807; 
lean_dec(x_729);
x_806 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_11);
return x_807;
}
}
}
else
{
uint8_t x_808; 
lean_dec(x_731);
lean_dec(x_730);
lean_dec(x_136);
x_808 = !lean_is_exclusive(x_729);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_729, 1);
lean_dec(x_809);
x_810 = lean_ctor_get(x_729, 0);
lean_dec(x_810);
x_811 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_811);
return x_729;
}
else
{
lean_object* x_812; lean_object* x_813; 
lean_dec(x_729);
x_812 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_813 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_813, 0, x_812);
lean_ctor_set(x_813, 1, x_11);
return x_813;
}
}
}
else
{
uint8_t x_814; 
lean_dec(x_730);
lean_dec(x_136);
x_814 = !lean_is_exclusive(x_729);
if (x_814 == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_729, 1);
lean_dec(x_815);
x_816 = lean_ctor_get(x_729, 0);
lean_dec(x_816);
x_817 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_729, 1, x_11);
lean_ctor_set(x_729, 0, x_817);
return x_729;
}
else
{
lean_object* x_818; lean_object* x_819; 
lean_dec(x_729);
x_818 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_819 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_11);
return x_819;
}
}
}
}
else
{
lean_object* x_820; lean_object* x_821; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_820 = l_Lean_Expr_getAppFnArgs(x_134);
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
if (lean_obj_tag(x_821) == 1)
{
lean_object* x_822; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
if (lean_obj_tag(x_822) == 1)
{
lean_object* x_823; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
if (lean_obj_tag(x_823) == 0)
{
uint8_t x_824; 
x_824 = !lean_is_exclusive(x_820);
if (x_824 == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; uint8_t x_829; 
x_825 = lean_ctor_get(x_820, 1);
x_826 = lean_ctor_get(x_820, 0);
lean_dec(x_826);
x_827 = lean_ctor_get(x_821, 1);
lean_inc(x_827);
lean_dec(x_821);
x_828 = lean_ctor_get(x_822, 1);
lean_inc(x_828);
lean_dec(x_822);
x_829 = lean_string_dec_eq(x_828, x_79);
lean_dec(x_828);
if (x_829 == 0)
{
lean_object* x_830; 
lean_dec(x_827);
lean_dec(x_825);
lean_dec(x_136);
x_830 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_830);
return x_820;
}
else
{
uint8_t x_831; 
x_831 = lean_string_dec_eq(x_827, x_150);
lean_dec(x_827);
if (x_831 == 0)
{
lean_object* x_832; 
lean_dec(x_825);
lean_dec(x_136);
x_832 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_832);
return x_820;
}
else
{
lean_object* x_833; uint8_t x_834; 
x_833 = lean_array_get_size(x_825);
x_834 = lean_nat_dec_eq(x_833, x_154);
lean_dec(x_833);
if (x_834 == 0)
{
lean_object* x_835; 
lean_dec(x_825);
lean_dec(x_136);
x_835 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_835);
return x_820;
}
else
{
lean_object* x_836; 
x_836 = lean_array_fget(x_825, x_157);
if (lean_obj_tag(x_836) == 4)
{
lean_object* x_837; 
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
if (lean_obj_tag(x_837) == 1)
{
lean_object* x_838; 
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; uint8_t x_841; 
x_839 = lean_ctor_get(x_836, 1);
lean_inc(x_839);
lean_dec(x_836);
x_840 = lean_ctor_get(x_837, 1);
lean_inc(x_840);
lean_dec(x_837);
x_841 = lean_string_dec_eq(x_840, x_163);
lean_dec(x_840);
if (x_841 == 0)
{
lean_object* x_842; 
lean_dec(x_839);
lean_dec(x_825);
lean_dec(x_136);
x_842 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_842);
return x_820;
}
else
{
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_843 = lean_array_fget(x_825, x_166);
lean_dec(x_825);
x_844 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_845 = l_Lean_mkAppB(x_844, x_843, x_136);
x_846 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_847 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_846, x_845);
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_847);
return x_820;
}
else
{
uint8_t x_848; 
lean_free_object(x_820);
lean_dec(x_825);
lean_dec(x_136);
x_848 = !lean_is_exclusive(x_839);
if (x_848 == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_839, 1);
lean_dec(x_849);
x_850 = lean_ctor_get(x_839, 0);
lean_dec(x_850);
x_851 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_839, 0);
lean_ctor_set(x_839, 1, x_11);
lean_ctor_set(x_839, 0, x_851);
return x_839;
}
else
{
lean_object* x_852; lean_object* x_853; 
lean_dec(x_839);
x_852 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_853 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_11);
return x_853;
}
}
}
}
else
{
lean_object* x_854; 
lean_dec(x_838);
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_825);
lean_dec(x_136);
x_854 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_854);
return x_820;
}
}
else
{
lean_object* x_855; 
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_825);
lean_dec(x_136);
x_855 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_855);
return x_820;
}
}
else
{
lean_object* x_856; 
lean_dec(x_836);
lean_dec(x_825);
lean_dec(x_136);
x_856 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_856);
return x_820;
}
}
}
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_860; 
x_857 = lean_ctor_get(x_820, 1);
lean_inc(x_857);
lean_dec(x_820);
x_858 = lean_ctor_get(x_821, 1);
lean_inc(x_858);
lean_dec(x_821);
x_859 = lean_ctor_get(x_822, 1);
lean_inc(x_859);
lean_dec(x_822);
x_860 = lean_string_dec_eq(x_859, x_79);
lean_dec(x_859);
if (x_860 == 0)
{
lean_object* x_861; lean_object* x_862; 
lean_dec(x_858);
lean_dec(x_857);
lean_dec(x_136);
x_861 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_862 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_11);
return x_862;
}
else
{
uint8_t x_863; 
x_863 = lean_string_dec_eq(x_858, x_150);
lean_dec(x_858);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; 
lean_dec(x_857);
lean_dec(x_136);
x_864 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_865 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_11);
return x_865;
}
else
{
lean_object* x_866; uint8_t x_867; 
x_866 = lean_array_get_size(x_857);
x_867 = lean_nat_dec_eq(x_866, x_154);
lean_dec(x_866);
if (x_867 == 0)
{
lean_object* x_868; lean_object* x_869; 
lean_dec(x_857);
lean_dec(x_136);
x_868 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_869 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_869, 0, x_868);
lean_ctor_set(x_869, 1, x_11);
return x_869;
}
else
{
lean_object* x_870; 
x_870 = lean_array_fget(x_857, x_157);
if (lean_obj_tag(x_870) == 4)
{
lean_object* x_871; 
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
if (lean_obj_tag(x_871) == 1)
{
lean_object* x_872; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; uint8_t x_875; 
x_873 = lean_ctor_get(x_870, 1);
lean_inc(x_873);
lean_dec(x_870);
x_874 = lean_ctor_get(x_871, 1);
lean_inc(x_874);
lean_dec(x_871);
x_875 = lean_string_dec_eq(x_874, x_163);
lean_dec(x_874);
if (x_875 == 0)
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_873);
lean_dec(x_857);
lean_dec(x_136);
x_876 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_877 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_877, 0, x_876);
lean_ctor_set(x_877, 1, x_11);
return x_877;
}
else
{
if (lean_obj_tag(x_873) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = lean_array_fget(x_857, x_166);
lean_dec(x_857);
x_879 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_880 = l_Lean_mkAppB(x_879, x_878, x_136);
x_881 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_882 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_881, x_880);
x_883 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_11);
return x_883;
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_857);
lean_dec(x_136);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_884 = x_873;
} else {
 lean_dec_ref(x_873);
 x_884 = lean_box(0);
}
x_885 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_884)) {
 x_886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_886 = x_884;
 lean_ctor_set_tag(x_886, 0);
}
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_11);
return x_886;
}
}
}
else
{
lean_object* x_887; lean_object* x_888; 
lean_dec(x_872);
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_857);
lean_dec(x_136);
x_887 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_888 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_888, 0, x_887);
lean_ctor_set(x_888, 1, x_11);
return x_888;
}
}
else
{
lean_object* x_889; lean_object* x_890; 
lean_dec(x_871);
lean_dec(x_870);
lean_dec(x_857);
lean_dec(x_136);
x_889 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_890 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_890, 0, x_889);
lean_ctor_set(x_890, 1, x_11);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_870);
lean_dec(x_857);
lean_dec(x_136);
x_891 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_892 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_892, 0, x_891);
lean_ctor_set(x_892, 1, x_11);
return x_892;
}
}
}
}
}
}
else
{
uint8_t x_893; 
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_136);
x_893 = !lean_is_exclusive(x_820);
if (x_893 == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_820, 1);
lean_dec(x_894);
x_895 = lean_ctor_get(x_820, 0);
lean_dec(x_895);
x_896 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_896);
return x_820;
}
else
{
lean_object* x_897; lean_object* x_898; 
lean_dec(x_820);
x_897 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_898 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_898, 0, x_897);
lean_ctor_set(x_898, 1, x_11);
return x_898;
}
}
}
else
{
uint8_t x_899; 
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_136);
x_899 = !lean_is_exclusive(x_820);
if (x_899 == 0)
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_900 = lean_ctor_get(x_820, 1);
lean_dec(x_900);
x_901 = lean_ctor_get(x_820, 0);
lean_dec(x_901);
x_902 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_902);
return x_820;
}
else
{
lean_object* x_903; lean_object* x_904; 
lean_dec(x_820);
x_903 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_904 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_11);
return x_904;
}
}
}
else
{
uint8_t x_905; 
lean_dec(x_821);
lean_dec(x_136);
x_905 = !lean_is_exclusive(x_820);
if (x_905 == 0)
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_906 = lean_ctor_get(x_820, 1);
lean_dec(x_906);
x_907 = lean_ctor_get(x_820, 0);
lean_dec(x_907);
x_908 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_820, 1, x_11);
lean_ctor_set(x_820, 0, x_908);
return x_820;
}
else
{
lean_object* x_909; lean_object* x_910; 
lean_dec(x_820);
x_909 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_910 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_910, 0, x_909);
lean_ctor_set(x_910, 1, x_11);
return x_910;
}
}
}
}
else
{
lean_object* x_911; lean_object* x_912; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_911 = l_Lean_Expr_getAppFnArgs(x_134);
x_912 = lean_ctor_get(x_911, 0);
lean_inc(x_912);
if (lean_obj_tag(x_912) == 1)
{
lean_object* x_913; 
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
if (lean_obj_tag(x_913) == 1)
{
lean_object* x_914; 
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
if (lean_obj_tag(x_914) == 0)
{
uint8_t x_915; 
x_915 = !lean_is_exclusive(x_911);
if (x_915 == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; uint8_t x_920; 
x_916 = lean_ctor_get(x_911, 1);
x_917 = lean_ctor_get(x_911, 0);
lean_dec(x_917);
x_918 = lean_ctor_get(x_912, 1);
lean_inc(x_918);
lean_dec(x_912);
x_919 = lean_ctor_get(x_913, 1);
lean_inc(x_919);
lean_dec(x_913);
x_920 = lean_string_dec_eq(x_919, x_79);
lean_dec(x_919);
if (x_920 == 0)
{
lean_object* x_921; 
lean_dec(x_918);
lean_dec(x_916);
lean_dec(x_136);
x_921 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_921);
return x_911;
}
else
{
uint8_t x_922; 
x_922 = lean_string_dec_eq(x_918, x_150);
lean_dec(x_918);
if (x_922 == 0)
{
lean_object* x_923; 
lean_dec(x_916);
lean_dec(x_136);
x_923 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_923);
return x_911;
}
else
{
lean_object* x_924; uint8_t x_925; 
x_924 = lean_array_get_size(x_916);
x_925 = lean_nat_dec_eq(x_924, x_154);
lean_dec(x_924);
if (x_925 == 0)
{
lean_object* x_926; 
lean_dec(x_916);
lean_dec(x_136);
x_926 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_926);
return x_911;
}
else
{
lean_object* x_927; 
x_927 = lean_array_fget(x_916, x_157);
if (lean_obj_tag(x_927) == 4)
{
lean_object* x_928; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
if (lean_obj_tag(x_928) == 1)
{
lean_object* x_929; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; uint8_t x_932; 
x_930 = lean_ctor_get(x_927, 1);
lean_inc(x_930);
lean_dec(x_927);
x_931 = lean_ctor_get(x_928, 1);
lean_inc(x_931);
lean_dec(x_928);
x_932 = lean_string_dec_eq(x_931, x_163);
lean_dec(x_931);
if (x_932 == 0)
{
lean_object* x_933; 
lean_dec(x_930);
lean_dec(x_916);
lean_dec(x_136);
x_933 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_933);
return x_911;
}
else
{
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_934 = lean_array_fget(x_916, x_166);
lean_dec(x_916);
x_935 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_936 = l_Lean_mkAppB(x_935, x_934, x_136);
x_937 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_938 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_937, x_936);
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_938);
return x_911;
}
else
{
uint8_t x_939; 
lean_free_object(x_911);
lean_dec(x_916);
lean_dec(x_136);
x_939 = !lean_is_exclusive(x_930);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_940 = lean_ctor_get(x_930, 1);
lean_dec(x_940);
x_941 = lean_ctor_get(x_930, 0);
lean_dec(x_941);
x_942 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_930, 0);
lean_ctor_set(x_930, 1, x_11);
lean_ctor_set(x_930, 0, x_942);
return x_930;
}
else
{
lean_object* x_943; lean_object* x_944; 
lean_dec(x_930);
x_943 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_944 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_944, 0, x_943);
lean_ctor_set(x_944, 1, x_11);
return x_944;
}
}
}
}
else
{
lean_object* x_945; 
lean_dec(x_929);
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_916);
lean_dec(x_136);
x_945 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_945);
return x_911;
}
}
else
{
lean_object* x_946; 
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_916);
lean_dec(x_136);
x_946 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_946);
return x_911;
}
}
else
{
lean_object* x_947; 
lean_dec(x_927);
lean_dec(x_916);
lean_dec(x_136);
x_947 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_947);
return x_911;
}
}
}
}
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; uint8_t x_951; 
x_948 = lean_ctor_get(x_911, 1);
lean_inc(x_948);
lean_dec(x_911);
x_949 = lean_ctor_get(x_912, 1);
lean_inc(x_949);
lean_dec(x_912);
x_950 = lean_ctor_get(x_913, 1);
lean_inc(x_950);
lean_dec(x_913);
x_951 = lean_string_dec_eq(x_950, x_79);
lean_dec(x_950);
if (x_951 == 0)
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_136);
x_952 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_953 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_953, 0, x_952);
lean_ctor_set(x_953, 1, x_11);
return x_953;
}
else
{
uint8_t x_954; 
x_954 = lean_string_dec_eq(x_949, x_150);
lean_dec(x_949);
if (x_954 == 0)
{
lean_object* x_955; lean_object* x_956; 
lean_dec(x_948);
lean_dec(x_136);
x_955 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_956 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_956, 0, x_955);
lean_ctor_set(x_956, 1, x_11);
return x_956;
}
else
{
lean_object* x_957; uint8_t x_958; 
x_957 = lean_array_get_size(x_948);
x_958 = lean_nat_dec_eq(x_957, x_154);
lean_dec(x_957);
if (x_958 == 0)
{
lean_object* x_959; lean_object* x_960; 
lean_dec(x_948);
lean_dec(x_136);
x_959 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_960 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_960, 0, x_959);
lean_ctor_set(x_960, 1, x_11);
return x_960;
}
else
{
lean_object* x_961; 
x_961 = lean_array_fget(x_948, x_157);
if (lean_obj_tag(x_961) == 4)
{
lean_object* x_962; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
if (lean_obj_tag(x_962) == 1)
{
lean_object* x_963; 
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; uint8_t x_966; 
x_964 = lean_ctor_get(x_961, 1);
lean_inc(x_964);
lean_dec(x_961);
x_965 = lean_ctor_get(x_962, 1);
lean_inc(x_965);
lean_dec(x_962);
x_966 = lean_string_dec_eq(x_965, x_163);
lean_dec(x_965);
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; 
lean_dec(x_964);
lean_dec(x_948);
lean_dec(x_136);
x_967 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_968 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_968, 0, x_967);
lean_ctor_set(x_968, 1, x_11);
return x_968;
}
else
{
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_969 = lean_array_fget(x_948, x_166);
lean_dec(x_948);
x_970 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_971 = l_Lean_mkAppB(x_970, x_969, x_136);
x_972 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_973 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_972, x_971);
x_974 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_974, 0, x_973);
lean_ctor_set(x_974, 1, x_11);
return x_974;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_948);
lean_dec(x_136);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_975 = x_964;
} else {
 lean_dec_ref(x_964);
 x_975 = lean_box(0);
}
x_976 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_975)) {
 x_977 = lean_alloc_ctor(0, 2, 0);
} else {
 x_977 = x_975;
 lean_ctor_set_tag(x_977, 0);
}
lean_ctor_set(x_977, 0, x_976);
lean_ctor_set(x_977, 1, x_11);
return x_977;
}
}
}
else
{
lean_object* x_978; lean_object* x_979; 
lean_dec(x_963);
lean_dec(x_962);
lean_dec(x_961);
lean_dec(x_948);
lean_dec(x_136);
x_978 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_978);
lean_ctor_set(x_979, 1, x_11);
return x_979;
}
}
else
{
lean_object* x_980; lean_object* x_981; 
lean_dec(x_962);
lean_dec(x_961);
lean_dec(x_948);
lean_dec(x_136);
x_980 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_981 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_11);
return x_981;
}
}
else
{
lean_object* x_982; lean_object* x_983; 
lean_dec(x_961);
lean_dec(x_948);
lean_dec(x_136);
x_982 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_983 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_11);
return x_983;
}
}
}
}
}
}
else
{
uint8_t x_984; 
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_dec(x_136);
x_984 = !lean_is_exclusive(x_911);
if (x_984 == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_911, 1);
lean_dec(x_985);
x_986 = lean_ctor_get(x_911, 0);
lean_dec(x_986);
x_987 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_987);
return x_911;
}
else
{
lean_object* x_988; lean_object* x_989; 
lean_dec(x_911);
x_988 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_989 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_989, 0, x_988);
lean_ctor_set(x_989, 1, x_11);
return x_989;
}
}
}
else
{
uint8_t x_990; 
lean_dec(x_913);
lean_dec(x_912);
lean_dec(x_136);
x_990 = !lean_is_exclusive(x_911);
if (x_990 == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_991 = lean_ctor_get(x_911, 1);
lean_dec(x_991);
x_992 = lean_ctor_get(x_911, 0);
lean_dec(x_992);
x_993 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_993);
return x_911;
}
else
{
lean_object* x_994; lean_object* x_995; 
lean_dec(x_911);
x_994 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_995 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_995, 0, x_994);
lean_ctor_set(x_995, 1, x_11);
return x_995;
}
}
}
else
{
uint8_t x_996; 
lean_dec(x_912);
lean_dec(x_136);
x_996 = !lean_is_exclusive(x_911);
if (x_996 == 0)
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_997 = lean_ctor_get(x_911, 1);
lean_dec(x_997);
x_998 = lean_ctor_get(x_911, 0);
lean_dec(x_998);
x_999 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_911, 1, x_11);
lean_ctor_set(x_911, 0, x_999);
return x_911;
}
else
{
lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_911);
x_1000 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_11);
return x_1001;
}
}
}
}
else
{
uint8_t x_1002; 
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1002 = !lean_is_exclusive(x_161);
if (x_1002 == 0)
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_1003 = lean_ctor_get(x_161, 1);
lean_dec(x_1003);
x_1004 = lean_ctor_get(x_161, 0);
lean_dec(x_1004);
x_1005 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_161, 0);
lean_ctor_set(x_161, 1, x_11);
lean_ctor_set(x_161, 0, x_1005);
return x_161;
}
else
{
lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_161);
x_1006 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1007 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_11);
return x_1007;
}
}
}
}
else
{
lean_object* x_1008; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1008 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1008);
return x_137;
}
}
else
{
lean_object* x_1009; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1009 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1009);
return x_137;
}
}
else
{
lean_object* x_1010; 
lean_dec(x_158);
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1010 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1010);
return x_137;
}
}
}
}
}
else
{
lean_object* x_1011; uint8_t x_1012; 
lean_dec(x_145);
x_1011 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_1012 = lean_string_dec_eq(x_144, x_1011);
lean_dec(x_144);
if (x_1012 == 0)
{
lean_object* x_1013; 
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1013 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1013);
return x_137;
}
else
{
lean_object* x_1014; uint8_t x_1015; 
x_1014 = lean_array_get_size(x_142);
x_1015 = lean_nat_dec_eq(x_1014, x_130);
lean_dec(x_1014);
if (x_1015 == 0)
{
lean_object* x_1016; 
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1016 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1016);
return x_137;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_array_fget(x_142, x_133);
x_1018 = lean_array_fget(x_142, x_135);
lean_dec(x_142);
lean_inc(x_1017);
x_1019 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1017);
if (lean_obj_tag(x_1019) == 0)
{
lean_object* x_1020; 
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1020 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1020);
return x_137;
}
else
{
lean_object* x_1021; lean_object* x_1022; uint8_t x_1023; 
x_1021 = lean_ctor_get(x_1019, 0);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = lean_unsigned_to_nat(0u);
x_1023 = lean_nat_dec_eq(x_1021, x_1022);
lean_dec(x_1021);
if (x_1023 == 0)
{
lean_object* x_1024; uint8_t x_1062; 
lean_free_object(x_137);
x_1062 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_1062 == 0)
{
lean_object* x_1063; 
x_1063 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76;
x_1024 = x_1063;
goto block_1061;
}
else
{
lean_object* x_1064; 
x_1064 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_1024 = x_1064;
goto block_1061;
}
block_1061:
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1025 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_1026 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_1027 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
lean_inc(x_1017);
lean_inc(x_1024);
x_1028 = l_Lean_mkApp4(x_1025, x_1026, x_1027, x_1024, x_1017);
x_1029 = l_Lean_Meta_mkDecideProof(x_1028, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1029) == 0)
{
uint8_t x_1030; 
x_1030 = !lean_is_exclusive(x_1029);
if (x_1030 == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1031 = lean_ctor_get(x_1029, 0);
x_1032 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
x_1033 = l_Lean_mkApp3(x_1032, x_1017, x_1018, x_1031);
x_1034 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
lean_inc(x_1033);
lean_inc(x_136);
x_1035 = l_Lean_mkApp3(x_1034, x_136, x_1024, x_1033);
x_1036 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_136);
lean_inc(x_134);
x_1037 = l_Lean_mkApp3(x_1036, x_134, x_136, x_1035);
x_1038 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_1039 = l_Lean_mkApp3(x_1038, x_134, x_136, x_1033);
x_1040 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1041 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1040, x_1037);
x_1042 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1041, x_1039);
lean_ctor_set(x_1029, 0, x_1042);
return x_1029;
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1043 = lean_ctor_get(x_1029, 0);
x_1044 = lean_ctor_get(x_1029, 1);
lean_inc(x_1044);
lean_inc(x_1043);
lean_dec(x_1029);
x_1045 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
x_1046 = l_Lean_mkApp3(x_1045, x_1017, x_1018, x_1043);
x_1047 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
lean_inc(x_1046);
lean_inc(x_136);
x_1048 = l_Lean_mkApp3(x_1047, x_136, x_1024, x_1046);
x_1049 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_136);
lean_inc(x_134);
x_1050 = l_Lean_mkApp3(x_1049, x_134, x_136, x_1048);
x_1051 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_1052 = l_Lean_mkApp3(x_1051, x_134, x_136, x_1046);
x_1053 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1054 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1053, x_1050);
x_1055 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1054, x_1052);
x_1056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_1044);
return x_1056;
}
}
else
{
uint8_t x_1057; 
lean_dec(x_1024);
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_136);
lean_dec(x_134);
x_1057 = !lean_is_exclusive(x_1029);
if (x_1057 == 0)
{
return x_1029;
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1058 = lean_ctor_get(x_1029, 0);
x_1059 = lean_ctor_get(x_1029, 1);
lean_inc(x_1059);
lean_inc(x_1058);
lean_dec(x_1029);
x_1060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1060, 0, x_1058);
lean_ctor_set(x_1060, 1, x_1059);
return x_1060;
}
}
}
}
else
{
lean_object* x_1065; 
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1065 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1065);
return x_137;
}
}
}
}
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; uint8_t x_1070; 
x_1066 = lean_ctor_get(x_137, 1);
lean_inc(x_1066);
lean_dec(x_137);
x_1067 = lean_ctor_get(x_138, 1);
lean_inc(x_1067);
lean_dec(x_138);
x_1068 = lean_ctor_get(x_139, 1);
lean_inc(x_1068);
lean_dec(x_139);
x_1069 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_1070 = lean_string_dec_eq(x_1068, x_1069);
if (x_1070 == 0)
{
uint8_t x_1071; 
x_1071 = lean_string_dec_eq(x_1068, x_79);
lean_dec(x_1068);
if (x_1071 == 0)
{
lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1072 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1073 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1073, 0, x_1072);
lean_ctor_set(x_1073, 1, x_11);
return x_1073;
}
else
{
lean_object* x_1074; uint8_t x_1075; 
x_1074 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_1075 = lean_string_dec_eq(x_1067, x_1074);
lean_dec(x_1067);
if (x_1075 == 0)
{
lean_object* x_1076; lean_object* x_1077; 
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1076 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1077 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1077, 0, x_1076);
lean_ctor_set(x_1077, 1, x_11);
return x_1077;
}
else
{
lean_object* x_1078; lean_object* x_1079; uint8_t x_1080; 
x_1078 = lean_array_get_size(x_1066);
x_1079 = lean_unsigned_to_nat(3u);
x_1080 = lean_nat_dec_eq(x_1078, x_1079);
lean_dec(x_1078);
if (x_1080 == 0)
{
lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1081 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1082 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1082, 0, x_1081);
lean_ctor_set(x_1082, 1, x_11);
return x_1082;
}
else
{
lean_object* x_1083; lean_object* x_1084; 
x_1083 = lean_unsigned_to_nat(0u);
x_1084 = lean_array_fget(x_1066, x_1083);
if (lean_obj_tag(x_1084) == 4)
{
lean_object* x_1085; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
if (lean_obj_tag(x_1085) == 1)
{
lean_object* x_1086; 
x_1086 = lean_ctor_get(x_1085, 0);
lean_inc(x_1086);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; 
x_1087 = lean_ctor_get(x_1084, 1);
lean_inc(x_1087);
lean_dec(x_1084);
x_1088 = lean_ctor_get(x_1085, 1);
lean_inc(x_1088);
lean_dec(x_1085);
x_1089 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_1090 = lean_string_dec_eq(x_1088, x_1089);
lean_dec(x_1088);
if (x_1090 == 0)
{
lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_1087);
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1091 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1092 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1092, 0, x_1091);
lean_ctor_set(x_1092, 1, x_11);
return x_1092;
}
else
{
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1093 = lean_unsigned_to_nat(2u);
x_1094 = lean_array_fget(x_1066, x_1093);
lean_dec(x_1066);
lean_inc(x_1094);
x_1095 = l_Lean_Expr_getAppFnArgs(x_1094);
x_1096 = lean_ctor_get(x_1095, 0);
lean_inc(x_1096);
if (lean_obj_tag(x_1096) == 1)
{
lean_object* x_1097; 
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc(x_1097);
if (lean_obj_tag(x_1097) == 1)
{
lean_object* x_1098; 
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; uint8_t x_1103; 
x_1099 = lean_ctor_get(x_1095, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1095)) {
 lean_ctor_release(x_1095, 0);
 lean_ctor_release(x_1095, 1);
 x_1100 = x_1095;
} else {
 lean_dec_ref(x_1095);
 x_1100 = lean_box(0);
}
x_1101 = lean_ctor_get(x_1096, 1);
lean_inc(x_1101);
lean_dec(x_1096);
x_1102 = lean_ctor_get(x_1097, 1);
lean_inc(x_1102);
lean_dec(x_1097);
x_1103 = lean_string_dec_eq(x_1102, x_1069);
lean_dec(x_1102);
if (x_1103 == 0)
{
lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_1101);
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1094);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1104 = l_Lean_Expr_getAppFnArgs(x_134);
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
if (lean_obj_tag(x_1105) == 1)
{
lean_object* x_1106; 
x_1106 = lean_ctor_get(x_1105, 0);
lean_inc(x_1106);
if (lean_obj_tag(x_1106) == 1)
{
lean_object* x_1107; 
x_1107 = lean_ctor_get(x_1106, 0);
lean_inc(x_1107);
if (lean_obj_tag(x_1107) == 0)
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; uint8_t x_1112; 
x_1108 = lean_ctor_get(x_1104, 1);
lean_inc(x_1108);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1109 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1109 = lean_box(0);
}
x_1110 = lean_ctor_get(x_1105, 1);
lean_inc(x_1110);
lean_dec(x_1105);
x_1111 = lean_ctor_get(x_1106, 1);
lean_inc(x_1111);
lean_dec(x_1106);
x_1112 = lean_string_dec_eq(x_1111, x_79);
lean_dec(x_1111);
if (x_1112 == 0)
{
lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_1110);
lean_dec(x_1108);
lean_dec(x_136);
x_1113 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1109)) {
 x_1114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1114 = x_1109;
}
lean_ctor_set(x_1114, 0, x_1113);
lean_ctor_set(x_1114, 1, x_11);
return x_1114;
}
else
{
uint8_t x_1115; 
x_1115 = lean_string_dec_eq(x_1110, x_1074);
lean_dec(x_1110);
if (x_1115 == 0)
{
lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_1108);
lean_dec(x_136);
x_1116 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1109)) {
 x_1117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1117 = x_1109;
}
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_11);
return x_1117;
}
else
{
lean_object* x_1118; uint8_t x_1119; 
x_1118 = lean_array_get_size(x_1108);
x_1119 = lean_nat_dec_eq(x_1118, x_1079);
lean_dec(x_1118);
if (x_1119 == 0)
{
lean_object* x_1120; lean_object* x_1121; 
lean_dec(x_1108);
lean_dec(x_136);
x_1120 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1109)) {
 x_1121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1121 = x_1109;
}
lean_ctor_set(x_1121, 0, x_1120);
lean_ctor_set(x_1121, 1, x_11);
return x_1121;
}
else
{
lean_object* x_1122; 
x_1122 = lean_array_fget(x_1108, x_1083);
if (lean_obj_tag(x_1122) == 4)
{
lean_object* x_1123; 
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
if (lean_obj_tag(x_1123) == 1)
{
lean_object* x_1124; 
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
if (lean_obj_tag(x_1124) == 0)
{
lean_object* x_1125; lean_object* x_1126; uint8_t x_1127; 
x_1125 = lean_ctor_get(x_1122, 1);
lean_inc(x_1125);
lean_dec(x_1122);
x_1126 = lean_ctor_get(x_1123, 1);
lean_inc(x_1126);
lean_dec(x_1123);
x_1127 = lean_string_dec_eq(x_1126, x_1089);
lean_dec(x_1126);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; 
lean_dec(x_1125);
lean_dec(x_1108);
lean_dec(x_136);
x_1128 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1109)) {
 x_1129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1129 = x_1109;
}
lean_ctor_set(x_1129, 0, x_1128);
lean_ctor_set(x_1129, 1, x_11);
return x_1129;
}
else
{
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1130 = lean_array_fget(x_1108, x_1093);
lean_dec(x_1108);
x_1131 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_1132 = l_Lean_mkAppB(x_1131, x_1130, x_136);
x_1133 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1134 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1133, x_1132);
if (lean_is_scalar(x_1109)) {
 x_1135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1135 = x_1109;
}
lean_ctor_set(x_1135, 0, x_1134);
lean_ctor_set(x_1135, 1, x_11);
return x_1135;
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
lean_dec(x_1109);
lean_dec(x_1108);
lean_dec(x_136);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 lean_ctor_release(x_1125, 1);
 x_1136 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1136 = lean_box(0);
}
x_1137 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1136)) {
 x_1138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1138 = x_1136;
 lean_ctor_set_tag(x_1138, 0);
}
lean_ctor_set(x_1138, 0, x_1137);
lean_ctor_set(x_1138, 1, x_11);
return x_1138;
}
}
}
else
{
lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1124);
lean_dec(x_1123);
lean_dec(x_1122);
lean_dec(x_1108);
lean_dec(x_136);
x_1139 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1109)) {
 x_1140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1140 = x_1109;
}
lean_ctor_set(x_1140, 0, x_1139);
lean_ctor_set(x_1140, 1, x_11);
return x_1140;
}
}
else
{
lean_object* x_1141; lean_object* x_1142; 
lean_dec(x_1123);
lean_dec(x_1122);
lean_dec(x_1108);
lean_dec(x_136);
x_1141 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1109)) {
 x_1142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1142 = x_1109;
}
lean_ctor_set(x_1142, 0, x_1141);
lean_ctor_set(x_1142, 1, x_11);
return x_1142;
}
}
else
{
lean_object* x_1143; lean_object* x_1144; 
lean_dec(x_1122);
lean_dec(x_1108);
lean_dec(x_136);
x_1143 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1109)) {
 x_1144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1144 = x_1109;
}
lean_ctor_set(x_1144, 0, x_1143);
lean_ctor_set(x_1144, 1, x_11);
return x_1144;
}
}
}
}
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec(x_1107);
lean_dec(x_1106);
lean_dec(x_1105);
lean_dec(x_136);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1145 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1145 = lean_box(0);
}
x_1146 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1145)) {
 x_1147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1147 = x_1145;
}
lean_ctor_set(x_1147, 0, x_1146);
lean_ctor_set(x_1147, 1, x_11);
return x_1147;
}
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_1106);
lean_dec(x_1105);
lean_dec(x_136);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1148 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1148 = lean_box(0);
}
x_1149 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1148)) {
 x_1150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1150 = x_1148;
}
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_11);
return x_1150;
}
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
lean_dec(x_1105);
lean_dec(x_136);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1151 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1151 = lean_box(0);
}
x_1152 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1151)) {
 x_1153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1153 = x_1151;
}
lean_ctor_set(x_1153, 0, x_1152);
lean_ctor_set(x_1153, 1, x_11);
return x_1153;
}
}
else
{
lean_object* x_1154; uint8_t x_1155; 
x_1154 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_1155 = lean_string_dec_eq(x_1101, x_1154);
lean_dec(x_1101);
if (x_1155 == 0)
{
lean_object* x_1156; lean_object* x_1157; 
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1094);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1156 = l_Lean_Expr_getAppFnArgs(x_134);
x_1157 = lean_ctor_get(x_1156, 0);
lean_inc(x_1157);
if (lean_obj_tag(x_1157) == 1)
{
lean_object* x_1158; 
x_1158 = lean_ctor_get(x_1157, 0);
lean_inc(x_1158);
if (lean_obj_tag(x_1158) == 1)
{
lean_object* x_1159; 
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
if (lean_obj_tag(x_1159) == 0)
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; uint8_t x_1164; 
x_1160 = lean_ctor_get(x_1156, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_1156)) {
 lean_ctor_release(x_1156, 0);
 lean_ctor_release(x_1156, 1);
 x_1161 = x_1156;
} else {
 lean_dec_ref(x_1156);
 x_1161 = lean_box(0);
}
x_1162 = lean_ctor_get(x_1157, 1);
lean_inc(x_1162);
lean_dec(x_1157);
x_1163 = lean_ctor_get(x_1158, 1);
lean_inc(x_1163);
lean_dec(x_1158);
x_1164 = lean_string_dec_eq(x_1163, x_79);
lean_dec(x_1163);
if (x_1164 == 0)
{
lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_1162);
lean_dec(x_1160);
lean_dec(x_136);
x_1165 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1161)) {
 x_1166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1166 = x_1161;
}
lean_ctor_set(x_1166, 0, x_1165);
lean_ctor_set(x_1166, 1, x_11);
return x_1166;
}
else
{
uint8_t x_1167; 
x_1167 = lean_string_dec_eq(x_1162, x_1074);
lean_dec(x_1162);
if (x_1167 == 0)
{
lean_object* x_1168; lean_object* x_1169; 
lean_dec(x_1160);
lean_dec(x_136);
x_1168 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1161)) {
 x_1169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1169 = x_1161;
}
lean_ctor_set(x_1169, 0, x_1168);
lean_ctor_set(x_1169, 1, x_11);
return x_1169;
}
else
{
lean_object* x_1170; uint8_t x_1171; 
x_1170 = lean_array_get_size(x_1160);
x_1171 = lean_nat_dec_eq(x_1170, x_1079);
lean_dec(x_1170);
if (x_1171 == 0)
{
lean_object* x_1172; lean_object* x_1173; 
lean_dec(x_1160);
lean_dec(x_136);
x_1172 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1161)) {
 x_1173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1173 = x_1161;
}
lean_ctor_set(x_1173, 0, x_1172);
lean_ctor_set(x_1173, 1, x_11);
return x_1173;
}
else
{
lean_object* x_1174; 
x_1174 = lean_array_fget(x_1160, x_1083);
if (lean_obj_tag(x_1174) == 4)
{
lean_object* x_1175; 
x_1175 = lean_ctor_get(x_1174, 0);
lean_inc(x_1175);
if (lean_obj_tag(x_1175) == 1)
{
lean_object* x_1176; 
x_1176 = lean_ctor_get(x_1175, 0);
lean_inc(x_1176);
if (lean_obj_tag(x_1176) == 0)
{
lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; 
x_1177 = lean_ctor_get(x_1174, 1);
lean_inc(x_1177);
lean_dec(x_1174);
x_1178 = lean_ctor_get(x_1175, 1);
lean_inc(x_1178);
lean_dec(x_1175);
x_1179 = lean_string_dec_eq(x_1178, x_1089);
lean_dec(x_1178);
if (x_1179 == 0)
{
lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_1177);
lean_dec(x_1160);
lean_dec(x_136);
x_1180 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1161)) {
 x_1181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1181 = x_1161;
}
lean_ctor_set(x_1181, 0, x_1180);
lean_ctor_set(x_1181, 1, x_11);
return x_1181;
}
else
{
if (lean_obj_tag(x_1177) == 0)
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1182 = lean_array_fget(x_1160, x_1093);
lean_dec(x_1160);
x_1183 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_1184 = l_Lean_mkAppB(x_1183, x_1182, x_136);
x_1185 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1186 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1185, x_1184);
if (lean_is_scalar(x_1161)) {
 x_1187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1187 = x_1161;
}
lean_ctor_set(x_1187, 0, x_1186);
lean_ctor_set(x_1187, 1, x_11);
return x_1187;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_136);
if (lean_is_exclusive(x_1177)) {
 lean_ctor_release(x_1177, 0);
 lean_ctor_release(x_1177, 1);
 x_1188 = x_1177;
} else {
 lean_dec_ref(x_1177);
 x_1188 = lean_box(0);
}
x_1189 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1188)) {
 x_1190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1190 = x_1188;
 lean_ctor_set_tag(x_1190, 0);
}
lean_ctor_set(x_1190, 0, x_1189);
lean_ctor_set(x_1190, 1, x_11);
return x_1190;
}
}
}
else
{
lean_object* x_1191; lean_object* x_1192; 
lean_dec(x_1176);
lean_dec(x_1175);
lean_dec(x_1174);
lean_dec(x_1160);
lean_dec(x_136);
x_1191 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1161)) {
 x_1192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1192 = x_1161;
}
lean_ctor_set(x_1192, 0, x_1191);
lean_ctor_set(x_1192, 1, x_11);
return x_1192;
}
}
else
{
lean_object* x_1193; lean_object* x_1194; 
lean_dec(x_1175);
lean_dec(x_1174);
lean_dec(x_1160);
lean_dec(x_136);
x_1193 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1161)) {
 x_1194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1194 = x_1161;
}
lean_ctor_set(x_1194, 0, x_1193);
lean_ctor_set(x_1194, 1, x_11);
return x_1194;
}
}
else
{
lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_1174);
lean_dec(x_1160);
lean_dec(x_136);
x_1195 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1161)) {
 x_1196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1196 = x_1161;
}
lean_ctor_set(x_1196, 0, x_1195);
lean_ctor_set(x_1196, 1, x_11);
return x_1196;
}
}
}
}
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1159);
lean_dec(x_1158);
lean_dec(x_1157);
lean_dec(x_136);
if (lean_is_exclusive(x_1156)) {
 lean_ctor_release(x_1156, 0);
 lean_ctor_release(x_1156, 1);
 x_1197 = x_1156;
} else {
 lean_dec_ref(x_1156);
 x_1197 = lean_box(0);
}
x_1198 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1197)) {
 x_1199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1199 = x_1197;
}
lean_ctor_set(x_1199, 0, x_1198);
lean_ctor_set(x_1199, 1, x_11);
return x_1199;
}
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
lean_dec(x_1158);
lean_dec(x_1157);
lean_dec(x_136);
if (lean_is_exclusive(x_1156)) {
 lean_ctor_release(x_1156, 0);
 lean_ctor_release(x_1156, 1);
 x_1200 = x_1156;
} else {
 lean_dec_ref(x_1156);
 x_1200 = lean_box(0);
}
x_1201 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1200)) {
 x_1202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1202 = x_1200;
}
lean_ctor_set(x_1202, 0, x_1201);
lean_ctor_set(x_1202, 1, x_11);
return x_1202;
}
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
lean_dec(x_1157);
lean_dec(x_136);
if (lean_is_exclusive(x_1156)) {
 lean_ctor_release(x_1156, 0);
 lean_ctor_release(x_1156, 1);
 x_1203 = x_1156;
} else {
 lean_dec_ref(x_1156);
 x_1203 = lean_box(0);
}
x_1204 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1203)) {
 x_1205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1205 = x_1203;
}
lean_ctor_set(x_1205, 0, x_1204);
lean_ctor_set(x_1205, 1, x_11);
return x_1205;
}
}
else
{
lean_object* x_1206; uint8_t x_1207; 
x_1206 = lean_array_get_size(x_1099);
x_1207 = lean_nat_dec_eq(x_1206, x_130);
lean_dec(x_1206);
if (x_1207 == 0)
{
lean_object* x_1208; lean_object* x_1209; 
lean_dec(x_1100);
lean_dec(x_1099);
lean_dec(x_1094);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1208 = l_Lean_Expr_getAppFnArgs(x_134);
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc(x_1209);
if (lean_obj_tag(x_1209) == 1)
{
lean_object* x_1210; 
x_1210 = lean_ctor_get(x_1209, 0);
lean_inc(x_1210);
if (lean_obj_tag(x_1210) == 1)
{
lean_object* x_1211; 
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
if (lean_obj_tag(x_1211) == 0)
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; uint8_t x_1216; 
x_1212 = lean_ctor_get(x_1208, 1);
lean_inc(x_1212);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1213 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1213 = lean_box(0);
}
x_1214 = lean_ctor_get(x_1209, 1);
lean_inc(x_1214);
lean_dec(x_1209);
x_1215 = lean_ctor_get(x_1210, 1);
lean_inc(x_1215);
lean_dec(x_1210);
x_1216 = lean_string_dec_eq(x_1215, x_79);
lean_dec(x_1215);
if (x_1216 == 0)
{
lean_object* x_1217; lean_object* x_1218; 
lean_dec(x_1214);
lean_dec(x_1212);
lean_dec(x_136);
x_1217 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1213)) {
 x_1218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1218 = x_1213;
}
lean_ctor_set(x_1218, 0, x_1217);
lean_ctor_set(x_1218, 1, x_11);
return x_1218;
}
else
{
uint8_t x_1219; 
x_1219 = lean_string_dec_eq(x_1214, x_1074);
lean_dec(x_1214);
if (x_1219 == 0)
{
lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_1212);
lean_dec(x_136);
x_1220 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1213)) {
 x_1221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1221 = x_1213;
}
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_11);
return x_1221;
}
else
{
lean_object* x_1222; uint8_t x_1223; 
x_1222 = lean_array_get_size(x_1212);
x_1223 = lean_nat_dec_eq(x_1222, x_1079);
lean_dec(x_1222);
if (x_1223 == 0)
{
lean_object* x_1224; lean_object* x_1225; 
lean_dec(x_1212);
lean_dec(x_136);
x_1224 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1213)) {
 x_1225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1225 = x_1213;
}
lean_ctor_set(x_1225, 0, x_1224);
lean_ctor_set(x_1225, 1, x_11);
return x_1225;
}
else
{
lean_object* x_1226; 
x_1226 = lean_array_fget(x_1212, x_1083);
if (lean_obj_tag(x_1226) == 4)
{
lean_object* x_1227; 
x_1227 = lean_ctor_get(x_1226, 0);
lean_inc(x_1227);
if (lean_obj_tag(x_1227) == 1)
{
lean_object* x_1228; 
x_1228 = lean_ctor_get(x_1227, 0);
lean_inc(x_1228);
if (lean_obj_tag(x_1228) == 0)
{
lean_object* x_1229; lean_object* x_1230; uint8_t x_1231; 
x_1229 = lean_ctor_get(x_1226, 1);
lean_inc(x_1229);
lean_dec(x_1226);
x_1230 = lean_ctor_get(x_1227, 1);
lean_inc(x_1230);
lean_dec(x_1227);
x_1231 = lean_string_dec_eq(x_1230, x_1089);
lean_dec(x_1230);
if (x_1231 == 0)
{
lean_object* x_1232; lean_object* x_1233; 
lean_dec(x_1229);
lean_dec(x_1212);
lean_dec(x_136);
x_1232 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1213)) {
 x_1233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1233 = x_1213;
}
lean_ctor_set(x_1233, 0, x_1232);
lean_ctor_set(x_1233, 1, x_11);
return x_1233;
}
else
{
if (lean_obj_tag(x_1229) == 0)
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1234 = lean_array_fget(x_1212, x_1093);
lean_dec(x_1212);
x_1235 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_1236 = l_Lean_mkAppB(x_1235, x_1234, x_136);
x_1237 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1238 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1237, x_1236);
if (lean_is_scalar(x_1213)) {
 x_1239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1239 = x_1213;
}
lean_ctor_set(x_1239, 0, x_1238);
lean_ctor_set(x_1239, 1, x_11);
return x_1239;
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
lean_dec(x_1213);
lean_dec(x_1212);
lean_dec(x_136);
if (lean_is_exclusive(x_1229)) {
 lean_ctor_release(x_1229, 0);
 lean_ctor_release(x_1229, 1);
 x_1240 = x_1229;
} else {
 lean_dec_ref(x_1229);
 x_1240 = lean_box(0);
}
x_1241 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1240)) {
 x_1242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1242 = x_1240;
 lean_ctor_set_tag(x_1242, 0);
}
lean_ctor_set(x_1242, 0, x_1241);
lean_ctor_set(x_1242, 1, x_11);
return x_1242;
}
}
}
else
{
lean_object* x_1243; lean_object* x_1244; 
lean_dec(x_1228);
lean_dec(x_1227);
lean_dec(x_1226);
lean_dec(x_1212);
lean_dec(x_136);
x_1243 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1213)) {
 x_1244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1244 = x_1213;
}
lean_ctor_set(x_1244, 0, x_1243);
lean_ctor_set(x_1244, 1, x_11);
return x_1244;
}
}
else
{
lean_object* x_1245; lean_object* x_1246; 
lean_dec(x_1227);
lean_dec(x_1226);
lean_dec(x_1212);
lean_dec(x_136);
x_1245 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1213)) {
 x_1246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1246 = x_1213;
}
lean_ctor_set(x_1246, 0, x_1245);
lean_ctor_set(x_1246, 1, x_11);
return x_1246;
}
}
else
{
lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_1226);
lean_dec(x_1212);
lean_dec(x_136);
x_1247 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1213)) {
 x_1248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1248 = x_1213;
}
lean_ctor_set(x_1248, 0, x_1247);
lean_ctor_set(x_1248, 1, x_11);
return x_1248;
}
}
}
}
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_1211);
lean_dec(x_1210);
lean_dec(x_1209);
lean_dec(x_136);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1249 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1249 = lean_box(0);
}
x_1250 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1249)) {
 x_1251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1251 = x_1249;
}
lean_ctor_set(x_1251, 0, x_1250);
lean_ctor_set(x_1251, 1, x_11);
return x_1251;
}
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1210);
lean_dec(x_1209);
lean_dec(x_136);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1252 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1252 = lean_box(0);
}
x_1253 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1252)) {
 x_1254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1254 = x_1252;
}
lean_ctor_set(x_1254, 0, x_1253);
lean_ctor_set(x_1254, 1, x_11);
return x_1254;
}
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
lean_dec(x_1209);
lean_dec(x_136);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1255 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1255 = lean_box(0);
}
x_1256 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1255)) {
 x_1257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1257 = x_1255;
}
lean_ctor_set(x_1257, 0, x_1256);
lean_ctor_set(x_1257, 1, x_11);
return x_1257;
}
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1258 = lean_array_fget(x_1099, x_133);
x_1259 = lean_array_fget(x_1099, x_135);
lean_dec(x_1099);
lean_inc(x_1258);
x_1260 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1258);
if (lean_obj_tag(x_1260) == 0)
{
lean_object* x_1261; lean_object* x_1262; 
lean_dec(x_1259);
lean_dec(x_1258);
lean_dec(x_1094);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1261 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1100)) {
 x_1262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1262 = x_1100;
}
lean_ctor_set(x_1262, 0, x_1261);
lean_ctor_set(x_1262, 1, x_11);
return x_1262;
}
else
{
lean_object* x_1263; uint8_t x_1264; 
x_1263 = lean_ctor_get(x_1260, 0);
lean_inc(x_1263);
lean_dec(x_1260);
x_1264 = lean_nat_dec_eq(x_1263, x_1083);
lean_dec(x_1263);
if (x_1264 == 0)
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
lean_dec(x_1100);
x_1265 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_1266 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_1267 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
x_1268 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
lean_inc(x_1258);
x_1269 = l_Lean_mkApp4(x_1265, x_1266, x_1267, x_1268, x_1258);
x_1270 = l_Lean_Meta_mkDecideProof(x_1269, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1270) == 0)
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; uint8_t x_1280; 
x_1271 = lean_ctor_get(x_1270, 0);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1270, 1);
lean_inc(x_1272);
if (lean_is_exclusive(x_1270)) {
 lean_ctor_release(x_1270, 0);
 lean_ctor_release(x_1270, 1);
 x_1273 = x_1270;
} else {
 lean_dec_ref(x_1270);
 x_1273 = lean_box(0);
}
x_1274 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_1275 = l_Lean_mkApp3(x_1274, x_1258, x_1259, x_1271);
x_1276 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_1277 = l_Lean_mkAppB(x_1276, x_1094, x_1275);
x_1278 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_inc(x_1277);
lean_inc(x_136);
lean_inc(x_134);
x_1279 = l_Lean_mkApp3(x_1278, x_134, x_136, x_1277);
x_1280 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_1280 == 0)
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1281 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_1282 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
lean_inc(x_136);
x_1283 = l_Lean_mkApp3(x_1281, x_136, x_1282, x_1277);
x_1284 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_1285 = l_Lean_mkApp3(x_1284, x_134, x_136, x_1283);
x_1286 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1287 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1286, x_1285);
x_1288 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1287, x_1279);
if (lean_is_scalar(x_1273)) {
 x_1289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1289 = x_1273;
}
lean_ctor_set(x_1289, 0, x_1288);
lean_ctor_set(x_1289, 1, x_1272);
return x_1289;
}
else
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
x_1290 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_1291 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_136);
x_1292 = l_Lean_mkApp3(x_1290, x_136, x_1291, x_1277);
x_1293 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_1294 = l_Lean_mkApp3(x_1293, x_134, x_136, x_1292);
x_1295 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1296 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1295, x_1294);
x_1297 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1296, x_1279);
if (lean_is_scalar(x_1273)) {
 x_1298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1298 = x_1273;
}
lean_ctor_set(x_1298, 0, x_1297);
lean_ctor_set(x_1298, 1, x_1272);
return x_1298;
}
}
else
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
lean_dec(x_1259);
lean_dec(x_1258);
lean_dec(x_1094);
lean_dec(x_136);
lean_dec(x_134);
x_1299 = lean_ctor_get(x_1270, 0);
lean_inc(x_1299);
x_1300 = lean_ctor_get(x_1270, 1);
lean_inc(x_1300);
if (lean_is_exclusive(x_1270)) {
 lean_ctor_release(x_1270, 0);
 lean_ctor_release(x_1270, 1);
 x_1301 = x_1270;
} else {
 lean_dec_ref(x_1270);
 x_1301 = lean_box(0);
}
if (lean_is_scalar(x_1301)) {
 x_1302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1302 = x_1301;
}
lean_ctor_set(x_1302, 0, x_1299);
lean_ctor_set(x_1302, 1, x_1300);
return x_1302;
}
}
else
{
lean_object* x_1303; lean_object* x_1304; 
lean_dec(x_1259);
lean_dec(x_1258);
lean_dec(x_1094);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1303 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1100)) {
 x_1304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1304 = x_1100;
}
lean_ctor_set(x_1304, 0, x_1303);
lean_ctor_set(x_1304, 1, x_11);
return x_1304;
}
}
}
}
}
}
else
{
lean_object* x_1305; lean_object* x_1306; 
lean_dec(x_1098);
lean_dec(x_1097);
lean_dec(x_1096);
lean_dec(x_1095);
lean_dec(x_1094);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1305 = l_Lean_Expr_getAppFnArgs(x_134);
x_1306 = lean_ctor_get(x_1305, 0);
lean_inc(x_1306);
if (lean_obj_tag(x_1306) == 1)
{
lean_object* x_1307; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
if (lean_obj_tag(x_1307) == 1)
{
lean_object* x_1308; 
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
if (lean_obj_tag(x_1308) == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; uint8_t x_1313; 
x_1309 = lean_ctor_get(x_1305, 1);
lean_inc(x_1309);
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 lean_ctor_release(x_1305, 1);
 x_1310 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1310 = lean_box(0);
}
x_1311 = lean_ctor_get(x_1306, 1);
lean_inc(x_1311);
lean_dec(x_1306);
x_1312 = lean_ctor_get(x_1307, 1);
lean_inc(x_1312);
lean_dec(x_1307);
x_1313 = lean_string_dec_eq(x_1312, x_79);
lean_dec(x_1312);
if (x_1313 == 0)
{
lean_object* x_1314; lean_object* x_1315; 
lean_dec(x_1311);
lean_dec(x_1309);
lean_dec(x_136);
x_1314 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1310)) {
 x_1315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1315 = x_1310;
}
lean_ctor_set(x_1315, 0, x_1314);
lean_ctor_set(x_1315, 1, x_11);
return x_1315;
}
else
{
uint8_t x_1316; 
x_1316 = lean_string_dec_eq(x_1311, x_1074);
lean_dec(x_1311);
if (x_1316 == 0)
{
lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_1309);
lean_dec(x_136);
x_1317 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1310)) {
 x_1318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1318 = x_1310;
}
lean_ctor_set(x_1318, 0, x_1317);
lean_ctor_set(x_1318, 1, x_11);
return x_1318;
}
else
{
lean_object* x_1319; uint8_t x_1320; 
x_1319 = lean_array_get_size(x_1309);
x_1320 = lean_nat_dec_eq(x_1319, x_1079);
lean_dec(x_1319);
if (x_1320 == 0)
{
lean_object* x_1321; lean_object* x_1322; 
lean_dec(x_1309);
lean_dec(x_136);
x_1321 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1310)) {
 x_1322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1322 = x_1310;
}
lean_ctor_set(x_1322, 0, x_1321);
lean_ctor_set(x_1322, 1, x_11);
return x_1322;
}
else
{
lean_object* x_1323; 
x_1323 = lean_array_fget(x_1309, x_1083);
if (lean_obj_tag(x_1323) == 4)
{
lean_object* x_1324; 
x_1324 = lean_ctor_get(x_1323, 0);
lean_inc(x_1324);
if (lean_obj_tag(x_1324) == 1)
{
lean_object* x_1325; 
x_1325 = lean_ctor_get(x_1324, 0);
lean_inc(x_1325);
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1326; lean_object* x_1327; uint8_t x_1328; 
x_1326 = lean_ctor_get(x_1323, 1);
lean_inc(x_1326);
lean_dec(x_1323);
x_1327 = lean_ctor_get(x_1324, 1);
lean_inc(x_1327);
lean_dec(x_1324);
x_1328 = lean_string_dec_eq(x_1327, x_1089);
lean_dec(x_1327);
if (x_1328 == 0)
{
lean_object* x_1329; lean_object* x_1330; 
lean_dec(x_1326);
lean_dec(x_1309);
lean_dec(x_136);
x_1329 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1310)) {
 x_1330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1330 = x_1310;
}
lean_ctor_set(x_1330, 0, x_1329);
lean_ctor_set(x_1330, 1, x_11);
return x_1330;
}
else
{
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1331 = lean_array_fget(x_1309, x_1093);
lean_dec(x_1309);
x_1332 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_1333 = l_Lean_mkAppB(x_1332, x_1331, x_136);
x_1334 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1335 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1334, x_1333);
if (lean_is_scalar(x_1310)) {
 x_1336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1336 = x_1310;
}
lean_ctor_set(x_1336, 0, x_1335);
lean_ctor_set(x_1336, 1, x_11);
return x_1336;
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; 
lean_dec(x_1310);
lean_dec(x_1309);
lean_dec(x_136);
if (lean_is_exclusive(x_1326)) {
 lean_ctor_release(x_1326, 0);
 lean_ctor_release(x_1326, 1);
 x_1337 = x_1326;
} else {
 lean_dec_ref(x_1326);
 x_1337 = lean_box(0);
}
x_1338 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1337)) {
 x_1339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1339 = x_1337;
 lean_ctor_set_tag(x_1339, 0);
}
lean_ctor_set(x_1339, 0, x_1338);
lean_ctor_set(x_1339, 1, x_11);
return x_1339;
}
}
}
else
{
lean_object* x_1340; lean_object* x_1341; 
lean_dec(x_1325);
lean_dec(x_1324);
lean_dec(x_1323);
lean_dec(x_1309);
lean_dec(x_136);
x_1340 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1310)) {
 x_1341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1341 = x_1310;
}
lean_ctor_set(x_1341, 0, x_1340);
lean_ctor_set(x_1341, 1, x_11);
return x_1341;
}
}
else
{
lean_object* x_1342; lean_object* x_1343; 
lean_dec(x_1324);
lean_dec(x_1323);
lean_dec(x_1309);
lean_dec(x_136);
x_1342 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1310)) {
 x_1343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1343 = x_1310;
}
lean_ctor_set(x_1343, 0, x_1342);
lean_ctor_set(x_1343, 1, x_11);
return x_1343;
}
}
else
{
lean_object* x_1344; lean_object* x_1345; 
lean_dec(x_1323);
lean_dec(x_1309);
lean_dec(x_136);
x_1344 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1310)) {
 x_1345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1345 = x_1310;
}
lean_ctor_set(x_1345, 0, x_1344);
lean_ctor_set(x_1345, 1, x_11);
return x_1345;
}
}
}
}
}
else
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
lean_dec(x_1308);
lean_dec(x_1307);
lean_dec(x_1306);
lean_dec(x_136);
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 lean_ctor_release(x_1305, 1);
 x_1346 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1346 = lean_box(0);
}
x_1347 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1346)) {
 x_1348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1348 = x_1346;
}
lean_ctor_set(x_1348, 0, x_1347);
lean_ctor_set(x_1348, 1, x_11);
return x_1348;
}
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
lean_dec(x_1307);
lean_dec(x_1306);
lean_dec(x_136);
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 lean_ctor_release(x_1305, 1);
 x_1349 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1349 = lean_box(0);
}
x_1350 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1349)) {
 x_1351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1351 = x_1349;
}
lean_ctor_set(x_1351, 0, x_1350);
lean_ctor_set(x_1351, 1, x_11);
return x_1351;
}
}
else
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
lean_dec(x_1306);
lean_dec(x_136);
if (lean_is_exclusive(x_1305)) {
 lean_ctor_release(x_1305, 0);
 lean_ctor_release(x_1305, 1);
 x_1352 = x_1305;
} else {
 lean_dec_ref(x_1305);
 x_1352 = lean_box(0);
}
x_1353 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1352)) {
 x_1354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1354 = x_1352;
}
lean_ctor_set(x_1354, 0, x_1353);
lean_ctor_set(x_1354, 1, x_11);
return x_1354;
}
}
}
else
{
lean_object* x_1355; lean_object* x_1356; 
lean_dec(x_1097);
lean_dec(x_1096);
lean_dec(x_1095);
lean_dec(x_1094);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1355 = l_Lean_Expr_getAppFnArgs(x_134);
x_1356 = lean_ctor_get(x_1355, 0);
lean_inc(x_1356);
if (lean_obj_tag(x_1356) == 1)
{
lean_object* x_1357; 
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
if (lean_obj_tag(x_1357) == 1)
{
lean_object* x_1358; 
x_1358 = lean_ctor_get(x_1357, 0);
lean_inc(x_1358);
if (lean_obj_tag(x_1358) == 0)
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; uint8_t x_1363; 
x_1359 = lean_ctor_get(x_1355, 1);
lean_inc(x_1359);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 x_1360 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1360 = lean_box(0);
}
x_1361 = lean_ctor_get(x_1356, 1);
lean_inc(x_1361);
lean_dec(x_1356);
x_1362 = lean_ctor_get(x_1357, 1);
lean_inc(x_1362);
lean_dec(x_1357);
x_1363 = lean_string_dec_eq(x_1362, x_79);
lean_dec(x_1362);
if (x_1363 == 0)
{
lean_object* x_1364; lean_object* x_1365; 
lean_dec(x_1361);
lean_dec(x_1359);
lean_dec(x_136);
x_1364 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1360)) {
 x_1365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1365 = x_1360;
}
lean_ctor_set(x_1365, 0, x_1364);
lean_ctor_set(x_1365, 1, x_11);
return x_1365;
}
else
{
uint8_t x_1366; 
x_1366 = lean_string_dec_eq(x_1361, x_1074);
lean_dec(x_1361);
if (x_1366 == 0)
{
lean_object* x_1367; lean_object* x_1368; 
lean_dec(x_1359);
lean_dec(x_136);
x_1367 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1360)) {
 x_1368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1368 = x_1360;
}
lean_ctor_set(x_1368, 0, x_1367);
lean_ctor_set(x_1368, 1, x_11);
return x_1368;
}
else
{
lean_object* x_1369; uint8_t x_1370; 
x_1369 = lean_array_get_size(x_1359);
x_1370 = lean_nat_dec_eq(x_1369, x_1079);
lean_dec(x_1369);
if (x_1370 == 0)
{
lean_object* x_1371; lean_object* x_1372; 
lean_dec(x_1359);
lean_dec(x_136);
x_1371 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1360)) {
 x_1372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1372 = x_1360;
}
lean_ctor_set(x_1372, 0, x_1371);
lean_ctor_set(x_1372, 1, x_11);
return x_1372;
}
else
{
lean_object* x_1373; 
x_1373 = lean_array_fget(x_1359, x_1083);
if (lean_obj_tag(x_1373) == 4)
{
lean_object* x_1374; 
x_1374 = lean_ctor_get(x_1373, 0);
lean_inc(x_1374);
if (lean_obj_tag(x_1374) == 1)
{
lean_object* x_1375; 
x_1375 = lean_ctor_get(x_1374, 0);
lean_inc(x_1375);
if (lean_obj_tag(x_1375) == 0)
{
lean_object* x_1376; lean_object* x_1377; uint8_t x_1378; 
x_1376 = lean_ctor_get(x_1373, 1);
lean_inc(x_1376);
lean_dec(x_1373);
x_1377 = lean_ctor_get(x_1374, 1);
lean_inc(x_1377);
lean_dec(x_1374);
x_1378 = lean_string_dec_eq(x_1377, x_1089);
lean_dec(x_1377);
if (x_1378 == 0)
{
lean_object* x_1379; lean_object* x_1380; 
lean_dec(x_1376);
lean_dec(x_1359);
lean_dec(x_136);
x_1379 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1360)) {
 x_1380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1380 = x_1360;
}
lean_ctor_set(x_1380, 0, x_1379);
lean_ctor_set(x_1380, 1, x_11);
return x_1380;
}
else
{
if (lean_obj_tag(x_1376) == 0)
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1381 = lean_array_fget(x_1359, x_1093);
lean_dec(x_1359);
x_1382 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_1383 = l_Lean_mkAppB(x_1382, x_1381, x_136);
x_1384 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1385 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1384, x_1383);
if (lean_is_scalar(x_1360)) {
 x_1386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1386 = x_1360;
}
lean_ctor_set(x_1386, 0, x_1385);
lean_ctor_set(x_1386, 1, x_11);
return x_1386;
}
else
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_1360);
lean_dec(x_1359);
lean_dec(x_136);
if (lean_is_exclusive(x_1376)) {
 lean_ctor_release(x_1376, 0);
 lean_ctor_release(x_1376, 1);
 x_1387 = x_1376;
} else {
 lean_dec_ref(x_1376);
 x_1387 = lean_box(0);
}
x_1388 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1387)) {
 x_1389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1389 = x_1387;
 lean_ctor_set_tag(x_1389, 0);
}
lean_ctor_set(x_1389, 0, x_1388);
lean_ctor_set(x_1389, 1, x_11);
return x_1389;
}
}
}
else
{
lean_object* x_1390; lean_object* x_1391; 
lean_dec(x_1375);
lean_dec(x_1374);
lean_dec(x_1373);
lean_dec(x_1359);
lean_dec(x_136);
x_1390 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1360)) {
 x_1391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1391 = x_1360;
}
lean_ctor_set(x_1391, 0, x_1390);
lean_ctor_set(x_1391, 1, x_11);
return x_1391;
}
}
else
{
lean_object* x_1392; lean_object* x_1393; 
lean_dec(x_1374);
lean_dec(x_1373);
lean_dec(x_1359);
lean_dec(x_136);
x_1392 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1360)) {
 x_1393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1393 = x_1360;
}
lean_ctor_set(x_1393, 0, x_1392);
lean_ctor_set(x_1393, 1, x_11);
return x_1393;
}
}
else
{
lean_object* x_1394; lean_object* x_1395; 
lean_dec(x_1373);
lean_dec(x_1359);
lean_dec(x_136);
x_1394 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1360)) {
 x_1395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1395 = x_1360;
}
lean_ctor_set(x_1395, 0, x_1394);
lean_ctor_set(x_1395, 1, x_11);
return x_1395;
}
}
}
}
}
else
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1358);
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_136);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 x_1396 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1396 = lean_box(0);
}
x_1397 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1396)) {
 x_1398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1398 = x_1396;
}
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_11);
return x_1398;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1357);
lean_dec(x_1356);
lean_dec(x_136);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 x_1399 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1399 = lean_box(0);
}
x_1400 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1399)) {
 x_1401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1401 = x_1399;
}
lean_ctor_set(x_1401, 0, x_1400);
lean_ctor_set(x_1401, 1, x_11);
return x_1401;
}
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
lean_dec(x_1356);
lean_dec(x_136);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 x_1402 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1402 = lean_box(0);
}
x_1403 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1402)) {
 x_1404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1404 = x_1402;
}
lean_ctor_set(x_1404, 0, x_1403);
lean_ctor_set(x_1404, 1, x_11);
return x_1404;
}
}
}
else
{
lean_object* x_1405; lean_object* x_1406; 
lean_dec(x_1096);
lean_dec(x_1095);
lean_dec(x_1094);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1405 = l_Lean_Expr_getAppFnArgs(x_134);
x_1406 = lean_ctor_get(x_1405, 0);
lean_inc(x_1406);
if (lean_obj_tag(x_1406) == 1)
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
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; uint8_t x_1413; 
x_1409 = lean_ctor_get(x_1405, 1);
lean_inc(x_1409);
if (lean_is_exclusive(x_1405)) {
 lean_ctor_release(x_1405, 0);
 lean_ctor_release(x_1405, 1);
 x_1410 = x_1405;
} else {
 lean_dec_ref(x_1405);
 x_1410 = lean_box(0);
}
x_1411 = lean_ctor_get(x_1406, 1);
lean_inc(x_1411);
lean_dec(x_1406);
x_1412 = lean_ctor_get(x_1407, 1);
lean_inc(x_1412);
lean_dec(x_1407);
x_1413 = lean_string_dec_eq(x_1412, x_79);
lean_dec(x_1412);
if (x_1413 == 0)
{
lean_object* x_1414; lean_object* x_1415; 
lean_dec(x_1411);
lean_dec(x_1409);
lean_dec(x_136);
x_1414 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1410)) {
 x_1415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1415 = x_1410;
}
lean_ctor_set(x_1415, 0, x_1414);
lean_ctor_set(x_1415, 1, x_11);
return x_1415;
}
else
{
uint8_t x_1416; 
x_1416 = lean_string_dec_eq(x_1411, x_1074);
lean_dec(x_1411);
if (x_1416 == 0)
{
lean_object* x_1417; lean_object* x_1418; 
lean_dec(x_1409);
lean_dec(x_136);
x_1417 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1410)) {
 x_1418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1418 = x_1410;
}
lean_ctor_set(x_1418, 0, x_1417);
lean_ctor_set(x_1418, 1, x_11);
return x_1418;
}
else
{
lean_object* x_1419; uint8_t x_1420; 
x_1419 = lean_array_get_size(x_1409);
x_1420 = lean_nat_dec_eq(x_1419, x_1079);
lean_dec(x_1419);
if (x_1420 == 0)
{
lean_object* x_1421; lean_object* x_1422; 
lean_dec(x_1409);
lean_dec(x_136);
x_1421 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1410)) {
 x_1422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1422 = x_1410;
}
lean_ctor_set(x_1422, 0, x_1421);
lean_ctor_set(x_1422, 1, x_11);
return x_1422;
}
else
{
lean_object* x_1423; 
x_1423 = lean_array_fget(x_1409, x_1083);
if (lean_obj_tag(x_1423) == 4)
{
lean_object* x_1424; 
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
if (lean_obj_tag(x_1424) == 1)
{
lean_object* x_1425; 
x_1425 = lean_ctor_get(x_1424, 0);
lean_inc(x_1425);
if (lean_obj_tag(x_1425) == 0)
{
lean_object* x_1426; lean_object* x_1427; uint8_t x_1428; 
x_1426 = lean_ctor_get(x_1423, 1);
lean_inc(x_1426);
lean_dec(x_1423);
x_1427 = lean_ctor_get(x_1424, 1);
lean_inc(x_1427);
lean_dec(x_1424);
x_1428 = lean_string_dec_eq(x_1427, x_1089);
lean_dec(x_1427);
if (x_1428 == 0)
{
lean_object* x_1429; lean_object* x_1430; 
lean_dec(x_1426);
lean_dec(x_1409);
lean_dec(x_136);
x_1429 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1410)) {
 x_1430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1430 = x_1410;
}
lean_ctor_set(x_1430, 0, x_1429);
lean_ctor_set(x_1430, 1, x_11);
return x_1430;
}
else
{
if (lean_obj_tag(x_1426) == 0)
{
lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1431 = lean_array_fget(x_1409, x_1093);
lean_dec(x_1409);
x_1432 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_1433 = l_Lean_mkAppB(x_1432, x_1431, x_136);
x_1434 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1435 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1434, x_1433);
if (lean_is_scalar(x_1410)) {
 x_1436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1436 = x_1410;
}
lean_ctor_set(x_1436, 0, x_1435);
lean_ctor_set(x_1436, 1, x_11);
return x_1436;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
lean_dec(x_1410);
lean_dec(x_1409);
lean_dec(x_136);
if (lean_is_exclusive(x_1426)) {
 lean_ctor_release(x_1426, 0);
 lean_ctor_release(x_1426, 1);
 x_1437 = x_1426;
} else {
 lean_dec_ref(x_1426);
 x_1437 = lean_box(0);
}
x_1438 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1437)) {
 x_1439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1439 = x_1437;
 lean_ctor_set_tag(x_1439, 0);
}
lean_ctor_set(x_1439, 0, x_1438);
lean_ctor_set(x_1439, 1, x_11);
return x_1439;
}
}
}
else
{
lean_object* x_1440; lean_object* x_1441; 
lean_dec(x_1425);
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_1409);
lean_dec(x_136);
x_1440 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1410)) {
 x_1441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1441 = x_1410;
}
lean_ctor_set(x_1441, 0, x_1440);
lean_ctor_set(x_1441, 1, x_11);
return x_1441;
}
}
else
{
lean_object* x_1442; lean_object* x_1443; 
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_1409);
lean_dec(x_136);
x_1442 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1410)) {
 x_1443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1443 = x_1410;
}
lean_ctor_set(x_1443, 0, x_1442);
lean_ctor_set(x_1443, 1, x_11);
return x_1443;
}
}
else
{
lean_object* x_1444; lean_object* x_1445; 
lean_dec(x_1423);
lean_dec(x_1409);
lean_dec(x_136);
x_1444 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1410)) {
 x_1445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1445 = x_1410;
}
lean_ctor_set(x_1445, 0, x_1444);
lean_ctor_set(x_1445, 1, x_11);
return x_1445;
}
}
}
}
}
else
{
lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; 
lean_dec(x_1408);
lean_dec(x_1407);
lean_dec(x_1406);
lean_dec(x_136);
if (lean_is_exclusive(x_1405)) {
 lean_ctor_release(x_1405, 0);
 lean_ctor_release(x_1405, 1);
 x_1446 = x_1405;
} else {
 lean_dec_ref(x_1405);
 x_1446 = lean_box(0);
}
x_1447 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1446)) {
 x_1448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1448 = x_1446;
}
lean_ctor_set(x_1448, 0, x_1447);
lean_ctor_set(x_1448, 1, x_11);
return x_1448;
}
}
else
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
lean_dec(x_1407);
lean_dec(x_1406);
lean_dec(x_136);
if (lean_is_exclusive(x_1405)) {
 lean_ctor_release(x_1405, 0);
 lean_ctor_release(x_1405, 1);
 x_1449 = x_1405;
} else {
 lean_dec_ref(x_1405);
 x_1449 = lean_box(0);
}
x_1450 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1449)) {
 x_1451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1451 = x_1449;
}
lean_ctor_set(x_1451, 0, x_1450);
lean_ctor_set(x_1451, 1, x_11);
return x_1451;
}
}
else
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
lean_dec(x_1406);
lean_dec(x_136);
if (lean_is_exclusive(x_1405)) {
 lean_ctor_release(x_1405, 0);
 lean_ctor_release(x_1405, 1);
 x_1452 = x_1405;
} else {
 lean_dec_ref(x_1405);
 x_1452 = lean_box(0);
}
x_1453 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1452)) {
 x_1454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1454 = x_1452;
}
lean_ctor_set(x_1454, 0, x_1453);
lean_ctor_set(x_1454, 1, x_11);
return x_1454;
}
}
}
else
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_exclusive(x_1087)) {
 lean_ctor_release(x_1087, 0);
 lean_ctor_release(x_1087, 1);
 x_1455 = x_1087;
} else {
 lean_dec_ref(x_1087);
 x_1455 = lean_box(0);
}
x_1456 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1455)) {
 x_1457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1457 = x_1455;
 lean_ctor_set_tag(x_1457, 0);
}
lean_ctor_set(x_1457, 0, x_1456);
lean_ctor_set(x_1457, 1, x_11);
return x_1457;
}
}
}
else
{
lean_object* x_1458; lean_object* x_1459; 
lean_dec(x_1086);
lean_dec(x_1085);
lean_dec(x_1084);
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1458 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1459, 0, x_1458);
lean_ctor_set(x_1459, 1, x_11);
return x_1459;
}
}
else
{
lean_object* x_1460; lean_object* x_1461; 
lean_dec(x_1085);
lean_dec(x_1084);
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1460 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1461, 0, x_1460);
lean_ctor_set(x_1461, 1, x_11);
return x_1461;
}
}
else
{
lean_object* x_1462; lean_object* x_1463; 
lean_dec(x_1084);
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1462 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1463, 0, x_1462);
lean_ctor_set(x_1463, 1, x_11);
return x_1463;
}
}
}
}
}
else
{
lean_object* x_1464; uint8_t x_1465; 
lean_dec(x_1068);
x_1464 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_1465 = lean_string_dec_eq(x_1067, x_1464);
lean_dec(x_1067);
if (x_1465 == 0)
{
lean_object* x_1466; lean_object* x_1467; 
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1466 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1467, 0, x_1466);
lean_ctor_set(x_1467, 1, x_11);
return x_1467;
}
else
{
lean_object* x_1468; uint8_t x_1469; 
x_1468 = lean_array_get_size(x_1066);
x_1469 = lean_nat_dec_eq(x_1468, x_130);
lean_dec(x_1468);
if (x_1469 == 0)
{
lean_object* x_1470; lean_object* x_1471; 
lean_dec(x_1066);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1470 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1471, 0, x_1470);
lean_ctor_set(x_1471, 1, x_11);
return x_1471;
}
else
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1472 = lean_array_fget(x_1066, x_133);
x_1473 = lean_array_fget(x_1066, x_135);
lean_dec(x_1066);
lean_inc(x_1472);
x_1474 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1472);
if (lean_obj_tag(x_1474) == 0)
{
lean_object* x_1475; lean_object* x_1476; 
lean_dec(x_1473);
lean_dec(x_1472);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1475 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1476, 0, x_1475);
lean_ctor_set(x_1476, 1, x_11);
return x_1476;
}
else
{
lean_object* x_1477; lean_object* x_1478; uint8_t x_1479; 
x_1477 = lean_ctor_get(x_1474, 0);
lean_inc(x_1477);
lean_dec(x_1474);
x_1478 = lean_unsigned_to_nat(0u);
x_1479 = lean_nat_dec_eq(x_1477, x_1478);
lean_dec(x_1477);
if (x_1479 == 0)
{
lean_object* x_1480; uint8_t x_1506; 
x_1506 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_1506 == 0)
{
lean_object* x_1507; 
x_1507 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76;
x_1480 = x_1507;
goto block_1505;
}
else
{
lean_object* x_1508; 
x_1508 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_1480 = x_1508;
goto block_1505;
}
block_1505:
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
x_1481 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_1482 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_1483 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
lean_inc(x_1472);
lean_inc(x_1480);
x_1484 = l_Lean_mkApp4(x_1481, x_1482, x_1483, x_1480, x_1472);
x_1485 = l_Lean_Meta_mkDecideProof(x_1484, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1485) == 0)
{
lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
x_1486 = lean_ctor_get(x_1485, 0);
lean_inc(x_1486);
x_1487 = lean_ctor_get(x_1485, 1);
lean_inc(x_1487);
if (lean_is_exclusive(x_1485)) {
 lean_ctor_release(x_1485, 0);
 lean_ctor_release(x_1485, 1);
 x_1488 = x_1485;
} else {
 lean_dec_ref(x_1485);
 x_1488 = lean_box(0);
}
x_1489 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
x_1490 = l_Lean_mkApp3(x_1489, x_1472, x_1473, x_1486);
x_1491 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
lean_inc(x_1490);
lean_inc(x_136);
x_1492 = l_Lean_mkApp3(x_1491, x_136, x_1480, x_1490);
x_1493 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_136);
lean_inc(x_134);
x_1494 = l_Lean_mkApp3(x_1493, x_134, x_136, x_1492);
x_1495 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_1496 = l_Lean_mkApp3(x_1495, x_134, x_136, x_1490);
x_1497 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1498 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1497, x_1494);
x_1499 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1498, x_1496);
if (lean_is_scalar(x_1488)) {
 x_1500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1500 = x_1488;
}
lean_ctor_set(x_1500, 0, x_1499);
lean_ctor_set(x_1500, 1, x_1487);
return x_1500;
}
else
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; 
lean_dec(x_1480);
lean_dec(x_1473);
lean_dec(x_1472);
lean_dec(x_136);
lean_dec(x_134);
x_1501 = lean_ctor_get(x_1485, 0);
lean_inc(x_1501);
x_1502 = lean_ctor_get(x_1485, 1);
lean_inc(x_1502);
if (lean_is_exclusive(x_1485)) {
 lean_ctor_release(x_1485, 0);
 lean_ctor_release(x_1485, 1);
 x_1503 = x_1485;
} else {
 lean_dec_ref(x_1485);
 x_1503 = lean_box(0);
}
if (lean_is_scalar(x_1503)) {
 x_1504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1504 = x_1503;
}
lean_ctor_set(x_1504, 0, x_1501);
lean_ctor_set(x_1504, 1, x_1502);
return x_1504;
}
}
}
else
{
lean_object* x_1509; lean_object* x_1510; 
lean_dec(x_1473);
lean_dec(x_1472);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1509 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1510, 0, x_1509);
lean_ctor_set(x_1510, 1, x_11);
return x_1510;
}
}
}
}
}
}
}
else
{
uint8_t x_1511; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1511 = !lean_is_exclusive(x_137);
if (x_1511 == 0)
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
x_1512 = lean_ctor_get(x_137, 1);
lean_dec(x_1512);
x_1513 = lean_ctor_get(x_137, 0);
lean_dec(x_1513);
x_1514 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1514);
return x_137;
}
else
{
lean_object* x_1515; lean_object* x_1516; 
lean_dec(x_137);
x_1515 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1516, 0, x_1515);
lean_ctor_set(x_1516, 1, x_11);
return x_1516;
}
}
}
else
{
uint8_t x_1517; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1517 = !lean_is_exclusive(x_137);
if (x_1517 == 0)
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
x_1518 = lean_ctor_get(x_137, 1);
lean_dec(x_1518);
x_1519 = lean_ctor_get(x_137, 0);
lean_dec(x_1519);
x_1520 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1520);
return x_137;
}
else
{
lean_object* x_1521; lean_object* x_1522; 
lean_dec(x_137);
x_1521 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1522, 0, x_1521);
lean_ctor_set(x_1522, 1, x_11);
return x_1522;
}
}
}
else
{
uint8_t x_1523; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1523 = !lean_is_exclusive(x_137);
if (x_1523 == 0)
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; 
x_1524 = lean_ctor_get(x_137, 1);
lean_dec(x_1524);
x_1525 = lean_ctor_get(x_137, 0);
lean_dec(x_1525);
x_1526 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_137, 1, x_11);
lean_ctor_set(x_137, 0, x_1526);
return x_137;
}
else
{
lean_object* x_1527; lean_object* x_1528; 
lean_dec(x_137);
x_1527 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1528, 0, x_1527);
lean_ctor_set(x_1528, 1, x_11);
return x_1528;
}
}
}
}
}
}
else
{
lean_object* x_1529; uint8_t x_1530; 
lean_dec(x_78);
x_1529 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_1530 = lean_string_dec_eq(x_77, x_1529);
lean_dec(x_77);
if (x_1530 == 0)
{
lean_object* x_1531; 
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1531 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1531);
return x_12;
}
else
{
lean_object* x_1532; lean_object* x_1533; uint8_t x_1534; 
x_1532 = lean_array_get_size(x_75);
x_1533 = lean_unsigned_to_nat(6u);
x_1534 = lean_nat_dec_eq(x_1532, x_1533);
lean_dec(x_1532);
if (x_1534 == 0)
{
lean_object* x_1535; 
lean_dec(x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1535 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1535);
return x_12;
}
else
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; 
x_1536 = lean_unsigned_to_nat(4u);
x_1537 = lean_array_fget(x_75, x_1536);
x_1538 = lean_unsigned_to_nat(5u);
x_1539 = lean_array_fget(x_75, x_1538);
lean_dec(x_75);
lean_inc(x_1539);
x_1540 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_1539);
if (lean_obj_tag(x_1540) == 0)
{
lean_object* x_1541; 
lean_dec(x_1539);
lean_dec(x_1537);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1541 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1541);
return x_12;
}
else
{
lean_object* x_1542; lean_object* x_1543; uint8_t x_1544; 
x_1542 = lean_ctor_get(x_1540, 0);
lean_inc(x_1542);
lean_dec(x_1540);
x_1543 = lean_unsigned_to_nat(0u);
x_1544 = lean_nat_dec_eq(x_1542, x_1543);
lean_dec(x_1542);
if (x_1544 == 0)
{
lean_object* x_1545; uint8_t x_1584; 
lean_free_object(x_12);
x_1584 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_1584 == 0)
{
lean_object* x_1585; 
x_1585 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90;
x_1545 = x_1585;
goto block_1583;
}
else
{
lean_object* x_1586; 
x_1586 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_1545 = x_1586;
goto block_1583;
}
block_1583:
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; 
x_1546 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
x_1547 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
lean_inc(x_1545);
lean_inc(x_1539);
x_1548 = l_Lean_mkApp3(x_1546, x_1547, x_1539, x_1545);
x_1549 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
x_1550 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
lean_inc(x_1539);
x_1551 = l_Lean_mkApp4(x_1549, x_1547, x_1550, x_1545, x_1539);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_1552 = l_Lean_Meta_mkDecideProof(x_1548, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1552) == 0)
{
lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
x_1553 = lean_ctor_get(x_1552, 0);
lean_inc(x_1553);
x_1554 = lean_ctor_get(x_1552, 1);
lean_inc(x_1554);
lean_dec(x_1552);
x_1555 = l_Lean_Meta_mkDecideProof(x_1551, x_7, x_8, x_9, x_10, x_1554);
if (lean_obj_tag(x_1555) == 0)
{
uint8_t x_1556; 
x_1556 = !lean_is_exclusive(x_1555);
if (x_1556 == 0)
{
lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; 
x_1557 = lean_ctor_get(x_1555, 0);
x_1558 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
lean_inc(x_1539);
lean_inc(x_1537);
x_1559 = l_Lean_mkApp3(x_1558, x_1537, x_1539, x_1553);
x_1560 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88;
x_1561 = l_Lean_mkApp3(x_1560, x_1537, x_1539, x_1557);
x_1562 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1563 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1562, x_1559);
x_1564 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1563, x_1561);
lean_ctor_set(x_1555, 0, x_1564);
return x_1555;
}
else
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; 
x_1565 = lean_ctor_get(x_1555, 0);
x_1566 = lean_ctor_get(x_1555, 1);
lean_inc(x_1566);
lean_inc(x_1565);
lean_dec(x_1555);
x_1567 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
lean_inc(x_1539);
lean_inc(x_1537);
x_1568 = l_Lean_mkApp3(x_1567, x_1537, x_1539, x_1553);
x_1569 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88;
x_1570 = l_Lean_mkApp3(x_1569, x_1537, x_1539, x_1565);
x_1571 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1572 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1571, x_1568);
x_1573 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1572, x_1570);
x_1574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1574, 0, x_1573);
lean_ctor_set(x_1574, 1, x_1566);
return x_1574;
}
}
else
{
uint8_t x_1575; 
lean_dec(x_1553);
lean_dec(x_1539);
lean_dec(x_1537);
x_1575 = !lean_is_exclusive(x_1555);
if (x_1575 == 0)
{
return x_1555;
}
else
{
lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; 
x_1576 = lean_ctor_get(x_1555, 0);
x_1577 = lean_ctor_get(x_1555, 1);
lean_inc(x_1577);
lean_inc(x_1576);
lean_dec(x_1555);
x_1578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1578, 0, x_1576);
lean_ctor_set(x_1578, 1, x_1577);
return x_1578;
}
}
}
else
{
uint8_t x_1579; 
lean_dec(x_1551);
lean_dec(x_1539);
lean_dec(x_1537);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1579 = !lean_is_exclusive(x_1552);
if (x_1579 == 0)
{
return x_1552;
}
else
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1580 = lean_ctor_get(x_1552, 0);
x_1581 = lean_ctor_get(x_1552, 1);
lean_inc(x_1581);
lean_inc(x_1580);
lean_dec(x_1552);
x_1582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1582, 0, x_1580);
lean_ctor_set(x_1582, 1, x_1581);
return x_1582;
}
}
}
}
else
{
lean_object* x_1587; 
lean_dec(x_1539);
lean_dec(x_1537);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1587 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1587);
return x_12;
}
}
}
}
}
}
else
{
lean_object* x_1588; uint8_t x_1589; 
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1588 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_1589 = lean_string_dec_eq(x_77, x_1588);
lean_dec(x_77);
if (x_1589 == 0)
{
lean_object* x_1590; 
lean_dec(x_75);
x_1590 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1590);
return x_12;
}
else
{
lean_object* x_1591; lean_object* x_1592; uint8_t x_1593; 
x_1591 = lean_array_get_size(x_75);
x_1592 = lean_unsigned_to_nat(3u);
x_1593 = lean_nat_dec_eq(x_1591, x_1592);
lean_dec(x_1591);
if (x_1593 == 0)
{
lean_object* x_1594; 
lean_dec(x_75);
x_1594 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1594);
return x_12;
}
else
{
lean_object* x_1595; lean_object* x_1596; 
x_1595 = lean_unsigned_to_nat(0u);
x_1596 = lean_array_fget(x_75, x_1595);
if (lean_obj_tag(x_1596) == 4)
{
lean_object* x_1597; 
x_1597 = lean_ctor_get(x_1596, 0);
lean_inc(x_1597);
if (lean_obj_tag(x_1597) == 1)
{
lean_object* x_1598; 
x_1598 = lean_ctor_get(x_1597, 0);
lean_inc(x_1598);
if (lean_obj_tag(x_1598) == 0)
{
lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; uint8_t x_1602; 
x_1599 = lean_ctor_get(x_1596, 1);
lean_inc(x_1599);
lean_dec(x_1596);
x_1600 = lean_ctor_get(x_1597, 1);
lean_inc(x_1600);
lean_dec(x_1597);
x_1601 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_1602 = lean_string_dec_eq(x_1600, x_1601);
lean_dec(x_1600);
if (x_1602 == 0)
{
lean_object* x_1603; 
lean_dec(x_1599);
lean_dec(x_75);
x_1603 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1603);
return x_12;
}
else
{
lean_free_object(x_12);
if (lean_obj_tag(x_1599) == 0)
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; uint8_t x_1610; lean_object* x_1611; 
x_1604 = lean_unsigned_to_nat(2u);
x_1605 = lean_array_fget(x_75, x_1604);
lean_dec(x_75);
x_1606 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93;
lean_inc(x_1605);
x_1607 = l_Lean_Expr_app___override(x_1606, x_1605);
x_1608 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1609 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1608, x_1607);
x_1610 = lean_ctor_get_uint8(x_4, 1);
x_1611 = l_Lean_Expr_getAppFnArgs(x_1605);
if (x_1610 == 0)
{
lean_object* x_1612; 
x_1612 = lean_ctor_get(x_1611, 0);
lean_inc(x_1612);
if (lean_obj_tag(x_1612) == 1)
{
lean_object* x_1613; 
x_1613 = lean_ctor_get(x_1612, 0);
lean_inc(x_1613);
if (lean_obj_tag(x_1613) == 1)
{
lean_object* x_1614; 
x_1614 = lean_ctor_get(x_1613, 0);
lean_inc(x_1614);
if (lean_obj_tag(x_1614) == 0)
{
uint8_t x_1615; 
x_1615 = !lean_is_exclusive(x_1611);
if (x_1615 == 0)
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; uint8_t x_1620; 
x_1616 = lean_ctor_get(x_1611, 1);
x_1617 = lean_ctor_get(x_1611, 0);
lean_dec(x_1617);
x_1618 = lean_ctor_get(x_1612, 1);
lean_inc(x_1618);
lean_dec(x_1612);
x_1619 = lean_ctor_get(x_1613, 1);
lean_inc(x_1619);
lean_dec(x_1613);
x_1620 = lean_string_dec_eq(x_1619, x_1601);
if (x_1620 == 0)
{
lean_object* x_1621; uint8_t x_1622; 
x_1621 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_1622 = lean_string_dec_eq(x_1619, x_1621);
if (x_1622 == 0)
{
lean_object* x_1623; uint8_t x_1624; 
x_1623 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_1624 = lean_string_dec_eq(x_1619, x_1623);
lean_dec(x_1619);
if (x_1624 == 0)
{
lean_dec(x_1618);
lean_dec(x_1616);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1625; uint8_t x_1626; 
x_1625 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_1626 = lean_string_dec_eq(x_1618, x_1625);
lean_dec(x_1618);
if (x_1626 == 0)
{
lean_dec(x_1616);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1627; uint8_t x_1628; 
x_1627 = lean_array_get_size(x_1616);
x_1628 = lean_nat_dec_eq(x_1627, x_1604);
lean_dec(x_1627);
if (x_1628 == 0)
{
lean_dec(x_1616);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; 
x_1629 = lean_array_fget(x_1616, x_1595);
x_1630 = lean_unsigned_to_nat(1u);
x_1631 = lean_array_fget(x_1616, x_1630);
lean_dec(x_1616);
x_1632 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_1633 = l_Lean_mkAppB(x_1632, x_1629, x_1631);
x_1634 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1633);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1634);
return x_1611;
}
}
}
}
else
{
lean_object* x_1635; uint8_t x_1636; 
lean_dec(x_1619);
x_1635 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_1636 = lean_string_dec_eq(x_1618, x_1635);
lean_dec(x_1618);
if (x_1636 == 0)
{
lean_dec(x_1616);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1637; uint8_t x_1638; 
x_1637 = lean_array_get_size(x_1616);
x_1638 = lean_nat_dec_eq(x_1637, x_1604);
lean_dec(x_1637);
if (x_1638 == 0)
{
lean_dec(x_1616);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1639 = lean_array_fget(x_1616, x_1595);
x_1640 = lean_unsigned_to_nat(1u);
x_1641 = lean_array_fget(x_1616, x_1640);
lean_dec(x_1616);
x_1642 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_1643 = l_Lean_mkAppB(x_1642, x_1639, x_1641);
x_1644 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1643);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1644);
return x_1611;
}
}
}
}
else
{
lean_object* x_1645; uint8_t x_1646; 
lean_dec(x_1619);
x_1645 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_1646 = lean_string_dec_eq(x_1618, x_1645);
lean_dec(x_1618);
if (x_1646 == 0)
{
lean_dec(x_1616);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1647; lean_object* x_1648; uint8_t x_1649; 
x_1647 = lean_array_get_size(x_1616);
x_1648 = lean_unsigned_to_nat(1u);
x_1649 = lean_nat_dec_eq(x_1647, x_1648);
lean_dec(x_1647);
if (x_1649 == 0)
{
lean_dec(x_1616);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; 
x_1650 = lean_array_fget(x_1616, x_1595);
lean_dec(x_1616);
x_1651 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_1650);
x_1652 = l_Lean_Expr_app___override(x_1651, x_1650);
x_1653 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_1654 = l_Lean_Expr_app___override(x_1653, x_1650);
x_1655 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1652);
x_1656 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1655, x_1654);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1656);
return x_1611;
}
}
}
}
else
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; uint8_t x_1660; 
x_1657 = lean_ctor_get(x_1611, 1);
lean_inc(x_1657);
lean_dec(x_1611);
x_1658 = lean_ctor_get(x_1612, 1);
lean_inc(x_1658);
lean_dec(x_1612);
x_1659 = lean_ctor_get(x_1613, 1);
lean_inc(x_1659);
lean_dec(x_1613);
x_1660 = lean_string_dec_eq(x_1659, x_1601);
if (x_1660 == 0)
{
lean_object* x_1661; uint8_t x_1662; 
x_1661 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_1662 = lean_string_dec_eq(x_1659, x_1661);
if (x_1662 == 0)
{
lean_object* x_1663; uint8_t x_1664; 
x_1663 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_1664 = lean_string_dec_eq(x_1659, x_1663);
lean_dec(x_1659);
if (x_1664 == 0)
{
lean_object* x_1665; 
lean_dec(x_1658);
lean_dec(x_1657);
x_1665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1665, 0, x_1609);
lean_ctor_set(x_1665, 1, x_11);
return x_1665;
}
else
{
lean_object* x_1666; uint8_t x_1667; 
x_1666 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_1667 = lean_string_dec_eq(x_1658, x_1666);
lean_dec(x_1658);
if (x_1667 == 0)
{
lean_object* x_1668; 
lean_dec(x_1657);
x_1668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1668, 0, x_1609);
lean_ctor_set(x_1668, 1, x_11);
return x_1668;
}
else
{
lean_object* x_1669; uint8_t x_1670; 
x_1669 = lean_array_get_size(x_1657);
x_1670 = lean_nat_dec_eq(x_1669, x_1604);
lean_dec(x_1669);
if (x_1670 == 0)
{
lean_object* x_1671; 
lean_dec(x_1657);
x_1671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1671, 0, x_1609);
lean_ctor_set(x_1671, 1, x_11);
return x_1671;
}
else
{
lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
x_1672 = lean_array_fget(x_1657, x_1595);
x_1673 = lean_unsigned_to_nat(1u);
x_1674 = lean_array_fget(x_1657, x_1673);
lean_dec(x_1657);
x_1675 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_1676 = l_Lean_mkAppB(x_1675, x_1672, x_1674);
x_1677 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1676);
x_1678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1678, 0, x_1677);
lean_ctor_set(x_1678, 1, x_11);
return x_1678;
}
}
}
}
else
{
lean_object* x_1679; uint8_t x_1680; 
lean_dec(x_1659);
x_1679 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_1680 = lean_string_dec_eq(x_1658, x_1679);
lean_dec(x_1658);
if (x_1680 == 0)
{
lean_object* x_1681; 
lean_dec(x_1657);
x_1681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1681, 0, x_1609);
lean_ctor_set(x_1681, 1, x_11);
return x_1681;
}
else
{
lean_object* x_1682; uint8_t x_1683; 
x_1682 = lean_array_get_size(x_1657);
x_1683 = lean_nat_dec_eq(x_1682, x_1604);
lean_dec(x_1682);
if (x_1683 == 0)
{
lean_object* x_1684; 
lean_dec(x_1657);
x_1684 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1684, 0, x_1609);
lean_ctor_set(x_1684, 1, x_11);
return x_1684;
}
else
{
lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; 
x_1685 = lean_array_fget(x_1657, x_1595);
x_1686 = lean_unsigned_to_nat(1u);
x_1687 = lean_array_fget(x_1657, x_1686);
lean_dec(x_1657);
x_1688 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_1689 = l_Lean_mkAppB(x_1688, x_1685, x_1687);
x_1690 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1689);
x_1691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1691, 0, x_1690);
lean_ctor_set(x_1691, 1, x_11);
return x_1691;
}
}
}
}
else
{
lean_object* x_1692; uint8_t x_1693; 
lean_dec(x_1659);
x_1692 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_1693 = lean_string_dec_eq(x_1658, x_1692);
lean_dec(x_1658);
if (x_1693 == 0)
{
lean_object* x_1694; 
lean_dec(x_1657);
x_1694 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1694, 0, x_1609);
lean_ctor_set(x_1694, 1, x_11);
return x_1694;
}
else
{
lean_object* x_1695; lean_object* x_1696; uint8_t x_1697; 
x_1695 = lean_array_get_size(x_1657);
x_1696 = lean_unsigned_to_nat(1u);
x_1697 = lean_nat_dec_eq(x_1695, x_1696);
lean_dec(x_1695);
if (x_1697 == 0)
{
lean_object* x_1698; 
lean_dec(x_1657);
x_1698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1698, 0, x_1609);
lean_ctor_set(x_1698, 1, x_11);
return x_1698;
}
else
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; 
x_1699 = lean_array_fget(x_1657, x_1595);
lean_dec(x_1657);
x_1700 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_1699);
x_1701 = l_Lean_Expr_app___override(x_1700, x_1699);
x_1702 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_1703 = l_Lean_Expr_app___override(x_1702, x_1699);
x_1704 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1701);
x_1705 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1704, x_1703);
x_1706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1706, 0, x_1705);
lean_ctor_set(x_1706, 1, x_11);
return x_1706;
}
}
}
}
}
else
{
uint8_t x_1707; 
lean_dec(x_1614);
lean_dec(x_1613);
lean_dec(x_1612);
x_1707 = !lean_is_exclusive(x_1611);
if (x_1707 == 0)
{
lean_object* x_1708; lean_object* x_1709; 
x_1708 = lean_ctor_get(x_1611, 1);
lean_dec(x_1708);
x_1709 = lean_ctor_get(x_1611, 0);
lean_dec(x_1709);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1710; 
lean_dec(x_1611);
x_1710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1710, 0, x_1609);
lean_ctor_set(x_1710, 1, x_11);
return x_1710;
}
}
}
else
{
uint8_t x_1711; 
lean_dec(x_1613);
lean_dec(x_1612);
x_1711 = !lean_is_exclusive(x_1611);
if (x_1711 == 0)
{
lean_object* x_1712; lean_object* x_1713; 
x_1712 = lean_ctor_get(x_1611, 1);
lean_dec(x_1712);
x_1713 = lean_ctor_get(x_1611, 0);
lean_dec(x_1713);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1714; 
lean_dec(x_1611);
x_1714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1714, 0, x_1609);
lean_ctor_set(x_1714, 1, x_11);
return x_1714;
}
}
}
else
{
uint8_t x_1715; 
lean_dec(x_1612);
x_1715 = !lean_is_exclusive(x_1611);
if (x_1715 == 0)
{
lean_object* x_1716; lean_object* x_1717; 
x_1716 = lean_ctor_get(x_1611, 1);
lean_dec(x_1716);
x_1717 = lean_ctor_get(x_1611, 0);
lean_dec(x_1717);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1718; 
lean_dec(x_1611);
x_1718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1718, 0, x_1609);
lean_ctor_set(x_1718, 1, x_11);
return x_1718;
}
}
}
else
{
lean_object* x_1719; 
x_1719 = lean_ctor_get(x_1611, 0);
lean_inc(x_1719);
if (lean_obj_tag(x_1719) == 1)
{
lean_object* x_1720; 
x_1720 = lean_ctor_get(x_1719, 0);
lean_inc(x_1720);
if (lean_obj_tag(x_1720) == 1)
{
lean_object* x_1721; 
x_1721 = lean_ctor_get(x_1720, 0);
lean_inc(x_1721);
if (lean_obj_tag(x_1721) == 0)
{
uint8_t x_1722; 
x_1722 = !lean_is_exclusive(x_1611);
if (x_1722 == 0)
{
lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; uint8_t x_1728; 
x_1723 = lean_ctor_get(x_1611, 1);
x_1724 = lean_ctor_get(x_1611, 0);
lean_dec(x_1724);
x_1725 = lean_ctor_get(x_1719, 1);
lean_inc(x_1725);
lean_dec(x_1719);
x_1726 = lean_ctor_get(x_1720, 1);
lean_inc(x_1726);
lean_dec(x_1720);
x_1727 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_1728 = lean_string_dec_eq(x_1726, x_1727);
if (x_1728 == 0)
{
uint8_t x_1729; 
x_1729 = lean_string_dec_eq(x_1726, x_1601);
if (x_1729 == 0)
{
lean_object* x_1730; uint8_t x_1731; 
x_1730 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_1731 = lean_string_dec_eq(x_1726, x_1730);
if (x_1731 == 0)
{
lean_object* x_1732; uint8_t x_1733; 
x_1732 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_1733 = lean_string_dec_eq(x_1726, x_1732);
lean_dec(x_1726);
if (x_1733 == 0)
{
lean_dec(x_1725);
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1734; uint8_t x_1735; 
x_1734 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_1735 = lean_string_dec_eq(x_1725, x_1734);
lean_dec(x_1725);
if (x_1735 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1736; uint8_t x_1737; 
x_1736 = lean_array_get_size(x_1723);
x_1737 = lean_nat_dec_eq(x_1736, x_1604);
lean_dec(x_1736);
if (x_1737 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; 
x_1738 = lean_array_fget(x_1723, x_1595);
x_1739 = lean_unsigned_to_nat(1u);
x_1740 = lean_array_fget(x_1723, x_1739);
lean_dec(x_1723);
x_1741 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_1742 = l_Lean_mkAppB(x_1741, x_1738, x_1740);
x_1743 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1742);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1743);
return x_1611;
}
}
}
}
else
{
lean_object* x_1744; uint8_t x_1745; 
lean_dec(x_1726);
x_1744 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_1745 = lean_string_dec_eq(x_1725, x_1744);
lean_dec(x_1725);
if (x_1745 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1746; uint8_t x_1747; 
x_1746 = lean_array_get_size(x_1723);
x_1747 = lean_nat_dec_eq(x_1746, x_1604);
lean_dec(x_1746);
if (x_1747 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; 
x_1748 = lean_array_fget(x_1723, x_1595);
x_1749 = lean_unsigned_to_nat(1u);
x_1750 = lean_array_fget(x_1723, x_1749);
lean_dec(x_1723);
x_1751 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_1752 = l_Lean_mkAppB(x_1751, x_1748, x_1750);
x_1753 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1752);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1753);
return x_1611;
}
}
}
}
else
{
lean_object* x_1754; uint8_t x_1755; 
lean_dec(x_1726);
x_1754 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_1755 = lean_string_dec_eq(x_1725, x_1754);
lean_dec(x_1725);
if (x_1755 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1756; lean_object* x_1757; uint8_t x_1758; 
x_1756 = lean_array_get_size(x_1723);
x_1757 = lean_unsigned_to_nat(1u);
x_1758 = lean_nat_dec_eq(x_1756, x_1757);
lean_dec(x_1756);
if (x_1758 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; 
x_1759 = lean_array_fget(x_1723, x_1595);
lean_dec(x_1723);
x_1760 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_1759);
x_1761 = l_Lean_Expr_app___override(x_1760, x_1759);
x_1762 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_1763 = l_Lean_Expr_app___override(x_1762, x_1759);
x_1764 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1761);
x_1765 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1764, x_1763);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1765);
return x_1611;
}
}
}
}
else
{
lean_object* x_1766; uint8_t x_1767; 
lean_dec(x_1726);
x_1766 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
x_1767 = lean_string_dec_eq(x_1725, x_1766);
lean_dec(x_1725);
if (x_1767 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1768; lean_object* x_1769; uint8_t x_1770; 
x_1768 = lean_array_get_size(x_1723);
x_1769 = lean_unsigned_to_nat(6u);
x_1770 = lean_nat_dec_eq(x_1768, x_1769);
lean_dec(x_1768);
if (x_1770 == 0)
{
lean_dec(x_1723);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
x_1771 = lean_unsigned_to_nat(4u);
x_1772 = lean_array_fget(x_1723, x_1771);
x_1773 = lean_unsigned_to_nat(5u);
x_1774 = lean_array_fget(x_1723, x_1773);
lean_dec(x_1723);
x_1775 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112;
x_1776 = l_Lean_mkAppB(x_1775, x_1772, x_1774);
x_1777 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1776);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1777);
return x_1611;
}
}
}
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; uint8_t x_1782; 
x_1778 = lean_ctor_get(x_1611, 1);
lean_inc(x_1778);
lean_dec(x_1611);
x_1779 = lean_ctor_get(x_1719, 1);
lean_inc(x_1779);
lean_dec(x_1719);
x_1780 = lean_ctor_get(x_1720, 1);
lean_inc(x_1780);
lean_dec(x_1720);
x_1781 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_1782 = lean_string_dec_eq(x_1780, x_1781);
if (x_1782 == 0)
{
uint8_t x_1783; 
x_1783 = lean_string_dec_eq(x_1780, x_1601);
if (x_1783 == 0)
{
lean_object* x_1784; uint8_t x_1785; 
x_1784 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_1785 = lean_string_dec_eq(x_1780, x_1784);
if (x_1785 == 0)
{
lean_object* x_1786; uint8_t x_1787; 
x_1786 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_1787 = lean_string_dec_eq(x_1780, x_1786);
lean_dec(x_1780);
if (x_1787 == 0)
{
lean_object* x_1788; 
lean_dec(x_1779);
lean_dec(x_1778);
x_1788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1788, 0, x_1609);
lean_ctor_set(x_1788, 1, x_11);
return x_1788;
}
else
{
lean_object* x_1789; uint8_t x_1790; 
x_1789 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_1790 = lean_string_dec_eq(x_1779, x_1789);
lean_dec(x_1779);
if (x_1790 == 0)
{
lean_object* x_1791; 
lean_dec(x_1778);
x_1791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1791, 0, x_1609);
lean_ctor_set(x_1791, 1, x_11);
return x_1791;
}
else
{
lean_object* x_1792; uint8_t x_1793; 
x_1792 = lean_array_get_size(x_1778);
x_1793 = lean_nat_dec_eq(x_1792, x_1604);
lean_dec(x_1792);
if (x_1793 == 0)
{
lean_object* x_1794; 
lean_dec(x_1778);
x_1794 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1794, 0, x_1609);
lean_ctor_set(x_1794, 1, x_11);
return x_1794;
}
else
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; 
x_1795 = lean_array_fget(x_1778, x_1595);
x_1796 = lean_unsigned_to_nat(1u);
x_1797 = lean_array_fget(x_1778, x_1796);
lean_dec(x_1778);
x_1798 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_1799 = l_Lean_mkAppB(x_1798, x_1795, x_1797);
x_1800 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1799);
x_1801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1801, 0, x_1800);
lean_ctor_set(x_1801, 1, x_11);
return x_1801;
}
}
}
}
else
{
lean_object* x_1802; uint8_t x_1803; 
lean_dec(x_1780);
x_1802 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_1803 = lean_string_dec_eq(x_1779, x_1802);
lean_dec(x_1779);
if (x_1803 == 0)
{
lean_object* x_1804; 
lean_dec(x_1778);
x_1804 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1804, 0, x_1609);
lean_ctor_set(x_1804, 1, x_11);
return x_1804;
}
else
{
lean_object* x_1805; uint8_t x_1806; 
x_1805 = lean_array_get_size(x_1778);
x_1806 = lean_nat_dec_eq(x_1805, x_1604);
lean_dec(x_1805);
if (x_1806 == 0)
{
lean_object* x_1807; 
lean_dec(x_1778);
x_1807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1807, 0, x_1609);
lean_ctor_set(x_1807, 1, x_11);
return x_1807;
}
else
{
lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; 
x_1808 = lean_array_fget(x_1778, x_1595);
x_1809 = lean_unsigned_to_nat(1u);
x_1810 = lean_array_fget(x_1778, x_1809);
lean_dec(x_1778);
x_1811 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_1812 = l_Lean_mkAppB(x_1811, x_1808, x_1810);
x_1813 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1812);
x_1814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1814, 0, x_1813);
lean_ctor_set(x_1814, 1, x_11);
return x_1814;
}
}
}
}
else
{
lean_object* x_1815; uint8_t x_1816; 
lean_dec(x_1780);
x_1815 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_1816 = lean_string_dec_eq(x_1779, x_1815);
lean_dec(x_1779);
if (x_1816 == 0)
{
lean_object* x_1817; 
lean_dec(x_1778);
x_1817 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1817, 0, x_1609);
lean_ctor_set(x_1817, 1, x_11);
return x_1817;
}
else
{
lean_object* x_1818; lean_object* x_1819; uint8_t x_1820; 
x_1818 = lean_array_get_size(x_1778);
x_1819 = lean_unsigned_to_nat(1u);
x_1820 = lean_nat_dec_eq(x_1818, x_1819);
lean_dec(x_1818);
if (x_1820 == 0)
{
lean_object* x_1821; 
lean_dec(x_1778);
x_1821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1821, 0, x_1609);
lean_ctor_set(x_1821, 1, x_11);
return x_1821;
}
else
{
lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; 
x_1822 = lean_array_fget(x_1778, x_1595);
lean_dec(x_1778);
x_1823 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_1822);
x_1824 = l_Lean_Expr_app___override(x_1823, x_1822);
x_1825 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_1826 = l_Lean_Expr_app___override(x_1825, x_1822);
x_1827 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1824);
x_1828 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1827, x_1826);
x_1829 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1829, 0, x_1828);
lean_ctor_set(x_1829, 1, x_11);
return x_1829;
}
}
}
}
else
{
lean_object* x_1830; uint8_t x_1831; 
lean_dec(x_1780);
x_1830 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
x_1831 = lean_string_dec_eq(x_1779, x_1830);
lean_dec(x_1779);
if (x_1831 == 0)
{
lean_object* x_1832; 
lean_dec(x_1778);
x_1832 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1832, 0, x_1609);
lean_ctor_set(x_1832, 1, x_11);
return x_1832;
}
else
{
lean_object* x_1833; lean_object* x_1834; uint8_t x_1835; 
x_1833 = lean_array_get_size(x_1778);
x_1834 = lean_unsigned_to_nat(6u);
x_1835 = lean_nat_dec_eq(x_1833, x_1834);
lean_dec(x_1833);
if (x_1835 == 0)
{
lean_object* x_1836; 
lean_dec(x_1778);
x_1836 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1836, 0, x_1609);
lean_ctor_set(x_1836, 1, x_11);
return x_1836;
}
else
{
lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; 
x_1837 = lean_unsigned_to_nat(4u);
x_1838 = lean_array_fget(x_1778, x_1837);
x_1839 = lean_unsigned_to_nat(5u);
x_1840 = lean_array_fget(x_1778, x_1839);
lean_dec(x_1778);
x_1841 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112;
x_1842 = l_Lean_mkAppB(x_1841, x_1838, x_1840);
x_1843 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1609, x_1842);
x_1844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1844, 0, x_1843);
lean_ctor_set(x_1844, 1, x_11);
return x_1844;
}
}
}
}
}
else
{
uint8_t x_1845; 
lean_dec(x_1721);
lean_dec(x_1720);
lean_dec(x_1719);
x_1845 = !lean_is_exclusive(x_1611);
if (x_1845 == 0)
{
lean_object* x_1846; lean_object* x_1847; 
x_1846 = lean_ctor_get(x_1611, 1);
lean_dec(x_1846);
x_1847 = lean_ctor_get(x_1611, 0);
lean_dec(x_1847);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1848; 
lean_dec(x_1611);
x_1848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1848, 0, x_1609);
lean_ctor_set(x_1848, 1, x_11);
return x_1848;
}
}
}
else
{
uint8_t x_1849; 
lean_dec(x_1720);
lean_dec(x_1719);
x_1849 = !lean_is_exclusive(x_1611);
if (x_1849 == 0)
{
lean_object* x_1850; lean_object* x_1851; 
x_1850 = lean_ctor_get(x_1611, 1);
lean_dec(x_1850);
x_1851 = lean_ctor_get(x_1611, 0);
lean_dec(x_1851);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1852; 
lean_dec(x_1611);
x_1852 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1852, 0, x_1609);
lean_ctor_set(x_1852, 1, x_11);
return x_1852;
}
}
}
else
{
uint8_t x_1853; 
lean_dec(x_1719);
x_1853 = !lean_is_exclusive(x_1611);
if (x_1853 == 0)
{
lean_object* x_1854; lean_object* x_1855; 
x_1854 = lean_ctor_get(x_1611, 1);
lean_dec(x_1854);
x_1855 = lean_ctor_get(x_1611, 0);
lean_dec(x_1855);
lean_ctor_set(x_1611, 1, x_11);
lean_ctor_set(x_1611, 0, x_1609);
return x_1611;
}
else
{
lean_object* x_1856; 
lean_dec(x_1611);
x_1856 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1856, 0, x_1609);
lean_ctor_set(x_1856, 1, x_11);
return x_1856;
}
}
}
}
else
{
uint8_t x_1857; 
lean_dec(x_75);
x_1857 = !lean_is_exclusive(x_1599);
if (x_1857 == 0)
{
lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; 
x_1858 = lean_ctor_get(x_1599, 1);
lean_dec(x_1858);
x_1859 = lean_ctor_get(x_1599, 0);
lean_dec(x_1859);
x_1860 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set_tag(x_1599, 0);
lean_ctor_set(x_1599, 1, x_11);
lean_ctor_set(x_1599, 0, x_1860);
return x_1599;
}
else
{
lean_object* x_1861; lean_object* x_1862; 
lean_dec(x_1599);
x_1861 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1862 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1862, 0, x_1861);
lean_ctor_set(x_1862, 1, x_11);
return x_1862;
}
}
}
}
else
{
lean_object* x_1863; 
lean_dec(x_1598);
lean_dec(x_1597);
lean_dec(x_1596);
lean_dec(x_75);
x_1863 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1863);
return x_12;
}
}
else
{
lean_object* x_1864; 
lean_dec(x_1597);
lean_dec(x_1596);
lean_dec(x_75);
x_1864 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1864);
return x_12;
}
}
else
{
lean_object* x_1865; 
lean_dec(x_1596);
lean_dec(x_75);
x_1865 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_1865);
return x_12;
}
}
}
}
}
else
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; uint8_t x_1870; 
x_1866 = lean_ctor_get(x_12, 1);
lean_inc(x_1866);
lean_dec(x_12);
x_1867 = lean_ctor_get(x_13, 1);
lean_inc(x_1867);
lean_dec(x_13);
x_1868 = lean_ctor_get(x_14, 1);
lean_inc(x_1868);
lean_dec(x_14);
x_1869 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_1870 = lean_string_dec_eq(x_1868, x_1869);
if (x_1870 == 0)
{
lean_object* x_1871; uint8_t x_1872; 
x_1871 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_1872 = lean_string_dec_eq(x_1868, x_1871);
if (x_1872 == 0)
{
lean_object* x_1873; uint8_t x_1874; 
x_1873 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8;
x_1874 = lean_string_dec_eq(x_1868, x_1873);
if (x_1874 == 0)
{
lean_object* x_1875; uint8_t x_1876; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1875 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_1876 = lean_string_dec_eq(x_1868, x_1875);
if (x_1876 == 0)
{
lean_object* x_1877; uint8_t x_1878; 
x_1877 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10;
x_1878 = lean_string_dec_eq(x_1868, x_1877);
lean_dec(x_1868);
if (x_1878 == 0)
{
lean_object* x_1879; lean_object* x_1880; 
lean_dec(x_1867);
lean_dec(x_1866);
x_1879 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1880 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1880, 0, x_1879);
lean_ctor_set(x_1880, 1, x_11);
return x_1880;
}
else
{
lean_object* x_1881; uint8_t x_1882; 
x_1881 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11;
x_1882 = lean_string_dec_eq(x_1867, x_1881);
lean_dec(x_1867);
if (x_1882 == 0)
{
lean_object* x_1883; lean_object* x_1884; 
lean_dec(x_1866);
x_1883 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1884 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1884, 0, x_1883);
lean_ctor_set(x_1884, 1, x_11);
return x_1884;
}
else
{
lean_object* x_1885; lean_object* x_1886; uint8_t x_1887; 
x_1885 = lean_array_get_size(x_1866);
x_1886 = lean_unsigned_to_nat(4u);
x_1887 = lean_nat_dec_eq(x_1885, x_1886);
lean_dec(x_1885);
if (x_1887 == 0)
{
lean_object* x_1888; lean_object* x_1889; 
lean_dec(x_1866);
x_1888 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1889 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1889, 0, x_1888);
lean_ctor_set(x_1889, 1, x_11);
return x_1889;
}
else
{
lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; 
x_1890 = lean_unsigned_to_nat(2u);
x_1891 = lean_array_fget(x_1866, x_1890);
x_1892 = lean_unsigned_to_nat(3u);
x_1893 = lean_array_fget(x_1866, x_1892);
lean_dec(x_1866);
x_1894 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14;
lean_inc(x_1893);
lean_inc(x_1891);
x_1895 = l_Lean_mkAppB(x_1894, x_1891, x_1893);
x_1896 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17;
x_1897 = l_Lean_mkAppB(x_1896, x_1891, x_1893);
x_1898 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1899 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1898, x_1895);
x_1900 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1899, x_1897);
x_1901 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1901, 0, x_1900);
lean_ctor_set(x_1901, 1, x_11);
return x_1901;
}
}
}
}
else
{
lean_object* x_1902; uint8_t x_1903; 
lean_dec(x_1868);
x_1902 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18;
x_1903 = lean_string_dec_eq(x_1867, x_1902);
lean_dec(x_1867);
if (x_1903 == 0)
{
lean_object* x_1904; lean_object* x_1905; 
lean_dec(x_1866);
x_1904 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1905 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1905, 0, x_1904);
lean_ctor_set(x_1905, 1, x_11);
return x_1905;
}
else
{
lean_object* x_1906; lean_object* x_1907; uint8_t x_1908; 
x_1906 = lean_array_get_size(x_1866);
x_1907 = lean_unsigned_to_nat(4u);
x_1908 = lean_nat_dec_eq(x_1906, x_1907);
lean_dec(x_1906);
if (x_1908 == 0)
{
lean_object* x_1909; lean_object* x_1910; 
lean_dec(x_1866);
x_1909 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1910 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1910, 0, x_1909);
lean_ctor_set(x_1910, 1, x_11);
return x_1910;
}
else
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; 
x_1911 = lean_unsigned_to_nat(2u);
x_1912 = lean_array_fget(x_1866, x_1911);
x_1913 = lean_unsigned_to_nat(3u);
x_1914 = lean_array_fget(x_1866, x_1913);
lean_dec(x_1866);
x_1915 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21;
lean_inc(x_1914);
lean_inc(x_1912);
x_1916 = l_Lean_mkAppB(x_1915, x_1912, x_1914);
x_1917 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24;
x_1918 = l_Lean_mkAppB(x_1917, x_1912, x_1914);
x_1919 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1920 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1919, x_1916);
x_1921 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_1920, x_1918);
x_1922 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1922, 0, x_1921);
lean_ctor_set(x_1922, 1, x_11);
return x_1922;
}
}
}
}
else
{
lean_object* x_1923; uint8_t x_1924; 
lean_dec(x_1868);
x_1923 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25;
x_1924 = lean_string_dec_eq(x_1867, x_1923);
lean_dec(x_1867);
if (x_1924 == 0)
{
lean_object* x_1925; lean_object* x_1926; 
lean_dec(x_1866);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1925 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1926 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1926, 0, x_1925);
lean_ctor_set(x_1926, 1, x_11);
return x_1926;
}
else
{
lean_object* x_1927; lean_object* x_1928; uint8_t x_1929; 
x_1927 = lean_array_get_size(x_1866);
x_1928 = lean_unsigned_to_nat(6u);
x_1929 = lean_nat_dec_eq(x_1927, x_1928);
lean_dec(x_1927);
if (x_1929 == 0)
{
lean_object* x_1930; lean_object* x_1931; 
lean_dec(x_1866);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1930 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_1931 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1931, 0, x_1930);
lean_ctor_set(x_1931, 1, x_11);
return x_1931;
}
else
{
lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; 
x_1932 = lean_unsigned_to_nat(4u);
x_1933 = lean_array_fget(x_1866, x_1932);
x_1934 = lean_unsigned_to_nat(5u);
x_1935 = lean_array_fget(x_1866, x_1934);
lean_dec(x_1866);
lean_inc(x_1935);
x_1936 = l_Lean_Expr_getAppFnArgs(x_1935);
x_1937 = lean_ctor_get(x_1936, 0);
lean_inc(x_1937);
if (lean_obj_tag(x_1937) == 1)
{
lean_object* x_1938; 
x_1938 = lean_ctor_get(x_1937, 0);
lean_inc(x_1938);
if (lean_obj_tag(x_1938) == 1)
{
lean_object* x_1939; 
x_1939 = lean_ctor_get(x_1938, 0);
lean_inc(x_1939);
if (lean_obj_tag(x_1939) == 0)
{
lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; uint8_t x_1945; 
x_1940 = lean_ctor_get(x_1936, 1);
lean_inc(x_1940);
if (lean_is_exclusive(x_1936)) {
 lean_ctor_release(x_1936, 0);
 lean_ctor_release(x_1936, 1);
 x_1941 = x_1936;
} else {
 lean_dec_ref(x_1936);
 x_1941 = lean_box(0);
}
x_1942 = lean_ctor_get(x_1937, 1);
lean_inc(x_1942);
lean_dec(x_1937);
x_1943 = lean_ctor_get(x_1938, 1);
lean_inc(x_1943);
lean_dec(x_1938);
x_1944 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_1945 = lean_string_dec_eq(x_1943, x_1944);
if (x_1945 == 0)
{
uint8_t x_1946; 
x_1946 = lean_string_dec_eq(x_1943, x_1869);
lean_dec(x_1943);
if (x_1946 == 0)
{
lean_object* x_1947; lean_object* x_1948; 
lean_dec(x_1942);
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1947 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_1948 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1948 = x_1941;
}
lean_ctor_set(x_1948, 0, x_1947);
lean_ctor_set(x_1948, 1, x_11);
return x_1948;
}
else
{
lean_object* x_1949; uint8_t x_1950; 
x_1949 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_1950 = lean_string_dec_eq(x_1942, x_1949);
lean_dec(x_1942);
if (x_1950 == 0)
{
lean_object* x_1951; lean_object* x_1952; 
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1951 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_1952 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1952 = x_1941;
}
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set(x_1952, 1, x_11);
return x_1952;
}
else
{
lean_object* x_1953; lean_object* x_1954; uint8_t x_1955; 
x_1953 = lean_array_get_size(x_1940);
x_1954 = lean_unsigned_to_nat(3u);
x_1955 = lean_nat_dec_eq(x_1953, x_1954);
lean_dec(x_1953);
if (x_1955 == 0)
{
lean_object* x_1956; lean_object* x_1957; 
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1956 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_1957 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1957 = x_1941;
}
lean_ctor_set(x_1957, 0, x_1956);
lean_ctor_set(x_1957, 1, x_11);
return x_1957;
}
else
{
lean_object* x_1958; lean_object* x_1959; 
x_1958 = lean_unsigned_to_nat(0u);
x_1959 = lean_array_fget(x_1940, x_1958);
if (lean_obj_tag(x_1959) == 4)
{
lean_object* x_1960; 
x_1960 = lean_ctor_get(x_1959, 0);
lean_inc(x_1960);
if (lean_obj_tag(x_1960) == 1)
{
lean_object* x_1961; 
x_1961 = lean_ctor_get(x_1960, 0);
lean_inc(x_1961);
if (lean_obj_tag(x_1961) == 0)
{
lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; uint8_t x_1965; 
x_1962 = lean_ctor_get(x_1959, 1);
lean_inc(x_1962);
lean_dec(x_1959);
x_1963 = lean_ctor_get(x_1960, 1);
lean_inc(x_1963);
lean_dec(x_1960);
x_1964 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_1965 = lean_string_dec_eq(x_1963, x_1964);
lean_dec(x_1963);
if (x_1965 == 0)
{
lean_object* x_1966; lean_object* x_1967; 
lean_dec(x_1962);
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1966 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_1967 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1967 = x_1941;
}
lean_ctor_set(x_1967, 0, x_1966);
lean_ctor_set(x_1967, 1, x_11);
return x_1967;
}
else
{
lean_dec(x_1941);
if (lean_obj_tag(x_1962) == 0)
{
lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; 
x_1968 = lean_unsigned_to_nat(2u);
x_1969 = lean_array_fget(x_1940, x_1968);
lean_dec(x_1940);
lean_inc(x_1969);
x_1970 = l_Lean_Expr_getAppFnArgs(x_1969);
x_1971 = lean_ctor_get(x_1970, 0);
lean_inc(x_1971);
if (lean_obj_tag(x_1971) == 1)
{
lean_object* x_1972; 
x_1972 = lean_ctor_get(x_1971, 0);
lean_inc(x_1972);
if (lean_obj_tag(x_1972) == 1)
{
lean_object* x_1973; 
x_1973 = lean_ctor_get(x_1972, 0);
lean_inc(x_1973);
if (lean_obj_tag(x_1973) == 0)
{
lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; uint8_t x_1978; 
x_1974 = lean_ctor_get(x_1970, 1);
lean_inc(x_1974);
if (lean_is_exclusive(x_1970)) {
 lean_ctor_release(x_1970, 0);
 lean_ctor_release(x_1970, 1);
 x_1975 = x_1970;
} else {
 lean_dec_ref(x_1970);
 x_1975 = lean_box(0);
}
x_1976 = lean_ctor_get(x_1971, 1);
lean_inc(x_1976);
lean_dec(x_1971);
x_1977 = lean_ctor_get(x_1972, 1);
lean_inc(x_1977);
lean_dec(x_1972);
x_1978 = lean_string_dec_eq(x_1977, x_1944);
lean_dec(x_1977);
if (x_1978 == 0)
{
lean_object* x_1979; lean_object* x_1980; 
lean_dec(x_1976);
lean_dec(x_1975);
lean_dec(x_1974);
lean_dec(x_1969);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_1979 = l_Lean_Expr_getAppFnArgs(x_1933);
x_1980 = lean_ctor_get(x_1979, 0);
lean_inc(x_1980);
if (lean_obj_tag(x_1980) == 1)
{
lean_object* x_1981; 
x_1981 = lean_ctor_get(x_1980, 0);
lean_inc(x_1981);
if (lean_obj_tag(x_1981) == 1)
{
lean_object* x_1982; 
x_1982 = lean_ctor_get(x_1981, 0);
lean_inc(x_1982);
if (lean_obj_tag(x_1982) == 0)
{
lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; uint8_t x_1987; 
x_1983 = lean_ctor_get(x_1979, 1);
lean_inc(x_1983);
if (lean_is_exclusive(x_1979)) {
 lean_ctor_release(x_1979, 0);
 lean_ctor_release(x_1979, 1);
 x_1984 = x_1979;
} else {
 lean_dec_ref(x_1979);
 x_1984 = lean_box(0);
}
x_1985 = lean_ctor_get(x_1980, 1);
lean_inc(x_1985);
lean_dec(x_1980);
x_1986 = lean_ctor_get(x_1981, 1);
lean_inc(x_1986);
lean_dec(x_1981);
x_1987 = lean_string_dec_eq(x_1986, x_1869);
lean_dec(x_1986);
if (x_1987 == 0)
{
lean_object* x_1988; lean_object* x_1989; 
lean_dec(x_1985);
lean_dec(x_1983);
lean_dec(x_1935);
x_1988 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1984)) {
 x_1989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1989 = x_1984;
}
lean_ctor_set(x_1989, 0, x_1988);
lean_ctor_set(x_1989, 1, x_11);
return x_1989;
}
else
{
uint8_t x_1990; 
x_1990 = lean_string_dec_eq(x_1985, x_1949);
lean_dec(x_1985);
if (x_1990 == 0)
{
lean_object* x_1991; lean_object* x_1992; 
lean_dec(x_1983);
lean_dec(x_1935);
x_1991 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1984)) {
 x_1992 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1992 = x_1984;
}
lean_ctor_set(x_1992, 0, x_1991);
lean_ctor_set(x_1992, 1, x_11);
return x_1992;
}
else
{
lean_object* x_1993; uint8_t x_1994; 
x_1993 = lean_array_get_size(x_1983);
x_1994 = lean_nat_dec_eq(x_1993, x_1954);
lean_dec(x_1993);
if (x_1994 == 0)
{
lean_object* x_1995; lean_object* x_1996; 
lean_dec(x_1983);
lean_dec(x_1935);
x_1995 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1984)) {
 x_1996 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1996 = x_1984;
}
lean_ctor_set(x_1996, 0, x_1995);
lean_ctor_set(x_1996, 1, x_11);
return x_1996;
}
else
{
lean_object* x_1997; 
x_1997 = lean_array_fget(x_1983, x_1958);
if (lean_obj_tag(x_1997) == 4)
{
lean_object* x_1998; 
x_1998 = lean_ctor_get(x_1997, 0);
lean_inc(x_1998);
if (lean_obj_tag(x_1998) == 1)
{
lean_object* x_1999; 
x_1999 = lean_ctor_get(x_1998, 0);
lean_inc(x_1999);
if (lean_obj_tag(x_1999) == 0)
{
lean_object* x_2000; lean_object* x_2001; uint8_t x_2002; 
x_2000 = lean_ctor_get(x_1997, 1);
lean_inc(x_2000);
lean_dec(x_1997);
x_2001 = lean_ctor_get(x_1998, 1);
lean_inc(x_2001);
lean_dec(x_1998);
x_2002 = lean_string_dec_eq(x_2001, x_1964);
lean_dec(x_2001);
if (x_2002 == 0)
{
lean_object* x_2003; lean_object* x_2004; 
lean_dec(x_2000);
lean_dec(x_1983);
lean_dec(x_1935);
x_2003 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1984)) {
 x_2004 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2004 = x_1984;
}
lean_ctor_set(x_2004, 0, x_2003);
lean_ctor_set(x_2004, 1, x_11);
return x_2004;
}
else
{
if (lean_obj_tag(x_2000) == 0)
{
lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; 
x_2005 = lean_array_fget(x_1983, x_1968);
lean_dec(x_1983);
x_2006 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2007 = l_Lean_mkAppB(x_2006, x_2005, x_1935);
x_2008 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2009 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2008, x_2007);
if (lean_is_scalar(x_1984)) {
 x_2010 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2010 = x_1984;
}
lean_ctor_set(x_2010, 0, x_2009);
lean_ctor_set(x_2010, 1, x_11);
return x_2010;
}
else
{
lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; 
lean_dec(x_1984);
lean_dec(x_1983);
lean_dec(x_1935);
if (lean_is_exclusive(x_2000)) {
 lean_ctor_release(x_2000, 0);
 lean_ctor_release(x_2000, 1);
 x_2011 = x_2000;
} else {
 lean_dec_ref(x_2000);
 x_2011 = lean_box(0);
}
x_2012 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2011)) {
 x_2013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2013 = x_2011;
 lean_ctor_set_tag(x_2013, 0);
}
lean_ctor_set(x_2013, 0, x_2012);
lean_ctor_set(x_2013, 1, x_11);
return x_2013;
}
}
}
else
{
lean_object* x_2014; lean_object* x_2015; 
lean_dec(x_1999);
lean_dec(x_1998);
lean_dec(x_1997);
lean_dec(x_1983);
lean_dec(x_1935);
x_2014 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1984)) {
 x_2015 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2015 = x_1984;
}
lean_ctor_set(x_2015, 0, x_2014);
lean_ctor_set(x_2015, 1, x_11);
return x_2015;
}
}
else
{
lean_object* x_2016; lean_object* x_2017; 
lean_dec(x_1998);
lean_dec(x_1997);
lean_dec(x_1983);
lean_dec(x_1935);
x_2016 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1984)) {
 x_2017 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2017 = x_1984;
}
lean_ctor_set(x_2017, 0, x_2016);
lean_ctor_set(x_2017, 1, x_11);
return x_2017;
}
}
else
{
lean_object* x_2018; lean_object* x_2019; 
lean_dec(x_1997);
lean_dec(x_1983);
lean_dec(x_1935);
x_2018 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1984)) {
 x_2019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2019 = x_1984;
}
lean_ctor_set(x_2019, 0, x_2018);
lean_ctor_set(x_2019, 1, x_11);
return x_2019;
}
}
}
}
}
else
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; 
lean_dec(x_1982);
lean_dec(x_1981);
lean_dec(x_1980);
lean_dec(x_1935);
if (lean_is_exclusive(x_1979)) {
 lean_ctor_release(x_1979, 0);
 lean_ctor_release(x_1979, 1);
 x_2020 = x_1979;
} else {
 lean_dec_ref(x_1979);
 x_2020 = lean_box(0);
}
x_2021 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2020)) {
 x_2022 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2022 = x_2020;
}
lean_ctor_set(x_2022, 0, x_2021);
lean_ctor_set(x_2022, 1, x_11);
return x_2022;
}
}
else
{
lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; 
lean_dec(x_1981);
lean_dec(x_1980);
lean_dec(x_1935);
if (lean_is_exclusive(x_1979)) {
 lean_ctor_release(x_1979, 0);
 lean_ctor_release(x_1979, 1);
 x_2023 = x_1979;
} else {
 lean_dec_ref(x_1979);
 x_2023 = lean_box(0);
}
x_2024 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2023)) {
 x_2025 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2025 = x_2023;
}
lean_ctor_set(x_2025, 0, x_2024);
lean_ctor_set(x_2025, 1, x_11);
return x_2025;
}
}
else
{
lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; 
lean_dec(x_1980);
lean_dec(x_1935);
if (lean_is_exclusive(x_1979)) {
 lean_ctor_release(x_1979, 0);
 lean_ctor_release(x_1979, 1);
 x_2026 = x_1979;
} else {
 lean_dec_ref(x_1979);
 x_2026 = lean_box(0);
}
x_2027 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2026)) {
 x_2028 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2028 = x_2026;
}
lean_ctor_set(x_2028, 0, x_2027);
lean_ctor_set(x_2028, 1, x_11);
return x_2028;
}
}
else
{
lean_object* x_2029; uint8_t x_2030; 
x_2029 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_2030 = lean_string_dec_eq(x_1976, x_2029);
lean_dec(x_1976);
if (x_2030 == 0)
{
lean_object* x_2031; lean_object* x_2032; 
lean_dec(x_1975);
lean_dec(x_1974);
lean_dec(x_1969);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2031 = l_Lean_Expr_getAppFnArgs(x_1933);
x_2032 = lean_ctor_get(x_2031, 0);
lean_inc(x_2032);
if (lean_obj_tag(x_2032) == 1)
{
lean_object* x_2033; 
x_2033 = lean_ctor_get(x_2032, 0);
lean_inc(x_2033);
if (lean_obj_tag(x_2033) == 1)
{
lean_object* x_2034; 
x_2034 = lean_ctor_get(x_2033, 0);
lean_inc(x_2034);
if (lean_obj_tag(x_2034) == 0)
{
lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; uint8_t x_2039; 
x_2035 = lean_ctor_get(x_2031, 1);
lean_inc(x_2035);
if (lean_is_exclusive(x_2031)) {
 lean_ctor_release(x_2031, 0);
 lean_ctor_release(x_2031, 1);
 x_2036 = x_2031;
} else {
 lean_dec_ref(x_2031);
 x_2036 = lean_box(0);
}
x_2037 = lean_ctor_get(x_2032, 1);
lean_inc(x_2037);
lean_dec(x_2032);
x_2038 = lean_ctor_get(x_2033, 1);
lean_inc(x_2038);
lean_dec(x_2033);
x_2039 = lean_string_dec_eq(x_2038, x_1869);
lean_dec(x_2038);
if (x_2039 == 0)
{
lean_object* x_2040; lean_object* x_2041; 
lean_dec(x_2037);
lean_dec(x_2035);
lean_dec(x_1935);
x_2040 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2036)) {
 x_2041 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2041 = x_2036;
}
lean_ctor_set(x_2041, 0, x_2040);
lean_ctor_set(x_2041, 1, x_11);
return x_2041;
}
else
{
uint8_t x_2042; 
x_2042 = lean_string_dec_eq(x_2037, x_1949);
lean_dec(x_2037);
if (x_2042 == 0)
{
lean_object* x_2043; lean_object* x_2044; 
lean_dec(x_2035);
lean_dec(x_1935);
x_2043 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2036)) {
 x_2044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2044 = x_2036;
}
lean_ctor_set(x_2044, 0, x_2043);
lean_ctor_set(x_2044, 1, x_11);
return x_2044;
}
else
{
lean_object* x_2045; uint8_t x_2046; 
x_2045 = lean_array_get_size(x_2035);
x_2046 = lean_nat_dec_eq(x_2045, x_1954);
lean_dec(x_2045);
if (x_2046 == 0)
{
lean_object* x_2047; lean_object* x_2048; 
lean_dec(x_2035);
lean_dec(x_1935);
x_2047 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2036)) {
 x_2048 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2048 = x_2036;
}
lean_ctor_set(x_2048, 0, x_2047);
lean_ctor_set(x_2048, 1, x_11);
return x_2048;
}
else
{
lean_object* x_2049; 
x_2049 = lean_array_fget(x_2035, x_1958);
if (lean_obj_tag(x_2049) == 4)
{
lean_object* x_2050; 
x_2050 = lean_ctor_get(x_2049, 0);
lean_inc(x_2050);
if (lean_obj_tag(x_2050) == 1)
{
lean_object* x_2051; 
x_2051 = lean_ctor_get(x_2050, 0);
lean_inc(x_2051);
if (lean_obj_tag(x_2051) == 0)
{
lean_object* x_2052; lean_object* x_2053; uint8_t x_2054; 
x_2052 = lean_ctor_get(x_2049, 1);
lean_inc(x_2052);
lean_dec(x_2049);
x_2053 = lean_ctor_get(x_2050, 1);
lean_inc(x_2053);
lean_dec(x_2050);
x_2054 = lean_string_dec_eq(x_2053, x_1964);
lean_dec(x_2053);
if (x_2054 == 0)
{
lean_object* x_2055; lean_object* x_2056; 
lean_dec(x_2052);
lean_dec(x_2035);
lean_dec(x_1935);
x_2055 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2036)) {
 x_2056 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2056 = x_2036;
}
lean_ctor_set(x_2056, 0, x_2055);
lean_ctor_set(x_2056, 1, x_11);
return x_2056;
}
else
{
if (lean_obj_tag(x_2052) == 0)
{
lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; 
x_2057 = lean_array_fget(x_2035, x_1968);
lean_dec(x_2035);
x_2058 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2059 = l_Lean_mkAppB(x_2058, x_2057, x_1935);
x_2060 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2061 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2060, x_2059);
if (lean_is_scalar(x_2036)) {
 x_2062 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2062 = x_2036;
}
lean_ctor_set(x_2062, 0, x_2061);
lean_ctor_set(x_2062, 1, x_11);
return x_2062;
}
else
{
lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; 
lean_dec(x_2036);
lean_dec(x_2035);
lean_dec(x_1935);
if (lean_is_exclusive(x_2052)) {
 lean_ctor_release(x_2052, 0);
 lean_ctor_release(x_2052, 1);
 x_2063 = x_2052;
} else {
 lean_dec_ref(x_2052);
 x_2063 = lean_box(0);
}
x_2064 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2063)) {
 x_2065 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2065 = x_2063;
 lean_ctor_set_tag(x_2065, 0);
}
lean_ctor_set(x_2065, 0, x_2064);
lean_ctor_set(x_2065, 1, x_11);
return x_2065;
}
}
}
else
{
lean_object* x_2066; lean_object* x_2067; 
lean_dec(x_2051);
lean_dec(x_2050);
lean_dec(x_2049);
lean_dec(x_2035);
lean_dec(x_1935);
x_2066 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2036)) {
 x_2067 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2067 = x_2036;
}
lean_ctor_set(x_2067, 0, x_2066);
lean_ctor_set(x_2067, 1, x_11);
return x_2067;
}
}
else
{
lean_object* x_2068; lean_object* x_2069; 
lean_dec(x_2050);
lean_dec(x_2049);
lean_dec(x_2035);
lean_dec(x_1935);
x_2068 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2036)) {
 x_2069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2069 = x_2036;
}
lean_ctor_set(x_2069, 0, x_2068);
lean_ctor_set(x_2069, 1, x_11);
return x_2069;
}
}
else
{
lean_object* x_2070; lean_object* x_2071; 
lean_dec(x_2049);
lean_dec(x_2035);
lean_dec(x_1935);
x_2070 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2036)) {
 x_2071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2071 = x_2036;
}
lean_ctor_set(x_2071, 0, x_2070);
lean_ctor_set(x_2071, 1, x_11);
return x_2071;
}
}
}
}
}
else
{
lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; 
lean_dec(x_2034);
lean_dec(x_2033);
lean_dec(x_2032);
lean_dec(x_1935);
if (lean_is_exclusive(x_2031)) {
 lean_ctor_release(x_2031, 0);
 lean_ctor_release(x_2031, 1);
 x_2072 = x_2031;
} else {
 lean_dec_ref(x_2031);
 x_2072 = lean_box(0);
}
x_2073 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2072)) {
 x_2074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2074 = x_2072;
}
lean_ctor_set(x_2074, 0, x_2073);
lean_ctor_set(x_2074, 1, x_11);
return x_2074;
}
}
else
{
lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; 
lean_dec(x_2033);
lean_dec(x_2032);
lean_dec(x_1935);
if (lean_is_exclusive(x_2031)) {
 lean_ctor_release(x_2031, 0);
 lean_ctor_release(x_2031, 1);
 x_2075 = x_2031;
} else {
 lean_dec_ref(x_2031);
 x_2075 = lean_box(0);
}
x_2076 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2075)) {
 x_2077 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2077 = x_2075;
}
lean_ctor_set(x_2077, 0, x_2076);
lean_ctor_set(x_2077, 1, x_11);
return x_2077;
}
}
else
{
lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; 
lean_dec(x_2032);
lean_dec(x_1935);
if (lean_is_exclusive(x_2031)) {
 lean_ctor_release(x_2031, 0);
 lean_ctor_release(x_2031, 1);
 x_2078 = x_2031;
} else {
 lean_dec_ref(x_2031);
 x_2078 = lean_box(0);
}
x_2079 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2078)) {
 x_2080 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2080 = x_2078;
}
lean_ctor_set(x_2080, 0, x_2079);
lean_ctor_set(x_2080, 1, x_11);
return x_2080;
}
}
else
{
lean_object* x_2081; uint8_t x_2082; 
x_2081 = lean_array_get_size(x_1974);
x_2082 = lean_nat_dec_eq(x_2081, x_1928);
lean_dec(x_2081);
if (x_2082 == 0)
{
lean_object* x_2083; lean_object* x_2084; 
lean_dec(x_1975);
lean_dec(x_1974);
lean_dec(x_1969);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2083 = l_Lean_Expr_getAppFnArgs(x_1933);
x_2084 = lean_ctor_get(x_2083, 0);
lean_inc(x_2084);
if (lean_obj_tag(x_2084) == 1)
{
lean_object* x_2085; 
x_2085 = lean_ctor_get(x_2084, 0);
lean_inc(x_2085);
if (lean_obj_tag(x_2085) == 1)
{
lean_object* x_2086; 
x_2086 = lean_ctor_get(x_2085, 0);
lean_inc(x_2086);
if (lean_obj_tag(x_2086) == 0)
{
lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; uint8_t x_2091; 
x_2087 = lean_ctor_get(x_2083, 1);
lean_inc(x_2087);
if (lean_is_exclusive(x_2083)) {
 lean_ctor_release(x_2083, 0);
 lean_ctor_release(x_2083, 1);
 x_2088 = x_2083;
} else {
 lean_dec_ref(x_2083);
 x_2088 = lean_box(0);
}
x_2089 = lean_ctor_get(x_2084, 1);
lean_inc(x_2089);
lean_dec(x_2084);
x_2090 = lean_ctor_get(x_2085, 1);
lean_inc(x_2090);
lean_dec(x_2085);
x_2091 = lean_string_dec_eq(x_2090, x_1869);
lean_dec(x_2090);
if (x_2091 == 0)
{
lean_object* x_2092; lean_object* x_2093; 
lean_dec(x_2089);
lean_dec(x_2087);
lean_dec(x_1935);
x_2092 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2088)) {
 x_2093 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2093 = x_2088;
}
lean_ctor_set(x_2093, 0, x_2092);
lean_ctor_set(x_2093, 1, x_11);
return x_2093;
}
else
{
uint8_t x_2094; 
x_2094 = lean_string_dec_eq(x_2089, x_1949);
lean_dec(x_2089);
if (x_2094 == 0)
{
lean_object* x_2095; lean_object* x_2096; 
lean_dec(x_2087);
lean_dec(x_1935);
x_2095 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2088)) {
 x_2096 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2096 = x_2088;
}
lean_ctor_set(x_2096, 0, x_2095);
lean_ctor_set(x_2096, 1, x_11);
return x_2096;
}
else
{
lean_object* x_2097; uint8_t x_2098; 
x_2097 = lean_array_get_size(x_2087);
x_2098 = lean_nat_dec_eq(x_2097, x_1954);
lean_dec(x_2097);
if (x_2098 == 0)
{
lean_object* x_2099; lean_object* x_2100; 
lean_dec(x_2087);
lean_dec(x_1935);
x_2099 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2088)) {
 x_2100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2100 = x_2088;
}
lean_ctor_set(x_2100, 0, x_2099);
lean_ctor_set(x_2100, 1, x_11);
return x_2100;
}
else
{
lean_object* x_2101; 
x_2101 = lean_array_fget(x_2087, x_1958);
if (lean_obj_tag(x_2101) == 4)
{
lean_object* x_2102; 
x_2102 = lean_ctor_get(x_2101, 0);
lean_inc(x_2102);
if (lean_obj_tag(x_2102) == 1)
{
lean_object* x_2103; 
x_2103 = lean_ctor_get(x_2102, 0);
lean_inc(x_2103);
if (lean_obj_tag(x_2103) == 0)
{
lean_object* x_2104; lean_object* x_2105; uint8_t x_2106; 
x_2104 = lean_ctor_get(x_2101, 1);
lean_inc(x_2104);
lean_dec(x_2101);
x_2105 = lean_ctor_get(x_2102, 1);
lean_inc(x_2105);
lean_dec(x_2102);
x_2106 = lean_string_dec_eq(x_2105, x_1964);
lean_dec(x_2105);
if (x_2106 == 0)
{
lean_object* x_2107; lean_object* x_2108; 
lean_dec(x_2104);
lean_dec(x_2087);
lean_dec(x_1935);
x_2107 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2088)) {
 x_2108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2108 = x_2088;
}
lean_ctor_set(x_2108, 0, x_2107);
lean_ctor_set(x_2108, 1, x_11);
return x_2108;
}
else
{
if (lean_obj_tag(x_2104) == 0)
{
lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; 
x_2109 = lean_array_fget(x_2087, x_1968);
lean_dec(x_2087);
x_2110 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2111 = l_Lean_mkAppB(x_2110, x_2109, x_1935);
x_2112 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2113 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2112, x_2111);
if (lean_is_scalar(x_2088)) {
 x_2114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2114 = x_2088;
}
lean_ctor_set(x_2114, 0, x_2113);
lean_ctor_set(x_2114, 1, x_11);
return x_2114;
}
else
{
lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; 
lean_dec(x_2088);
lean_dec(x_2087);
lean_dec(x_1935);
if (lean_is_exclusive(x_2104)) {
 lean_ctor_release(x_2104, 0);
 lean_ctor_release(x_2104, 1);
 x_2115 = x_2104;
} else {
 lean_dec_ref(x_2104);
 x_2115 = lean_box(0);
}
x_2116 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2115)) {
 x_2117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2117 = x_2115;
 lean_ctor_set_tag(x_2117, 0);
}
lean_ctor_set(x_2117, 0, x_2116);
lean_ctor_set(x_2117, 1, x_11);
return x_2117;
}
}
}
else
{
lean_object* x_2118; lean_object* x_2119; 
lean_dec(x_2103);
lean_dec(x_2102);
lean_dec(x_2101);
lean_dec(x_2087);
lean_dec(x_1935);
x_2118 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2088)) {
 x_2119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2119 = x_2088;
}
lean_ctor_set(x_2119, 0, x_2118);
lean_ctor_set(x_2119, 1, x_11);
return x_2119;
}
}
else
{
lean_object* x_2120; lean_object* x_2121; 
lean_dec(x_2102);
lean_dec(x_2101);
lean_dec(x_2087);
lean_dec(x_1935);
x_2120 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2088)) {
 x_2121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2121 = x_2088;
}
lean_ctor_set(x_2121, 0, x_2120);
lean_ctor_set(x_2121, 1, x_11);
return x_2121;
}
}
else
{
lean_object* x_2122; lean_object* x_2123; 
lean_dec(x_2101);
lean_dec(x_2087);
lean_dec(x_1935);
x_2122 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2088)) {
 x_2123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2123 = x_2088;
}
lean_ctor_set(x_2123, 0, x_2122);
lean_ctor_set(x_2123, 1, x_11);
return x_2123;
}
}
}
}
}
else
{
lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; 
lean_dec(x_2086);
lean_dec(x_2085);
lean_dec(x_2084);
lean_dec(x_1935);
if (lean_is_exclusive(x_2083)) {
 lean_ctor_release(x_2083, 0);
 lean_ctor_release(x_2083, 1);
 x_2124 = x_2083;
} else {
 lean_dec_ref(x_2083);
 x_2124 = lean_box(0);
}
x_2125 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2124)) {
 x_2126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2126 = x_2124;
}
lean_ctor_set(x_2126, 0, x_2125);
lean_ctor_set(x_2126, 1, x_11);
return x_2126;
}
}
else
{
lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
lean_dec(x_2085);
lean_dec(x_2084);
lean_dec(x_1935);
if (lean_is_exclusive(x_2083)) {
 lean_ctor_release(x_2083, 0);
 lean_ctor_release(x_2083, 1);
 x_2127 = x_2083;
} else {
 lean_dec_ref(x_2083);
 x_2127 = lean_box(0);
}
x_2128 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2127)) {
 x_2129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2129 = x_2127;
}
lean_ctor_set(x_2129, 0, x_2128);
lean_ctor_set(x_2129, 1, x_11);
return x_2129;
}
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; 
lean_dec(x_2084);
lean_dec(x_1935);
if (lean_is_exclusive(x_2083)) {
 lean_ctor_release(x_2083, 0);
 lean_ctor_release(x_2083, 1);
 x_2130 = x_2083;
} else {
 lean_dec_ref(x_2083);
 x_2130 = lean_box(0);
}
x_2131 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2130)) {
 x_2132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2132 = x_2130;
}
lean_ctor_set(x_2132, 0, x_2131);
lean_ctor_set(x_2132, 1, x_11);
return x_2132;
}
}
else
{
lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; 
x_2133 = lean_array_fget(x_1974, x_1932);
x_2134 = lean_array_fget(x_1974, x_1934);
lean_dec(x_1974);
lean_inc(x_2133);
x_2135 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_2133);
if (lean_obj_tag(x_2135) == 0)
{
lean_object* x_2136; lean_object* x_2137; 
lean_dec(x_2134);
lean_dec(x_2133);
lean_dec(x_1969);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2136 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1975)) {
 x_2137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2137 = x_1975;
}
lean_ctor_set(x_2137, 0, x_2136);
lean_ctor_set(x_2137, 1, x_11);
return x_2137;
}
else
{
lean_object* x_2138; uint8_t x_2139; 
x_2138 = lean_ctor_get(x_2135, 0);
lean_inc(x_2138);
lean_dec(x_2135);
x_2139 = lean_nat_dec_eq(x_2138, x_1958);
lean_dec(x_2138);
if (x_2139 == 0)
{
lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; 
lean_dec(x_1975);
x_2140 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_2141 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_2142 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
x_2143 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
lean_inc(x_2133);
x_2144 = l_Lean_mkApp4(x_2140, x_2141, x_2142, x_2143, x_2133);
x_2145 = l_Lean_Meta_mkDecideProof(x_2144, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_2145) == 0)
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; uint8_t x_2155; 
x_2146 = lean_ctor_get(x_2145, 0);
lean_inc(x_2146);
x_2147 = lean_ctor_get(x_2145, 1);
lean_inc(x_2147);
if (lean_is_exclusive(x_2145)) {
 lean_ctor_release(x_2145, 0);
 lean_ctor_release(x_2145, 1);
 x_2148 = x_2145;
} else {
 lean_dec_ref(x_2145);
 x_2148 = lean_box(0);
}
x_2149 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_2150 = l_Lean_mkApp3(x_2149, x_2133, x_2134, x_2146);
x_2151 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_2152 = l_Lean_mkAppB(x_2151, x_1969, x_2150);
x_2153 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_inc(x_2152);
lean_inc(x_1935);
lean_inc(x_1933);
x_2154 = l_Lean_mkApp3(x_2153, x_1933, x_1935, x_2152);
x_2155 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_2155 == 0)
{
lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; 
x_2156 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_2157 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
lean_inc(x_1935);
x_2158 = l_Lean_mkApp3(x_2156, x_1935, x_2157, x_2152);
x_2159 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_2160 = l_Lean_mkApp3(x_2159, x_1933, x_1935, x_2158);
x_2161 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2162 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2161, x_2160);
x_2163 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2162, x_2154);
if (lean_is_scalar(x_2148)) {
 x_2164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2164 = x_2148;
}
lean_ctor_set(x_2164, 0, x_2163);
lean_ctor_set(x_2164, 1, x_2147);
return x_2164;
}
else
{
lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; 
x_2165 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_2166 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_1935);
x_2167 = l_Lean_mkApp3(x_2165, x_1935, x_2166, x_2152);
x_2168 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_2169 = l_Lean_mkApp3(x_2168, x_1933, x_1935, x_2167);
x_2170 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2171 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2170, x_2169);
x_2172 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2171, x_2154);
if (lean_is_scalar(x_2148)) {
 x_2173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2173 = x_2148;
}
lean_ctor_set(x_2173, 0, x_2172);
lean_ctor_set(x_2173, 1, x_2147);
return x_2173;
}
}
else
{
lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; 
lean_dec(x_2134);
lean_dec(x_2133);
lean_dec(x_1969);
lean_dec(x_1935);
lean_dec(x_1933);
x_2174 = lean_ctor_get(x_2145, 0);
lean_inc(x_2174);
x_2175 = lean_ctor_get(x_2145, 1);
lean_inc(x_2175);
if (lean_is_exclusive(x_2145)) {
 lean_ctor_release(x_2145, 0);
 lean_ctor_release(x_2145, 1);
 x_2176 = x_2145;
} else {
 lean_dec_ref(x_2145);
 x_2176 = lean_box(0);
}
if (lean_is_scalar(x_2176)) {
 x_2177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2177 = x_2176;
}
lean_ctor_set(x_2177, 0, x_2174);
lean_ctor_set(x_2177, 1, x_2175);
return x_2177;
}
}
else
{
lean_object* x_2178; lean_object* x_2179; 
lean_dec(x_2134);
lean_dec(x_2133);
lean_dec(x_1969);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2178 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1975)) {
 x_2179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2179 = x_1975;
}
lean_ctor_set(x_2179, 0, x_2178);
lean_ctor_set(x_2179, 1, x_11);
return x_2179;
}
}
}
}
}
}
else
{
lean_object* x_2180; lean_object* x_2181; 
lean_dec(x_1973);
lean_dec(x_1972);
lean_dec(x_1971);
lean_dec(x_1970);
lean_dec(x_1969);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2180 = l_Lean_Expr_getAppFnArgs(x_1933);
x_2181 = lean_ctor_get(x_2180, 0);
lean_inc(x_2181);
if (lean_obj_tag(x_2181) == 1)
{
lean_object* x_2182; 
x_2182 = lean_ctor_get(x_2181, 0);
lean_inc(x_2182);
if (lean_obj_tag(x_2182) == 1)
{
lean_object* x_2183; 
x_2183 = lean_ctor_get(x_2182, 0);
lean_inc(x_2183);
if (lean_obj_tag(x_2183) == 0)
{
lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; uint8_t x_2188; 
x_2184 = lean_ctor_get(x_2180, 1);
lean_inc(x_2184);
if (lean_is_exclusive(x_2180)) {
 lean_ctor_release(x_2180, 0);
 lean_ctor_release(x_2180, 1);
 x_2185 = x_2180;
} else {
 lean_dec_ref(x_2180);
 x_2185 = lean_box(0);
}
x_2186 = lean_ctor_get(x_2181, 1);
lean_inc(x_2186);
lean_dec(x_2181);
x_2187 = lean_ctor_get(x_2182, 1);
lean_inc(x_2187);
lean_dec(x_2182);
x_2188 = lean_string_dec_eq(x_2187, x_1869);
lean_dec(x_2187);
if (x_2188 == 0)
{
lean_object* x_2189; lean_object* x_2190; 
lean_dec(x_2186);
lean_dec(x_2184);
lean_dec(x_1935);
x_2189 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2185)) {
 x_2190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2190 = x_2185;
}
lean_ctor_set(x_2190, 0, x_2189);
lean_ctor_set(x_2190, 1, x_11);
return x_2190;
}
else
{
uint8_t x_2191; 
x_2191 = lean_string_dec_eq(x_2186, x_1949);
lean_dec(x_2186);
if (x_2191 == 0)
{
lean_object* x_2192; lean_object* x_2193; 
lean_dec(x_2184);
lean_dec(x_1935);
x_2192 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2185)) {
 x_2193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2193 = x_2185;
}
lean_ctor_set(x_2193, 0, x_2192);
lean_ctor_set(x_2193, 1, x_11);
return x_2193;
}
else
{
lean_object* x_2194; uint8_t x_2195; 
x_2194 = lean_array_get_size(x_2184);
x_2195 = lean_nat_dec_eq(x_2194, x_1954);
lean_dec(x_2194);
if (x_2195 == 0)
{
lean_object* x_2196; lean_object* x_2197; 
lean_dec(x_2184);
lean_dec(x_1935);
x_2196 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2185)) {
 x_2197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2197 = x_2185;
}
lean_ctor_set(x_2197, 0, x_2196);
lean_ctor_set(x_2197, 1, x_11);
return x_2197;
}
else
{
lean_object* x_2198; 
x_2198 = lean_array_fget(x_2184, x_1958);
if (lean_obj_tag(x_2198) == 4)
{
lean_object* x_2199; 
x_2199 = lean_ctor_get(x_2198, 0);
lean_inc(x_2199);
if (lean_obj_tag(x_2199) == 1)
{
lean_object* x_2200; 
x_2200 = lean_ctor_get(x_2199, 0);
lean_inc(x_2200);
if (lean_obj_tag(x_2200) == 0)
{
lean_object* x_2201; lean_object* x_2202; uint8_t x_2203; 
x_2201 = lean_ctor_get(x_2198, 1);
lean_inc(x_2201);
lean_dec(x_2198);
x_2202 = lean_ctor_get(x_2199, 1);
lean_inc(x_2202);
lean_dec(x_2199);
x_2203 = lean_string_dec_eq(x_2202, x_1964);
lean_dec(x_2202);
if (x_2203 == 0)
{
lean_object* x_2204; lean_object* x_2205; 
lean_dec(x_2201);
lean_dec(x_2184);
lean_dec(x_1935);
x_2204 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2185)) {
 x_2205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2205 = x_2185;
}
lean_ctor_set(x_2205, 0, x_2204);
lean_ctor_set(x_2205, 1, x_11);
return x_2205;
}
else
{
if (lean_obj_tag(x_2201) == 0)
{
lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; 
x_2206 = lean_array_fget(x_2184, x_1968);
lean_dec(x_2184);
x_2207 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2208 = l_Lean_mkAppB(x_2207, x_2206, x_1935);
x_2209 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2210 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2209, x_2208);
if (lean_is_scalar(x_2185)) {
 x_2211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2211 = x_2185;
}
lean_ctor_set(x_2211, 0, x_2210);
lean_ctor_set(x_2211, 1, x_11);
return x_2211;
}
else
{
lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; 
lean_dec(x_2185);
lean_dec(x_2184);
lean_dec(x_1935);
if (lean_is_exclusive(x_2201)) {
 lean_ctor_release(x_2201, 0);
 lean_ctor_release(x_2201, 1);
 x_2212 = x_2201;
} else {
 lean_dec_ref(x_2201);
 x_2212 = lean_box(0);
}
x_2213 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2212)) {
 x_2214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2214 = x_2212;
 lean_ctor_set_tag(x_2214, 0);
}
lean_ctor_set(x_2214, 0, x_2213);
lean_ctor_set(x_2214, 1, x_11);
return x_2214;
}
}
}
else
{
lean_object* x_2215; lean_object* x_2216; 
lean_dec(x_2200);
lean_dec(x_2199);
lean_dec(x_2198);
lean_dec(x_2184);
lean_dec(x_1935);
x_2215 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2185)) {
 x_2216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2216 = x_2185;
}
lean_ctor_set(x_2216, 0, x_2215);
lean_ctor_set(x_2216, 1, x_11);
return x_2216;
}
}
else
{
lean_object* x_2217; lean_object* x_2218; 
lean_dec(x_2199);
lean_dec(x_2198);
lean_dec(x_2184);
lean_dec(x_1935);
x_2217 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2185)) {
 x_2218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2218 = x_2185;
}
lean_ctor_set(x_2218, 0, x_2217);
lean_ctor_set(x_2218, 1, x_11);
return x_2218;
}
}
else
{
lean_object* x_2219; lean_object* x_2220; 
lean_dec(x_2198);
lean_dec(x_2184);
lean_dec(x_1935);
x_2219 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2185)) {
 x_2220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2220 = x_2185;
}
lean_ctor_set(x_2220, 0, x_2219);
lean_ctor_set(x_2220, 1, x_11);
return x_2220;
}
}
}
}
}
else
{
lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; 
lean_dec(x_2183);
lean_dec(x_2182);
lean_dec(x_2181);
lean_dec(x_1935);
if (lean_is_exclusive(x_2180)) {
 lean_ctor_release(x_2180, 0);
 lean_ctor_release(x_2180, 1);
 x_2221 = x_2180;
} else {
 lean_dec_ref(x_2180);
 x_2221 = lean_box(0);
}
x_2222 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2221)) {
 x_2223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2223 = x_2221;
}
lean_ctor_set(x_2223, 0, x_2222);
lean_ctor_set(x_2223, 1, x_11);
return x_2223;
}
}
else
{
lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; 
lean_dec(x_2182);
lean_dec(x_2181);
lean_dec(x_1935);
if (lean_is_exclusive(x_2180)) {
 lean_ctor_release(x_2180, 0);
 lean_ctor_release(x_2180, 1);
 x_2224 = x_2180;
} else {
 lean_dec_ref(x_2180);
 x_2224 = lean_box(0);
}
x_2225 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2224)) {
 x_2226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2226 = x_2224;
}
lean_ctor_set(x_2226, 0, x_2225);
lean_ctor_set(x_2226, 1, x_11);
return x_2226;
}
}
else
{
lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; 
lean_dec(x_2181);
lean_dec(x_1935);
if (lean_is_exclusive(x_2180)) {
 lean_ctor_release(x_2180, 0);
 lean_ctor_release(x_2180, 1);
 x_2227 = x_2180;
} else {
 lean_dec_ref(x_2180);
 x_2227 = lean_box(0);
}
x_2228 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2227)) {
 x_2229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2229 = x_2227;
}
lean_ctor_set(x_2229, 0, x_2228);
lean_ctor_set(x_2229, 1, x_11);
return x_2229;
}
}
}
else
{
lean_object* x_2230; lean_object* x_2231; 
lean_dec(x_1972);
lean_dec(x_1971);
lean_dec(x_1970);
lean_dec(x_1969);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2230 = l_Lean_Expr_getAppFnArgs(x_1933);
x_2231 = lean_ctor_get(x_2230, 0);
lean_inc(x_2231);
if (lean_obj_tag(x_2231) == 1)
{
lean_object* x_2232; 
x_2232 = lean_ctor_get(x_2231, 0);
lean_inc(x_2232);
if (lean_obj_tag(x_2232) == 1)
{
lean_object* x_2233; 
x_2233 = lean_ctor_get(x_2232, 0);
lean_inc(x_2233);
if (lean_obj_tag(x_2233) == 0)
{
lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; uint8_t x_2238; 
x_2234 = lean_ctor_get(x_2230, 1);
lean_inc(x_2234);
if (lean_is_exclusive(x_2230)) {
 lean_ctor_release(x_2230, 0);
 lean_ctor_release(x_2230, 1);
 x_2235 = x_2230;
} else {
 lean_dec_ref(x_2230);
 x_2235 = lean_box(0);
}
x_2236 = lean_ctor_get(x_2231, 1);
lean_inc(x_2236);
lean_dec(x_2231);
x_2237 = lean_ctor_get(x_2232, 1);
lean_inc(x_2237);
lean_dec(x_2232);
x_2238 = lean_string_dec_eq(x_2237, x_1869);
lean_dec(x_2237);
if (x_2238 == 0)
{
lean_object* x_2239; lean_object* x_2240; 
lean_dec(x_2236);
lean_dec(x_2234);
lean_dec(x_1935);
x_2239 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2235)) {
 x_2240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2240 = x_2235;
}
lean_ctor_set(x_2240, 0, x_2239);
lean_ctor_set(x_2240, 1, x_11);
return x_2240;
}
else
{
uint8_t x_2241; 
x_2241 = lean_string_dec_eq(x_2236, x_1949);
lean_dec(x_2236);
if (x_2241 == 0)
{
lean_object* x_2242; lean_object* x_2243; 
lean_dec(x_2234);
lean_dec(x_1935);
x_2242 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2235)) {
 x_2243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2243 = x_2235;
}
lean_ctor_set(x_2243, 0, x_2242);
lean_ctor_set(x_2243, 1, x_11);
return x_2243;
}
else
{
lean_object* x_2244; uint8_t x_2245; 
x_2244 = lean_array_get_size(x_2234);
x_2245 = lean_nat_dec_eq(x_2244, x_1954);
lean_dec(x_2244);
if (x_2245 == 0)
{
lean_object* x_2246; lean_object* x_2247; 
lean_dec(x_2234);
lean_dec(x_1935);
x_2246 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2235)) {
 x_2247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2247 = x_2235;
}
lean_ctor_set(x_2247, 0, x_2246);
lean_ctor_set(x_2247, 1, x_11);
return x_2247;
}
else
{
lean_object* x_2248; 
x_2248 = lean_array_fget(x_2234, x_1958);
if (lean_obj_tag(x_2248) == 4)
{
lean_object* x_2249; 
x_2249 = lean_ctor_get(x_2248, 0);
lean_inc(x_2249);
if (lean_obj_tag(x_2249) == 1)
{
lean_object* x_2250; 
x_2250 = lean_ctor_get(x_2249, 0);
lean_inc(x_2250);
if (lean_obj_tag(x_2250) == 0)
{
lean_object* x_2251; lean_object* x_2252; uint8_t x_2253; 
x_2251 = lean_ctor_get(x_2248, 1);
lean_inc(x_2251);
lean_dec(x_2248);
x_2252 = lean_ctor_get(x_2249, 1);
lean_inc(x_2252);
lean_dec(x_2249);
x_2253 = lean_string_dec_eq(x_2252, x_1964);
lean_dec(x_2252);
if (x_2253 == 0)
{
lean_object* x_2254; lean_object* x_2255; 
lean_dec(x_2251);
lean_dec(x_2234);
lean_dec(x_1935);
x_2254 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2235)) {
 x_2255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2255 = x_2235;
}
lean_ctor_set(x_2255, 0, x_2254);
lean_ctor_set(x_2255, 1, x_11);
return x_2255;
}
else
{
if (lean_obj_tag(x_2251) == 0)
{
lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; 
x_2256 = lean_array_fget(x_2234, x_1968);
lean_dec(x_2234);
x_2257 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2258 = l_Lean_mkAppB(x_2257, x_2256, x_1935);
x_2259 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2260 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2259, x_2258);
if (lean_is_scalar(x_2235)) {
 x_2261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2261 = x_2235;
}
lean_ctor_set(x_2261, 0, x_2260);
lean_ctor_set(x_2261, 1, x_11);
return x_2261;
}
else
{
lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; 
lean_dec(x_2235);
lean_dec(x_2234);
lean_dec(x_1935);
if (lean_is_exclusive(x_2251)) {
 lean_ctor_release(x_2251, 0);
 lean_ctor_release(x_2251, 1);
 x_2262 = x_2251;
} else {
 lean_dec_ref(x_2251);
 x_2262 = lean_box(0);
}
x_2263 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2262)) {
 x_2264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2264 = x_2262;
 lean_ctor_set_tag(x_2264, 0);
}
lean_ctor_set(x_2264, 0, x_2263);
lean_ctor_set(x_2264, 1, x_11);
return x_2264;
}
}
}
else
{
lean_object* x_2265; lean_object* x_2266; 
lean_dec(x_2250);
lean_dec(x_2249);
lean_dec(x_2248);
lean_dec(x_2234);
lean_dec(x_1935);
x_2265 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2235)) {
 x_2266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2266 = x_2235;
}
lean_ctor_set(x_2266, 0, x_2265);
lean_ctor_set(x_2266, 1, x_11);
return x_2266;
}
}
else
{
lean_object* x_2267; lean_object* x_2268; 
lean_dec(x_2249);
lean_dec(x_2248);
lean_dec(x_2234);
lean_dec(x_1935);
x_2267 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2235)) {
 x_2268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2268 = x_2235;
}
lean_ctor_set(x_2268, 0, x_2267);
lean_ctor_set(x_2268, 1, x_11);
return x_2268;
}
}
else
{
lean_object* x_2269; lean_object* x_2270; 
lean_dec(x_2248);
lean_dec(x_2234);
lean_dec(x_1935);
x_2269 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2235)) {
 x_2270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2270 = x_2235;
}
lean_ctor_set(x_2270, 0, x_2269);
lean_ctor_set(x_2270, 1, x_11);
return x_2270;
}
}
}
}
}
else
{
lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; 
lean_dec(x_2233);
lean_dec(x_2232);
lean_dec(x_2231);
lean_dec(x_1935);
if (lean_is_exclusive(x_2230)) {
 lean_ctor_release(x_2230, 0);
 lean_ctor_release(x_2230, 1);
 x_2271 = x_2230;
} else {
 lean_dec_ref(x_2230);
 x_2271 = lean_box(0);
}
x_2272 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2271)) {
 x_2273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2273 = x_2271;
}
lean_ctor_set(x_2273, 0, x_2272);
lean_ctor_set(x_2273, 1, x_11);
return x_2273;
}
}
else
{
lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; 
lean_dec(x_2232);
lean_dec(x_2231);
lean_dec(x_1935);
if (lean_is_exclusive(x_2230)) {
 lean_ctor_release(x_2230, 0);
 lean_ctor_release(x_2230, 1);
 x_2274 = x_2230;
} else {
 lean_dec_ref(x_2230);
 x_2274 = lean_box(0);
}
x_2275 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2274)) {
 x_2276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2276 = x_2274;
}
lean_ctor_set(x_2276, 0, x_2275);
lean_ctor_set(x_2276, 1, x_11);
return x_2276;
}
}
else
{
lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; 
lean_dec(x_2231);
lean_dec(x_1935);
if (lean_is_exclusive(x_2230)) {
 lean_ctor_release(x_2230, 0);
 lean_ctor_release(x_2230, 1);
 x_2277 = x_2230;
} else {
 lean_dec_ref(x_2230);
 x_2277 = lean_box(0);
}
x_2278 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2277)) {
 x_2279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2279 = x_2277;
}
lean_ctor_set(x_2279, 0, x_2278);
lean_ctor_set(x_2279, 1, x_11);
return x_2279;
}
}
}
else
{
lean_object* x_2280; lean_object* x_2281; 
lean_dec(x_1971);
lean_dec(x_1970);
lean_dec(x_1969);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2280 = l_Lean_Expr_getAppFnArgs(x_1933);
x_2281 = lean_ctor_get(x_2280, 0);
lean_inc(x_2281);
if (lean_obj_tag(x_2281) == 1)
{
lean_object* x_2282; 
x_2282 = lean_ctor_get(x_2281, 0);
lean_inc(x_2282);
if (lean_obj_tag(x_2282) == 1)
{
lean_object* x_2283; 
x_2283 = lean_ctor_get(x_2282, 0);
lean_inc(x_2283);
if (lean_obj_tag(x_2283) == 0)
{
lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; uint8_t x_2288; 
x_2284 = lean_ctor_get(x_2280, 1);
lean_inc(x_2284);
if (lean_is_exclusive(x_2280)) {
 lean_ctor_release(x_2280, 0);
 lean_ctor_release(x_2280, 1);
 x_2285 = x_2280;
} else {
 lean_dec_ref(x_2280);
 x_2285 = lean_box(0);
}
x_2286 = lean_ctor_get(x_2281, 1);
lean_inc(x_2286);
lean_dec(x_2281);
x_2287 = lean_ctor_get(x_2282, 1);
lean_inc(x_2287);
lean_dec(x_2282);
x_2288 = lean_string_dec_eq(x_2287, x_1869);
lean_dec(x_2287);
if (x_2288 == 0)
{
lean_object* x_2289; lean_object* x_2290; 
lean_dec(x_2286);
lean_dec(x_2284);
lean_dec(x_1935);
x_2289 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2285)) {
 x_2290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2290 = x_2285;
}
lean_ctor_set(x_2290, 0, x_2289);
lean_ctor_set(x_2290, 1, x_11);
return x_2290;
}
else
{
uint8_t x_2291; 
x_2291 = lean_string_dec_eq(x_2286, x_1949);
lean_dec(x_2286);
if (x_2291 == 0)
{
lean_object* x_2292; lean_object* x_2293; 
lean_dec(x_2284);
lean_dec(x_1935);
x_2292 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2285)) {
 x_2293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2293 = x_2285;
}
lean_ctor_set(x_2293, 0, x_2292);
lean_ctor_set(x_2293, 1, x_11);
return x_2293;
}
else
{
lean_object* x_2294; uint8_t x_2295; 
x_2294 = lean_array_get_size(x_2284);
x_2295 = lean_nat_dec_eq(x_2294, x_1954);
lean_dec(x_2294);
if (x_2295 == 0)
{
lean_object* x_2296; lean_object* x_2297; 
lean_dec(x_2284);
lean_dec(x_1935);
x_2296 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2285)) {
 x_2297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2297 = x_2285;
}
lean_ctor_set(x_2297, 0, x_2296);
lean_ctor_set(x_2297, 1, x_11);
return x_2297;
}
else
{
lean_object* x_2298; 
x_2298 = lean_array_fget(x_2284, x_1958);
if (lean_obj_tag(x_2298) == 4)
{
lean_object* x_2299; 
x_2299 = lean_ctor_get(x_2298, 0);
lean_inc(x_2299);
if (lean_obj_tag(x_2299) == 1)
{
lean_object* x_2300; 
x_2300 = lean_ctor_get(x_2299, 0);
lean_inc(x_2300);
if (lean_obj_tag(x_2300) == 0)
{
lean_object* x_2301; lean_object* x_2302; uint8_t x_2303; 
x_2301 = lean_ctor_get(x_2298, 1);
lean_inc(x_2301);
lean_dec(x_2298);
x_2302 = lean_ctor_get(x_2299, 1);
lean_inc(x_2302);
lean_dec(x_2299);
x_2303 = lean_string_dec_eq(x_2302, x_1964);
lean_dec(x_2302);
if (x_2303 == 0)
{
lean_object* x_2304; lean_object* x_2305; 
lean_dec(x_2301);
lean_dec(x_2284);
lean_dec(x_1935);
x_2304 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2285)) {
 x_2305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2305 = x_2285;
}
lean_ctor_set(x_2305, 0, x_2304);
lean_ctor_set(x_2305, 1, x_11);
return x_2305;
}
else
{
if (lean_obj_tag(x_2301) == 0)
{
lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; 
x_2306 = lean_array_fget(x_2284, x_1968);
lean_dec(x_2284);
x_2307 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2308 = l_Lean_mkAppB(x_2307, x_2306, x_1935);
x_2309 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2310 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2309, x_2308);
if (lean_is_scalar(x_2285)) {
 x_2311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2311 = x_2285;
}
lean_ctor_set(x_2311, 0, x_2310);
lean_ctor_set(x_2311, 1, x_11);
return x_2311;
}
else
{
lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; 
lean_dec(x_2285);
lean_dec(x_2284);
lean_dec(x_1935);
if (lean_is_exclusive(x_2301)) {
 lean_ctor_release(x_2301, 0);
 lean_ctor_release(x_2301, 1);
 x_2312 = x_2301;
} else {
 lean_dec_ref(x_2301);
 x_2312 = lean_box(0);
}
x_2313 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2312)) {
 x_2314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2314 = x_2312;
 lean_ctor_set_tag(x_2314, 0);
}
lean_ctor_set(x_2314, 0, x_2313);
lean_ctor_set(x_2314, 1, x_11);
return x_2314;
}
}
}
else
{
lean_object* x_2315; lean_object* x_2316; 
lean_dec(x_2300);
lean_dec(x_2299);
lean_dec(x_2298);
lean_dec(x_2284);
lean_dec(x_1935);
x_2315 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2285)) {
 x_2316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2316 = x_2285;
}
lean_ctor_set(x_2316, 0, x_2315);
lean_ctor_set(x_2316, 1, x_11);
return x_2316;
}
}
else
{
lean_object* x_2317; lean_object* x_2318; 
lean_dec(x_2299);
lean_dec(x_2298);
lean_dec(x_2284);
lean_dec(x_1935);
x_2317 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2285)) {
 x_2318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2318 = x_2285;
}
lean_ctor_set(x_2318, 0, x_2317);
lean_ctor_set(x_2318, 1, x_11);
return x_2318;
}
}
else
{
lean_object* x_2319; lean_object* x_2320; 
lean_dec(x_2298);
lean_dec(x_2284);
lean_dec(x_1935);
x_2319 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2285)) {
 x_2320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2320 = x_2285;
}
lean_ctor_set(x_2320, 0, x_2319);
lean_ctor_set(x_2320, 1, x_11);
return x_2320;
}
}
}
}
}
else
{
lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; 
lean_dec(x_2283);
lean_dec(x_2282);
lean_dec(x_2281);
lean_dec(x_1935);
if (lean_is_exclusive(x_2280)) {
 lean_ctor_release(x_2280, 0);
 lean_ctor_release(x_2280, 1);
 x_2321 = x_2280;
} else {
 lean_dec_ref(x_2280);
 x_2321 = lean_box(0);
}
x_2322 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2321)) {
 x_2323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2323 = x_2321;
}
lean_ctor_set(x_2323, 0, x_2322);
lean_ctor_set(x_2323, 1, x_11);
return x_2323;
}
}
else
{
lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; 
lean_dec(x_2282);
lean_dec(x_2281);
lean_dec(x_1935);
if (lean_is_exclusive(x_2280)) {
 lean_ctor_release(x_2280, 0);
 lean_ctor_release(x_2280, 1);
 x_2324 = x_2280;
} else {
 lean_dec_ref(x_2280);
 x_2324 = lean_box(0);
}
x_2325 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2324)) {
 x_2326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2326 = x_2324;
}
lean_ctor_set(x_2326, 0, x_2325);
lean_ctor_set(x_2326, 1, x_11);
return x_2326;
}
}
else
{
lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; 
lean_dec(x_2281);
lean_dec(x_1935);
if (lean_is_exclusive(x_2280)) {
 lean_ctor_release(x_2280, 0);
 lean_ctor_release(x_2280, 1);
 x_2327 = x_2280;
} else {
 lean_dec_ref(x_2280);
 x_2327 = lean_box(0);
}
x_2328 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2327)) {
 x_2329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2329 = x_2327;
}
lean_ctor_set(x_2329, 0, x_2328);
lean_ctor_set(x_2329, 1, x_11);
return x_2329;
}
}
}
else
{
lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; 
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_exclusive(x_1962)) {
 lean_ctor_release(x_1962, 0);
 lean_ctor_release(x_1962, 1);
 x_2330 = x_1962;
} else {
 lean_dec_ref(x_1962);
 x_2330 = lean_box(0);
}
x_2331 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2330)) {
 x_2332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2332 = x_2330;
 lean_ctor_set_tag(x_2332, 0);
}
lean_ctor_set(x_2332, 0, x_2331);
lean_ctor_set(x_2332, 1, x_11);
return x_2332;
}
}
}
else
{
lean_object* x_2333; lean_object* x_2334; 
lean_dec(x_1961);
lean_dec(x_1960);
lean_dec(x_1959);
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2333 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_2334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2334 = x_1941;
}
lean_ctor_set(x_2334, 0, x_2333);
lean_ctor_set(x_2334, 1, x_11);
return x_2334;
}
}
else
{
lean_object* x_2335; lean_object* x_2336; 
lean_dec(x_1960);
lean_dec(x_1959);
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2335 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_2336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2336 = x_1941;
}
lean_ctor_set(x_2336, 0, x_2335);
lean_ctor_set(x_2336, 1, x_11);
return x_2336;
}
}
else
{
lean_object* x_2337; lean_object* x_2338; 
lean_dec(x_1959);
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2337 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_2338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2338 = x_1941;
}
lean_ctor_set(x_2338, 0, x_2337);
lean_ctor_set(x_2338, 1, x_11);
return x_2338;
}
}
}
}
}
else
{
lean_object* x_2339; uint8_t x_2340; 
lean_dec(x_1943);
x_2339 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_2340 = lean_string_dec_eq(x_1942, x_2339);
lean_dec(x_1942);
if (x_2340 == 0)
{
lean_object* x_2341; lean_object* x_2342; 
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2341 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_2342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2342 = x_1941;
}
lean_ctor_set(x_2342, 0, x_2341);
lean_ctor_set(x_2342, 1, x_11);
return x_2342;
}
else
{
lean_object* x_2343; uint8_t x_2344; 
x_2343 = lean_array_get_size(x_1940);
x_2344 = lean_nat_dec_eq(x_2343, x_1928);
lean_dec(x_2343);
if (x_2344 == 0)
{
lean_object* x_2345; lean_object* x_2346; 
lean_dec(x_1940);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2345 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_2346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2346 = x_1941;
}
lean_ctor_set(x_2346, 0, x_2345);
lean_ctor_set(x_2346, 1, x_11);
return x_2346;
}
else
{
lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; 
x_2347 = lean_array_fget(x_1940, x_1932);
x_2348 = lean_array_fget(x_1940, x_1934);
lean_dec(x_1940);
lean_inc(x_2347);
x_2349 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_2347);
if (lean_obj_tag(x_2349) == 0)
{
lean_object* x_2350; lean_object* x_2351; 
lean_dec(x_2348);
lean_dec(x_2347);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2350 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_2351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2351 = x_1941;
}
lean_ctor_set(x_2351, 0, x_2350);
lean_ctor_set(x_2351, 1, x_11);
return x_2351;
}
else
{
lean_object* x_2352; lean_object* x_2353; uint8_t x_2354; 
x_2352 = lean_ctor_get(x_2349, 0);
lean_inc(x_2352);
lean_dec(x_2349);
x_2353 = lean_unsigned_to_nat(0u);
x_2354 = lean_nat_dec_eq(x_2352, x_2353);
lean_dec(x_2352);
if (x_2354 == 0)
{
lean_object* x_2355; uint8_t x_2381; 
lean_dec(x_1941);
x_2381 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_2381 == 0)
{
lean_object* x_2382; 
x_2382 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76;
x_2355 = x_2382;
goto block_2380;
}
else
{
lean_object* x_2383; 
x_2383 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_2355 = x_2383;
goto block_2380;
}
block_2380:
{
lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; 
x_2356 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_2357 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_2358 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
lean_inc(x_2347);
lean_inc(x_2355);
x_2359 = l_Lean_mkApp4(x_2356, x_2357, x_2358, x_2355, x_2347);
x_2360 = l_Lean_Meta_mkDecideProof(x_2359, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_2360) == 0)
{
lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; 
x_2361 = lean_ctor_get(x_2360, 0);
lean_inc(x_2361);
x_2362 = lean_ctor_get(x_2360, 1);
lean_inc(x_2362);
if (lean_is_exclusive(x_2360)) {
 lean_ctor_release(x_2360, 0);
 lean_ctor_release(x_2360, 1);
 x_2363 = x_2360;
} else {
 lean_dec_ref(x_2360);
 x_2363 = lean_box(0);
}
x_2364 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
x_2365 = l_Lean_mkApp3(x_2364, x_2347, x_2348, x_2361);
x_2366 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
lean_inc(x_2365);
lean_inc(x_1935);
x_2367 = l_Lean_mkApp3(x_2366, x_1935, x_2355, x_2365);
x_2368 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_1935);
lean_inc(x_1933);
x_2369 = l_Lean_mkApp3(x_2368, x_1933, x_1935, x_2367);
x_2370 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_2371 = l_Lean_mkApp3(x_2370, x_1933, x_1935, x_2365);
x_2372 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2373 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2372, x_2369);
x_2374 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2373, x_2371);
if (lean_is_scalar(x_2363)) {
 x_2375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2375 = x_2363;
}
lean_ctor_set(x_2375, 0, x_2374);
lean_ctor_set(x_2375, 1, x_2362);
return x_2375;
}
else
{
lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; 
lean_dec(x_2355);
lean_dec(x_2348);
lean_dec(x_2347);
lean_dec(x_1935);
lean_dec(x_1933);
x_2376 = lean_ctor_get(x_2360, 0);
lean_inc(x_2376);
x_2377 = lean_ctor_get(x_2360, 1);
lean_inc(x_2377);
if (lean_is_exclusive(x_2360)) {
 lean_ctor_release(x_2360, 0);
 lean_ctor_release(x_2360, 1);
 x_2378 = x_2360;
} else {
 lean_dec_ref(x_2360);
 x_2378 = lean_box(0);
}
if (lean_is_scalar(x_2378)) {
 x_2379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2379 = x_2378;
}
lean_ctor_set(x_2379, 0, x_2376);
lean_ctor_set(x_2379, 1, x_2377);
return x_2379;
}
}
}
else
{
lean_object* x_2384; lean_object* x_2385; 
lean_dec(x_2348);
lean_dec(x_2347);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2384 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_1941)) {
 x_2385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2385 = x_1941;
}
lean_ctor_set(x_2385, 0, x_2384);
lean_ctor_set(x_2385, 1, x_11);
return x_2385;
}
}
}
}
}
}
else
{
lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; 
lean_dec(x_1939);
lean_dec(x_1938);
lean_dec(x_1937);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_exclusive(x_1936)) {
 lean_ctor_release(x_1936, 0);
 lean_ctor_release(x_1936, 1);
 x_2386 = x_1936;
} else {
 lean_dec_ref(x_1936);
 x_2386 = lean_box(0);
}
x_2387 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2386)) {
 x_2388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2388 = x_2386;
}
lean_ctor_set(x_2388, 0, x_2387);
lean_ctor_set(x_2388, 1, x_11);
return x_2388;
}
}
else
{
lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; 
lean_dec(x_1938);
lean_dec(x_1937);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_exclusive(x_1936)) {
 lean_ctor_release(x_1936, 0);
 lean_ctor_release(x_1936, 1);
 x_2389 = x_1936;
} else {
 lean_dec_ref(x_1936);
 x_2389 = lean_box(0);
}
x_2390 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2389)) {
 x_2391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2391 = x_2389;
}
lean_ctor_set(x_2391, 0, x_2390);
lean_ctor_set(x_2391, 1, x_11);
return x_2391;
}
}
else
{
lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; 
lean_dec(x_1937);
lean_dec(x_1935);
lean_dec(x_1933);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_exclusive(x_1936)) {
 lean_ctor_release(x_1936, 0);
 lean_ctor_release(x_1936, 1);
 x_2392 = x_1936;
} else {
 lean_dec_ref(x_1936);
 x_2392 = lean_box(0);
}
x_2393 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2392)) {
 x_2394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2394 = x_2392;
}
lean_ctor_set(x_2394, 0, x_2393);
lean_ctor_set(x_2394, 1, x_11);
return x_2394;
}
}
}
}
}
else
{
lean_object* x_2395; uint8_t x_2396; 
lean_dec(x_1868);
x_2395 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_2396 = lean_string_dec_eq(x_1867, x_2395);
lean_dec(x_1867);
if (x_2396 == 0)
{
lean_object* x_2397; lean_object* x_2398; 
lean_dec(x_1866);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2397 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2398, 0, x_2397);
lean_ctor_set(x_2398, 1, x_11);
return x_2398;
}
else
{
lean_object* x_2399; lean_object* x_2400; uint8_t x_2401; 
x_2399 = lean_array_get_size(x_1866);
x_2400 = lean_unsigned_to_nat(6u);
x_2401 = lean_nat_dec_eq(x_2399, x_2400);
lean_dec(x_2399);
if (x_2401 == 0)
{
lean_object* x_2402; lean_object* x_2403; 
lean_dec(x_1866);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2402 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2403, 0, x_2402);
lean_ctor_set(x_2403, 1, x_11);
return x_2403;
}
else
{
lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; 
x_2404 = lean_unsigned_to_nat(4u);
x_2405 = lean_array_fget(x_1866, x_2404);
x_2406 = lean_unsigned_to_nat(5u);
x_2407 = lean_array_fget(x_1866, x_2406);
lean_dec(x_1866);
lean_inc(x_2407);
x_2408 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_2407);
if (lean_obj_tag(x_2408) == 0)
{
lean_object* x_2409; lean_object* x_2410; 
lean_dec(x_2407);
lean_dec(x_2405);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2409 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2410, 0, x_2409);
lean_ctor_set(x_2410, 1, x_11);
return x_2410;
}
else
{
lean_object* x_2411; lean_object* x_2412; uint8_t x_2413; 
x_2411 = lean_ctor_get(x_2408, 0);
lean_inc(x_2411);
lean_dec(x_2408);
x_2412 = lean_unsigned_to_nat(0u);
x_2413 = lean_nat_dec_eq(x_2411, x_2412);
lean_dec(x_2411);
if (x_2413 == 0)
{
lean_object* x_2414; uint8_t x_2445; 
x_2445 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_2445 == 0)
{
lean_object* x_2446; 
x_2446 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90;
x_2414 = x_2446;
goto block_2444;
}
else
{
lean_object* x_2447; 
x_2447 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_2414 = x_2447;
goto block_2444;
}
block_2444:
{
lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; 
x_2415 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
x_2416 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
lean_inc(x_2414);
lean_inc(x_2407);
x_2417 = l_Lean_mkApp3(x_2415, x_2416, x_2407, x_2414);
x_2418 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
x_2419 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
lean_inc(x_2407);
x_2420 = l_Lean_mkApp4(x_2418, x_2416, x_2419, x_2414, x_2407);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_2421 = l_Lean_Meta_mkDecideProof(x_2417, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_2421) == 0)
{
lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; 
x_2422 = lean_ctor_get(x_2421, 0);
lean_inc(x_2422);
x_2423 = lean_ctor_get(x_2421, 1);
lean_inc(x_2423);
lean_dec(x_2421);
x_2424 = l_Lean_Meta_mkDecideProof(x_2420, x_7, x_8, x_9, x_10, x_2423);
if (lean_obj_tag(x_2424) == 0)
{
lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; 
x_2425 = lean_ctor_get(x_2424, 0);
lean_inc(x_2425);
x_2426 = lean_ctor_get(x_2424, 1);
lean_inc(x_2426);
if (lean_is_exclusive(x_2424)) {
 lean_ctor_release(x_2424, 0);
 lean_ctor_release(x_2424, 1);
 x_2427 = x_2424;
} else {
 lean_dec_ref(x_2424);
 x_2427 = lean_box(0);
}
x_2428 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
lean_inc(x_2407);
lean_inc(x_2405);
x_2429 = l_Lean_mkApp3(x_2428, x_2405, x_2407, x_2422);
x_2430 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88;
x_2431 = l_Lean_mkApp3(x_2430, x_2405, x_2407, x_2425);
x_2432 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2433 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2432, x_2429);
x_2434 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2433, x_2431);
if (lean_is_scalar(x_2427)) {
 x_2435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2435 = x_2427;
}
lean_ctor_set(x_2435, 0, x_2434);
lean_ctor_set(x_2435, 1, x_2426);
return x_2435;
}
else
{
lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; 
lean_dec(x_2422);
lean_dec(x_2407);
lean_dec(x_2405);
x_2436 = lean_ctor_get(x_2424, 0);
lean_inc(x_2436);
x_2437 = lean_ctor_get(x_2424, 1);
lean_inc(x_2437);
if (lean_is_exclusive(x_2424)) {
 lean_ctor_release(x_2424, 0);
 lean_ctor_release(x_2424, 1);
 x_2438 = x_2424;
} else {
 lean_dec_ref(x_2424);
 x_2438 = lean_box(0);
}
if (lean_is_scalar(x_2438)) {
 x_2439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2439 = x_2438;
}
lean_ctor_set(x_2439, 0, x_2436);
lean_ctor_set(x_2439, 1, x_2437);
return x_2439;
}
}
else
{
lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; 
lean_dec(x_2420);
lean_dec(x_2407);
lean_dec(x_2405);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2440 = lean_ctor_get(x_2421, 0);
lean_inc(x_2440);
x_2441 = lean_ctor_get(x_2421, 1);
lean_inc(x_2441);
if (lean_is_exclusive(x_2421)) {
 lean_ctor_release(x_2421, 0);
 lean_ctor_release(x_2421, 1);
 x_2442 = x_2421;
} else {
 lean_dec_ref(x_2421);
 x_2442 = lean_box(0);
}
if (lean_is_scalar(x_2442)) {
 x_2443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2443 = x_2442;
}
lean_ctor_set(x_2443, 0, x_2440);
lean_ctor_set(x_2443, 1, x_2441);
return x_2443;
}
}
}
else
{
lean_object* x_2448; lean_object* x_2449; 
lean_dec(x_2407);
lean_dec(x_2405);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2448 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2449, 0, x_2448);
lean_ctor_set(x_2449, 1, x_11);
return x_2449;
}
}
}
}
}
}
else
{
lean_object* x_2450; uint8_t x_2451; 
lean_dec(x_1868);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2450 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_2451 = lean_string_dec_eq(x_1867, x_2450);
lean_dec(x_1867);
if (x_2451 == 0)
{
lean_object* x_2452; lean_object* x_2453; 
lean_dec(x_1866);
x_2452 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2453, 0, x_2452);
lean_ctor_set(x_2453, 1, x_11);
return x_2453;
}
else
{
lean_object* x_2454; lean_object* x_2455; uint8_t x_2456; 
x_2454 = lean_array_get_size(x_1866);
x_2455 = lean_unsigned_to_nat(3u);
x_2456 = lean_nat_dec_eq(x_2454, x_2455);
lean_dec(x_2454);
if (x_2456 == 0)
{
lean_object* x_2457; lean_object* x_2458; 
lean_dec(x_1866);
x_2457 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2458, 0, x_2457);
lean_ctor_set(x_2458, 1, x_11);
return x_2458;
}
else
{
lean_object* x_2459; lean_object* x_2460; 
x_2459 = lean_unsigned_to_nat(0u);
x_2460 = lean_array_fget(x_1866, x_2459);
if (lean_obj_tag(x_2460) == 4)
{
lean_object* x_2461; 
x_2461 = lean_ctor_get(x_2460, 0);
lean_inc(x_2461);
if (lean_obj_tag(x_2461) == 1)
{
lean_object* x_2462; 
x_2462 = lean_ctor_get(x_2461, 0);
lean_inc(x_2462);
if (lean_obj_tag(x_2462) == 0)
{
lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; uint8_t x_2466; 
x_2463 = lean_ctor_get(x_2460, 1);
lean_inc(x_2463);
lean_dec(x_2460);
x_2464 = lean_ctor_get(x_2461, 1);
lean_inc(x_2464);
lean_dec(x_2461);
x_2465 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2466 = lean_string_dec_eq(x_2464, x_2465);
lean_dec(x_2464);
if (x_2466 == 0)
{
lean_object* x_2467; lean_object* x_2468; 
lean_dec(x_2463);
lean_dec(x_1866);
x_2467 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2468, 0, x_2467);
lean_ctor_set(x_2468, 1, x_11);
return x_2468;
}
else
{
if (lean_obj_tag(x_2463) == 0)
{
lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; uint8_t x_2475; lean_object* x_2476; 
x_2469 = lean_unsigned_to_nat(2u);
x_2470 = lean_array_fget(x_1866, x_2469);
lean_dec(x_1866);
x_2471 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93;
lean_inc(x_2470);
x_2472 = l_Lean_Expr_app___override(x_2471, x_2470);
x_2473 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2474 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2473, x_2472);
x_2475 = lean_ctor_get_uint8(x_4, 1);
x_2476 = l_Lean_Expr_getAppFnArgs(x_2470);
if (x_2475 == 0)
{
lean_object* x_2477; 
x_2477 = lean_ctor_get(x_2476, 0);
lean_inc(x_2477);
if (lean_obj_tag(x_2477) == 1)
{
lean_object* x_2478; 
x_2478 = lean_ctor_get(x_2477, 0);
lean_inc(x_2478);
if (lean_obj_tag(x_2478) == 1)
{
lean_object* x_2479; 
x_2479 = lean_ctor_get(x_2478, 0);
lean_inc(x_2479);
if (lean_obj_tag(x_2479) == 0)
{
lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; uint8_t x_2484; 
x_2480 = lean_ctor_get(x_2476, 1);
lean_inc(x_2480);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2481 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2481 = lean_box(0);
}
x_2482 = lean_ctor_get(x_2477, 1);
lean_inc(x_2482);
lean_dec(x_2477);
x_2483 = lean_ctor_get(x_2478, 1);
lean_inc(x_2483);
lean_dec(x_2478);
x_2484 = lean_string_dec_eq(x_2483, x_2465);
if (x_2484 == 0)
{
lean_object* x_2485; uint8_t x_2486; 
x_2485 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_2486 = lean_string_dec_eq(x_2483, x_2485);
if (x_2486 == 0)
{
lean_object* x_2487; uint8_t x_2488; 
x_2487 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_2488 = lean_string_dec_eq(x_2483, x_2487);
lean_dec(x_2483);
if (x_2488 == 0)
{
lean_object* x_2489; 
lean_dec(x_2482);
lean_dec(x_2480);
if (lean_is_scalar(x_2481)) {
 x_2489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2489 = x_2481;
}
lean_ctor_set(x_2489, 0, x_2474);
lean_ctor_set(x_2489, 1, x_11);
return x_2489;
}
else
{
lean_object* x_2490; uint8_t x_2491; 
x_2490 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_2491 = lean_string_dec_eq(x_2482, x_2490);
lean_dec(x_2482);
if (x_2491 == 0)
{
lean_object* x_2492; 
lean_dec(x_2480);
if (lean_is_scalar(x_2481)) {
 x_2492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2492 = x_2481;
}
lean_ctor_set(x_2492, 0, x_2474);
lean_ctor_set(x_2492, 1, x_11);
return x_2492;
}
else
{
lean_object* x_2493; uint8_t x_2494; 
x_2493 = lean_array_get_size(x_2480);
x_2494 = lean_nat_dec_eq(x_2493, x_2469);
lean_dec(x_2493);
if (x_2494 == 0)
{
lean_object* x_2495; 
lean_dec(x_2480);
if (lean_is_scalar(x_2481)) {
 x_2495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2495 = x_2481;
}
lean_ctor_set(x_2495, 0, x_2474);
lean_ctor_set(x_2495, 1, x_11);
return x_2495;
}
else
{
lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; 
x_2496 = lean_array_fget(x_2480, x_2459);
x_2497 = lean_unsigned_to_nat(1u);
x_2498 = lean_array_fget(x_2480, x_2497);
lean_dec(x_2480);
x_2499 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_2500 = l_Lean_mkAppB(x_2499, x_2496, x_2498);
x_2501 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2474, x_2500);
if (lean_is_scalar(x_2481)) {
 x_2502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2502 = x_2481;
}
lean_ctor_set(x_2502, 0, x_2501);
lean_ctor_set(x_2502, 1, x_11);
return x_2502;
}
}
}
}
else
{
lean_object* x_2503; uint8_t x_2504; 
lean_dec(x_2483);
x_2503 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_2504 = lean_string_dec_eq(x_2482, x_2503);
lean_dec(x_2482);
if (x_2504 == 0)
{
lean_object* x_2505; 
lean_dec(x_2480);
if (lean_is_scalar(x_2481)) {
 x_2505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2505 = x_2481;
}
lean_ctor_set(x_2505, 0, x_2474);
lean_ctor_set(x_2505, 1, x_11);
return x_2505;
}
else
{
lean_object* x_2506; uint8_t x_2507; 
x_2506 = lean_array_get_size(x_2480);
x_2507 = lean_nat_dec_eq(x_2506, x_2469);
lean_dec(x_2506);
if (x_2507 == 0)
{
lean_object* x_2508; 
lean_dec(x_2480);
if (lean_is_scalar(x_2481)) {
 x_2508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2508 = x_2481;
}
lean_ctor_set(x_2508, 0, x_2474);
lean_ctor_set(x_2508, 1, x_11);
return x_2508;
}
else
{
lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; lean_object* x_2515; 
x_2509 = lean_array_fget(x_2480, x_2459);
x_2510 = lean_unsigned_to_nat(1u);
x_2511 = lean_array_fget(x_2480, x_2510);
lean_dec(x_2480);
x_2512 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_2513 = l_Lean_mkAppB(x_2512, x_2509, x_2511);
x_2514 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2474, x_2513);
if (lean_is_scalar(x_2481)) {
 x_2515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2515 = x_2481;
}
lean_ctor_set(x_2515, 0, x_2514);
lean_ctor_set(x_2515, 1, x_11);
return x_2515;
}
}
}
}
else
{
lean_object* x_2516; uint8_t x_2517; 
lean_dec(x_2483);
x_2516 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_2517 = lean_string_dec_eq(x_2482, x_2516);
lean_dec(x_2482);
if (x_2517 == 0)
{
lean_object* x_2518; 
lean_dec(x_2480);
if (lean_is_scalar(x_2481)) {
 x_2518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2518 = x_2481;
}
lean_ctor_set(x_2518, 0, x_2474);
lean_ctor_set(x_2518, 1, x_11);
return x_2518;
}
else
{
lean_object* x_2519; lean_object* x_2520; uint8_t x_2521; 
x_2519 = lean_array_get_size(x_2480);
x_2520 = lean_unsigned_to_nat(1u);
x_2521 = lean_nat_dec_eq(x_2519, x_2520);
lean_dec(x_2519);
if (x_2521 == 0)
{
lean_object* x_2522; 
lean_dec(x_2480);
if (lean_is_scalar(x_2481)) {
 x_2522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2522 = x_2481;
}
lean_ctor_set(x_2522, 0, x_2474);
lean_ctor_set(x_2522, 1, x_11);
return x_2522;
}
else
{
lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; 
x_2523 = lean_array_fget(x_2480, x_2459);
lean_dec(x_2480);
x_2524 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_2523);
x_2525 = l_Lean_Expr_app___override(x_2524, x_2523);
x_2526 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_2527 = l_Lean_Expr_app___override(x_2526, x_2523);
x_2528 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2474, x_2525);
x_2529 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2528, x_2527);
if (lean_is_scalar(x_2481)) {
 x_2530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2530 = x_2481;
}
lean_ctor_set(x_2530, 0, x_2529);
lean_ctor_set(x_2530, 1, x_11);
return x_2530;
}
}
}
}
else
{
lean_object* x_2531; lean_object* x_2532; 
lean_dec(x_2479);
lean_dec(x_2478);
lean_dec(x_2477);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2531 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2531 = lean_box(0);
}
if (lean_is_scalar(x_2531)) {
 x_2532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2532 = x_2531;
}
lean_ctor_set(x_2532, 0, x_2474);
lean_ctor_set(x_2532, 1, x_11);
return x_2532;
}
}
else
{
lean_object* x_2533; lean_object* x_2534; 
lean_dec(x_2478);
lean_dec(x_2477);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2533 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2533 = lean_box(0);
}
if (lean_is_scalar(x_2533)) {
 x_2534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2534 = x_2533;
}
lean_ctor_set(x_2534, 0, x_2474);
lean_ctor_set(x_2534, 1, x_11);
return x_2534;
}
}
else
{
lean_object* x_2535; lean_object* x_2536; 
lean_dec(x_2477);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2535 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2535 = lean_box(0);
}
if (lean_is_scalar(x_2535)) {
 x_2536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2536 = x_2535;
}
lean_ctor_set(x_2536, 0, x_2474);
lean_ctor_set(x_2536, 1, x_11);
return x_2536;
}
}
else
{
lean_object* x_2537; 
x_2537 = lean_ctor_get(x_2476, 0);
lean_inc(x_2537);
if (lean_obj_tag(x_2537) == 1)
{
lean_object* x_2538; 
x_2538 = lean_ctor_get(x_2537, 0);
lean_inc(x_2538);
if (lean_obj_tag(x_2538) == 1)
{
lean_object* x_2539; 
x_2539 = lean_ctor_get(x_2538, 0);
lean_inc(x_2539);
if (lean_obj_tag(x_2539) == 0)
{
lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; uint8_t x_2545; 
x_2540 = lean_ctor_get(x_2476, 1);
lean_inc(x_2540);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2541 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2541 = lean_box(0);
}
x_2542 = lean_ctor_get(x_2537, 1);
lean_inc(x_2542);
lean_dec(x_2537);
x_2543 = lean_ctor_get(x_2538, 1);
lean_inc(x_2543);
lean_dec(x_2538);
x_2544 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_2545 = lean_string_dec_eq(x_2543, x_2544);
if (x_2545 == 0)
{
uint8_t x_2546; 
x_2546 = lean_string_dec_eq(x_2543, x_2465);
if (x_2546 == 0)
{
lean_object* x_2547; uint8_t x_2548; 
x_2547 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_2548 = lean_string_dec_eq(x_2543, x_2547);
if (x_2548 == 0)
{
lean_object* x_2549; uint8_t x_2550; 
x_2549 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_2550 = lean_string_dec_eq(x_2543, x_2549);
lean_dec(x_2543);
if (x_2550 == 0)
{
lean_object* x_2551; 
lean_dec(x_2542);
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2551 = x_2541;
}
lean_ctor_set(x_2551, 0, x_2474);
lean_ctor_set(x_2551, 1, x_11);
return x_2551;
}
else
{
lean_object* x_2552; uint8_t x_2553; 
x_2552 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_2553 = lean_string_dec_eq(x_2542, x_2552);
lean_dec(x_2542);
if (x_2553 == 0)
{
lean_object* x_2554; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2554 = x_2541;
}
lean_ctor_set(x_2554, 0, x_2474);
lean_ctor_set(x_2554, 1, x_11);
return x_2554;
}
else
{
lean_object* x_2555; uint8_t x_2556; 
x_2555 = lean_array_get_size(x_2540);
x_2556 = lean_nat_dec_eq(x_2555, x_2469);
lean_dec(x_2555);
if (x_2556 == 0)
{
lean_object* x_2557; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2557 = x_2541;
}
lean_ctor_set(x_2557, 0, x_2474);
lean_ctor_set(x_2557, 1, x_11);
return x_2557;
}
else
{
lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; 
x_2558 = lean_array_fget(x_2540, x_2459);
x_2559 = lean_unsigned_to_nat(1u);
x_2560 = lean_array_fget(x_2540, x_2559);
lean_dec(x_2540);
x_2561 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_2562 = l_Lean_mkAppB(x_2561, x_2558, x_2560);
x_2563 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2474, x_2562);
if (lean_is_scalar(x_2541)) {
 x_2564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2564 = x_2541;
}
lean_ctor_set(x_2564, 0, x_2563);
lean_ctor_set(x_2564, 1, x_11);
return x_2564;
}
}
}
}
else
{
lean_object* x_2565; uint8_t x_2566; 
lean_dec(x_2543);
x_2565 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_2566 = lean_string_dec_eq(x_2542, x_2565);
lean_dec(x_2542);
if (x_2566 == 0)
{
lean_object* x_2567; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2567 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2567 = x_2541;
}
lean_ctor_set(x_2567, 0, x_2474);
lean_ctor_set(x_2567, 1, x_11);
return x_2567;
}
else
{
lean_object* x_2568; uint8_t x_2569; 
x_2568 = lean_array_get_size(x_2540);
x_2569 = lean_nat_dec_eq(x_2568, x_2469);
lean_dec(x_2568);
if (x_2569 == 0)
{
lean_object* x_2570; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2570 = x_2541;
}
lean_ctor_set(x_2570, 0, x_2474);
lean_ctor_set(x_2570, 1, x_11);
return x_2570;
}
else
{
lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; 
x_2571 = lean_array_fget(x_2540, x_2459);
x_2572 = lean_unsigned_to_nat(1u);
x_2573 = lean_array_fget(x_2540, x_2572);
lean_dec(x_2540);
x_2574 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_2575 = l_Lean_mkAppB(x_2574, x_2571, x_2573);
x_2576 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2474, x_2575);
if (lean_is_scalar(x_2541)) {
 x_2577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2577 = x_2541;
}
lean_ctor_set(x_2577, 0, x_2576);
lean_ctor_set(x_2577, 1, x_11);
return x_2577;
}
}
}
}
else
{
lean_object* x_2578; uint8_t x_2579; 
lean_dec(x_2543);
x_2578 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_2579 = lean_string_dec_eq(x_2542, x_2578);
lean_dec(x_2542);
if (x_2579 == 0)
{
lean_object* x_2580; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2580 = x_2541;
}
lean_ctor_set(x_2580, 0, x_2474);
lean_ctor_set(x_2580, 1, x_11);
return x_2580;
}
else
{
lean_object* x_2581; lean_object* x_2582; uint8_t x_2583; 
x_2581 = lean_array_get_size(x_2540);
x_2582 = lean_unsigned_to_nat(1u);
x_2583 = lean_nat_dec_eq(x_2581, x_2582);
lean_dec(x_2581);
if (x_2583 == 0)
{
lean_object* x_2584; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2584 = x_2541;
}
lean_ctor_set(x_2584, 0, x_2474);
lean_ctor_set(x_2584, 1, x_11);
return x_2584;
}
else
{
lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; 
x_2585 = lean_array_fget(x_2540, x_2459);
lean_dec(x_2540);
x_2586 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_2585);
x_2587 = l_Lean_Expr_app___override(x_2586, x_2585);
x_2588 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_2589 = l_Lean_Expr_app___override(x_2588, x_2585);
x_2590 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2474, x_2587);
x_2591 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2590, x_2589);
if (lean_is_scalar(x_2541)) {
 x_2592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2592 = x_2541;
}
lean_ctor_set(x_2592, 0, x_2591);
lean_ctor_set(x_2592, 1, x_11);
return x_2592;
}
}
}
}
else
{
lean_object* x_2593; uint8_t x_2594; 
lean_dec(x_2543);
x_2593 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
x_2594 = lean_string_dec_eq(x_2542, x_2593);
lean_dec(x_2542);
if (x_2594 == 0)
{
lean_object* x_2595; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2595 = x_2541;
}
lean_ctor_set(x_2595, 0, x_2474);
lean_ctor_set(x_2595, 1, x_11);
return x_2595;
}
else
{
lean_object* x_2596; lean_object* x_2597; uint8_t x_2598; 
x_2596 = lean_array_get_size(x_2540);
x_2597 = lean_unsigned_to_nat(6u);
x_2598 = lean_nat_dec_eq(x_2596, x_2597);
lean_dec(x_2596);
if (x_2598 == 0)
{
lean_object* x_2599; 
lean_dec(x_2540);
if (lean_is_scalar(x_2541)) {
 x_2599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2599 = x_2541;
}
lean_ctor_set(x_2599, 0, x_2474);
lean_ctor_set(x_2599, 1, x_11);
return x_2599;
}
else
{
lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; 
x_2600 = lean_unsigned_to_nat(4u);
x_2601 = lean_array_fget(x_2540, x_2600);
x_2602 = lean_unsigned_to_nat(5u);
x_2603 = lean_array_fget(x_2540, x_2602);
lean_dec(x_2540);
x_2604 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112;
x_2605 = l_Lean_mkAppB(x_2604, x_2601, x_2603);
x_2606 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_2474, x_2605);
if (lean_is_scalar(x_2541)) {
 x_2607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2607 = x_2541;
}
lean_ctor_set(x_2607, 0, x_2606);
lean_ctor_set(x_2607, 1, x_11);
return x_2607;
}
}
}
}
else
{
lean_object* x_2608; lean_object* x_2609; 
lean_dec(x_2539);
lean_dec(x_2538);
lean_dec(x_2537);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2608 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2608 = lean_box(0);
}
if (lean_is_scalar(x_2608)) {
 x_2609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2609 = x_2608;
}
lean_ctor_set(x_2609, 0, x_2474);
lean_ctor_set(x_2609, 1, x_11);
return x_2609;
}
}
else
{
lean_object* x_2610; lean_object* x_2611; 
lean_dec(x_2538);
lean_dec(x_2537);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2610 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2610 = lean_box(0);
}
if (lean_is_scalar(x_2610)) {
 x_2611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2611 = x_2610;
}
lean_ctor_set(x_2611, 0, x_2474);
lean_ctor_set(x_2611, 1, x_11);
return x_2611;
}
}
else
{
lean_object* x_2612; lean_object* x_2613; 
lean_dec(x_2537);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2612 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2612 = lean_box(0);
}
if (lean_is_scalar(x_2612)) {
 x_2613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2613 = x_2612;
}
lean_ctor_set(x_2613, 0, x_2474);
lean_ctor_set(x_2613, 1, x_11);
return x_2613;
}
}
}
else
{
lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; 
lean_dec(x_1866);
if (lean_is_exclusive(x_2463)) {
 lean_ctor_release(x_2463, 0);
 lean_ctor_release(x_2463, 1);
 x_2614 = x_2463;
} else {
 lean_dec_ref(x_2463);
 x_2614 = lean_box(0);
}
x_2615 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
if (lean_is_scalar(x_2614)) {
 x_2616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2616 = x_2614;
 lean_ctor_set_tag(x_2616, 0);
}
lean_ctor_set(x_2616, 0, x_2615);
lean_ctor_set(x_2616, 1, x_11);
return x_2616;
}
}
}
else
{
lean_object* x_2617; lean_object* x_2618; 
lean_dec(x_2462);
lean_dec(x_2461);
lean_dec(x_2460);
lean_dec(x_1866);
x_2617 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2618, 0, x_2617);
lean_ctor_set(x_2618, 1, x_11);
return x_2618;
}
}
else
{
lean_object* x_2619; lean_object* x_2620; 
lean_dec(x_2461);
lean_dec(x_2460);
lean_dec(x_1866);
x_2619 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2620, 0, x_2619);
lean_ctor_set(x_2620, 1, x_11);
return x_2620;
}
}
else
{
lean_object* x_2621; lean_object* x_2622; 
lean_dec(x_2460);
lean_dec(x_1866);
x_2621 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2622 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2622, 0, x_2621);
lean_ctor_set(x_2622, 1, x_11);
return x_2622;
}
}
}
}
}
}
else
{
uint8_t x_2623; 
lean_dec(x_73);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2623 = !lean_is_exclusive(x_12);
if (x_2623 == 0)
{
lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; 
x_2624 = lean_ctor_get(x_12, 1);
lean_dec(x_2624);
x_2625 = lean_ctor_get(x_12, 0);
lean_dec(x_2625);
x_2626 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_2626);
return x_12;
}
else
{
lean_object* x_2627; lean_object* x_2628; 
lean_dec(x_12);
x_2627 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2628, 0, x_2627);
lean_ctor_set(x_2628, 1, x_11);
return x_2628;
}
}
}
default: 
{
uint8_t x_2629; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2629 = !lean_is_exclusive(x_12);
if (x_2629 == 0)
{
lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; 
x_2630 = lean_ctor_get(x_12, 1);
lean_dec(x_2630);
x_2631 = lean_ctor_get(x_12, 0);
lean_dec(x_2631);
x_2632 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_2632);
return x_12;
}
else
{
lean_object* x_2633; lean_object* x_2634; 
lean_dec(x_12);
x_2633 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2634, 0, x_2633);
lean_ctor_set(x_2634, 1, x_11);
return x_2634;
}
}
}
}
else
{
uint8_t x_2635; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2635 = !lean_is_exclusive(x_12);
if (x_2635 == 0)
{
lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; 
x_2636 = lean_ctor_get(x_12, 1);
lean_dec(x_2636);
x_2637 = lean_ctor_get(x_12, 0);
lean_dec(x_2637);
x_2638 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 0, x_2638);
return x_12;
}
else
{
lean_object* x_2639; lean_object* x_2640; 
lean_dec(x_12);
x_2639 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_2640 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2640, 0, x_2639);
lean_ctor_set(x_2640, 1, x_11);
return x_2640;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1;
x_13 = lean_st_ref_get(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_9, 2);
x_17 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_15, x_16, x_1);
lean_dec(x_15);
x_18 = lean_box(x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_ctor_get(x_9, 2);
x_22 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_19, x_21, x_1);
lean_dec(x_19);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Elab_Tactic_Omega_lookup___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__8(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Elab_Tactic_Omega_lookup___spec__7(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_1, x_2, x_8);
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
x_15 = l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Elab_Tactic_Omega_lookup___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__6(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_6, x_9, x_19);
x_21 = l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_2, x_3, x_10);
x_22 = lean_array_uset(x_20, x_9, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Expr_hash(x_2);
lean_inc(x_25);
x_27 = lean_hashmap_mk_idx(x_25, x_26);
x_28 = lean_array_uget(x_24, x_27);
x_29 = l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_23, x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_24, x_27, x_32);
x_34 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_25);
lean_dec(x_25);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_HashMapImp_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__6(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
x_38 = lean_box(0);
x_39 = lean_array_uset(x_24, x_27, x_38);
x_40 = l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_2, x_3, x_28);
x_41 = lean_array_uset(x_39, x_27, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__11(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_ctor_set(x_2, 1, x_1);
x_1 = x_2;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_List_foldlM___at_Lean_Elab_Tactic_Omega_lookup___spec__11(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__12(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
static double _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_11, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; double x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_19, 3);
x_23 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1;
x_24 = 0;
x_25 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2;
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_24);
x_27 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_28);
lean_ctor_set(x_17, 0, x_13);
x_29 = l_Lean_PersistentArray_push___rarg(x_22, x_17);
lean_ctor_set(x_19, 3, x_29);
x_30 = lean_st_ref_set(x_11, x_19, x_21);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; double x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_37 = lean_ctor_get(x_17, 1);
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
x_40 = lean_ctor_get(x_19, 2);
x_41 = lean_ctor_get(x_19, 3);
x_42 = lean_ctor_get(x_19, 4);
x_43 = lean_ctor_get(x_19, 5);
x_44 = lean_ctor_get(x_19, 6);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_45 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1;
x_46 = 0;
x_47 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2;
x_48 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_float(x_48, sizeof(void*)*2, x_45);
lean_ctor_set_float(x_48, sizeof(void*)*2 + 8, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 16, x_46);
x_49 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_50 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_15);
lean_ctor_set(x_50, 2, x_49);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_50);
lean_ctor_set(x_17, 0, x_13);
x_51 = l_Lean_PersistentArray_push___rarg(x_41, x_17);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_42);
lean_ctor_set(x_52, 5, x_43);
lean_ctor_set(x_52, 6, x_44);
x_53 = lean_st_ref_set(x_11, x_52, x_37);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; double x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 6);
lean_inc(x_66);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 lean_ctor_release(x_58, 6);
 x_67 = x_58;
} else {
 lean_dec_ref(x_58);
 x_67 = lean_box(0);
}
x_68 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1;
x_69 = 0;
x_70 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2;
x_71 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_float(x_71, sizeof(void*)*2, x_68);
lean_ctor_set_float(x_71, sizeof(void*)*2 + 8, x_68);
lean_ctor_set_uint8(x_71, sizeof(void*)*2 + 16, x_69);
x_72 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_73 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_15);
lean_ctor_set(x_73, 2, x_72);
lean_inc(x_13);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_13);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_PersistentArray_push___rarg(x_63, x_74);
if (lean_is_scalar(x_67)) {
 x_76 = lean_alloc_ctor(0, 7, 0);
} else {
 x_76 = x_67;
}
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_61);
lean_ctor_set(x_76, 2, x_62);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_64);
lean_ctor_set(x_76, 5, x_65);
lean_ctor_set(x_76, 6, x_66);
x_77 = lean_st_ref_set(x_11, x_76, x_59);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_st_ref_take(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_inc(x_17);
lean_inc(x_15);
x_18 = l_Lean_HashMap_insert___at_Lean_Elab_Tactic_Omega_lookup___spec__4(x_15, x_1, x_17);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_st_ref_set(x_5, x_18, x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_15, 1, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
x_29 = lean_st_ref_set(x_5, x_18, x_16);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_32);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
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
x_1 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_15 = l_Lean_Elab_Tactic_Omega_analyzeAtom(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_18, 1);
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_3);
x_30 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_18);
lean_dec(x_3);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_30, 1);
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_16);
x_40 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(x_39, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_List_map___at_Lean_MessageData_instCoeListExpr___spec__1(x_42);
x_45 = l_Lean_MessageData_ofList(x_44);
x_46 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_45);
lean_ctor_set(x_30, 0, x_46);
x_47 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_47);
lean_ctor_set(x_18, 0, x_30);
x_48 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_50);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_49);
return x_51;
}
else
{
uint8_t x_52; 
lean_free_object(x_30);
lean_free_object(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_16);
x_58 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_59 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(x_57, x_58, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_List_map___at_Lean_MessageData_instCoeListExpr___spec__1(x_60);
x_63 = l_Lean_MessageData_ofList(x_62);
x_64 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_66);
lean_ctor_set(x_18, 0, x_65);
x_67 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_61);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_69);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_73 = x_59;
} else {
 lean_dec_ref(x_59);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_free_object(x_18);
lean_dec(x_3);
x_75 = lean_box(0);
x_76 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_75, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_18, 1);
lean_inc(x_77);
lean_dec(x_18);
x_78 = lean_ctor_get(x_16, 0);
lean_inc(x_78);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_inc(x_3);
x_81 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_77);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_3);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_box(0);
x_86 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_85, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
x_89 = l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_16);
x_90 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_91 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(x_89, x_90, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_87);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_List_map___at_Lean_MessageData_instCoeListExpr___spec__1(x_92);
x_95 = l_Lean_MessageData_ofList(x_94);
x_96 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(7, 2, 0);
} else {
 x_97 = x_88;
 lean_ctor_set_tag(x_97, 7);
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_3, x_99, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_101, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_102);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_88);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_104 = lean_ctor_get(x_91, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_106 = x_91;
} else {
 lean_dec_ref(x_91);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_3);
x_108 = lean_box(0);
x_109 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_108, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_77);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_15);
if (x_110 == 0)
{
return x_15;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_15, 0);
x_112 = lean_ctor_get(x_15, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_15);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
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
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Meta_Canonicalizer_canon(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_14, x_18);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_16);
x_21 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_22 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_12);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_18, x_21, x_21, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_22, 1);
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
lean_inc(x_18);
x_31 = l_Lean_MessageData_ofExpr(x_18);
x_32 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_32);
x_33 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_33);
lean_ctor_set(x_12, 0, x_22);
x_34 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_21, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_18, x_21, x_21, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
lean_inc(x_18);
x_39 = l_Lean_MessageData_ofExpr(x_18);
x_40 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_42);
lean_ctor_set(x_12, 0, x_41);
x_43 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_21, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_18, x_21, x_21, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_47 = lean_ctor_get(x_20, 0);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_box(0);
lean_ctor_set(x_12, 1, x_48);
lean_ctor_set(x_12, 0, x_47);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_16, 0);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_16);
x_51 = l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_14, x_49);
lean_dec(x_14);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_53 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_12);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_box(0);
x_58 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_49, x_52, x_52, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
lean_inc(x_49);
x_61 = l_Lean_MessageData_ofExpr(x_49);
x_62 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(7, 2, 0);
} else {
 x_63 = x_60;
 lean_ctor_set_tag(x_63, 7);
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_64);
lean_ctor_set(x_12, 0, x_63);
x_65 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_52, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_49, x_52, x_52, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
lean_dec(x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_49);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_69 = lean_ctor_get(x_51, 0);
lean_inc(x_69);
lean_dec(x_51);
x_70 = lean_box(0);
lean_ctor_set(x_12, 1, x_70);
lean_ctor_set(x_12, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_12);
lean_ctor_set(x_71, 1, x_50);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_12, 0);
x_77 = lean_ctor_get(x_12, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_78 = l_Lean_Meta_Canonicalizer_canon(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_76, x_79);
lean_dec(x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_81);
x_83 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_84 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_80);
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
x_89 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_79, x_83, x_83, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_87);
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
lean_inc(x_79);
x_92 = l_Lean_MessageData_ofExpr(x_79);
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
x_97 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_83, x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_79, x_83, x_83, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
lean_dec(x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_79);
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
if (lean_is_scalar(x_81)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_81;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_80);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_76);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_105 = lean_ctor_get(x_78, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_78, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_107 = x_78;
} else {
 lean_dec_ref(x_78);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
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
l_Lean_Elab_Tactic_Omega_State_atoms___default = _init_l_Lean_Elab_Tactic_Omega_State_atoms___default();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_State_atoms___default);
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__1);
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2);
l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3 = _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__3);
l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1 = _init_l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1();
lean_mark_persistent(l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1);
l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___closed__1 = _init_l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4___closed__1);
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
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9);
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
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55);
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
l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1);
l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1();
l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2);
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

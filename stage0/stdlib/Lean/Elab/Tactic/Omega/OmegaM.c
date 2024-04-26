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
static lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___closed__2;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__22;
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
lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__46;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_cfg___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms___boxed(lean_object*);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_13, x_18);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_4, x_20);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_OmegaM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
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
x_17 = l_Lean_Meta_Canonicalizer_CanonM_run___rarg(x_15, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
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
lean_dec(x_1);
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
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_1 = lean_mk_string_from_bytes("Int", 3);
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
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Omega", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Coeffs", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofList", 6);
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
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cast", 4);
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
x_1 = lean_mk_string_from_bytes("HAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HMul", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HSub", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HDiv", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HPow", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hPow", 4);
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
x_1 = lean_mk_string_from_bytes("hDiv", 4);
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
x_1 = lean_mk_string_from_bytes("hSub", 4);
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
x_1 = lean_mk_string_from_bytes("hMul", 4);
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
x_1 = lean_mk_string_from_bytes("hAdd", 4);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_nat_to_int(x_6);
x_12 = lean_nat_to_int(x_10);
x_13 = lean_apply_2(x_1, x_11, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_nat_to_int(x_6);
x_16 = lean_nat_to_int(x_14);
x_17 = lean_apply_2(x_1, x_15, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
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
x_1 = lean_mk_string_from_bytes("ite", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ite_disjunction", 15);
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
x_1 = lean_mk_string_from_bytes("HMod", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Min", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Max", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("max", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le_max_left", 11);
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
x_1 = lean_mk_string_from_bytes("le_max_right", 12);
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
x_1 = lean_mk_string_from_bytes("min", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("min_le_left", 11);
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
x_1 = lean_mk_string_from_bytes("min_le_right", 12);
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
x_1 = lean_mk_string_from_bytes("hMod", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("emod_ofNat_nonneg", 17);
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
x_1 = lean_mk_string_from_bytes("LT", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
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
x_1 = lean_mk_string_from_bytes("instLTNat", 9);
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
x_1 = lean_mk_string_from_bytes("pos_pow_of_pos", 14);
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
x_1 = lean_mk_string_from_bytes("ofNat_pos_of_pos", 16);
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
x_1 = lean_mk_string_from_bytes("emod_nonneg", 11);
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
x_1 = lean_mk_string_from_bytes("ne_of_gt", 8);
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
x_1 = lean_mk_string_from_bytes("emod_lt_of_pos", 14);
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
x_1 = lean_mk_string_from_bytes("Neg", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("neg", 3);
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
x_1 = lean_mk_string_from_bytes("instNegInt", 10);
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
x_1 = lean_mk_string_from_bytes("instLTInt", 9);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40;
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
x_1 = lean_mk_string_from_bytes("Ne", 2);
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
x_1 = lean_mk_string_from_bytes("mul_ediv_self_le", 16);
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
x_1 = lean_mk_string_from_bytes("lt_mul_ediv_self_add", 20);
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
x_1 = lean_mk_string_from_bytes("ofNat_nonneg", 12);
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
x_1 = lean_mk_string_from_bytes("Fin", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("BitVec", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isLt", 4);
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
x_1 = lean_mk_string_from_bytes("val", 3);
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
x_1 = lean_mk_string_from_bytes("natAbs", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le_natAbs", 9);
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
x_1 = lean_mk_string_from_bytes("neg_le_natAbs", 13);
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
x_1 = lean_mk_string_from_bytes("ofNat_sub_dichotomy", 19);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__2;
x_18 = lean_string_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_array_get_size(x_15);
x_22 = lean_unsigned_to_nat(5u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_fget(x_15, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_array_fget(x_15, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_array_fget(x_15, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_array_fget(x_15, x_32);
x_34 = lean_unsigned_to_nat(4u);
x_35 = lean_array_fget(x_15, x_34);
lean_dec(x_15);
x_36 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__3;
x_37 = lean_expr_eqv(x_27, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_38 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_11);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__7;
x_41 = l_Lean_mkApp5(x_40, x_27, x_29, x_31, x_33, x_35);
x_42 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_43 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_42, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_11);
return x_44;
}
}
}
}
case 1:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_dec(x_12);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_dec(x_14);
x_49 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_50 = lean_string_dec_eq(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
x_52 = lean_string_dec_eq(x_48, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__8;
x_54 = lean_string_dec_eq(x_48, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_55 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__9;
x_56 = lean_string_dec_eq(x_48, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__10;
x_58 = lean_string_dec_eq(x_48, x_57);
lean_dec(x_48);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_47);
lean_dec(x_46);
x_59 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_11);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__11;
x_62 = lean_string_dec_eq(x_47, x_61);
lean_dec(x_47);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_46);
x_63 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_11);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_array_get_size(x_46);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_46);
x_68 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_11);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_array_fget(x_46, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_array_fget(x_46, x_72);
lean_dec(x_46);
x_74 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__14;
lean_inc(x_73);
lean_inc(x_71);
x_75 = l_Lean_mkAppB(x_74, x_71, x_73);
x_76 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__17;
x_77 = l_Lean_mkAppB(x_76, x_71, x_73);
x_78 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_79 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_78, x_75);
x_80 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_79, x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_11);
return x_81;
}
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_48);
x_82 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__18;
x_83 = lean_string_dec_eq(x_47, x_82);
lean_dec(x_47);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_46);
x_84 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_11);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_array_get_size(x_46);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_eq(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_46);
x_89 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_11);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_array_fget(x_46, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_array_fget(x_46, x_93);
lean_dec(x_46);
x_95 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__21;
lean_inc(x_94);
lean_inc(x_92);
x_96 = l_Lean_mkAppB(x_95, x_92, x_94);
x_97 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24;
x_98 = l_Lean_mkAppB(x_97, x_92, x_94);
x_99 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_100 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_99, x_96);
x_101 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_100, x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_11);
return x_102;
}
}
}
}
else
{
lean_object* x_103; uint8_t x_104; 
lean_dec(x_48);
x_103 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__25;
x_104 = lean_string_dec_eq(x_47, x_103);
lean_dec(x_47);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_105 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_11);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_array_get_size(x_46);
x_108 = lean_unsigned_to_nat(6u);
x_109 = lean_nat_dec_eq(x_107, x_108);
lean_dec(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_110 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_11);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_unsigned_to_nat(4u);
x_113 = lean_array_fget(x_46, x_112);
x_114 = lean_unsigned_to_nat(5u);
x_115 = lean_array_fget(x_46, x_114);
lean_dec(x_46);
lean_inc(x_115);
x_116 = l_Lean_Expr_getAppFnArgs(x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 1)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 1)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
x_124 = lean_string_dec_eq(x_122, x_123);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = lean_string_dec_eq(x_122, x_49);
lean_dec(x_122);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_126 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_11);
return x_127;
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_129 = lean_string_dec_eq(x_121, x_128);
lean_dec(x_121);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_130 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_11);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_array_get_size(x_120);
x_133 = lean_unsigned_to_nat(3u);
x_134 = lean_nat_dec_eq(x_132, x_133);
lean_dec(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_135 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_11);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_array_fget(x_120, x_137);
if (lean_obj_tag(x_138) == 4)
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
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_144 = lean_string_dec_eq(x_142, x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_141);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_145 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_11);
return x_146;
}
else
{
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_unsigned_to_nat(2u);
x_148 = lean_array_fget(x_120, x_147);
lean_dec(x_120);
lean_inc(x_148);
x_149 = l_Lean_Expr_getAppFnArgs(x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 1)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 1)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
lean_dec(x_151);
x_156 = lean_string_dec_eq(x_155, x_123);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_157 = l_Lean_Expr_getAppFnArgs(x_113);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 1)
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
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_dec(x_158);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = lean_string_dec_eq(x_163, x_49);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_115);
x_165 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_11);
return x_166;
}
else
{
uint8_t x_167; 
x_167 = lean_string_dec_eq(x_162, x_128);
lean_dec(x_162);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_115);
x_168 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_11);
return x_169;
}
else
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_array_get_size(x_161);
x_171 = lean_nat_dec_eq(x_170, x_133);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_161);
lean_dec(x_115);
x_172 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_11);
return x_173;
}
else
{
lean_object* x_174; 
x_174 = lean_array_fget(x_161, x_137);
if (lean_obj_tag(x_174) == 4)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 1)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_179 = lean_string_dec_eq(x_178, x_143);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_177);
lean_dec(x_161);
lean_dec(x_115);
x_180 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_11);
return x_181;
}
else
{
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_array_fget(x_161, x_147);
lean_dec(x_161);
x_183 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_184 = l_Lean_mkAppB(x_183, x_182, x_115);
x_185 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_186 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_185, x_184);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_11);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_177);
lean_dec(x_161);
lean_dec(x_115);
x_188 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_11);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_161);
lean_dec(x_115);
x_190 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_11);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_161);
lean_dec(x_115);
x_192 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_11);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_174);
lean_dec(x_161);
lean_dec(x_115);
x_194 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_11);
return x_195;
}
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_115);
x_196 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_11);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_115);
x_198 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_11);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_115);
x_200 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_11);
return x_201;
}
}
else
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_203 = lean_string_dec_eq(x_154, x_202);
lean_dec(x_154);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_204 = l_Lean_Expr_getAppFnArgs(x_113);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 1)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 1)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 1);
lean_inc(x_208);
lean_dec(x_204);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_dec(x_206);
x_211 = lean_string_dec_eq(x_210, x_49);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_115);
x_212 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_11);
return x_213;
}
else
{
uint8_t x_214; 
x_214 = lean_string_dec_eq(x_209, x_128);
lean_dec(x_209);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_208);
lean_dec(x_115);
x_215 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_11);
return x_216;
}
else
{
lean_object* x_217; uint8_t x_218; 
x_217 = lean_array_get_size(x_208);
x_218 = lean_nat_dec_eq(x_217, x_133);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_208);
lean_dec(x_115);
x_219 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_11);
return x_220;
}
else
{
lean_object* x_221; 
x_221 = lean_array_fget(x_208, x_137);
if (lean_obj_tag(x_221) == 4)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 1)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_string_dec_eq(x_225, x_143);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_224);
lean_dec(x_208);
lean_dec(x_115);
x_227 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_11);
return x_228;
}
else
{
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = lean_array_fget(x_208, x_147);
lean_dec(x_208);
x_230 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_231 = l_Lean_mkAppB(x_230, x_229, x_115);
x_232 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_233 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_232, x_231);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_11);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_224);
lean_dec(x_208);
lean_dec(x_115);
x_235 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_11);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_208);
lean_dec(x_115);
x_237 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_11);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_208);
lean_dec(x_115);
x_239 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_11);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_221);
lean_dec(x_208);
lean_dec(x_115);
x_241 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_11);
return x_242;
}
}
}
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_115);
x_243 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_11);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_115);
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
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_115);
x_247 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_11);
return x_248;
}
}
else
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_array_get_size(x_153);
x_250 = lean_nat_dec_eq(x_249, x_108);
lean_dec(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_251 = l_Lean_Expr_getAppFnArgs(x_113);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 1)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 1)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_255 = lean_ctor_get(x_251, 1);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_ctor_get(x_252, 1);
lean_inc(x_256);
lean_dec(x_252);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
lean_dec(x_253);
x_258 = lean_string_dec_eq(x_257, x_49);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_115);
x_259 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_11);
return x_260;
}
else
{
uint8_t x_261; 
x_261 = lean_string_dec_eq(x_256, x_128);
lean_dec(x_256);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_255);
lean_dec(x_115);
x_262 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_11);
return x_263;
}
else
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_array_get_size(x_255);
x_265 = lean_nat_dec_eq(x_264, x_133);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_255);
lean_dec(x_115);
x_266 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_11);
return x_267;
}
else
{
lean_object* x_268; 
x_268 = lean_array_fget(x_255, x_137);
if (lean_obj_tag(x_268) == 4)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
if (lean_obj_tag(x_269) == 1)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_string_dec_eq(x_272, x_143);
lean_dec(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_271);
lean_dec(x_255);
lean_dec(x_115);
x_274 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_11);
return x_275;
}
else
{
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_276 = lean_array_fget(x_255, x_147);
lean_dec(x_255);
x_277 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_278 = l_Lean_mkAppB(x_277, x_276, x_115);
x_279 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_280 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_279, x_278);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_11);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_271);
lean_dec(x_255);
lean_dec(x_115);
x_282 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_11);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_255);
lean_dec(x_115);
x_284 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_11);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_255);
lean_dec(x_115);
x_286 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_11);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_268);
lean_dec(x_255);
lean_dec(x_115);
x_288 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_11);
return x_289;
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_115);
x_290 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_11);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_115);
x_292 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_11);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_115);
x_294 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_11);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_array_fget(x_153, x_112);
x_297 = lean_array_fget(x_153, x_114);
lean_dec(x_153);
lean_inc(x_296);
x_298 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_296);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_299 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_11);
return x_300;
}
else
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_ctor_get(x_298, 0);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_nat_dec_eq(x_301, x_137);
lean_dec(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_303 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_304 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_305 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
x_306 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
lean_inc(x_296);
x_307 = l_Lean_mkApp4(x_303, x_304, x_305, x_306, x_296);
x_308 = l_Lean_Meta_mkDecideProof(x_307, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_312 = l_Lean_mkApp3(x_311, x_296, x_297, x_310);
x_313 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_314 = l_Lean_mkAppB(x_313, x_148, x_312);
x_315 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_inc(x_314);
lean_inc(x_115);
lean_inc(x_113);
x_316 = l_Lean_mkApp3(x_315, x_113, x_115, x_314);
x_317 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_318 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_319 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
lean_inc(x_115);
x_320 = l_Lean_mkApp3(x_318, x_115, x_319, x_314);
x_321 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_322 = l_Lean_mkApp3(x_321, x_113, x_115, x_320);
x_323 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_324 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_323, x_322);
x_325 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_324, x_316);
lean_ctor_set(x_308, 0, x_325);
return x_308;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_326 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_327 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_115);
x_328 = l_Lean_mkApp3(x_326, x_115, x_327, x_314);
x_329 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_330 = l_Lean_mkApp3(x_329, x_113, x_115, x_328);
x_331 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_332 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_331, x_330);
x_333 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_332, x_316);
lean_ctor_set(x_308, 0, x_333);
return x_308;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_334 = lean_ctor_get(x_308, 0);
x_335 = lean_ctor_get(x_308, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_308);
x_336 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_337 = l_Lean_mkApp3(x_336, x_296, x_297, x_334);
x_338 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_339 = l_Lean_mkAppB(x_338, x_148, x_337);
x_340 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
lean_inc(x_339);
lean_inc(x_115);
lean_inc(x_113);
x_341 = l_Lean_mkApp3(x_340, x_113, x_115, x_339);
x_342 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_343 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_344 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
lean_inc(x_115);
x_345 = l_Lean_mkApp3(x_343, x_115, x_344, x_339);
x_346 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_347 = l_Lean_mkApp3(x_346, x_113, x_115, x_345);
x_348 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_349 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_348, x_347);
x_350 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_349, x_341);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_335);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_352 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
x_353 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_115);
x_354 = l_Lean_mkApp3(x_352, x_115, x_353, x_339);
x_355 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_356 = l_Lean_mkApp3(x_355, x_113, x_115, x_354);
x_357 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_358 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_357, x_356);
x_359 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_358, x_341);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_335);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
x_361 = !lean_is_exclusive(x_308);
if (x_361 == 0)
{
return x_308;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_308, 0);
x_363 = lean_ctor_get(x_308, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_308);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_365 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_11);
return x_366;
}
}
}
}
}
}
else
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_367 = l_Lean_Expr_getAppFnArgs(x_113);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 1)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
if (lean_obj_tag(x_369) == 1)
{
lean_object* x_370; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_371 = lean_ctor_get(x_367, 1);
lean_inc(x_371);
lean_dec(x_367);
x_372 = lean_ctor_get(x_368, 1);
lean_inc(x_372);
lean_dec(x_368);
x_373 = lean_ctor_get(x_369, 1);
lean_inc(x_373);
lean_dec(x_369);
x_374 = lean_string_dec_eq(x_373, x_49);
lean_dec(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_115);
x_375 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_11);
return x_376;
}
else
{
uint8_t x_377; 
x_377 = lean_string_dec_eq(x_372, x_128);
lean_dec(x_372);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; 
lean_dec(x_371);
lean_dec(x_115);
x_378 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_11);
return x_379;
}
else
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_array_get_size(x_371);
x_381 = lean_nat_dec_eq(x_380, x_133);
lean_dec(x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_371);
lean_dec(x_115);
x_382 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_11);
return x_383;
}
else
{
lean_object* x_384; 
x_384 = lean_array_fget(x_371, x_137);
if (lean_obj_tag(x_384) == 4)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
if (lean_obj_tag(x_385) == 1)
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_387 = lean_ctor_get(x_384, 1);
lean_inc(x_387);
lean_dec(x_384);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_dec(x_385);
x_389 = lean_string_dec_eq(x_388, x_143);
lean_dec(x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_387);
lean_dec(x_371);
lean_dec(x_115);
x_390 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_11);
return x_391;
}
else
{
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_392 = lean_array_fget(x_371, x_147);
lean_dec(x_371);
x_393 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_394 = l_Lean_mkAppB(x_393, x_392, x_115);
x_395 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_396 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_395, x_394);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_11);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; 
lean_dec(x_387);
lean_dec(x_371);
lean_dec(x_115);
x_398 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_11);
return x_399;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_371);
lean_dec(x_115);
x_400 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_11);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_371);
lean_dec(x_115);
x_402 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_11);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_384);
lean_dec(x_371);
lean_dec(x_115);
x_404 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_11);
return x_405;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_115);
x_406 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_11);
return x_407;
}
}
else
{
lean_object* x_408; lean_object* x_409; 
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_115);
x_408 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_11);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_115);
x_410 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_11);
return x_411;
}
}
}
else
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_412 = l_Lean_Expr_getAppFnArgs(x_113);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
if (lean_obj_tag(x_413) == 1)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_obj_tag(x_414) == 1)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_416 = lean_ctor_get(x_412, 1);
lean_inc(x_416);
lean_dec(x_412);
x_417 = lean_ctor_get(x_413, 1);
lean_inc(x_417);
lean_dec(x_413);
x_418 = lean_ctor_get(x_414, 1);
lean_inc(x_418);
lean_dec(x_414);
x_419 = lean_string_dec_eq(x_418, x_49);
lean_dec(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; 
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_115);
x_420 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_11);
return x_421;
}
else
{
uint8_t x_422; 
x_422 = lean_string_dec_eq(x_417, x_128);
lean_dec(x_417);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; 
lean_dec(x_416);
lean_dec(x_115);
x_423 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_11);
return x_424;
}
else
{
lean_object* x_425; uint8_t x_426; 
x_425 = lean_array_get_size(x_416);
x_426 = lean_nat_dec_eq(x_425, x_133);
lean_dec(x_425);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_416);
lean_dec(x_115);
x_427 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_11);
return x_428;
}
else
{
lean_object* x_429; 
x_429 = lean_array_fget(x_416, x_137);
if (lean_obj_tag(x_429) == 4)
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
lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_432 = lean_ctor_get(x_429, 1);
lean_inc(x_432);
lean_dec(x_429);
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
lean_dec(x_430);
x_434 = lean_string_dec_eq(x_433, x_143);
lean_dec(x_433);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_432);
lean_dec(x_416);
lean_dec(x_115);
x_435 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_11);
return x_436;
}
else
{
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_437 = lean_array_fget(x_416, x_147);
lean_dec(x_416);
x_438 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_439 = l_Lean_mkAppB(x_438, x_437, x_115);
x_440 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_441 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_440, x_439);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_11);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_432);
lean_dec(x_416);
lean_dec(x_115);
x_443 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_11);
return x_444;
}
}
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_416);
lean_dec(x_115);
x_445 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_11);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_416);
lean_dec(x_115);
x_447 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_11);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_429);
lean_dec(x_416);
lean_dec(x_115);
x_449 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_11);
return x_450;
}
}
}
}
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_115);
x_451 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_11);
return x_452;
}
}
else
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_115);
x_453 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_11);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_115);
x_455 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_11);
return x_456;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_457 = l_Lean_Expr_getAppFnArgs(x_113);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
if (lean_obj_tag(x_458) == 1)
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 1)
{
lean_object* x_460; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; 
x_461 = lean_ctor_get(x_457, 1);
lean_inc(x_461);
lean_dec(x_457);
x_462 = lean_ctor_get(x_458, 1);
lean_inc(x_462);
lean_dec(x_458);
x_463 = lean_ctor_get(x_459, 1);
lean_inc(x_463);
lean_dec(x_459);
x_464 = lean_string_dec_eq(x_463, x_49);
lean_dec(x_463);
if (x_464 == 0)
{
lean_object* x_465; lean_object* x_466; 
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_115);
x_465 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_11);
return x_466;
}
else
{
uint8_t x_467; 
x_467 = lean_string_dec_eq(x_462, x_128);
lean_dec(x_462);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_461);
lean_dec(x_115);
x_468 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_11);
return x_469;
}
else
{
lean_object* x_470; uint8_t x_471; 
x_470 = lean_array_get_size(x_461);
x_471 = lean_nat_dec_eq(x_470, x_133);
lean_dec(x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; 
lean_dec(x_461);
lean_dec(x_115);
x_472 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_11);
return x_473;
}
else
{
lean_object* x_474; 
x_474 = lean_array_fget(x_461, x_137);
if (lean_obj_tag(x_474) == 4)
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 1)
{
lean_object* x_476; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_477 = lean_ctor_get(x_474, 1);
lean_inc(x_477);
lean_dec(x_474);
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_dec(x_475);
x_479 = lean_string_dec_eq(x_478, x_143);
lean_dec(x_478);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_477);
lean_dec(x_461);
lean_dec(x_115);
x_480 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_11);
return x_481;
}
else
{
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_482 = lean_array_fget(x_461, x_147);
lean_dec(x_461);
x_483 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_484 = l_Lean_mkAppB(x_483, x_482, x_115);
x_485 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_486 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_485, x_484);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_11);
return x_487;
}
else
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_477);
lean_dec(x_461);
lean_dec(x_115);
x_488 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_11);
return x_489;
}
}
}
else
{
lean_object* x_490; lean_object* x_491; 
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_461);
lean_dec(x_115);
x_490 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_11);
return x_491;
}
}
else
{
lean_object* x_492; lean_object* x_493; 
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_461);
lean_dec(x_115);
x_492 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_11);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; 
lean_dec(x_474);
lean_dec(x_461);
lean_dec(x_115);
x_494 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_11);
return x_495;
}
}
}
}
}
else
{
lean_object* x_496; lean_object* x_497; 
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_115);
x_496 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_11);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; 
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_115);
x_498 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_11);
return x_499;
}
}
else
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_115);
x_500 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_11);
return x_501;
}
}
}
else
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_141);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_502 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_11);
return x_503;
}
}
}
else
{
lean_object* x_504; lean_object* x_505; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_504 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_11);
return x_505;
}
}
else
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_506 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_11);
return x_507;
}
}
else
{
lean_object* x_508; lean_object* x_509; 
lean_dec(x_138);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_508 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_11);
return x_509;
}
}
}
}
}
else
{
lean_object* x_510; uint8_t x_511; 
lean_dec(x_122);
x_510 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_511 = lean_string_dec_eq(x_121, x_510);
lean_dec(x_121);
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_512 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_11);
return x_513;
}
else
{
lean_object* x_514; uint8_t x_515; 
x_514 = lean_array_get_size(x_120);
x_515 = lean_nat_dec_eq(x_514, x_108);
lean_dec(x_514);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_516 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_11);
return x_517;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_array_fget(x_120, x_112);
x_519 = lean_array_fget(x_120, x_114);
lean_dec(x_120);
lean_inc(x_518);
x_520 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_518);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_521 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_11);
return x_522;
}
else
{
lean_object* x_523; lean_object* x_524; uint8_t x_525; 
x_523 = lean_ctor_get(x_520, 0);
lean_inc(x_523);
lean_dec(x_520);
x_524 = lean_unsigned_to_nat(0u);
x_525 = lean_nat_dec_eq(x_523, x_524);
lean_dec(x_523);
if (x_525 == 0)
{
lean_object* x_526; uint8_t x_564; 
x_564 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_564 == 0)
{
lean_object* x_565; 
x_565 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76;
x_526 = x_565;
goto block_563;
}
else
{
lean_object* x_566; 
x_566 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_526 = x_566;
goto block_563;
}
block_563:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_527 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
x_528 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_529 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
lean_inc(x_518);
lean_inc(x_526);
x_530 = l_Lean_mkApp4(x_527, x_528, x_529, x_526, x_518);
x_531 = l_Lean_Meta_mkDecideProof(x_530, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_531) == 0)
{
uint8_t x_532; 
x_532 = !lean_is_exclusive(x_531);
if (x_532 == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_533 = lean_ctor_get(x_531, 0);
x_534 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
x_535 = l_Lean_mkApp3(x_534, x_518, x_519, x_533);
x_536 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
lean_inc(x_535);
lean_inc(x_115);
x_537 = l_Lean_mkApp3(x_536, x_115, x_526, x_535);
x_538 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_115);
lean_inc(x_113);
x_539 = l_Lean_mkApp3(x_538, x_113, x_115, x_537);
x_540 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_541 = l_Lean_mkApp3(x_540, x_113, x_115, x_535);
x_542 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_543 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_542, x_539);
x_544 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_543, x_541);
lean_ctor_set(x_531, 0, x_544);
return x_531;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_545 = lean_ctor_get(x_531, 0);
x_546 = lean_ctor_get(x_531, 1);
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_531);
x_547 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
x_548 = l_Lean_mkApp3(x_547, x_518, x_519, x_545);
x_549 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51;
lean_inc(x_548);
lean_inc(x_115);
x_550 = l_Lean_mkApp3(x_549, x_115, x_526, x_548);
x_551 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_115);
lean_inc(x_113);
x_552 = l_Lean_mkApp3(x_551, x_113, x_115, x_550);
x_553 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_554 = l_Lean_mkApp3(x_553, x_113, x_115, x_548);
x_555 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_556 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_555, x_552);
x_557 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_556, x_554);
x_558 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_546);
return x_558;
}
}
else
{
uint8_t x_559; 
lean_dec(x_526);
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_115);
lean_dec(x_113);
x_559 = !lean_is_exclusive(x_531);
if (x_559 == 0)
{
return x_531;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_531, 0);
x_561 = lean_ctor_get(x_531, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_531);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
}
}
else
{
lean_object* x_567; lean_object* x_568; 
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_567 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_11);
return x_568;
}
}
}
}
}
}
else
{
lean_object* x_569; lean_object* x_570; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_569 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_11);
return x_570;
}
}
else
{
lean_object* x_571; lean_object* x_572; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_571 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_11);
return x_572;
}
}
else
{
lean_object* x_573; lean_object* x_574; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_573 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_11);
return x_574;
}
}
}
}
}
else
{
lean_object* x_575; uint8_t x_576; 
lean_dec(x_48);
x_575 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_576 = lean_string_dec_eq(x_47, x_575);
lean_dec(x_47);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_577 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_11);
return x_578;
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_579 = lean_array_get_size(x_46);
x_580 = lean_unsigned_to_nat(6u);
x_581 = lean_nat_dec_eq(x_579, x_580);
lean_dec(x_579);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_582 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_583 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_583, 0, x_582);
lean_ctor_set(x_583, 1, x_11);
return x_583;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_584 = lean_unsigned_to_nat(4u);
x_585 = lean_array_fget(x_46, x_584);
x_586 = lean_unsigned_to_nat(5u);
x_587 = lean_array_fget(x_46, x_586);
lean_dec(x_46);
lean_inc(x_587);
x_588 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_587);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; 
lean_dec(x_587);
lean_dec(x_585);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_589 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_11);
return x_590;
}
else
{
lean_object* x_591; lean_object* x_592; uint8_t x_593; 
x_591 = lean_ctor_get(x_588, 0);
lean_inc(x_591);
lean_dec(x_588);
x_592 = lean_unsigned_to_nat(0u);
x_593 = lean_nat_dec_eq(x_591, x_592);
lean_dec(x_591);
if (x_593 == 0)
{
lean_object* x_594; uint8_t x_633; 
x_633 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
if (x_633 == 0)
{
lean_object* x_634; 
x_634 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90;
x_594 = x_634;
goto block_632;
}
else
{
lean_object* x_635; 
x_635 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
x_594 = x_635;
goto block_632;
}
block_632:
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_595 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
x_596 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
lean_inc(x_594);
lean_inc(x_587);
x_597 = l_Lean_mkApp3(x_595, x_596, x_587, x_594);
x_598 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
x_599 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
lean_inc(x_587);
x_600 = l_Lean_mkApp4(x_598, x_596, x_599, x_594, x_587);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_601 = l_Lean_Meta_mkDecideProof(x_597, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = l_Lean_Meta_mkDecideProof(x_600, x_7, x_8, x_9, x_10, x_603);
if (lean_obj_tag(x_604) == 0)
{
uint8_t x_605; 
x_605 = !lean_is_exclusive(x_604);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_606 = lean_ctor_get(x_604, 0);
x_607 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
lean_inc(x_587);
lean_inc(x_585);
x_608 = l_Lean_mkApp3(x_607, x_585, x_587, x_602);
x_609 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88;
x_610 = l_Lean_mkApp3(x_609, x_585, x_587, x_606);
x_611 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_612 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_611, x_608);
x_613 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_612, x_610);
lean_ctor_set(x_604, 0, x_613);
return x_604;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_614 = lean_ctor_get(x_604, 0);
x_615 = lean_ctor_get(x_604, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_604);
x_616 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
lean_inc(x_587);
lean_inc(x_585);
x_617 = l_Lean_mkApp3(x_616, x_585, x_587, x_602);
x_618 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88;
x_619 = l_Lean_mkApp3(x_618, x_585, x_587, x_614);
x_620 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_621 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_620, x_617);
x_622 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_621, x_619);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_615);
return x_623;
}
}
else
{
uint8_t x_624; 
lean_dec(x_602);
lean_dec(x_587);
lean_dec(x_585);
x_624 = !lean_is_exclusive(x_604);
if (x_624 == 0)
{
return x_604;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_604, 0);
x_626 = lean_ctor_get(x_604, 1);
lean_inc(x_626);
lean_inc(x_625);
lean_dec(x_604);
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_625);
lean_ctor_set(x_627, 1, x_626);
return x_627;
}
}
}
else
{
uint8_t x_628; 
lean_dec(x_600);
lean_dec(x_587);
lean_dec(x_585);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_628 = !lean_is_exclusive(x_601);
if (x_628 == 0)
{
return x_601;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_601, 0);
x_630 = lean_ctor_get(x_601, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_601);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
}
else
{
lean_object* x_636; lean_object* x_637; 
lean_dec(x_587);
lean_dec(x_585);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_636 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_637 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_11);
return x_637;
}
}
}
}
}
}
else
{
lean_object* x_638; uint8_t x_639; 
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_638 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_639 = lean_string_dec_eq(x_47, x_638);
lean_dec(x_47);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; 
lean_dec(x_46);
x_640 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_11);
return x_641;
}
else
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; 
x_642 = lean_array_get_size(x_46);
x_643 = lean_unsigned_to_nat(3u);
x_644 = lean_nat_dec_eq(x_642, x_643);
lean_dec(x_642);
if (x_644 == 0)
{
lean_object* x_645; lean_object* x_646; 
lean_dec(x_46);
x_645 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_11);
return x_646;
}
else
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_unsigned_to_nat(0u);
x_648 = lean_array_fget(x_46, x_647);
if (lean_obj_tag(x_648) == 4)
{
lean_object* x_649; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
if (lean_obj_tag(x_649) == 1)
{
lean_object* x_650; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; 
x_651 = lean_ctor_get(x_648, 1);
lean_inc(x_651);
lean_dec(x_648);
x_652 = lean_ctor_get(x_649, 1);
lean_inc(x_652);
lean_dec(x_649);
x_653 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_654 = lean_string_dec_eq(x_652, x_653);
lean_dec(x_652);
if (x_654 == 0)
{
lean_object* x_655; lean_object* x_656; 
lean_dec(x_651);
lean_dec(x_46);
x_655 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_11);
return x_656;
}
else
{
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; lean_object* x_664; 
x_657 = lean_unsigned_to_nat(2u);
x_658 = lean_array_fget(x_46, x_657);
lean_dec(x_46);
x_659 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93;
lean_inc(x_658);
x_660 = l_Lean_Expr_app___override(x_659, x_658);
x_661 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_662 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_661, x_660);
x_663 = lean_ctor_get_uint8(x_4, 1);
x_664 = l_Lean_Expr_getAppFnArgs(x_658);
if (x_663 == 0)
{
lean_object* x_665; 
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
lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; 
x_668 = lean_ctor_get(x_664, 1);
lean_inc(x_668);
lean_dec(x_664);
x_669 = lean_ctor_get(x_665, 1);
lean_inc(x_669);
lean_dec(x_665);
x_670 = lean_ctor_get(x_666, 1);
lean_inc(x_670);
lean_dec(x_666);
x_671 = lean_string_dec_eq(x_670, x_653);
if (x_671 == 0)
{
lean_object* x_672; uint8_t x_673; 
x_672 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_673 = lean_string_dec_eq(x_670, x_672);
if (x_673 == 0)
{
lean_object* x_674; uint8_t x_675; 
x_674 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_675 = lean_string_dec_eq(x_670, x_674);
lean_dec(x_670);
if (x_675 == 0)
{
lean_object* x_676; 
lean_dec(x_669);
lean_dec(x_668);
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_662);
lean_ctor_set(x_676, 1, x_11);
return x_676;
}
else
{
lean_object* x_677; uint8_t x_678; 
x_677 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_678 = lean_string_dec_eq(x_669, x_677);
lean_dec(x_669);
if (x_678 == 0)
{
lean_object* x_679; 
lean_dec(x_668);
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_662);
lean_ctor_set(x_679, 1, x_11);
return x_679;
}
else
{
lean_object* x_680; uint8_t x_681; 
x_680 = lean_array_get_size(x_668);
x_681 = lean_nat_dec_eq(x_680, x_657);
lean_dec(x_680);
if (x_681 == 0)
{
lean_object* x_682; 
lean_dec(x_668);
x_682 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_682, 0, x_662);
lean_ctor_set(x_682, 1, x_11);
return x_682;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_683 = lean_array_fget(x_668, x_647);
x_684 = lean_unsigned_to_nat(1u);
x_685 = lean_array_fget(x_668, x_684);
lean_dec(x_668);
x_686 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_687 = l_Lean_mkAppB(x_686, x_683, x_685);
x_688 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_662, x_687);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_11);
return x_689;
}
}
}
}
else
{
lean_object* x_690; uint8_t x_691; 
lean_dec(x_670);
x_690 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_691 = lean_string_dec_eq(x_669, x_690);
lean_dec(x_669);
if (x_691 == 0)
{
lean_object* x_692; 
lean_dec(x_668);
x_692 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_692, 0, x_662);
lean_ctor_set(x_692, 1, x_11);
return x_692;
}
else
{
lean_object* x_693; uint8_t x_694; 
x_693 = lean_array_get_size(x_668);
x_694 = lean_nat_dec_eq(x_693, x_657);
lean_dec(x_693);
if (x_694 == 0)
{
lean_object* x_695; 
lean_dec(x_668);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_662);
lean_ctor_set(x_695, 1, x_11);
return x_695;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_696 = lean_array_fget(x_668, x_647);
x_697 = lean_unsigned_to_nat(1u);
x_698 = lean_array_fget(x_668, x_697);
lean_dec(x_668);
x_699 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_700 = l_Lean_mkAppB(x_699, x_696, x_698);
x_701 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_662, x_700);
x_702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_702, 0, x_701);
lean_ctor_set(x_702, 1, x_11);
return x_702;
}
}
}
}
else
{
lean_object* x_703; uint8_t x_704; 
lean_dec(x_670);
x_703 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_704 = lean_string_dec_eq(x_669, x_703);
lean_dec(x_669);
if (x_704 == 0)
{
lean_object* x_705; 
lean_dec(x_668);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_662);
lean_ctor_set(x_705, 1, x_11);
return x_705;
}
else
{
lean_object* x_706; lean_object* x_707; uint8_t x_708; 
x_706 = lean_array_get_size(x_668);
x_707 = lean_unsigned_to_nat(1u);
x_708 = lean_nat_dec_eq(x_706, x_707);
lean_dec(x_706);
if (x_708 == 0)
{
lean_object* x_709; 
lean_dec(x_668);
x_709 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_709, 0, x_662);
lean_ctor_set(x_709, 1, x_11);
return x_709;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_710 = lean_array_fget(x_668, x_647);
lean_dec(x_668);
x_711 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_710);
x_712 = l_Lean_Expr_app___override(x_711, x_710);
x_713 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_714 = l_Lean_Expr_app___override(x_713, x_710);
x_715 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_662, x_712);
x_716 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_715, x_714);
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_11);
return x_717;
}
}
}
}
else
{
lean_object* x_718; 
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_662);
lean_ctor_set(x_718, 1, x_11);
return x_718;
}
}
else
{
lean_object* x_719; 
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_662);
lean_ctor_set(x_719, 1, x_11);
return x_719;
}
}
else
{
lean_object* x_720; 
lean_dec(x_665);
lean_dec(x_664);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_662);
lean_ctor_set(x_720, 1, x_11);
return x_720;
}
}
else
{
lean_object* x_721; 
x_721 = lean_ctor_get(x_664, 0);
lean_inc(x_721);
if (lean_obj_tag(x_721) == 1)
{
lean_object* x_722; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
if (lean_obj_tag(x_722) == 1)
{
lean_object* x_723; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; uint8_t x_728; 
x_724 = lean_ctor_get(x_664, 1);
lean_inc(x_724);
lean_dec(x_664);
x_725 = lean_ctor_get(x_721, 1);
lean_inc(x_725);
lean_dec(x_721);
x_726 = lean_ctor_get(x_722, 1);
lean_inc(x_726);
lean_dec(x_722);
x_727 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_728 = lean_string_dec_eq(x_726, x_727);
if (x_728 == 0)
{
uint8_t x_729; 
x_729 = lean_string_dec_eq(x_726, x_653);
if (x_729 == 0)
{
lean_object* x_730; uint8_t x_731; 
x_730 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_731 = lean_string_dec_eq(x_726, x_730);
if (x_731 == 0)
{
lean_object* x_732; uint8_t x_733; 
x_732 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_733 = lean_string_dec_eq(x_726, x_732);
lean_dec(x_726);
if (x_733 == 0)
{
lean_object* x_734; 
lean_dec(x_725);
lean_dec(x_724);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_662);
lean_ctor_set(x_734, 1, x_11);
return x_734;
}
else
{
lean_object* x_735; uint8_t x_736; 
x_735 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_736 = lean_string_dec_eq(x_725, x_735);
lean_dec(x_725);
if (x_736 == 0)
{
lean_object* x_737; 
lean_dec(x_724);
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_662);
lean_ctor_set(x_737, 1, x_11);
return x_737;
}
else
{
lean_object* x_738; uint8_t x_739; 
x_738 = lean_array_get_size(x_724);
x_739 = lean_nat_dec_eq(x_738, x_657);
lean_dec(x_738);
if (x_739 == 0)
{
lean_object* x_740; 
lean_dec(x_724);
x_740 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_740, 0, x_662);
lean_ctor_set(x_740, 1, x_11);
return x_740;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_741 = lean_array_fget(x_724, x_647);
x_742 = lean_unsigned_to_nat(1u);
x_743 = lean_array_fget(x_724, x_742);
lean_dec(x_724);
x_744 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_745 = l_Lean_mkAppB(x_744, x_741, x_743);
x_746 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_662, x_745);
x_747 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_11);
return x_747;
}
}
}
}
else
{
lean_object* x_748; uint8_t x_749; 
lean_dec(x_726);
x_748 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_749 = lean_string_dec_eq(x_725, x_748);
lean_dec(x_725);
if (x_749 == 0)
{
lean_object* x_750; 
lean_dec(x_724);
x_750 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_750, 0, x_662);
lean_ctor_set(x_750, 1, x_11);
return x_750;
}
else
{
lean_object* x_751; uint8_t x_752; 
x_751 = lean_array_get_size(x_724);
x_752 = lean_nat_dec_eq(x_751, x_657);
lean_dec(x_751);
if (x_752 == 0)
{
lean_object* x_753; 
lean_dec(x_724);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_662);
lean_ctor_set(x_753, 1, x_11);
return x_753;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_754 = lean_array_fget(x_724, x_647);
x_755 = lean_unsigned_to_nat(1u);
x_756 = lean_array_fget(x_724, x_755);
lean_dec(x_724);
x_757 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102;
x_758 = l_Lean_mkAppB(x_757, x_754, x_756);
x_759 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_662, x_758);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_11);
return x_760;
}
}
}
}
else
{
lean_object* x_761; uint8_t x_762; 
lean_dec(x_726);
x_761 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
x_762 = lean_string_dec_eq(x_725, x_761);
lean_dec(x_725);
if (x_762 == 0)
{
lean_object* x_763; 
lean_dec(x_724);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_662);
lean_ctor_set(x_763, 1, x_11);
return x_763;
}
else
{
lean_object* x_764; lean_object* x_765; uint8_t x_766; 
x_764 = lean_array_get_size(x_724);
x_765 = lean_unsigned_to_nat(1u);
x_766 = lean_nat_dec_eq(x_764, x_765);
lean_dec(x_764);
if (x_766 == 0)
{
lean_object* x_767; 
lean_dec(x_724);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_662);
lean_ctor_set(x_767, 1, x_11);
return x_767;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_768 = lean_array_fget(x_724, x_647);
lean_dec(x_724);
x_769 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
lean_inc(x_768);
x_770 = l_Lean_Expr_app___override(x_769, x_768);
x_771 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_772 = l_Lean_Expr_app___override(x_771, x_768);
x_773 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_662, x_770);
x_774 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_773, x_772);
x_775 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_775, 0, x_774);
lean_ctor_set(x_775, 1, x_11);
return x_775;
}
}
}
}
else
{
lean_object* x_776; uint8_t x_777; 
lean_dec(x_726);
x_776 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
x_777 = lean_string_dec_eq(x_725, x_776);
lean_dec(x_725);
if (x_777 == 0)
{
lean_object* x_778; 
lean_dec(x_724);
x_778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_778, 0, x_662);
lean_ctor_set(x_778, 1, x_11);
return x_778;
}
else
{
lean_object* x_779; lean_object* x_780; uint8_t x_781; 
x_779 = lean_array_get_size(x_724);
x_780 = lean_unsigned_to_nat(6u);
x_781 = lean_nat_dec_eq(x_779, x_780);
lean_dec(x_779);
if (x_781 == 0)
{
lean_object* x_782; 
lean_dec(x_724);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_662);
lean_ctor_set(x_782, 1, x_11);
return x_782;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_783 = lean_unsigned_to_nat(4u);
x_784 = lean_array_fget(x_724, x_783);
x_785 = lean_unsigned_to_nat(5u);
x_786 = lean_array_fget(x_724, x_785);
lean_dec(x_724);
x_787 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__112;
x_788 = l_Lean_mkAppB(x_787, x_784, x_786);
x_789 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_662, x_788);
x_790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_11);
return x_790;
}
}
}
}
else
{
lean_object* x_791; 
lean_dec(x_723);
lean_dec(x_722);
lean_dec(x_721);
lean_dec(x_664);
x_791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_791, 0, x_662);
lean_ctor_set(x_791, 1, x_11);
return x_791;
}
}
else
{
lean_object* x_792; 
lean_dec(x_722);
lean_dec(x_721);
lean_dec(x_664);
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_662);
lean_ctor_set(x_792, 1, x_11);
return x_792;
}
}
else
{
lean_object* x_793; 
lean_dec(x_721);
lean_dec(x_664);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_662);
lean_ctor_set(x_793, 1, x_11);
return x_793;
}
}
}
else
{
lean_object* x_794; lean_object* x_795; 
lean_dec(x_651);
lean_dec(x_46);
x_794 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_795 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_11);
return x_795;
}
}
}
else
{
lean_object* x_796; lean_object* x_797; 
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_46);
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
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_46);
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
lean_dec(x_648);
lean_dec(x_46);
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
else
{
lean_object* x_802; lean_object* x_803; 
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_802 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_803 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_11);
return x_803;
}
}
default: 
{
lean_object* x_804; lean_object* x_805; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_804 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_805 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_11);
return x_805;
}
}
}
else
{
lean_object* x_806; lean_object* x_807; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_806 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_11);
return x_807;
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
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Expr_hash(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Elab_Tactic_Omega_lookup___spec__6(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Elab_Tactic_Omega_lookup___spec__9(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_Omega_lookup___spec__12(x_3, x_8, x_9, x_2);
lean_dec(x_3);
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
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_18, 3);
x_22 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1;
x_23 = 0;
x_24 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_PersistentArray_push___rarg(x_21, x_28);
lean_ctor_set(x_18, 3, x_29);
x_30 = lean_st_ref_set(x_11, x_18, x_19);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; double x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
x_39 = lean_ctor_get(x_18, 2);
x_40 = lean_ctor_get(x_18, 3);
x_41 = lean_ctor_get(x_18, 4);
x_42 = lean_ctor_get(x_18, 5);
x_43 = lean_ctor_get(x_18, 6);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_44 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__1;
x_45 = 0;
x_46 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14___closed__2;
x_47 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_float(x_47, sizeof(void*)*2, x_44);
lean_ctor_set_float(x_47, sizeof(void*)*2 + 8, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 16, x_45);
x_48 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_49 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_15);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_13);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_13);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_PersistentArray_push___rarg(x_40, x_50);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_38);
lean_ctor_set(x_52, 2, x_39);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_41);
lean_ctor_set(x_52, 5, x_42);
lean_ctor_set(x_52, 6, x_43);
x_53 = lean_st_ref_set(x_11, x_52, x_19);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_st_ref_take(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_inc(x_17);
x_18 = l_Lean_HashMap_insert___at_Lean_Elab_Tactic_Omega_lookup___spec__4(x_15, x_1, x_17);
x_19 = lean_st_ref_set(x_5, x_18, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("New facts: ", 11);
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
lean_dec(x_4);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_inc(x_3);
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_16);
x_35 = l_Lean_HashSet_toList___at_Lean_Elab_Tactic_Omega_lookup___spec__10(x_16);
x_36 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_37 = l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(x_35, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_38, x_36);
x_41 = l_Lean_MessageData_ofList(x_40);
lean_dec(x_40);
x_42 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_3, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_48);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_47);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
x_54 = lean_box(0);
x_55 = l_Lean_Elab_Tactic_Omega_lookup___lambda__1(x_1, x_16, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
return x_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_15);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("omega", 5);
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
x_1 = lean_mk_string_from_bytes("New atom: ", 10);
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
lean_inc(x_6);
x_15 = l_Lean_Meta_Canonicalizer_canon(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_15);
x_20 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_21 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_17, x_20, x_20, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
lean_inc(x_17);
x_28 = l_Lean_MessageData_ofExpr(x_17);
x_29 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_20, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_17, x_20, x_20, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_19, 0);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_15, 0, x_39);
return x_15;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
lean_inc(x_40);
x_42 = l_Lean_HashMapImp_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__1(x_13, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lean_Elab_Tactic_Omega_lookup___closed__2;
x_44 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_40, x_43, x_43, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
lean_inc(x_40);
x_51 = l_Lean_MessageData_ofExpr(x_40);
x_52 = l_Lean_Elab_Tactic_Omega_lookup___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(x_43, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2(x_40, x_43, x_43, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_42, 0);
lean_inc(x_60);
lean_dec(x_42);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_41);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
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

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
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Elab_Tactic_Omega_lookup___spec__2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Elab_Tactic_Omega_lookup___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__15;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_Omega_lookup___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__24;
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
static lean_object* l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4;
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
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
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
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_Tactic_Omega_lookup___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Omega_atoms(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Omega_withoutModifyingState___rarg___closed__1;
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_Omega_atoms___spec__4(lean_object*, lean_object*, lean_object*);
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
static uint8_t l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
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
x_1 = lean_mk_string_from_bytes("LT", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__26;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__27;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29() {
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
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__31;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instLTNat", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__33;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pos_pow_of_pos", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__38;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat_pos_of_pos", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__41() {
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
x_1 = lean_mk_string_from_bytes("emod_nonneg", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__43;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
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
x_1 = lean_mk_string_from_bytes("ne_of_gt", 8);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49;
x_2 = lean_int_dec_le(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("emod_lt_of_pos", 14);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Neg", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("neg", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__54;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__55;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__29;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instNegInt", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__59;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__60;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__62;
x_2 = l_Int_toNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__63;
x_2 = l_Lean_instToExprInt_mkNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__49;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instLTInt", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__68;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__69;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__37;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__71;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__57;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Ne", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__74;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__76;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__75;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__77;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__28;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mul_ediv_self_le", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__80;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__81;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt_mul_ediv_self_add", 20);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__56;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__6;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__86;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
x_3 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__61;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__64;
x_5 = l_Lean_mkApp3(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__88() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat_nonneg", 12);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Fin", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("BitVec", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isLt", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__95;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("val", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__98() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__94;
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
x_1 = lean_mk_string_from_bytes("natAbs", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le_natAbs", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__102() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__101;
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
x_1 = lean_mk_string_from_bytes("neg_le_natAbs", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__105() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__1;
x_2 = l_Lean_Elab_Tactic_Omega_atomsCoeffs___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__104;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
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
x_1 = lean_mk_string_from_bytes("ofNat_sub_dichotomy", 19);
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
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_157 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_11);
return x_158;
}
else
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_160 = lean_string_dec_eq(x_154, x_159);
lean_dec(x_154);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_161 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_11);
return x_162;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_array_get_size(x_153);
x_164 = lean_nat_dec_eq(x_163, x_108);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_165 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_11);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_array_fget(x_153, x_112);
x_168 = lean_array_fget(x_153, x_114);
lean_dec(x_153);
lean_inc(x_167);
x_169 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_170 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_11);
return x_171;
}
else
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_nat_dec_eq(x_172, x_137);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_175 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__32;
x_176 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__35;
x_177 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__36;
lean_inc(x_167);
x_178 = l_Lean_mkApp4(x_174, x_175, x_176, x_177, x_167);
x_179 = l_Lean_Meta_mkDecideProof(x_178, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
x_183 = l_Lean_mkApp3(x_182, x_167, x_168, x_181);
x_184 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_185 = l_Lean_mkAppB(x_184, x_148, x_183);
x_186 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
lean_inc(x_185);
lean_inc(x_115);
lean_inc(x_113);
x_187 = l_Lean_mkApp3(x_186, x_113, x_115, x_185);
x_188 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_189 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_190 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65;
lean_inc(x_115);
x_191 = l_Lean_mkApp3(x_189, x_115, x_190, x_185);
x_192 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_193 = l_Lean_mkApp3(x_192, x_113, x_115, x_191);
x_194 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_195 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_194, x_193);
x_196 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_195, x_187);
lean_ctor_set(x_179, 0, x_196);
return x_179;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_197 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_198 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
lean_inc(x_115);
x_199 = l_Lean_mkApp3(x_197, x_115, x_198, x_185);
x_200 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_201 = l_Lean_mkApp3(x_200, x_113, x_115, x_199);
x_202 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_203 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_202, x_201);
x_204 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_203, x_187);
lean_ctor_set(x_179, 0, x_204);
return x_179;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_205 = lean_ctor_get(x_179, 0);
x_206 = lean_ctor_get(x_179, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_179);
x_207 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__39;
x_208 = l_Lean_mkApp3(x_207, x_167, x_168, x_205);
x_209 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__42;
x_210 = l_Lean_mkAppB(x_209, x_148, x_208);
x_211 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
lean_inc(x_210);
lean_inc(x_115);
lean_inc(x_113);
x_212 = l_Lean_mkApp3(x_211, x_113, x_115, x_210);
x_213 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_214 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_215 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__65;
lean_inc(x_115);
x_216 = l_Lean_mkApp3(x_214, x_115, x_215, x_210);
x_217 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_218 = l_Lean_mkApp3(x_217, x_113, x_115, x_216);
x_219 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_220 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_219, x_218);
x_221 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_220, x_212);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_206);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_223 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
x_224 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
lean_inc(x_115);
x_225 = l_Lean_mkApp3(x_223, x_115, x_224, x_210);
x_226 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
x_227 = l_Lean_mkApp3(x_226, x_113, x_115, x_225);
x_228 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_229 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_228, x_227);
x_230 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_229, x_212);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_206);
return x_231;
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
x_232 = !lean_is_exclusive(x_179);
if (x_232 == 0)
{
return x_179;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_179, 0);
x_234 = lean_ctor_get(x_179, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_179);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_236 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_11);
return x_237;
}
}
}
}
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_238 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_11);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_240 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_11);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_242 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_11);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_141);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_244 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_11);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
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
x_246 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_11);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_248 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_11);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_138);
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_250 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_11);
return x_251;
}
}
}
}
}
else
{
lean_object* x_252; uint8_t x_253; 
lean_dec(x_122);
x_252 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
x_253 = lean_string_dec_eq(x_121, x_252);
lean_dec(x_121);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_254 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_11);
return x_255;
}
else
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_array_get_size(x_120);
x_257 = lean_nat_dec_eq(x_256, x_108);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_258 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_11);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_array_fget(x_120, x_112);
x_261 = lean_array_fget(x_120, x_114);
lean_dec(x_120);
lean_inc(x_260);
x_262 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_260);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_263 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_11);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
lean_dec(x_262);
x_266 = lean_unsigned_to_nat(0u);
x_267 = lean_nat_dec_eq(x_265, x_266);
lean_dec(x_265);
if (x_267 == 0)
{
lean_object* x_268; uint8_t x_306; 
x_306 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
if (x_306 == 0)
{
lean_object* x_307; 
x_307 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__73;
x_268 = x_307;
goto block_305;
}
else
{
lean_object* x_308; 
x_308 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
x_268 = x_308;
goto block_305;
}
block_305:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_269 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__30;
x_270 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
x_271 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_260);
lean_inc(x_268);
x_272 = l_Lean_mkApp4(x_269, x_270, x_271, x_268, x_260);
x_273 = l_Lean_Meta_mkDecideProof(x_272, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_275 = lean_ctor_get(x_273, 0);
x_276 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
x_277 = l_Lean_mkApp3(x_276, x_260, x_261, x_275);
x_278 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_277);
lean_inc(x_115);
x_279 = l_Lean_mkApp3(x_278, x_115, x_268, x_277);
x_280 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
lean_inc(x_115);
lean_inc(x_113);
x_281 = l_Lean_mkApp3(x_280, x_113, x_115, x_279);
x_282 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
x_283 = l_Lean_mkApp3(x_282, x_113, x_115, x_277);
x_284 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_285 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_284, x_281);
x_286 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_285, x_283);
lean_ctor_set(x_273, 0, x_286);
return x_273;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_287 = lean_ctor_get(x_273, 0);
x_288 = lean_ctor_get(x_273, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_273);
x_289 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__72;
x_290 = l_Lean_mkApp3(x_289, x_260, x_261, x_287);
x_291 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__48;
lean_inc(x_290);
lean_inc(x_115);
x_292 = l_Lean_mkApp3(x_291, x_115, x_268, x_290);
x_293 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__45;
lean_inc(x_115);
lean_inc(x_113);
x_294 = l_Lean_mkApp3(x_293, x_113, x_115, x_292);
x_295 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53;
x_296 = l_Lean_mkApp3(x_295, x_113, x_115, x_290);
x_297 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_298 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_297, x_294);
x_299 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_298, x_296);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_288);
return x_300;
}
}
else
{
uint8_t x_301; 
lean_dec(x_268);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_115);
lean_dec(x_113);
x_301 = !lean_is_exclusive(x_273);
if (x_301 == 0)
{
return x_273;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_273, 0);
x_303 = lean_ctor_get(x_273, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_273);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_309 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_11);
return x_310;
}
}
}
}
}
}
else
{
lean_object* x_311; lean_object* x_312; 
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
x_311 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_11);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_313 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_11);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_315 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_11);
return x_316;
}
}
}
}
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_48);
x_317 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
x_318 = lean_string_dec_eq(x_47, x_317);
lean_dec(x_47);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_319 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_11);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_array_get_size(x_46);
x_322 = lean_unsigned_to_nat(6u);
x_323 = lean_nat_dec_eq(x_321, x_322);
lean_dec(x_321);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_324 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_11);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_326 = lean_unsigned_to_nat(4u);
x_327 = lean_array_fget(x_46, x_326);
x_328 = lean_unsigned_to_nat(5u);
x_329 = lean_array_fget(x_46, x_328);
lean_dec(x_46);
lean_inc(x_329);
x_330 = l_Lean_Elab_Tactic_Omega_natCast_x3f(x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_329);
lean_dec(x_327);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_331 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_11);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
lean_dec(x_330);
x_334 = lean_unsigned_to_nat(0u);
x_335 = lean_nat_dec_eq(x_333, x_334);
lean_dec(x_333);
if (x_335 == 0)
{
lean_object* x_336; uint8_t x_375; 
x_375 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__50;
if (x_375 == 0)
{
lean_object* x_376; 
x_376 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__87;
x_336 = x_376;
goto block_374;
}
else
{
lean_object* x_377; 
x_377 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__67;
x_336 = x_377;
goto block_374;
}
block_374:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__78;
x_338 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__58;
lean_inc(x_336);
lean_inc(x_329);
x_339 = l_Lean_mkApp3(x_337, x_338, x_329, x_336);
x_340 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__79;
x_341 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__70;
lean_inc(x_329);
x_342 = l_Lean_mkApp4(x_340, x_338, x_341, x_336, x_329);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_343 = l_Lean_Meta_mkDecideProof(x_339, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = l_Lean_Meta_mkDecideProof(x_342, x_7, x_8, x_9, x_10, x_345);
if (lean_obj_tag(x_346) == 0)
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_348 = lean_ctor_get(x_346, 0);
x_349 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
lean_inc(x_329);
lean_inc(x_327);
x_350 = l_Lean_mkApp3(x_349, x_327, x_329, x_344);
x_351 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
x_352 = l_Lean_mkApp3(x_351, x_327, x_329, x_348);
x_353 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_354 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_353, x_350);
x_355 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_354, x_352);
lean_ctor_set(x_346, 0, x_355);
return x_346;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_356 = lean_ctor_get(x_346, 0);
x_357 = lean_ctor_get(x_346, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_346);
x_358 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__82;
lean_inc(x_329);
lean_inc(x_327);
x_359 = l_Lean_mkApp3(x_358, x_327, x_329, x_344);
x_360 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__85;
x_361 = l_Lean_mkApp3(x_360, x_327, x_329, x_356);
x_362 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_363 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_362, x_359);
x_364 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_363, x_361);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_357);
return x_365;
}
}
else
{
uint8_t x_366; 
lean_dec(x_344);
lean_dec(x_329);
lean_dec(x_327);
x_366 = !lean_is_exclusive(x_346);
if (x_366 == 0)
{
return x_346;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_346, 0);
x_368 = lean_ctor_get(x_346, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_346);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_342);
lean_dec(x_329);
lean_dec(x_327);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_370 = !lean_is_exclusive(x_343);
if (x_370 == 0)
{
return x_343;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_343, 0);
x_372 = lean_ctor_get(x_343, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_343);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; 
lean_dec(x_329);
lean_dec(x_327);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_378 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_11);
return x_379;
}
}
}
}
}
}
else
{
lean_object* x_380; uint8_t x_381; 
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_380 = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__2;
x_381 = lean_string_dec_eq(x_47, x_380);
lean_dec(x_47);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_46);
x_382 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_11);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_384 = lean_array_get_size(x_46);
x_385 = lean_unsigned_to_nat(3u);
x_386 = lean_nat_dec_eq(x_384, x_385);
lean_dec(x_384);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_46);
x_387 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_11);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_unsigned_to_nat(0u);
x_390 = lean_array_fget(x_46, x_389);
if (lean_obj_tag(x_390) == 4)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_obj_tag(x_391) == 1)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_393 = lean_ctor_get(x_390, 1);
lean_inc(x_393);
lean_dec(x_390);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_dec(x_391);
x_395 = l_Lean_Elab_Tactic_Omega_atomsList___rarg___closed__1;
x_396 = lean_string_dec_eq(x_394, x_395);
lean_dec(x_394);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_393);
lean_dec(x_46);
x_397 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_11);
return x_398;
}
else
{
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; 
x_399 = lean_unsigned_to_nat(2u);
x_400 = lean_array_fget(x_46, x_399);
lean_dec(x_46);
x_401 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__90;
lean_inc(x_400);
x_402 = l_Lean_Expr_app___override(x_401, x_400);
x_403 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_404 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_403, x_402);
x_405 = lean_ctor_get_uint8(x_4, 1);
x_406 = l_Lean_Expr_getAppFnArgs(x_400);
if (x_405 == 0)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_obj_tag(x_407) == 1)
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_obj_tag(x_408) == 1)
{
lean_object* x_409; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_410 = lean_ctor_get(x_406, 1);
lean_inc(x_410);
lean_dec(x_406);
x_411 = lean_ctor_get(x_407, 1);
lean_inc(x_411);
lean_dec(x_407);
x_412 = lean_ctor_get(x_408, 1);
lean_inc(x_412);
lean_dec(x_408);
x_413 = lean_string_dec_eq(x_412, x_395);
if (x_413 == 0)
{
lean_object* x_414; uint8_t x_415; 
x_414 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91;
x_415 = lean_string_dec_eq(x_412, x_414);
if (x_415 == 0)
{
lean_object* x_416; uint8_t x_417; 
x_416 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92;
x_417 = lean_string_dec_eq(x_412, x_416);
lean_dec(x_412);
if (x_417 == 0)
{
lean_object* x_418; 
lean_dec(x_411);
lean_dec(x_410);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_404);
lean_ctor_set(x_418, 1, x_11);
return x_418;
}
else
{
lean_object* x_419; uint8_t x_420; 
x_419 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93;
x_420 = lean_string_dec_eq(x_411, x_419);
lean_dec(x_411);
if (x_420 == 0)
{
lean_object* x_421; 
lean_dec(x_410);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_404);
lean_ctor_set(x_421, 1, x_11);
return x_421;
}
else
{
lean_object* x_422; uint8_t x_423; 
x_422 = lean_array_get_size(x_410);
x_423 = lean_nat_dec_eq(x_422, x_399);
lean_dec(x_422);
if (x_423 == 0)
{
lean_object* x_424; 
lean_dec(x_410);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_404);
lean_ctor_set(x_424, 1, x_11);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_425 = lean_array_fget(x_410, x_389);
x_426 = lean_unsigned_to_nat(1u);
x_427 = lean_array_fget(x_410, x_426);
lean_dec(x_410);
x_428 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_429 = l_Lean_mkAppB(x_428, x_425, x_427);
x_430 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_404, x_429);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_11);
return x_431;
}
}
}
}
else
{
lean_object* x_432; uint8_t x_433; 
lean_dec(x_412);
x_432 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97;
x_433 = lean_string_dec_eq(x_411, x_432);
lean_dec(x_411);
if (x_433 == 0)
{
lean_object* x_434; 
lean_dec(x_410);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_404);
lean_ctor_set(x_434, 1, x_11);
return x_434;
}
else
{
lean_object* x_435; uint8_t x_436; 
x_435 = lean_array_get_size(x_410);
x_436 = lean_nat_dec_eq(x_435, x_399);
lean_dec(x_435);
if (x_436 == 0)
{
lean_object* x_437; 
lean_dec(x_410);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_404);
lean_ctor_set(x_437, 1, x_11);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_438 = lean_array_fget(x_410, x_389);
x_439 = lean_unsigned_to_nat(1u);
x_440 = lean_array_fget(x_410, x_439);
lean_dec(x_410);
x_441 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_442 = l_Lean_mkAppB(x_441, x_438, x_440);
x_443 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_404, x_442);
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
lean_object* x_445; uint8_t x_446; 
lean_dec(x_412);
x_445 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_446 = lean_string_dec_eq(x_411, x_445);
lean_dec(x_411);
if (x_446 == 0)
{
lean_object* x_447; 
lean_dec(x_410);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_404);
lean_ctor_set(x_447, 1, x_11);
return x_447;
}
else
{
lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_448 = lean_array_get_size(x_410);
x_449 = lean_unsigned_to_nat(1u);
x_450 = lean_nat_dec_eq(x_448, x_449);
lean_dec(x_448);
if (x_450 == 0)
{
lean_object* x_451; 
lean_dec(x_410);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_11);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_452 = lean_array_fget(x_410, x_389);
lean_dec(x_410);
x_453 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
lean_inc(x_452);
x_454 = l_Lean_Expr_app___override(x_453, x_452);
x_455 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
x_456 = l_Lean_Expr_app___override(x_455, x_452);
x_457 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_404, x_454);
x_458 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_457, x_456);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_11);
return x_459;
}
}
}
}
else
{
lean_object* x_460; 
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_404);
lean_ctor_set(x_460, 1, x_11);
return x_460;
}
}
else
{
lean_object* x_461; 
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_404);
lean_ctor_set(x_461, 1, x_11);
return x_461;
}
}
else
{
lean_object* x_462; 
lean_dec(x_407);
lean_dec(x_406);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_404);
lean_ctor_set(x_462, 1, x_11);
return x_462;
}
}
else
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_406, 0);
lean_inc(x_463);
if (lean_obj_tag(x_463) == 1)
{
lean_object* x_464; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 1)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_466 = lean_ctor_get(x_406, 1);
lean_inc(x_466);
lean_dec(x_406);
x_467 = lean_ctor_get(x_463, 1);
lean_inc(x_467);
lean_dec(x_463);
x_468 = lean_ctor_get(x_464, 1);
lean_inc(x_468);
lean_dec(x_464);
x_469 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
x_470 = lean_string_dec_eq(x_468, x_469);
if (x_470 == 0)
{
uint8_t x_471; 
x_471 = lean_string_dec_eq(x_468, x_395);
if (x_471 == 0)
{
lean_object* x_472; uint8_t x_473; 
x_472 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__91;
x_473 = lean_string_dec_eq(x_468, x_472);
if (x_473 == 0)
{
lean_object* x_474; uint8_t x_475; 
x_474 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__92;
x_475 = lean_string_dec_eq(x_468, x_474);
lean_dec(x_468);
if (x_475 == 0)
{
lean_object* x_476; 
lean_dec(x_467);
lean_dec(x_466);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_404);
lean_ctor_set(x_476, 1, x_11);
return x_476;
}
else
{
lean_object* x_477; uint8_t x_478; 
x_477 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__93;
x_478 = lean_string_dec_eq(x_467, x_477);
lean_dec(x_467);
if (x_478 == 0)
{
lean_object* x_479; 
lean_dec(x_466);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_404);
lean_ctor_set(x_479, 1, x_11);
return x_479;
}
else
{
lean_object* x_480; uint8_t x_481; 
x_480 = lean_array_get_size(x_466);
x_481 = lean_nat_dec_eq(x_480, x_399);
lean_dec(x_480);
if (x_481 == 0)
{
lean_object* x_482; 
lean_dec(x_466);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_404);
lean_ctor_set(x_482, 1, x_11);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_483 = lean_array_fget(x_466, x_389);
x_484 = lean_unsigned_to_nat(1u);
x_485 = lean_array_fget(x_466, x_484);
lean_dec(x_466);
x_486 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__96;
x_487 = l_Lean_mkAppB(x_486, x_483, x_485);
x_488 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_404, x_487);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_11);
return x_489;
}
}
}
}
else
{
lean_object* x_490; uint8_t x_491; 
lean_dec(x_468);
x_490 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__97;
x_491 = lean_string_dec_eq(x_467, x_490);
lean_dec(x_467);
if (x_491 == 0)
{
lean_object* x_492; 
lean_dec(x_466);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_404);
lean_ctor_set(x_492, 1, x_11);
return x_492;
}
else
{
lean_object* x_493; uint8_t x_494; 
x_493 = lean_array_get_size(x_466);
x_494 = lean_nat_dec_eq(x_493, x_399);
lean_dec(x_493);
if (x_494 == 0)
{
lean_object* x_495; 
lean_dec(x_466);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_404);
lean_ctor_set(x_495, 1, x_11);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_496 = lean_array_fget(x_466, x_389);
x_497 = lean_unsigned_to_nat(1u);
x_498 = lean_array_fget(x_466, x_497);
lean_dec(x_466);
x_499 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__99;
x_500 = l_Lean_mkAppB(x_499, x_496, x_498);
x_501 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_404, x_500);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_11);
return x_502;
}
}
}
}
else
{
lean_object* x_503; uint8_t x_504; 
lean_dec(x_468);
x_503 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__100;
x_504 = lean_string_dec_eq(x_467, x_503);
lean_dec(x_467);
if (x_504 == 0)
{
lean_object* x_505; 
lean_dec(x_466);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_404);
lean_ctor_set(x_505, 1, x_11);
return x_505;
}
else
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_506 = lean_array_get_size(x_466);
x_507 = lean_unsigned_to_nat(1u);
x_508 = lean_nat_dec_eq(x_506, x_507);
lean_dec(x_506);
if (x_508 == 0)
{
lean_object* x_509; 
lean_dec(x_466);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_404);
lean_ctor_set(x_509, 1, x_11);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_510 = lean_array_fget(x_466, x_389);
lean_dec(x_466);
x_511 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__103;
lean_inc(x_510);
x_512 = l_Lean_Expr_app___override(x_511, x_510);
x_513 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__106;
x_514 = l_Lean_Expr_app___override(x_513, x_510);
x_515 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_404, x_512);
x_516 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_515, x_514);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_11);
return x_517;
}
}
}
}
else
{
lean_object* x_518; uint8_t x_519; 
lean_dec(x_468);
x_518 = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
x_519 = lean_string_dec_eq(x_467, x_518);
lean_dec(x_467);
if (x_519 == 0)
{
lean_object* x_520; 
lean_dec(x_466);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_404);
lean_ctor_set(x_520, 1, x_11);
return x_520;
}
else
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_521 = lean_array_get_size(x_466);
x_522 = lean_unsigned_to_nat(6u);
x_523 = lean_nat_dec_eq(x_521, x_522);
lean_dec(x_521);
if (x_523 == 0)
{
lean_object* x_524; 
lean_dec(x_466);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_404);
lean_ctor_set(x_524, 1, x_11);
return x_524;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_525 = lean_unsigned_to_nat(4u);
x_526 = lean_array_fget(x_466, x_525);
x_527 = lean_unsigned_to_nat(5u);
x_528 = lean_array_fget(x_466, x_527);
lean_dec(x_466);
x_529 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__109;
x_530 = l_Lean_mkAppB(x_529, x_526, x_528);
x_531 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_404, x_530);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_11);
return x_532;
}
}
}
}
else
{
lean_object* x_533; 
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_406);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_404);
lean_ctor_set(x_533, 1, x_11);
return x_533;
}
}
else
{
lean_object* x_534; 
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_406);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_404);
lean_ctor_set(x_534, 1, x_11);
return x_534;
}
}
else
{
lean_object* x_535; 
lean_dec(x_463);
lean_dec(x_406);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_404);
lean_ctor_set(x_535, 1, x_11);
return x_535;
}
}
}
else
{
lean_object* x_536; lean_object* x_537; 
lean_dec(x_393);
lean_dec(x_46);
x_536 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_11);
return x_537;
}
}
}
else
{
lean_object* x_538; lean_object* x_539; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_46);
x_538 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_11);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_46);
x_540 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_11);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_390);
lean_dec(x_46);
x_542 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_11);
return x_543;
}
}
}
}
}
else
{
lean_object* x_544; lean_object* x_545; 
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_544 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_11);
return x_545;
}
}
default: 
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_546 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_11);
return x_547;
}
}
}
else
{
lean_object* x_548; lean_object* x_549; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_548 = l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__1;
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_11);
return x_549;
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
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_18, 3);
x_22 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_23 = 0;
x_24 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
lean_inc(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentArray_push___rarg(x_21, x_25);
lean_ctor_set(x_18, 3, x_26);
x_27 = lean_st_ref_set(x_11, x_18, x_19);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
x_36 = lean_ctor_get(x_18, 2);
x_37 = lean_ctor_get(x_18, 3);
x_38 = lean_ctor_get(x_18, 4);
x_39 = lean_ctor_get(x_18, 5);
x_40 = lean_ctor_get(x_18, 6);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_41 = l_Lean_HashMap_toArray___at_Lean_Elab_Tactic_Omega_atoms___spec__1___closed__1;
x_42 = 0;
x_43 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_15);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_42);
lean_inc(x_13);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_PersistentArray_push___rarg(x_37, x_44);
x_46 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 4, x_38);
lean_ctor_set(x_46, 5, x_39);
lean_ctor_set(x_46, 6, x_40);
x_47 = lean_st_ref_set(x_11, x_46, x_19);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3;
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
x_40 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_38, x_36);
x_41 = l_Lean_MessageData_ofList(x_40);
lean_dec(x_40);
x_42 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4;
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
x_31 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4;
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
x_54 = l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4;
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
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__51);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__52);
l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53 = _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_analyzeAtom___closed__53);
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
l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Elab_Tactic_Omega_lookup___spec__3___closed__1);
l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__1);
l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__2);
l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__3);
l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Omega_lookup___lambda__2___closed__4);
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

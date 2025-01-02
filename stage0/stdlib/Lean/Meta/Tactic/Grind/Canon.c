// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Canon
// Imports: Init.Grind.Util Lean.Meta.Basic Lean.Meta.FunInfo Lean.Util.FVarSubset Lean.Util.PtrSet Lean.Util.FVarSubset
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl___closed__1;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrMap___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__1;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_fvarsSubset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1;
static lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState___closed__2;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_Grind_Canon_canonInst___closed__1;
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__6;
static uint64_t l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3;
lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
static lean_object* _init_l_Lean_Meta_Grind_Canon_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instInhabitedState___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instInhabitedState___closed__2;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Canon_instInhabitedState___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_expr_eqv(x_10, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_expr_eqv(x_14, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_13);
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_15, x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_free_object(x_1);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
}
case 1:
{
lean_object* x_22; size_t x_23; 
lean_free_object(x_1);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_usize_shift_right(x_2, x_6);
x_1 = x_22;
x_2 = x_23;
goto _start;
}
default: 
{
lean_object* x_25; 
lean_free_object(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = 5;
x_28 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_29 = lean_usize_land(x_2, x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_box(2);
x_32 = lean_array_get(x_31, x_26, x_30);
lean_dec(x_30);
lean_dec(x_26);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_expr_eqv(x_35, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_34);
x_40 = lean_box(0);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_eq(x_36, x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_34);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_34);
return x_43;
}
}
}
case 1:
{
lean_object* x_44; size_t x_45; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_usize_shift_right(x_2, x_27);
x_1 = x_44;
x_2 = x_45;
goto _start;
}
default: 
{
lean_object* x_47; 
x_47 = lean_box(0);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(x_48, x_49, lean_box(0), x_50, x_3);
lean_dec(x_49);
lean_dec(x_48);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Expr_hash(x_3);
x_6 = lean_uint64_of_nat(x_4);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(x_1, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = l_Lean_isTracingEnabledForCore(x_1, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_st_ref_take(x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_15, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; double x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_25 = 0;
x_26 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_27 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_float(x_27, sizeof(void*)*2, x_24);
lean_ctor_set_float(x_27, sizeof(void*)*2 + 8, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 16, x_25);
x_28 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_12);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_9);
lean_ctor_set(x_14, 1, x_29);
lean_ctor_set(x_14, 0, x_9);
x_30 = l_Lean_PersistentArray_push___rarg(x_23, x_14);
lean_ctor_set(x_16, 0, x_30);
x_31 = lean_st_ref_set(x_7, x_15, x_18);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 0, x_34);
lean_ctor_set(x_31, 0, x_10);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint64_t x_38; lean_object* x_39; double x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get_uint64(x_16, sizeof(void*)*1);
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
lean_dec(x_16);
x_40 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_41 = 0;
x_42 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_43 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_float(x_43, sizeof(void*)*2, x_40);
lean_ctor_set_float(x_43, sizeof(void*)*2 + 8, x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 16, x_41);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_45 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_12);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_9);
lean_ctor_set(x_14, 1, x_45);
lean_ctor_set(x_14, 0, x_9);
x_46 = l_Lean_PersistentArray_push___rarg(x_39, x_14);
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_38);
lean_ctor_set(x_15, 3, x_47);
x_48 = lean_st_ref_set(x_7, x_15, x_18);
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
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 0, x_51);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; double x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
x_55 = lean_ctor_get(x_15, 2);
x_56 = lean_ctor_get(x_15, 4);
x_57 = lean_ctor_get(x_15, 5);
x_58 = lean_ctor_get(x_15, 6);
x_59 = lean_ctor_get(x_15, 7);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_60 = lean_ctor_get_uint64(x_16, sizeof(void*)*1);
x_61 = lean_ctor_get(x_16, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_62 = x_16;
} else {
 lean_dec_ref(x_16);
 x_62 = lean_box(0);
}
x_63 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_64 = 0;
x_65 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_66 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_float(x_66, sizeof(void*)*2, x_63);
lean_ctor_set_float(x_66, sizeof(void*)*2 + 8, x_63);
lean_ctor_set_uint8(x_66, sizeof(void*)*2 + 16, x_64);
x_67 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_68 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_12);
lean_ctor_set(x_68, 2, x_67);
lean_inc(x_9);
lean_ctor_set(x_14, 1, x_68);
lean_ctor_set(x_14, 0, x_9);
x_69 = l_Lean_PersistentArray_push___rarg(x_61, x_14);
if (lean_is_scalar(x_62)) {
 x_70 = lean_alloc_ctor(0, 1, 8);
} else {
 x_70 = x_62;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set_uint64(x_70, sizeof(void*)*1, x_60);
x_71 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_71, 0, x_53);
lean_ctor_set(x_71, 1, x_54);
lean_ctor_set(x_71, 2, x_55);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_56);
lean_ctor_set(x_71, 5, x_57);
lean_ctor_set(x_71, 6, x_58);
lean_ctor_set(x_71, 7, x_59);
x_72 = lean_st_ref_set(x_7, x_71, x_18);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 0, x_75);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_10);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
lean_dec(x_14);
x_78 = lean_ctor_get(x_15, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_15, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_15, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_15, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_15, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_15, 6);
lean_inc(x_83);
x_84 = lean_ctor_get(x_15, 7);
lean_inc(x_84);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 lean_ctor_release(x_15, 6);
 lean_ctor_release(x_15, 7);
 x_85 = x_15;
} else {
 lean_dec_ref(x_15);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_16, sizeof(void*)*1);
x_87 = lean_ctor_get(x_16, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_88 = x_16;
} else {
 lean_dec_ref(x_16);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_90 = 0;
x_91 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_12);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_9);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_9);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___rarg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 8, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_78);
lean_ctor_set(x_98, 1, x_79);
lean_ctor_set(x_98, 2, x_80);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set(x_98, 4, x_81);
lean_ctor_set(x_98, 5, x_82);
lean_ctor_set(x_98, 6, x_83);
lean_ctor_set(x_98, 7, x_84);
x_99 = lean_st_ref_set(x_7, x_98, x_77);
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
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 0, x_102);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_10);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint64_t x_119; lean_object* x_120; lean_object* x_121; double x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_104 = lean_ctor_get(x_10, 0);
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_10);
x_106 = lean_st_ref_take(x_7, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_107, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_107, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_107, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_107, 7);
lean_inc(x_117);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 lean_ctor_release(x_107, 5);
 lean_ctor_release(x_107, 6);
 lean_ctor_release(x_107, 7);
 x_118 = x_107;
} else {
 lean_dec_ref(x_107);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get_uint64(x_108, sizeof(void*)*1);
x_120 = lean_ctor_get(x_108, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_121 = x_108;
} else {
 lean_dec_ref(x_108);
 x_121 = lean_box(0);
}
x_122 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_123 = 0;
x_124 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_125 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set_float(x_125, sizeof(void*)*2, x_122);
lean_ctor_set_float(x_125, sizeof(void*)*2 + 8, x_122);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 16, x_123);
x_126 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_127 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_104);
lean_ctor_set(x_127, 2, x_126);
lean_inc(x_9);
if (lean_is_scalar(x_110)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_110;
}
lean_ctor_set(x_128, 0, x_9);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_PersistentArray_push___rarg(x_120, x_128);
if (lean_is_scalar(x_121)) {
 x_130 = lean_alloc_ctor(0, 1, 8);
} else {
 x_130 = x_121;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set_uint64(x_130, sizeof(void*)*1, x_119);
if (lean_is_scalar(x_118)) {
 x_131 = lean_alloc_ctor(0, 8, 0);
} else {
 x_131 = x_118;
}
lean_ctor_set(x_131, 0, x_111);
lean_ctor_set(x_131, 1, x_112);
lean_ctor_set(x_131, 2, x_113);
lean_ctor_set(x_131, 3, x_130);
lean_ctor_set(x_131, 4, x_114);
lean_ctor_set(x_131, 5, x_115);
lean_ctor_set(x_131, 6, x_116);
lean_ctor_set(x_131, 7, x_117);
x_132 = lean_st_ref_set(x_7, x_131, x_109);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
return x_137;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("issues", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1;
x_2 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the following `grind` static elements are definitionally equal with `default` transparency, but not with `instances` transparency", 129, 129);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nand", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static uint64_t _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = l_Lean_isDiagnosticsEnabled(x_9, x_10, x_11);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 1);
x_80 = lean_ctor_get(x_75, 0);
lean_dec(x_80);
lean_ctor_set(x_75, 1, x_6);
x_15 = x_75;
x_16 = x_79;
goto block_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_6);
x_15 = x_82;
x_16 = x_81;
goto block_74;
}
}
else
{
uint8_t x_83; 
lean_dec(x_76);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_75, 1);
x_85 = lean_ctor_get(x_75, 0);
lean_dec(x_85);
lean_inc(x_3);
x_86 = l_Lean_Expr_fvarsSubset(x_4, x_3);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_box(x_86);
lean_ctor_set(x_75, 1, x_6);
lean_ctor_set(x_75, 0, x_87);
x_15 = x_75;
x_16 = x_84;
goto block_74;
}
else
{
lean_object* x_88; uint64_t x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_88 = lean_ctor_get(x_7, 0);
lean_inc(x_88);
x_89 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_90 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_91 = lean_ctor_get(x_7, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_7, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_7, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_7, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_7, 6);
lean_inc(x_96);
x_97 = !lean_is_exclusive(x_88);
if (x_97 == 0)
{
uint8_t x_98; uint8_t x_99; uint8_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_99 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_100 = 1;
lean_ctor_set_uint8(x_88, 9, x_100);
x_101 = 2;
x_102 = lean_uint64_shift_right(x_89, x_101);
x_103 = lean_uint64_shift_left(x_102, x_101);
x_104 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_105 = lean_uint64_lor(x_103, x_104);
x_106 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_106, 0, x_88);
lean_ctor_set(x_106, 1, x_91);
lean_ctor_set(x_106, 2, x_92);
lean_ctor_set(x_106, 3, x_93);
lean_ctor_set(x_106, 4, x_94);
lean_ctor_set(x_106, 5, x_95);
lean_ctor_set(x_106, 6, x_96);
lean_ctor_set_uint64(x_106, sizeof(void*)*7, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 8, x_90);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 9, x_98);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 10, x_99);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_Meta_isExprDefEq(x_3, x_4, x_106, x_8, x_9, x_10, x_84);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_ctor_set(x_75, 1, x_6);
lean_ctor_set(x_75, 0, x_108);
x_15 = x_75;
x_16 = x_109;
goto block_74;
}
else
{
uint8_t x_110; 
lean_free_object(x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
return x_107;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_107, 0);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_107);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; lean_object* x_139; lean_object* x_140; 
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_115 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_116 = lean_ctor_get_uint8(x_88, 0);
x_117 = lean_ctor_get_uint8(x_88, 1);
x_118 = lean_ctor_get_uint8(x_88, 2);
x_119 = lean_ctor_get_uint8(x_88, 3);
x_120 = lean_ctor_get_uint8(x_88, 4);
x_121 = lean_ctor_get_uint8(x_88, 5);
x_122 = lean_ctor_get_uint8(x_88, 6);
x_123 = lean_ctor_get_uint8(x_88, 7);
x_124 = lean_ctor_get_uint8(x_88, 8);
x_125 = lean_ctor_get_uint8(x_88, 10);
x_126 = lean_ctor_get_uint8(x_88, 11);
x_127 = lean_ctor_get_uint8(x_88, 12);
x_128 = lean_ctor_get_uint8(x_88, 13);
x_129 = lean_ctor_get_uint8(x_88, 14);
x_130 = lean_ctor_get_uint8(x_88, 15);
x_131 = lean_ctor_get_uint8(x_88, 16);
lean_dec(x_88);
x_132 = 1;
x_133 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_133, 0, x_116);
lean_ctor_set_uint8(x_133, 1, x_117);
lean_ctor_set_uint8(x_133, 2, x_118);
lean_ctor_set_uint8(x_133, 3, x_119);
lean_ctor_set_uint8(x_133, 4, x_120);
lean_ctor_set_uint8(x_133, 5, x_121);
lean_ctor_set_uint8(x_133, 6, x_122);
lean_ctor_set_uint8(x_133, 7, x_123);
lean_ctor_set_uint8(x_133, 8, x_124);
lean_ctor_set_uint8(x_133, 9, x_132);
lean_ctor_set_uint8(x_133, 10, x_125);
lean_ctor_set_uint8(x_133, 11, x_126);
lean_ctor_set_uint8(x_133, 12, x_127);
lean_ctor_set_uint8(x_133, 13, x_128);
lean_ctor_set_uint8(x_133, 14, x_129);
lean_ctor_set_uint8(x_133, 15, x_130);
lean_ctor_set_uint8(x_133, 16, x_131);
x_134 = 2;
x_135 = lean_uint64_shift_right(x_89, x_134);
x_136 = lean_uint64_shift_left(x_135, x_134);
x_137 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_138 = lean_uint64_lor(x_136, x_137);
x_139 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_91);
lean_ctor_set(x_139, 2, x_92);
lean_ctor_set(x_139, 3, x_93);
lean_ctor_set(x_139, 4, x_94);
lean_ctor_set(x_139, 5, x_95);
lean_ctor_set(x_139, 6, x_96);
lean_ctor_set_uint64(x_139, sizeof(void*)*7, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 8, x_90);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 9, x_114);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 10, x_115);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l_Lean_Meta_isExprDefEq(x_3, x_4, x_139, x_8, x_9, x_10, x_84);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_ctor_set(x_75, 1, x_6);
lean_ctor_set(x_75, 0, x_141);
x_15 = x_75;
x_16 = x_142;
goto block_74;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_free_object(x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_145 = x_140;
} else {
 lean_dec_ref(x_140);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
}
else
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_75, 1);
lean_inc(x_147);
lean_dec(x_75);
lean_inc(x_3);
x_148 = l_Lean_Expr_fvarsSubset(x_4, x_3);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_6);
x_15 = x_150;
x_16 = x_147;
goto block_74;
}
else
{
lean_object* x_151; uint64_t x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; lean_object* x_186; lean_object* x_187; 
x_151 = lean_ctor_get(x_7, 0);
lean_inc(x_151);
x_152 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_153 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_154 = lean_ctor_get(x_7, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_7, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_7, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_7, 4);
lean_inc(x_157);
x_158 = lean_ctor_get(x_7, 5);
lean_inc(x_158);
x_159 = lean_ctor_get(x_7, 6);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_161 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_162 = lean_ctor_get_uint8(x_151, 0);
x_163 = lean_ctor_get_uint8(x_151, 1);
x_164 = lean_ctor_get_uint8(x_151, 2);
x_165 = lean_ctor_get_uint8(x_151, 3);
x_166 = lean_ctor_get_uint8(x_151, 4);
x_167 = lean_ctor_get_uint8(x_151, 5);
x_168 = lean_ctor_get_uint8(x_151, 6);
x_169 = lean_ctor_get_uint8(x_151, 7);
x_170 = lean_ctor_get_uint8(x_151, 8);
x_171 = lean_ctor_get_uint8(x_151, 10);
x_172 = lean_ctor_get_uint8(x_151, 11);
x_173 = lean_ctor_get_uint8(x_151, 12);
x_174 = lean_ctor_get_uint8(x_151, 13);
x_175 = lean_ctor_get_uint8(x_151, 14);
x_176 = lean_ctor_get_uint8(x_151, 15);
x_177 = lean_ctor_get_uint8(x_151, 16);
if (lean_is_exclusive(x_151)) {
 x_178 = x_151;
} else {
 lean_dec_ref(x_151);
 x_178 = lean_box(0);
}
x_179 = 1;
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 0, 17);
} else {
 x_180 = x_178;
}
lean_ctor_set_uint8(x_180, 0, x_162);
lean_ctor_set_uint8(x_180, 1, x_163);
lean_ctor_set_uint8(x_180, 2, x_164);
lean_ctor_set_uint8(x_180, 3, x_165);
lean_ctor_set_uint8(x_180, 4, x_166);
lean_ctor_set_uint8(x_180, 5, x_167);
lean_ctor_set_uint8(x_180, 6, x_168);
lean_ctor_set_uint8(x_180, 7, x_169);
lean_ctor_set_uint8(x_180, 8, x_170);
lean_ctor_set_uint8(x_180, 9, x_179);
lean_ctor_set_uint8(x_180, 10, x_171);
lean_ctor_set_uint8(x_180, 11, x_172);
lean_ctor_set_uint8(x_180, 12, x_173);
lean_ctor_set_uint8(x_180, 13, x_174);
lean_ctor_set_uint8(x_180, 14, x_175);
lean_ctor_set_uint8(x_180, 15, x_176);
lean_ctor_set_uint8(x_180, 16, x_177);
x_181 = 2;
x_182 = lean_uint64_shift_right(x_152, x_181);
x_183 = lean_uint64_shift_left(x_182, x_181);
x_184 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_185 = lean_uint64_lor(x_183, x_184);
x_186 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_186, 0, x_180);
lean_ctor_set(x_186, 1, x_154);
lean_ctor_set(x_186, 2, x_155);
lean_ctor_set(x_186, 3, x_156);
lean_ctor_set(x_186, 4, x_157);
lean_ctor_set(x_186, 5, x_158);
lean_ctor_set(x_186, 6, x_159);
lean_ctor_set_uint64(x_186, sizeof(void*)*7, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*7 + 8, x_153);
lean_ctor_set_uint8(x_186, sizeof(void*)*7 + 9, x_160);
lean_ctor_set_uint8(x_186, sizeof(void*)*7 + 10, x_161);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_187 = l_Lean_Meta_isExprDefEq(x_3, x_4, x_186, x_8, x_9, x_10, x_147);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_6);
x_15 = x_190;
x_16 = x_189;
goto block_74;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_193 = x_187;
} else {
 lean_dec_ref(x_187);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
}
block_74:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_15, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3;
x_29 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_28, x_27, x_7, x_8, x_9, x_10, x_16);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_29, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_30, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_43 = x_30;
} else {
 lean_dec_ref(x_30);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_2);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_dec(x_29);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_dec(x_30);
x_49 = l_Lean_indentExpr(x_3);
x_50 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_4);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_28, x_57, x_48, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_60, 0, x_63);
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_2);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_2);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_19);
lean_inc(x_1);
x_21 = l_Lean_Meta_isExprDefEq(x_1, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_7);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_4);
x_26 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1(x_2, x_4, x_1, x_19, x_25, x_10, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_33);
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_39 = x_27;
} else {
 lean_dec_ref(x_27);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec(x_28);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_ctor_get(x_28, 0);
lean_inc(x_45);
lean_dec(x_28);
x_7 = x_20;
x_8 = x_45;
x_9 = lean_box(0);
x_10 = x_44;
x_15 = x_43;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_21, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_10);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
x_55 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_54, x_1, x_19);
lean_ctor_set(x_10, 1, x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_19);
x_57 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_57);
lean_ctor_set(x_7, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_10);
lean_ctor_set(x_21, 0, x_58);
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
x_61 = lean_ctor_get(x_10, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
lean_inc(x_19);
x_62 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_60, x_1, x_19);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_19);
x_65 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_65);
lean_ctor_set(x_7, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_7);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_21, 0, x_66);
return x_21;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_dec(x_21);
x_68 = lean_ctor_get(x_10, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_10, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_10, 2);
lean_inc(x_70);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 x_71 = x_10;
} else {
 lean_dec_ref(x_10);
 x_71 = lean_box(0);
}
lean_inc(x_19);
x_72 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_69, x_1, x_19);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 3, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_19);
x_75 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_75);
lean_ctor_set(x_7, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_7);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_67);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_free_object(x_7);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_21);
if (x_78 == 0)
{
return x_21;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_21, 0);
x_80 = lean_ctor_get(x_21, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_21);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_7, 0);
x_83 = lean_ctor_get(x_7, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_82);
lean_inc(x_1);
x_84 = l_Lean_Meta_isExprDefEq(x_1, x_82, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
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
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_4);
x_89 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1(x_2, x_4, x_1, x_82, x_88, x_10, x_11, x_12, x_13, x_14, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_83);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_93 = x_89;
} else {
 lean_dec_ref(x_89);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_dec(x_89);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_dec(x_90);
x_101 = lean_ctor_get(x_91, 0);
lean_inc(x_101);
lean_dec(x_91);
x_7 = x_83;
x_8 = x_101;
x_9 = lean_box(0);
x_10 = x_100;
x_15 = x_99;
goto _start;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_83);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_103 = lean_ctor_get(x_89, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_105 = x_89;
} else {
 lean_dec_ref(x_89);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_83);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_107 = lean_ctor_get(x_84, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_108 = x_84;
} else {
 lean_dec_ref(x_84);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_10, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_10, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_10, 2);
lean_inc(x_111);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 x_112 = x_10;
} else {
 lean_dec_ref(x_10);
 x_112 = lean_box(0);
}
lean_inc(x_82);
x_113 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_110, x_1, x_82);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 3, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_111);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_82);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
if (lean_is_scalar(x_108)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_108;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_107);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_120 = lean_ctor_get(x_84, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_84, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_122 = x_84;
} else {
 lean_dec_ref(x_84);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
x_19 = l_Lean_Expr_hash(x_17);
lean_dec(x_17);
x_20 = lean_uint64_of_nat(x_18);
lean_dec(x_18);
x_21 = lean_uint64_mix_hash(x_19, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_shift_right(x_22, x_14);
x_24 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_6, x_23, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_24;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_expr_eqv(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_2 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
x_33 = lean_array_fset(x_5, x_2, x_3);
x_34 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_35 = lean_array_fset(x_5, x_2, x_3);
x_36 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = lean_expr_eqv(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_array_fset(x_17, x_12, x_27);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_fset(x_17, x_12, x_31);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_32);
return x_1;
}
else
{
lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_33 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
x_40 = lean_expr_eqv(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_37);
x_41 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_34, x_35, x_4, x_5);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_array_fset(x_17, x_12, x_42);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_43);
return x_1;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_eq(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_34, x_35, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
lean_dec(x_34);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
}
}
case 1:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_usize_shift_right(x_2, x_9);
x_53 = lean_usize_add(x_3, x_8);
x_54 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_51, x_52, x_53, x_4, x_5);
lean_ctor_set(x_15, 0, x_54);
x_55 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_55);
return x_1;
}
else
{
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_15, 0);
lean_inc(x_56);
lean_dec(x_15);
x_57 = lean_usize_shift_right(x_2, x_9);
x_58 = lean_usize_add(x_3, x_8);
x_59 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_56, x_57, x_58, x_4, x_5);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_array_fset(x_17, x_12, x_60);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_61);
return x_1;
}
}
default: 
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_5);
x_63 = lean_array_fset(x_17, x_12, x_62);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_63);
return x_1;
}
}
}
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = 1;
x_66 = 5;
x_67 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_68 = lean_usize_land(x_2, x_67);
x_69 = lean_usize_to_nat(x_68);
x_70 = lean_array_get_size(x_64);
x_71 = lean_nat_dec_lt(x_69, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_64);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_array_fget(x_64, x_69);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_64, x_69, x_74);
switch (lean_obj_tag(x_73)) {
case 0:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
x_83 = lean_expr_eqv(x_79, x_81);
lean_dec(x_81);
lean_dec(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_78);
x_84 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_76, x_77, x_4, x_5);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_array_fset(x_75, x_69, x_85);
lean_dec(x_69);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_eq(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_78);
x_89 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_76, x_77, x_4, x_5);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_array_fset(x_75, x_69, x_90);
lean_dec(x_69);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_77);
lean_dec(x_76);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_4);
lean_ctor_set(x_93, 1, x_5);
x_94 = lean_array_fset(x_75, x_69, x_93);
lean_dec(x_69);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
case 1:
{
lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_73, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_97 = x_73;
} else {
 lean_dec_ref(x_73);
 x_97 = lean_box(0);
}
x_98 = lean_usize_shift_right(x_2, x_66);
x_99 = lean_usize_add(x_3, x_65);
x_100 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_96, x_98, x_99, x_4, x_5);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_array_fset(x_75, x_69, x_101);
lean_dec(x_69);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_4);
lean_ctor_set(x_104, 1, x_5);
x_105 = lean_array_fset(x_75, x_69, x_104);
lean_dec(x_69);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; size_t x_110; uint8_t x_111; 
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(x_1, x_108, x_4, x_5);
x_110 = 7;
x_111 = lean_usize_dec_le(x_110, x_3);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_109);
x_113 = lean_unsigned_to_nat(4u);
x_114 = lean_nat_dec_lt(x_112, x_113);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
lean_dec(x_109);
x_117 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1;
x_118 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_3, x_115, x_116, lean_box(0), x_108, x_117);
lean_dec(x_116);
lean_dec(x_115);
return x_118;
}
else
{
return x_109;
}
}
else
{
return x_109;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; size_t x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_1, 0);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_1);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(x_121, x_122, x_4, x_5);
x_124 = 7;
x_125 = lean_usize_dec_le(x_124, x_3);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_123);
x_127 = lean_unsigned_to_nat(4u);
x_128 = lean_nat_dec_lt(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
lean_dec(x_123);
x_131 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1;
x_132 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_3, x_129, x_130, lean_box(0), x_122, x_131);
lean_dec(x_130);
lean_dec(x_129);
return x_132;
}
else
{
return x_123;
}
}
else
{
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; 
x_4 = 1;
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_Expr_hash(x_5);
lean_dec(x_5);
x_8 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_1, x_10, x_4, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_expr_eqv(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_expr_eqv(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
x_15 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(x_12, x_3, x_14);
lean_inc_n(x_1, 2);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_13, x_1, x_1);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_5, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
x_23 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(x_19, x_3, x_22);
lean_inc_n(x_1, 2);
x_24 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_20, x_1, x_1);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(x_14, x_13);
x_16 = lean_box(0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_17 = x_46;
goto block_45;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
lean_dec(x_15);
x_17 = x_47;
goto block_45;
}
block_45:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_4);
x_19 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_4, x_5, x_16, x_18, x_17, x_17, x_17, x_18, lean_box(0), x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_4, x_17, x_13, x_25, x_24, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_19, 0, x_34);
return x_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_37 = x_20;
} else {
 lean_dec_ref(x_20);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_22, 0);
lean_inc(x_38);
lean_dec(x_22);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_11, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
lean_inc(x_5);
x_14 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(x_1, x_2, x_5, x_3, x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint64_t x_13; uint8_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_14 = 1;
lean_ctor_set_uint8(x_11, 9, x_14);
x_15 = 2;
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_shift_left(x_16, x_15);
x_18 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_19 = lean_uint64_lor(x_17, x_18);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_19);
x_20 = 0;
x_21 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_20, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint64_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint8_t x_63; lean_object* x_64; 
x_39 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_40 = lean_ctor_get_uint8(x_11, 0);
x_41 = lean_ctor_get_uint8(x_11, 1);
x_42 = lean_ctor_get_uint8(x_11, 2);
x_43 = lean_ctor_get_uint8(x_11, 3);
x_44 = lean_ctor_get_uint8(x_11, 4);
x_45 = lean_ctor_get_uint8(x_11, 5);
x_46 = lean_ctor_get_uint8(x_11, 6);
x_47 = lean_ctor_get_uint8(x_11, 7);
x_48 = lean_ctor_get_uint8(x_11, 8);
x_49 = lean_ctor_get_uint8(x_11, 10);
x_50 = lean_ctor_get_uint8(x_11, 11);
x_51 = lean_ctor_get_uint8(x_11, 12);
x_52 = lean_ctor_get_uint8(x_11, 13);
x_53 = lean_ctor_get_uint8(x_11, 14);
x_54 = lean_ctor_get_uint8(x_11, 15);
x_55 = lean_ctor_get_uint8(x_11, 16);
lean_dec(x_11);
x_56 = 1;
x_57 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_57, 0, x_40);
lean_ctor_set_uint8(x_57, 1, x_41);
lean_ctor_set_uint8(x_57, 2, x_42);
lean_ctor_set_uint8(x_57, 3, x_43);
lean_ctor_set_uint8(x_57, 4, x_44);
lean_ctor_set_uint8(x_57, 5, x_45);
lean_ctor_set_uint8(x_57, 6, x_46);
lean_ctor_set_uint8(x_57, 7, x_47);
lean_ctor_set_uint8(x_57, 8, x_48);
lean_ctor_set_uint8(x_57, 9, x_56);
lean_ctor_set_uint8(x_57, 10, x_49);
lean_ctor_set_uint8(x_57, 11, x_50);
lean_ctor_set_uint8(x_57, 12, x_51);
lean_ctor_set_uint8(x_57, 13, x_52);
lean_ctor_set_uint8(x_57, 14, x_53);
lean_ctor_set_uint8(x_57, 15, x_54);
lean_ctor_set_uint8(x_57, 16, x_55);
x_58 = 2;
x_59 = lean_uint64_shift_right(x_39, x_58);
x_60 = lean_uint64_shift_left(x_59, x_58);
x_61 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_62 = lean_uint64_lor(x_60, x_61);
lean_ctor_set(x_5, 0, x_57);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_62);
x_63 = 0;
x_64 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_63, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_75 = x_64;
} else {
 lean_dec_ref(x_64);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; uint64_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_77 = lean_ctor_get(x_5, 0);
x_78 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_79 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_80 = lean_ctor_get(x_5, 1);
x_81 = lean_ctor_get(x_5, 2);
x_82 = lean_ctor_get(x_5, 3);
x_83 = lean_ctor_get(x_5, 4);
x_84 = lean_ctor_get(x_5, 5);
x_85 = lean_ctor_get(x_5, 6);
x_86 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_77);
lean_dec(x_5);
x_88 = lean_ctor_get_uint8(x_77, 0);
x_89 = lean_ctor_get_uint8(x_77, 1);
x_90 = lean_ctor_get_uint8(x_77, 2);
x_91 = lean_ctor_get_uint8(x_77, 3);
x_92 = lean_ctor_get_uint8(x_77, 4);
x_93 = lean_ctor_get_uint8(x_77, 5);
x_94 = lean_ctor_get_uint8(x_77, 6);
x_95 = lean_ctor_get_uint8(x_77, 7);
x_96 = lean_ctor_get_uint8(x_77, 8);
x_97 = lean_ctor_get_uint8(x_77, 10);
x_98 = lean_ctor_get_uint8(x_77, 11);
x_99 = lean_ctor_get_uint8(x_77, 12);
x_100 = lean_ctor_get_uint8(x_77, 13);
x_101 = lean_ctor_get_uint8(x_77, 14);
x_102 = lean_ctor_get_uint8(x_77, 15);
x_103 = lean_ctor_get_uint8(x_77, 16);
if (lean_is_exclusive(x_77)) {
 x_104 = x_77;
} else {
 lean_dec_ref(x_77);
 x_104 = lean_box(0);
}
x_105 = 1;
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 0, 17);
} else {
 x_106 = x_104;
}
lean_ctor_set_uint8(x_106, 0, x_88);
lean_ctor_set_uint8(x_106, 1, x_89);
lean_ctor_set_uint8(x_106, 2, x_90);
lean_ctor_set_uint8(x_106, 3, x_91);
lean_ctor_set_uint8(x_106, 4, x_92);
lean_ctor_set_uint8(x_106, 5, x_93);
lean_ctor_set_uint8(x_106, 6, x_94);
lean_ctor_set_uint8(x_106, 7, x_95);
lean_ctor_set_uint8(x_106, 8, x_96);
lean_ctor_set_uint8(x_106, 9, x_105);
lean_ctor_set_uint8(x_106, 10, x_97);
lean_ctor_set_uint8(x_106, 11, x_98);
lean_ctor_set_uint8(x_106, 12, x_99);
lean_ctor_set_uint8(x_106, 13, x_100);
lean_ctor_set_uint8(x_106, 14, x_101);
lean_ctor_set_uint8(x_106, 15, x_102);
lean_ctor_set_uint8(x_106, 16, x_103);
x_107 = 2;
x_108 = lean_uint64_shift_right(x_78, x_107);
x_109 = lean_uint64_shift_left(x_108, x_107);
x_110 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_111 = lean_uint64_lor(x_109, x_110);
x_112 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_112, 0, x_106);
lean_ctor_set(x_112, 1, x_80);
lean_ctor_set(x_112, 2, x_81);
lean_ctor_set(x_112, 3, x_82);
lean_ctor_set(x_112, 4, x_83);
lean_ctor_set(x_112, 5, x_84);
lean_ctor_set(x_112, 6, x_85);
lean_ctor_set_uint64(x_112, sizeof(void*)*7, x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 8, x_79);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 9, x_86);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 10, x_87);
x_113 = 0;
x_114 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_113, x_4, x_112, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
if (lean_is_scalar(x_117)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_117;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_114, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_114, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_125 = x_114;
} else {
 lean_dec_ref(x_114);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
static uint64_t _init_l_Lean_Meta_Grind_Canon_canonInst___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 3;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint64_t x_13; uint8_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_14 = 3;
lean_ctor_set_uint8(x_11, 9, x_14);
x_15 = 2;
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_shift_left(x_16, x_15);
x_18 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_19 = lean_uint64_lor(x_17, x_18);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_19);
x_20 = 1;
x_21 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_20, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint64_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint8_t x_63; lean_object* x_64; 
x_39 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_40 = lean_ctor_get_uint8(x_11, 0);
x_41 = lean_ctor_get_uint8(x_11, 1);
x_42 = lean_ctor_get_uint8(x_11, 2);
x_43 = lean_ctor_get_uint8(x_11, 3);
x_44 = lean_ctor_get_uint8(x_11, 4);
x_45 = lean_ctor_get_uint8(x_11, 5);
x_46 = lean_ctor_get_uint8(x_11, 6);
x_47 = lean_ctor_get_uint8(x_11, 7);
x_48 = lean_ctor_get_uint8(x_11, 8);
x_49 = lean_ctor_get_uint8(x_11, 10);
x_50 = lean_ctor_get_uint8(x_11, 11);
x_51 = lean_ctor_get_uint8(x_11, 12);
x_52 = lean_ctor_get_uint8(x_11, 13);
x_53 = lean_ctor_get_uint8(x_11, 14);
x_54 = lean_ctor_get_uint8(x_11, 15);
x_55 = lean_ctor_get_uint8(x_11, 16);
lean_dec(x_11);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_57, 0, x_40);
lean_ctor_set_uint8(x_57, 1, x_41);
lean_ctor_set_uint8(x_57, 2, x_42);
lean_ctor_set_uint8(x_57, 3, x_43);
lean_ctor_set_uint8(x_57, 4, x_44);
lean_ctor_set_uint8(x_57, 5, x_45);
lean_ctor_set_uint8(x_57, 6, x_46);
lean_ctor_set_uint8(x_57, 7, x_47);
lean_ctor_set_uint8(x_57, 8, x_48);
lean_ctor_set_uint8(x_57, 9, x_56);
lean_ctor_set_uint8(x_57, 10, x_49);
lean_ctor_set_uint8(x_57, 11, x_50);
lean_ctor_set_uint8(x_57, 12, x_51);
lean_ctor_set_uint8(x_57, 13, x_52);
lean_ctor_set_uint8(x_57, 14, x_53);
lean_ctor_set_uint8(x_57, 15, x_54);
lean_ctor_set_uint8(x_57, 16, x_55);
x_58 = 2;
x_59 = lean_uint64_shift_right(x_39, x_58);
x_60 = lean_uint64_shift_left(x_59, x_58);
x_61 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_62 = lean_uint64_lor(x_60, x_61);
lean_ctor_set(x_5, 0, x_57);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_62);
x_63 = 1;
x_64 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_63, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_75 = x_64;
} else {
 lean_dec_ref(x_64);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; uint64_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_77 = lean_ctor_get(x_5, 0);
x_78 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_79 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_80 = lean_ctor_get(x_5, 1);
x_81 = lean_ctor_get(x_5, 2);
x_82 = lean_ctor_get(x_5, 3);
x_83 = lean_ctor_get(x_5, 4);
x_84 = lean_ctor_get(x_5, 5);
x_85 = lean_ctor_get(x_5, 6);
x_86 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_77);
lean_dec(x_5);
x_88 = lean_ctor_get_uint8(x_77, 0);
x_89 = lean_ctor_get_uint8(x_77, 1);
x_90 = lean_ctor_get_uint8(x_77, 2);
x_91 = lean_ctor_get_uint8(x_77, 3);
x_92 = lean_ctor_get_uint8(x_77, 4);
x_93 = lean_ctor_get_uint8(x_77, 5);
x_94 = lean_ctor_get_uint8(x_77, 6);
x_95 = lean_ctor_get_uint8(x_77, 7);
x_96 = lean_ctor_get_uint8(x_77, 8);
x_97 = lean_ctor_get_uint8(x_77, 10);
x_98 = lean_ctor_get_uint8(x_77, 11);
x_99 = lean_ctor_get_uint8(x_77, 12);
x_100 = lean_ctor_get_uint8(x_77, 13);
x_101 = lean_ctor_get_uint8(x_77, 14);
x_102 = lean_ctor_get_uint8(x_77, 15);
x_103 = lean_ctor_get_uint8(x_77, 16);
if (lean_is_exclusive(x_77)) {
 x_104 = x_77;
} else {
 lean_dec_ref(x_77);
 x_104 = lean_box(0);
}
x_105 = 3;
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 0, 17);
} else {
 x_106 = x_104;
}
lean_ctor_set_uint8(x_106, 0, x_88);
lean_ctor_set_uint8(x_106, 1, x_89);
lean_ctor_set_uint8(x_106, 2, x_90);
lean_ctor_set_uint8(x_106, 3, x_91);
lean_ctor_set_uint8(x_106, 4, x_92);
lean_ctor_set_uint8(x_106, 5, x_93);
lean_ctor_set_uint8(x_106, 6, x_94);
lean_ctor_set_uint8(x_106, 7, x_95);
lean_ctor_set_uint8(x_106, 8, x_96);
lean_ctor_set_uint8(x_106, 9, x_105);
lean_ctor_set_uint8(x_106, 10, x_97);
lean_ctor_set_uint8(x_106, 11, x_98);
lean_ctor_set_uint8(x_106, 12, x_99);
lean_ctor_set_uint8(x_106, 13, x_100);
lean_ctor_set_uint8(x_106, 14, x_101);
lean_ctor_set_uint8(x_106, 15, x_102);
lean_ctor_set_uint8(x_106, 16, x_103);
x_107 = 2;
x_108 = lean_uint64_shift_right(x_78, x_107);
x_109 = lean_uint64_shift_left(x_108, x_107);
x_110 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_111 = lean_uint64_lor(x_109, x_110);
x_112 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_112, 0, x_106);
lean_ctor_set(x_112, 1, x_80);
lean_ctor_set(x_112, 2, x_81);
lean_ctor_set(x_112, 3, x_82);
lean_ctor_set(x_112, 4, x_83);
lean_ctor_set(x_112, 5, x_84);
lean_ctor_set(x_112, 6, x_85);
lean_ctor_set_uint64(x_112, sizeof(void*)*7, x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 8, x_79);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 9, x_86);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 10, x_87);
x_113 = 1;
x_114 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_113, x_4, x_112, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
if (lean_is_scalar(x_117)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_117;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_114, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_114, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_125 = x_114;
} else {
 lean_dec_ref(x_114);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isTypeFormer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = 2;
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = 2;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(x_3, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = l_Lean_Meta_ParamInfo_isInstImplicit(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(x_3, x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = 2;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Canon_shouldCanon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_StateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__2;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_ptr_addr(x_25);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_ptr_addr(x_1);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_ptr_addr(x_1);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(x_1, x_2, x_15);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_1);
x_14 = lean_ptr_addr(x_5);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_set(x_3, x_2, x_5);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_23 = lean_box(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_nat_dec_lt(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_202; uint8_t x_203; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_202 = lean_array_get_size(x_29);
x_203 = lean_nat_dec_lt(x_6, x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_instInhabitedExpr;
x_205 = l_outOfBounds___rarg(x_204);
x_31 = x_205;
goto block_201;
}
else
{
lean_object* x_206; 
x_206 = lean_array_fget(x_29, x_6);
x_31 = x_206;
goto block_201;
}
block_28:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_nat_add(x_6, x_25);
lean_dec(x_6);
x_5 = x_24;
x_6 = x_26;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_10 = x_23;
x_15 = x_21;
goto _start;
}
block_201:
{
lean_object* x_32; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_31);
x_32 = l_Lean_Meta_Grind_Canon_shouldCanon(x_2, x_6, x_31, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
switch (x_34) {
case 0:
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get_uint64(x_11, sizeof(void*)*7);
x_38 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 8);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 6);
lean_inc(x_44);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
uint8_t x_46; uint8_t x_47; uint8_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_46 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 9);
x_47 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 10);
x_48 = 1;
lean_ctor_set_uint8(x_35, 9, x_48);
x_49 = 2;
x_50 = lean_uint64_shift_right(x_37, x_49);
x_51 = lean_uint64_shift_left(x_50, x_49);
x_52 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_53 = lean_uint64_lor(x_51, x_52);
x_54 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set(x_54, 2, x_40);
lean_ctor_set(x_54, 3, x_41);
lean_ctor_set(x_54, 4, x_42);
lean_ctor_set(x_54, 5, x_43);
lean_ctor_set(x_54, 6, x_44);
lean_ctor_set_uint64(x_54, sizeof(void*)*7, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 8, x_38);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 9, x_46);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 10, x_47);
x_55 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_1);
x_56 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_6, x_31, x_55, x_10, x_54, x_12, x_13, x_14, x_36);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_unbox(x_30);
lean_dec(x_30);
x_62 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(x_31, x_6, x_29, x_61, x_59, x_9, x_60, x_11, x_12, x_13, x_14, x_58);
lean_dec(x_31);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_20 = x_63;
x_21 = x_64;
goto block_28;
}
else
{
uint8_t x_65; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
return x_56;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_56, 0);
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_56);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_69 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 9);
x_70 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 10);
x_71 = lean_ctor_get_uint8(x_35, 0);
x_72 = lean_ctor_get_uint8(x_35, 1);
x_73 = lean_ctor_get_uint8(x_35, 2);
x_74 = lean_ctor_get_uint8(x_35, 3);
x_75 = lean_ctor_get_uint8(x_35, 4);
x_76 = lean_ctor_get_uint8(x_35, 5);
x_77 = lean_ctor_get_uint8(x_35, 6);
x_78 = lean_ctor_get_uint8(x_35, 7);
x_79 = lean_ctor_get_uint8(x_35, 8);
x_80 = lean_ctor_get_uint8(x_35, 10);
x_81 = lean_ctor_get_uint8(x_35, 11);
x_82 = lean_ctor_get_uint8(x_35, 12);
x_83 = lean_ctor_get_uint8(x_35, 13);
x_84 = lean_ctor_get_uint8(x_35, 14);
x_85 = lean_ctor_get_uint8(x_35, 15);
x_86 = lean_ctor_get_uint8(x_35, 16);
lean_dec(x_35);
x_87 = 1;
x_88 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_88, 0, x_71);
lean_ctor_set_uint8(x_88, 1, x_72);
lean_ctor_set_uint8(x_88, 2, x_73);
lean_ctor_set_uint8(x_88, 3, x_74);
lean_ctor_set_uint8(x_88, 4, x_75);
lean_ctor_set_uint8(x_88, 5, x_76);
lean_ctor_set_uint8(x_88, 6, x_77);
lean_ctor_set_uint8(x_88, 7, x_78);
lean_ctor_set_uint8(x_88, 8, x_79);
lean_ctor_set_uint8(x_88, 9, x_87);
lean_ctor_set_uint8(x_88, 10, x_80);
lean_ctor_set_uint8(x_88, 11, x_81);
lean_ctor_set_uint8(x_88, 12, x_82);
lean_ctor_set_uint8(x_88, 13, x_83);
lean_ctor_set_uint8(x_88, 14, x_84);
lean_ctor_set_uint8(x_88, 15, x_85);
lean_ctor_set_uint8(x_88, 16, x_86);
x_89 = 2;
x_90 = lean_uint64_shift_right(x_37, x_89);
x_91 = lean_uint64_shift_left(x_90, x_89);
x_92 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_93 = lean_uint64_lor(x_91, x_92);
x_94 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_39);
lean_ctor_set(x_94, 2, x_40);
lean_ctor_set(x_94, 3, x_41);
lean_ctor_set(x_94, 4, x_42);
lean_ctor_set(x_94, 5, x_43);
lean_ctor_set(x_94, 6, x_44);
lean_ctor_set_uint64(x_94, sizeof(void*)*7, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 8, x_38);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 9, x_69);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 10, x_70);
x_95 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_1);
x_96 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_6, x_31, x_95, x_10, x_94, x_12, x_13, x_14, x_36);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_unbox(x_30);
lean_dec(x_30);
x_102 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(x_31, x_6, x_29, x_101, x_99, x_9, x_100, x_11, x_12, x_13, x_14, x_98);
lean_dec(x_31);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_20 = x_103;
x_21 = x_104;
goto block_28;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_105 = lean_ctor_get(x_96, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_107 = x_96;
} else {
 lean_dec_ref(x_96);
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
case 1:
{
lean_object* x_109; lean_object* x_110; uint64_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_109 = lean_ctor_get(x_11, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_32, 1);
lean_inc(x_110);
lean_dec(x_32);
x_111 = lean_ctor_get_uint64(x_11, sizeof(void*)*7);
x_112 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 8);
x_113 = lean_ctor_get(x_11, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_11, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_11, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_11, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_11, 5);
lean_inc(x_117);
x_118 = lean_ctor_get(x_11, 6);
lean_inc(x_118);
x_119 = !lean_is_exclusive(x_109);
if (x_119 == 0)
{
uint8_t x_120; uint8_t x_121; uint8_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
x_120 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 9);
x_121 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 10);
x_122 = 3;
lean_ctor_set_uint8(x_109, 9, x_122);
x_123 = 2;
x_124 = lean_uint64_shift_right(x_111, x_123);
x_125 = lean_uint64_shift_left(x_124, x_123);
x_126 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_127 = lean_uint64_lor(x_125, x_126);
x_128 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_128, 0, x_109);
lean_ctor_set(x_128, 1, x_113);
lean_ctor_set(x_128, 2, x_114);
lean_ctor_set(x_128, 3, x_115);
lean_ctor_set(x_128, 4, x_116);
lean_ctor_set(x_128, 5, x_117);
lean_ctor_set(x_128, 6, x_118);
lean_ctor_set_uint64(x_128, sizeof(void*)*7, x_127);
lean_ctor_set_uint8(x_128, sizeof(void*)*7 + 8, x_112);
lean_ctor_set_uint8(x_128, sizeof(void*)*7 + 9, x_120);
lean_ctor_set_uint8(x_128, sizeof(void*)*7 + 10, x_121);
x_129 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_1);
x_130 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_6, x_31, x_129, x_10, x_128, x_12, x_13, x_14, x_110);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_unbox(x_30);
lean_dec(x_30);
x_136 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(x_31, x_6, x_29, x_135, x_133, x_9, x_134, x_11, x_12, x_13, x_14, x_132);
lean_dec(x_31);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_20 = x_137;
x_21 = x_138;
goto block_28;
}
else
{
uint8_t x_139; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_130);
if (x_139 == 0)
{
return x_130;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_130, 0);
x_141 = lean_ctor_get(x_130, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_130);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_143 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 9);
x_144 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 10);
x_145 = lean_ctor_get_uint8(x_109, 0);
x_146 = lean_ctor_get_uint8(x_109, 1);
x_147 = lean_ctor_get_uint8(x_109, 2);
x_148 = lean_ctor_get_uint8(x_109, 3);
x_149 = lean_ctor_get_uint8(x_109, 4);
x_150 = lean_ctor_get_uint8(x_109, 5);
x_151 = lean_ctor_get_uint8(x_109, 6);
x_152 = lean_ctor_get_uint8(x_109, 7);
x_153 = lean_ctor_get_uint8(x_109, 8);
x_154 = lean_ctor_get_uint8(x_109, 10);
x_155 = lean_ctor_get_uint8(x_109, 11);
x_156 = lean_ctor_get_uint8(x_109, 12);
x_157 = lean_ctor_get_uint8(x_109, 13);
x_158 = lean_ctor_get_uint8(x_109, 14);
x_159 = lean_ctor_get_uint8(x_109, 15);
x_160 = lean_ctor_get_uint8(x_109, 16);
lean_dec(x_109);
x_161 = 3;
x_162 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_162, 0, x_145);
lean_ctor_set_uint8(x_162, 1, x_146);
lean_ctor_set_uint8(x_162, 2, x_147);
lean_ctor_set_uint8(x_162, 3, x_148);
lean_ctor_set_uint8(x_162, 4, x_149);
lean_ctor_set_uint8(x_162, 5, x_150);
lean_ctor_set_uint8(x_162, 6, x_151);
lean_ctor_set_uint8(x_162, 7, x_152);
lean_ctor_set_uint8(x_162, 8, x_153);
lean_ctor_set_uint8(x_162, 9, x_161);
lean_ctor_set_uint8(x_162, 10, x_154);
lean_ctor_set_uint8(x_162, 11, x_155);
lean_ctor_set_uint8(x_162, 12, x_156);
lean_ctor_set_uint8(x_162, 13, x_157);
lean_ctor_set_uint8(x_162, 14, x_158);
lean_ctor_set_uint8(x_162, 15, x_159);
lean_ctor_set_uint8(x_162, 16, x_160);
x_163 = 2;
x_164 = lean_uint64_shift_right(x_111, x_163);
x_165 = lean_uint64_shift_left(x_164, x_163);
x_166 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_167 = lean_uint64_lor(x_165, x_166);
x_168 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_113);
lean_ctor_set(x_168, 2, x_114);
lean_ctor_set(x_168, 3, x_115);
lean_ctor_set(x_168, 4, x_116);
lean_ctor_set(x_168, 5, x_117);
lean_ctor_set(x_168, 6, x_118);
lean_ctor_set_uint64(x_168, sizeof(void*)*7, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 8, x_112);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 9, x_143);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 10, x_144);
x_169 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_1);
x_170 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_6, x_31, x_169, x_10, x_168, x_12, x_13, x_14, x_110);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_unbox(x_30);
lean_dec(x_30);
x_176 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(x_31, x_6, x_29, x_175, x_173, x_9, x_174, x_11, x_12, x_13, x_14, x_172);
lean_dec(x_31);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_20 = x_177;
x_21 = x_178;
goto block_28;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_179 = lean_ctor_get(x_170, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
default: 
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_32, 1);
lean_inc(x_183);
lean_dec(x_32);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_31);
x_184 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_31, x_9, x_10, x_11, x_12, x_13, x_14, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_unbox(x_30);
lean_dec(x_30);
x_190 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(x_31, x_6, x_29, x_189, x_187, x_9, x_188, x_11, x_12, x_13, x_14, x_186);
lean_dec(x_31);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_20 = x_191;
x_21 = x_192;
goto block_28;
}
else
{
uint8_t x_193; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_184);
if (x_193 == 0)
{
return x_184;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_184, 0);
x_195 = lean_ctor_get(x_184, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_184);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_32);
if (x_197 == 0)
{
return x_32;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_32, 0);
x_199 = lean_ctor_get(x_32, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_32);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_array_get_size(x_16);
x_18 = lean_ptr_addr(x_1);
x_19 = lean_usize_to_uint64(x_18);
x_20 = 11;
x_21 = lean_uint64_mix_hash(x_19, x_20);
x_22 = 32;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = 16;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_30 = 1;
x_31 = lean_usize_sub(x_29, x_30);
x_32 = lean_usize_land(x_28, x_31);
x_33 = lean_array_uget(x_16, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_1, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_15, x_35);
lean_dec(x_15);
lean_inc(x_2);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_33);
x_38 = lean_array_uset(x_16, x_32, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(x_38);
lean_ctor_set(x_12, 1, x_45);
lean_ctor_set(x_12, 0, x_36);
x_46 = lean_st_ref_set(x_3, x_12, x_14);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_46, 0, x_10);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_ctor_set(x_12, 1, x_38);
lean_ctor_set(x_12, 0, x_36);
x_51 = lean_st_ref_set(x_3, x_12, x_14);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_51, 0, x_10);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_box(0);
x_57 = lean_array_uset(x_16, x_32, x_56);
lean_inc(x_2);
x_58 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(x_1, x_2, x_33);
x_59 = lean_array_uset(x_57, x_32, x_58);
lean_ctor_set(x_12, 1, x_59);
x_60 = lean_st_ref_set(x_3, x_12, x_14);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_60, 0, x_10);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_10);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_65 = lean_ctor_get(x_10, 1);
x_66 = lean_ctor_get(x_12, 0);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_12);
x_68 = lean_array_get_size(x_67);
x_69 = lean_ptr_addr(x_1);
x_70 = lean_usize_to_uint64(x_69);
x_71 = 11;
x_72 = lean_uint64_mix_hash(x_70, x_71);
x_73 = 32;
x_74 = lean_uint64_shift_right(x_72, x_73);
x_75 = lean_uint64_xor(x_72, x_74);
x_76 = 16;
x_77 = lean_uint64_shift_right(x_75, x_76);
x_78 = lean_uint64_xor(x_75, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_81 = 1;
x_82 = lean_usize_sub(x_80, x_81);
x_83 = lean_usize_land(x_79, x_82);
x_84 = lean_array_uget(x_67, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_66, x_86);
lean_dec(x_66);
lean_inc(x_2);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_2);
lean_ctor_set(x_88, 2, x_84);
x_89 = lean_array_uset(x_67, x_83, x_88);
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
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_st_ref_set(x_3, x_97, x_65);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_87);
lean_ctor_set(x_102, 1, x_89);
x_103 = lean_st_ref_set(x_3, x_102, x_65);
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
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_10);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_box(0);
x_108 = lean_array_uset(x_67, x_83, x_107);
lean_inc(x_2);
x_109 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(x_1, x_2, x_84);
x_110 = lean_array_uset(x_108, x_83, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_66);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_st_ref_set(x_3, x_111, x_65);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 0, x_2);
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_10);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; size_t x_132; size_t x_133; size_t x_134; size_t x_135; size_t x_136; lean_object* x_137; uint8_t x_138; 
x_116 = lean_ctor_get(x_10, 0);
x_117 = lean_ctor_get(x_10, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_10);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = lean_array_get_size(x_119);
x_122 = lean_ptr_addr(x_1);
x_123 = lean_usize_to_uint64(x_122);
x_124 = 11;
x_125 = lean_uint64_mix_hash(x_123, x_124);
x_126 = 32;
x_127 = lean_uint64_shift_right(x_125, x_126);
x_128 = lean_uint64_xor(x_125, x_127);
x_129 = 16;
x_130 = lean_uint64_shift_right(x_128, x_129);
x_131 = lean_uint64_xor(x_128, x_130);
x_132 = lean_uint64_to_usize(x_131);
x_133 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_134 = 1;
x_135 = lean_usize_sub(x_133, x_134);
x_136 = lean_usize_land(x_132, x_135);
x_137 = lean_array_uget(x_119, x_136);
x_138 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_1, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_118, x_139);
lean_dec(x_118);
lean_inc(x_2);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_1);
lean_ctor_set(x_141, 1, x_2);
lean_ctor_set(x_141, 2, x_137);
x_142 = lean_array_uset(x_119, x_136, x_141);
x_143 = lean_unsigned_to_nat(4u);
x_144 = lean_nat_mul(x_140, x_143);
x_145 = lean_unsigned_to_nat(3u);
x_146 = lean_nat_div(x_144, x_145);
lean_dec(x_144);
x_147 = lean_array_get_size(x_142);
x_148 = lean_nat_dec_le(x_146, x_147);
lean_dec(x_147);
lean_dec(x_146);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(x_142);
if (lean_is_scalar(x_120)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_120;
}
lean_ctor_set(x_150, 0, x_140);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_st_ref_set(x_3, x_150, x_117);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_2);
lean_ctor_set(x_154, 1, x_4);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
if (lean_is_scalar(x_120)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_120;
}
lean_ctor_set(x_156, 0, x_140);
lean_ctor_set(x_156, 1, x_142);
x_157 = lean_st_ref_set(x_3, x_156, x_117);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_2);
lean_ctor_set(x_160, 1, x_4);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_162 = lean_box(0);
x_163 = lean_array_uset(x_119, x_136, x_162);
lean_inc(x_2);
x_164 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(x_1, x_2, x_137);
x_165 = lean_array_uset(x_163, x_136, x_164);
if (lean_is_scalar(x_120)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_120;
}
lean_ctor_set(x_166, 0, x_118);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_st_ref_set(x_3, x_166, x_117);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_2);
lean_ctor_set(x_170, 1, x_4);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
return x_171;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nestedProof", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1;
x_2 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2;
x_3 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_12; lean_object* x_43; lean_object* x_77; uint8_t x_78; 
lean_dec(x_4);
x_77 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_78 = l_Lean_Expr_isConstOf(x_2, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_43 = x_79;
goto block_76;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_array_get_size(x_3);
x_81 = lean_unsigned_to_nat(2u);
x_82 = lean_nat_dec_eq(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_80);
x_83 = lean_box(0);
x_43 = x_83;
goto block_76;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_80);
lean_dec(x_80);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Lean_instInhabitedExpr;
x_87 = l_outOfBounds___rarg(x_86);
x_12 = x_87;
goto block_42;
}
else
{
lean_object* x_88; 
x_88 = lean_array_fget(x_3, x_84);
x_12 = x_88;
goto block_42;
}
}
}
block_42:
{
lean_object* x_13; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_12);
x_13 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_inc(x_18);
x_19 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_18, x_16);
if (lean_obj_tag(x_19) == 0)
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_21 = lean_ptr_addr(x_16);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
x_24 = lean_array_set(x_3, x_23, x_16);
x_25 = l_Lean_mkAppN(x_2, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
lean_inc(x_25);
x_28 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_18, x_16, x_25);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_25, x_5, x_29, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
lean_inc(x_1);
x_33 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_18, x_16, x_1);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_1);
x_35 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_34, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
lean_dec(x_19);
x_37 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_36, x_5, x_17, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
block_76:
{
lean_object* x_44; 
lean_dec(x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_44 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_get_size(x_3);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_50);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_55 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_47, x_51, x_51, x_54, x_49, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_51);
lean_dec(x_47);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_2);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
lean_inc(x_1);
x_62 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_61, x_7, x_8, x_9, x_10, x_60);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec(x_57);
x_66 = l_Lean_mkAppN(x_2, x_65);
lean_dec(x_65);
x_67 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_66, x_5, x_64, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_55);
if (x_68 == 0)
{
return x_55;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_55, 0);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_55);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_44);
if (x_72 == 0)
{
return x_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_44, 0);
x_74 = lean_ctor_get(x_44, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_44);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
case 1:
{
lean_object* x_89; lean_object* x_120; lean_object* x_154; uint8_t x_155; 
lean_dec(x_4);
x_154 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_155 = l_Lean_Expr_isConstOf(x_2, x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_box(0);
x_120 = x_156;
goto block_153;
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_array_get_size(x_3);
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_nat_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_157);
x_160 = lean_box(0);
x_120 = x_160;
goto block_153;
}
else
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_unsigned_to_nat(0u);
x_162 = lean_nat_dec_lt(x_161, x_157);
lean_dec(x_157);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_instInhabitedExpr;
x_164 = l_outOfBounds___rarg(x_163);
x_89 = x_164;
goto block_119;
}
else
{
lean_object* x_165; 
x_165 = lean_array_fget(x_3, x_161);
x_89 = x_165;
goto block_119;
}
}
}
block_119:
{
lean_object* x_90; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_89);
x_90 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_89, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_ctor_get(x_94, 2);
lean_inc(x_95);
lean_inc(x_95);
x_96 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_95, x_93);
if (lean_obj_tag(x_96) == 0)
{
size_t x_97; size_t x_98; uint8_t x_99; 
x_97 = lean_ptr_addr(x_89);
lean_dec(x_89);
x_98 = lean_ptr_addr(x_93);
x_99 = lean_usize_dec_eq(x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_unsigned_to_nat(0u);
lean_inc(x_93);
x_101 = lean_array_set(x_3, x_100, x_93);
x_102 = l_Lean_mkAppN(x_2, x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_94, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
lean_dec(x_94);
lean_inc(x_102);
x_105 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_95, x_93, x_102);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_102, x_5, x_106, x_7, x_8, x_9, x_10, x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_94, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_94, 1);
lean_inc(x_109);
lean_dec(x_94);
lean_inc(x_1);
x_110 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_95, x_93, x_1);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_110);
lean_inc(x_1);
x_112 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_111, x_7, x_8, x_9, x_10, x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_89);
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_ctor_get(x_96, 0);
lean_inc(x_113);
lean_dec(x_96);
x_114 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_113, x_5, x_94, x_7, x_8, x_9, x_10, x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_90);
if (x_115 == 0)
{
return x_90;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_90, 0);
x_117 = lean_ctor_get(x_90, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_90);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
block_153:
{
lean_object* x_121; 
lean_dec(x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_121 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_array_get_size(x_3);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_128, 2, x_127);
x_129 = 0;
x_130 = lean_box(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_3);
lean_ctor_set(x_131, 1, x_130);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_132 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_124, x_128, x_128, x_131, x_126, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_123);
lean_dec(x_128);
lean_dec(x_124);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_2);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_dec(x_132);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_dec(x_133);
lean_inc(x_1);
x_139 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_138, x_7, x_8, x_9, x_10, x_137);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_132, 1);
lean_inc(x_140);
lean_dec(x_132);
x_141 = lean_ctor_get(x_133, 1);
lean_inc(x_141);
lean_dec(x_133);
x_142 = lean_ctor_get(x_134, 0);
lean_inc(x_142);
lean_dec(x_134);
x_143 = l_Lean_mkAppN(x_2, x_142);
lean_dec(x_142);
x_144 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_143, x_5, x_141, x_7, x_8, x_9, x_10, x_140);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_144;
}
}
else
{
uint8_t x_145; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_132);
if (x_145 == 0)
{
return x_132;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_132, 0);
x_147 = lean_ctor_get(x_132, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_132);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_121);
if (x_149 == 0)
{
return x_121;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_121, 0);
x_151 = lean_ctor_get(x_121, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_121);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
case 2:
{
lean_object* x_166; lean_object* x_197; lean_object* x_231; uint8_t x_232; 
lean_dec(x_4);
x_231 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_232 = l_Lean_Expr_isConstOf(x_2, x_231);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_box(0);
x_197 = x_233;
goto block_230;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_array_get_size(x_3);
x_235 = lean_unsigned_to_nat(2u);
x_236 = lean_nat_dec_eq(x_234, x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_234);
x_237 = lean_box(0);
x_197 = x_237;
goto block_230;
}
else
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_unsigned_to_nat(0u);
x_239 = lean_nat_dec_lt(x_238, x_234);
lean_dec(x_234);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = l_Lean_instInhabitedExpr;
x_241 = l_outOfBounds___rarg(x_240);
x_166 = x_241;
goto block_196;
}
else
{
lean_object* x_242; 
x_242 = lean_array_fget(x_3, x_238);
x_166 = x_242;
goto block_196;
}
}
}
block_196:
{
lean_object* x_167; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_166);
x_167 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_166, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_ctor_get(x_171, 2);
lean_inc(x_172);
lean_inc(x_172);
x_173 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_172, x_170);
if (lean_obj_tag(x_173) == 0)
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_166);
lean_dec(x_166);
x_175 = lean_ptr_addr(x_170);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_177 = lean_unsigned_to_nat(0u);
lean_inc(x_170);
x_178 = lean_array_set(x_3, x_177, x_170);
x_179 = l_Lean_mkAppN(x_2, x_178);
lean_dec(x_178);
x_180 = lean_ctor_get(x_171, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
lean_dec(x_171);
lean_inc(x_179);
x_182 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_172, x_170, x_179);
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
lean_ctor_set(x_183, 2, x_182);
x_184 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_179, x_5, x_183, x_7, x_8, x_9, x_10, x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_3);
lean_dec(x_2);
x_185 = lean_ctor_get(x_171, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_171, 1);
lean_inc(x_186);
lean_dec(x_171);
lean_inc(x_1);
x_187 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_172, x_170, x_1);
x_188 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
lean_ctor_set(x_188, 2, x_187);
lean_inc(x_1);
x_189 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_188, x_7, x_8, x_9, x_10, x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_3);
lean_dec(x_2);
x_190 = lean_ctor_get(x_173, 0);
lean_inc(x_190);
lean_dec(x_173);
x_191 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_190, x_5, x_171, x_7, x_8, x_9, x_10, x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_166);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_167);
if (x_192 == 0)
{
return x_167;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_167, 0);
x_194 = lean_ctor_get(x_167, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_167);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
block_230:
{
lean_object* x_198; 
lean_dec(x_197);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_198 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_array_get_size(x_3);
x_203 = lean_unsigned_to_nat(0u);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_204);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_3);
lean_ctor_set(x_208, 1, x_207);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_209 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_201, x_205, x_205, x_208, x_203, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_200);
lean_dec(x_205);
lean_dec(x_201);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
x_213 = lean_unbox(x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_211);
lean_dec(x_2);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
lean_dec(x_209);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
lean_dec(x_210);
lean_inc(x_1);
x_216 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_215, x_7, x_8, x_9, x_10, x_214);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_209, 1);
lean_inc(x_217);
lean_dec(x_209);
x_218 = lean_ctor_get(x_210, 1);
lean_inc(x_218);
lean_dec(x_210);
x_219 = lean_ctor_get(x_211, 0);
lean_inc(x_219);
lean_dec(x_211);
x_220 = l_Lean_mkAppN(x_2, x_219);
lean_dec(x_219);
x_221 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_220, x_5, x_218, x_7, x_8, x_9, x_10, x_217);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_221;
}
}
else
{
uint8_t x_222; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_209);
if (x_222 == 0)
{
return x_209;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_209, 0);
x_224 = lean_ctor_get(x_209, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_209);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_198);
if (x_226 == 0)
{
return x_198;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_198, 0);
x_228 = lean_ctor_get(x_198, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_198);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
case 3:
{
lean_object* x_243; lean_object* x_274; lean_object* x_308; uint8_t x_309; 
lean_dec(x_4);
x_308 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_309 = l_Lean_Expr_isConstOf(x_2, x_308);
if (x_309 == 0)
{
lean_object* x_310; 
x_310 = lean_box(0);
x_274 = x_310;
goto block_307;
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = lean_array_get_size(x_3);
x_312 = lean_unsigned_to_nat(2u);
x_313 = lean_nat_dec_eq(x_311, x_312);
if (x_313 == 0)
{
lean_object* x_314; 
lean_dec(x_311);
x_314 = lean_box(0);
x_274 = x_314;
goto block_307;
}
else
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_unsigned_to_nat(0u);
x_316 = lean_nat_dec_lt(x_315, x_311);
lean_dec(x_311);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = l_Lean_instInhabitedExpr;
x_318 = l_outOfBounds___rarg(x_317);
x_243 = x_318;
goto block_273;
}
else
{
lean_object* x_319; 
x_319 = lean_array_fget(x_3, x_315);
x_243 = x_319;
goto block_273;
}
}
}
block_273:
{
lean_object* x_244; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_243);
x_244 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_243, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec(x_245);
x_249 = lean_ctor_get(x_248, 2);
lean_inc(x_249);
lean_inc(x_249);
x_250 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_249, x_247);
if (lean_obj_tag(x_250) == 0)
{
size_t x_251; size_t x_252; uint8_t x_253; 
x_251 = lean_ptr_addr(x_243);
lean_dec(x_243);
x_252 = lean_ptr_addr(x_247);
x_253 = lean_usize_dec_eq(x_251, x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_254 = lean_unsigned_to_nat(0u);
lean_inc(x_247);
x_255 = lean_array_set(x_3, x_254, x_247);
x_256 = l_Lean_mkAppN(x_2, x_255);
lean_dec(x_255);
x_257 = lean_ctor_get(x_248, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_248, 1);
lean_inc(x_258);
lean_dec(x_248);
lean_inc(x_256);
x_259 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_249, x_247, x_256);
x_260 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
lean_ctor_set(x_260, 2, x_259);
x_261 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_256, x_5, x_260, x_7, x_8, x_9, x_10, x_246);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_3);
lean_dec(x_2);
x_262 = lean_ctor_get(x_248, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_248, 1);
lean_inc(x_263);
lean_dec(x_248);
lean_inc(x_1);
x_264 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_249, x_247, x_1);
x_265 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
lean_ctor_set(x_265, 2, x_264);
lean_inc(x_1);
x_266 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_265, x_7, x_8, x_9, x_10, x_246);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_243);
lean_dec(x_3);
lean_dec(x_2);
x_267 = lean_ctor_get(x_250, 0);
lean_inc(x_267);
lean_dec(x_250);
x_268 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_267, x_5, x_248, x_7, x_8, x_9, x_10, x_246);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_268;
}
}
else
{
uint8_t x_269; 
lean_dec(x_243);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_269 = !lean_is_exclusive(x_244);
if (x_269 == 0)
{
return x_244;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_244, 0);
x_271 = lean_ctor_get(x_244, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_244);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
block_307:
{
lean_object* x_275; 
lean_dec(x_274);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_275 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_array_get_size(x_3);
x_280 = lean_unsigned_to_nat(0u);
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_279);
lean_ctor_set(x_282, 2, x_281);
x_283 = 0;
x_284 = lean_box(x_283);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_3);
lean_ctor_set(x_285, 1, x_284);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_286 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_278, x_282, x_282, x_285, x_280, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_277);
lean_dec(x_282);
lean_dec(x_278);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
x_290 = lean_unbox(x_289);
lean_dec(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_288);
lean_dec(x_2);
x_291 = lean_ctor_get(x_286, 1);
lean_inc(x_291);
lean_dec(x_286);
x_292 = lean_ctor_get(x_287, 1);
lean_inc(x_292);
lean_dec(x_287);
lean_inc(x_1);
x_293 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_292, x_7, x_8, x_9, x_10, x_291);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_ctor_get(x_286, 1);
lean_inc(x_294);
lean_dec(x_286);
x_295 = lean_ctor_get(x_287, 1);
lean_inc(x_295);
lean_dec(x_287);
x_296 = lean_ctor_get(x_288, 0);
lean_inc(x_296);
lean_dec(x_288);
x_297 = l_Lean_mkAppN(x_2, x_296);
lean_dec(x_296);
x_298 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_297, x_5, x_295, x_7, x_8, x_9, x_10, x_294);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_298;
}
}
else
{
uint8_t x_299; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_286);
if (x_299 == 0)
{
return x_286;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_286, 0);
x_301 = lean_ctor_get(x_286, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_286);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
else
{
uint8_t x_303; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_303 = !lean_is_exclusive(x_275);
if (x_303 == 0)
{
return x_275;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_275, 0);
x_305 = lean_ctor_get(x_275, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_275);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
}
case 4:
{
lean_object* x_320; lean_object* x_351; lean_object* x_385; uint8_t x_386; 
lean_dec(x_4);
x_385 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_386 = l_Lean_Expr_isConstOf(x_2, x_385);
if (x_386 == 0)
{
lean_object* x_387; 
x_387 = lean_box(0);
x_351 = x_387;
goto block_384;
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_388 = lean_array_get_size(x_3);
x_389 = lean_unsigned_to_nat(2u);
x_390 = lean_nat_dec_eq(x_388, x_389);
if (x_390 == 0)
{
lean_object* x_391; 
lean_dec(x_388);
x_391 = lean_box(0);
x_351 = x_391;
goto block_384;
}
else
{
lean_object* x_392; uint8_t x_393; 
x_392 = lean_unsigned_to_nat(0u);
x_393 = lean_nat_dec_lt(x_392, x_388);
lean_dec(x_388);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
x_394 = l_Lean_instInhabitedExpr;
x_395 = l_outOfBounds___rarg(x_394);
x_320 = x_395;
goto block_350;
}
else
{
lean_object* x_396; 
x_396 = lean_array_fget(x_3, x_392);
x_320 = x_396;
goto block_350;
}
}
}
block_350:
{
lean_object* x_321; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_320);
x_321 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_320, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_ctor_get(x_322, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_ctor_get(x_325, 2);
lean_inc(x_326);
lean_inc(x_326);
x_327 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_326, x_324);
if (lean_obj_tag(x_327) == 0)
{
size_t x_328; size_t x_329; uint8_t x_330; 
x_328 = lean_ptr_addr(x_320);
lean_dec(x_320);
x_329 = lean_ptr_addr(x_324);
x_330 = lean_usize_dec_eq(x_328, x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_331 = lean_unsigned_to_nat(0u);
lean_inc(x_324);
x_332 = lean_array_set(x_3, x_331, x_324);
x_333 = l_Lean_mkAppN(x_2, x_332);
lean_dec(x_332);
x_334 = lean_ctor_get(x_325, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_325, 1);
lean_inc(x_335);
lean_dec(x_325);
lean_inc(x_333);
x_336 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_326, x_324, x_333);
x_337 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
lean_ctor_set(x_337, 2, x_336);
x_338 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_333, x_5, x_337, x_7, x_8, x_9, x_10, x_323);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_3);
lean_dec(x_2);
x_339 = lean_ctor_get(x_325, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_325, 1);
lean_inc(x_340);
lean_dec(x_325);
lean_inc(x_1);
x_341 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_326, x_324, x_1);
x_342 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
lean_ctor_set(x_342, 2, x_341);
lean_inc(x_1);
x_343 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_342, x_7, x_8, x_9, x_10, x_323);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_320);
lean_dec(x_3);
lean_dec(x_2);
x_344 = lean_ctor_get(x_327, 0);
lean_inc(x_344);
lean_dec(x_327);
x_345 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_344, x_5, x_325, x_7, x_8, x_9, x_10, x_323);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_345;
}
}
else
{
uint8_t x_346; 
lean_dec(x_320);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_346 = !lean_is_exclusive(x_321);
if (x_346 == 0)
{
return x_321;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_321, 0);
x_348 = lean_ctor_get(x_321, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_321);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
block_384:
{
lean_object* x_352; 
lean_dec(x_351);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_352 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_353, 0);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_array_get_size(x_3);
x_357 = lean_unsigned_to_nat(0u);
x_358 = lean_unsigned_to_nat(1u);
x_359 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_356);
lean_ctor_set(x_359, 2, x_358);
x_360 = 0;
x_361 = lean_box(x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_3);
lean_ctor_set(x_362, 1, x_361);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_363 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_355, x_359, x_359, x_362, x_357, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_354);
lean_dec(x_359);
lean_dec(x_355);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
x_367 = lean_unbox(x_366);
lean_dec(x_366);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_365);
lean_dec(x_2);
x_368 = lean_ctor_get(x_363, 1);
lean_inc(x_368);
lean_dec(x_363);
x_369 = lean_ctor_get(x_364, 1);
lean_inc(x_369);
lean_dec(x_364);
lean_inc(x_1);
x_370 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_369, x_7, x_8, x_9, x_10, x_368);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_ctor_get(x_363, 1);
lean_inc(x_371);
lean_dec(x_363);
x_372 = lean_ctor_get(x_364, 1);
lean_inc(x_372);
lean_dec(x_364);
x_373 = lean_ctor_get(x_365, 0);
lean_inc(x_373);
lean_dec(x_365);
x_374 = l_Lean_mkAppN(x_2, x_373);
lean_dec(x_373);
x_375 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_374, x_5, x_372, x_7, x_8, x_9, x_10, x_371);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_375;
}
}
else
{
uint8_t x_376; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_363);
if (x_376 == 0)
{
return x_363;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_363, 0);
x_378 = lean_ctor_get(x_363, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_363);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
else
{
uint8_t x_380; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_380 = !lean_is_exclusive(x_352);
if (x_380 == 0)
{
return x_352;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_352, 0);
x_382 = lean_ctor_get(x_352, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_352);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
}
case 5:
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_397 = lean_ctor_get(x_2, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_2, 1);
lean_inc(x_398);
lean_dec(x_2);
x_399 = lean_array_set(x_3, x_4, x_398);
x_400 = lean_unsigned_to_nat(1u);
x_401 = lean_nat_sub(x_4, x_400);
lean_dec(x_4);
x_2 = x_397;
x_3 = x_399;
x_4 = x_401;
goto _start;
}
case 6:
{
lean_object* x_403; lean_object* x_434; lean_object* x_468; uint8_t x_469; 
lean_dec(x_4);
x_468 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_469 = l_Lean_Expr_isConstOf(x_2, x_468);
if (x_469 == 0)
{
lean_object* x_470; 
x_470 = lean_box(0);
x_434 = x_470;
goto block_467;
}
else
{
lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_471 = lean_array_get_size(x_3);
x_472 = lean_unsigned_to_nat(2u);
x_473 = lean_nat_dec_eq(x_471, x_472);
if (x_473 == 0)
{
lean_object* x_474; 
lean_dec(x_471);
x_474 = lean_box(0);
x_434 = x_474;
goto block_467;
}
else
{
lean_object* x_475; uint8_t x_476; 
x_475 = lean_unsigned_to_nat(0u);
x_476 = lean_nat_dec_lt(x_475, x_471);
lean_dec(x_471);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = l_Lean_instInhabitedExpr;
x_478 = l_outOfBounds___rarg(x_477);
x_403 = x_478;
goto block_433;
}
else
{
lean_object* x_479; 
x_479 = lean_array_fget(x_3, x_475);
x_403 = x_479;
goto block_433;
}
}
}
block_433:
{
lean_object* x_404; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_403);
x_404 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_403, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_409 = lean_ctor_get(x_408, 2);
lean_inc(x_409);
lean_inc(x_409);
x_410 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_409, x_407);
if (lean_obj_tag(x_410) == 0)
{
size_t x_411; size_t x_412; uint8_t x_413; 
x_411 = lean_ptr_addr(x_403);
lean_dec(x_403);
x_412 = lean_ptr_addr(x_407);
x_413 = lean_usize_dec_eq(x_411, x_412);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_414 = lean_unsigned_to_nat(0u);
lean_inc(x_407);
x_415 = lean_array_set(x_3, x_414, x_407);
x_416 = l_Lean_mkAppN(x_2, x_415);
lean_dec(x_415);
x_417 = lean_ctor_get(x_408, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_408, 1);
lean_inc(x_418);
lean_dec(x_408);
lean_inc(x_416);
x_419 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_409, x_407, x_416);
x_420 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
lean_ctor_set(x_420, 2, x_419);
x_421 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_416, x_5, x_420, x_7, x_8, x_9, x_10, x_406);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_3);
lean_dec(x_2);
x_422 = lean_ctor_get(x_408, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_408, 1);
lean_inc(x_423);
lean_dec(x_408);
lean_inc(x_1);
x_424 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_409, x_407, x_1);
x_425 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
lean_ctor_set(x_425, 2, x_424);
lean_inc(x_1);
x_426 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_425, x_7, x_8, x_9, x_10, x_406);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_409);
lean_dec(x_407);
lean_dec(x_403);
lean_dec(x_3);
lean_dec(x_2);
x_427 = lean_ctor_get(x_410, 0);
lean_inc(x_427);
lean_dec(x_410);
x_428 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_427, x_5, x_408, x_7, x_8, x_9, x_10, x_406);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_428;
}
}
else
{
uint8_t x_429; 
lean_dec(x_403);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_429 = !lean_is_exclusive(x_404);
if (x_429 == 0)
{
return x_404;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_404, 0);
x_431 = lean_ctor_get(x_404, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_404);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
block_467:
{
lean_object* x_435; 
lean_dec(x_434);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_435 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_438 = lean_ctor_get(x_436, 0);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_array_get_size(x_3);
x_440 = lean_unsigned_to_nat(0u);
x_441 = lean_unsigned_to_nat(1u);
x_442 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_439);
lean_ctor_set(x_442, 2, x_441);
x_443 = 0;
x_444 = lean_box(x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_3);
lean_ctor_set(x_445, 1, x_444);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_446 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_438, x_442, x_442, x_445, x_440, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_437);
lean_dec(x_442);
lean_dec(x_438);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
x_450 = lean_unbox(x_449);
lean_dec(x_449);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_448);
lean_dec(x_2);
x_451 = lean_ctor_get(x_446, 1);
lean_inc(x_451);
lean_dec(x_446);
x_452 = lean_ctor_get(x_447, 1);
lean_inc(x_452);
lean_dec(x_447);
lean_inc(x_1);
x_453 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_452, x_7, x_8, x_9, x_10, x_451);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_453;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_454 = lean_ctor_get(x_446, 1);
lean_inc(x_454);
lean_dec(x_446);
x_455 = lean_ctor_get(x_447, 1);
lean_inc(x_455);
lean_dec(x_447);
x_456 = lean_ctor_get(x_448, 0);
lean_inc(x_456);
lean_dec(x_448);
x_457 = l_Lean_mkAppN(x_2, x_456);
lean_dec(x_456);
x_458 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_457, x_5, x_455, x_7, x_8, x_9, x_10, x_454);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_458;
}
}
else
{
uint8_t x_459; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_459 = !lean_is_exclusive(x_446);
if (x_459 == 0)
{
return x_446;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_446, 0);
x_461 = lean_ctor_get(x_446, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_446);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
return x_462;
}
}
}
else
{
uint8_t x_463; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_463 = !lean_is_exclusive(x_435);
if (x_463 == 0)
{
return x_435;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_435, 0);
x_465 = lean_ctor_get(x_435, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_435);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
case 7:
{
lean_object* x_480; lean_object* x_511; lean_object* x_545; uint8_t x_546; 
lean_dec(x_4);
x_545 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_546 = l_Lean_Expr_isConstOf(x_2, x_545);
if (x_546 == 0)
{
lean_object* x_547; 
x_547 = lean_box(0);
x_511 = x_547;
goto block_544;
}
else
{
lean_object* x_548; lean_object* x_549; uint8_t x_550; 
x_548 = lean_array_get_size(x_3);
x_549 = lean_unsigned_to_nat(2u);
x_550 = lean_nat_dec_eq(x_548, x_549);
if (x_550 == 0)
{
lean_object* x_551; 
lean_dec(x_548);
x_551 = lean_box(0);
x_511 = x_551;
goto block_544;
}
else
{
lean_object* x_552; uint8_t x_553; 
x_552 = lean_unsigned_to_nat(0u);
x_553 = lean_nat_dec_lt(x_552, x_548);
lean_dec(x_548);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; 
x_554 = l_Lean_instInhabitedExpr;
x_555 = l_outOfBounds___rarg(x_554);
x_480 = x_555;
goto block_510;
}
else
{
lean_object* x_556; 
x_556 = lean_array_fget(x_3, x_552);
x_480 = x_556;
goto block_510;
}
}
}
block_510:
{
lean_object* x_481; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_480);
x_481 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_480, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_485);
lean_dec(x_482);
x_486 = lean_ctor_get(x_485, 2);
lean_inc(x_486);
lean_inc(x_486);
x_487 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_486, x_484);
if (lean_obj_tag(x_487) == 0)
{
size_t x_488; size_t x_489; uint8_t x_490; 
x_488 = lean_ptr_addr(x_480);
lean_dec(x_480);
x_489 = lean_ptr_addr(x_484);
x_490 = lean_usize_dec_eq(x_488, x_489);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_491 = lean_unsigned_to_nat(0u);
lean_inc(x_484);
x_492 = lean_array_set(x_3, x_491, x_484);
x_493 = l_Lean_mkAppN(x_2, x_492);
lean_dec(x_492);
x_494 = lean_ctor_get(x_485, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_485, 1);
lean_inc(x_495);
lean_dec(x_485);
lean_inc(x_493);
x_496 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_486, x_484, x_493);
x_497 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_495);
lean_ctor_set(x_497, 2, x_496);
x_498 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_493, x_5, x_497, x_7, x_8, x_9, x_10, x_483);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_498;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_3);
lean_dec(x_2);
x_499 = lean_ctor_get(x_485, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_485, 1);
lean_inc(x_500);
lean_dec(x_485);
lean_inc(x_1);
x_501 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_486, x_484, x_1);
x_502 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_500);
lean_ctor_set(x_502, 2, x_501);
lean_inc(x_1);
x_503 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_502, x_7, x_8, x_9, x_10, x_483);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; 
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_480);
lean_dec(x_3);
lean_dec(x_2);
x_504 = lean_ctor_get(x_487, 0);
lean_inc(x_504);
lean_dec(x_487);
x_505 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_504, x_5, x_485, x_7, x_8, x_9, x_10, x_483);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_505;
}
}
else
{
uint8_t x_506; 
lean_dec(x_480);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_481);
if (x_506 == 0)
{
return x_481;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_481, 0);
x_508 = lean_ctor_get(x_481, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_481);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
block_544:
{
lean_object* x_512; 
lean_dec(x_511);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_512 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = lean_ctor_get(x_513, 0);
lean_inc(x_515);
lean_dec(x_513);
x_516 = lean_array_get_size(x_3);
x_517 = lean_unsigned_to_nat(0u);
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_516);
lean_ctor_set(x_519, 2, x_518);
x_520 = 0;
x_521 = lean_box(x_520);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_3);
lean_ctor_set(x_522, 1, x_521);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_523 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_515, x_519, x_519, x_522, x_517, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_514);
lean_dec(x_519);
lean_dec(x_515);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
x_527 = lean_unbox(x_526);
lean_dec(x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_525);
lean_dec(x_2);
x_528 = lean_ctor_get(x_523, 1);
lean_inc(x_528);
lean_dec(x_523);
x_529 = lean_ctor_get(x_524, 1);
lean_inc(x_529);
lean_dec(x_524);
lean_inc(x_1);
x_530 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_529, x_7, x_8, x_9, x_10, x_528);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_530;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_531 = lean_ctor_get(x_523, 1);
lean_inc(x_531);
lean_dec(x_523);
x_532 = lean_ctor_get(x_524, 1);
lean_inc(x_532);
lean_dec(x_524);
x_533 = lean_ctor_get(x_525, 0);
lean_inc(x_533);
lean_dec(x_525);
x_534 = l_Lean_mkAppN(x_2, x_533);
lean_dec(x_533);
x_535 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_534, x_5, x_532, x_7, x_8, x_9, x_10, x_531);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_535;
}
}
else
{
uint8_t x_536; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_536 = !lean_is_exclusive(x_523);
if (x_536 == 0)
{
return x_523;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_537 = lean_ctor_get(x_523, 0);
x_538 = lean_ctor_get(x_523, 1);
lean_inc(x_538);
lean_inc(x_537);
lean_dec(x_523);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
return x_539;
}
}
}
else
{
uint8_t x_540; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_540 = !lean_is_exclusive(x_512);
if (x_540 == 0)
{
return x_512;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_512, 0);
x_542 = lean_ctor_get(x_512, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_512);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
}
case 8:
{
lean_object* x_557; lean_object* x_588; lean_object* x_622; uint8_t x_623; 
lean_dec(x_4);
x_622 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_623 = l_Lean_Expr_isConstOf(x_2, x_622);
if (x_623 == 0)
{
lean_object* x_624; 
x_624 = lean_box(0);
x_588 = x_624;
goto block_621;
}
else
{
lean_object* x_625; lean_object* x_626; uint8_t x_627; 
x_625 = lean_array_get_size(x_3);
x_626 = lean_unsigned_to_nat(2u);
x_627 = lean_nat_dec_eq(x_625, x_626);
if (x_627 == 0)
{
lean_object* x_628; 
lean_dec(x_625);
x_628 = lean_box(0);
x_588 = x_628;
goto block_621;
}
else
{
lean_object* x_629; uint8_t x_630; 
x_629 = lean_unsigned_to_nat(0u);
x_630 = lean_nat_dec_lt(x_629, x_625);
lean_dec(x_625);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
x_631 = l_Lean_instInhabitedExpr;
x_632 = l_outOfBounds___rarg(x_631);
x_557 = x_632;
goto block_587;
}
else
{
lean_object* x_633; 
x_633 = lean_array_fget(x_3, x_629);
x_557 = x_633;
goto block_587;
}
}
}
block_587:
{
lean_object* x_558; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_557);
x_558 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_557, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
x_561 = lean_ctor_get(x_559, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_559, 1);
lean_inc(x_562);
lean_dec(x_559);
x_563 = lean_ctor_get(x_562, 2);
lean_inc(x_563);
lean_inc(x_563);
x_564 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_563, x_561);
if (lean_obj_tag(x_564) == 0)
{
size_t x_565; size_t x_566; uint8_t x_567; 
x_565 = lean_ptr_addr(x_557);
lean_dec(x_557);
x_566 = lean_ptr_addr(x_561);
x_567 = lean_usize_dec_eq(x_565, x_566);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_568 = lean_unsigned_to_nat(0u);
lean_inc(x_561);
x_569 = lean_array_set(x_3, x_568, x_561);
x_570 = l_Lean_mkAppN(x_2, x_569);
lean_dec(x_569);
x_571 = lean_ctor_get(x_562, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_562, 1);
lean_inc(x_572);
lean_dec(x_562);
lean_inc(x_570);
x_573 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_563, x_561, x_570);
x_574 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_572);
lean_ctor_set(x_574, 2, x_573);
x_575 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_570, x_5, x_574, x_7, x_8, x_9, x_10, x_560);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_575;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_3);
lean_dec(x_2);
x_576 = lean_ctor_get(x_562, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_562, 1);
lean_inc(x_577);
lean_dec(x_562);
lean_inc(x_1);
x_578 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_563, x_561, x_1);
x_579 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
lean_ctor_set(x_579, 2, x_578);
lean_inc(x_1);
x_580 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_579, x_7, x_8, x_9, x_10, x_560);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; 
lean_dec(x_563);
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_3);
lean_dec(x_2);
x_581 = lean_ctor_get(x_564, 0);
lean_inc(x_581);
lean_dec(x_564);
x_582 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_581, x_5, x_562, x_7, x_8, x_9, x_10, x_560);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_582;
}
}
else
{
uint8_t x_583; 
lean_dec(x_557);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_558);
if (x_583 == 0)
{
return x_558;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_558, 0);
x_585 = lean_ctor_get(x_558, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_558);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
block_621:
{
lean_object* x_589; 
lean_dec(x_588);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_589 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_592 = lean_ctor_get(x_590, 0);
lean_inc(x_592);
lean_dec(x_590);
x_593 = lean_array_get_size(x_3);
x_594 = lean_unsigned_to_nat(0u);
x_595 = lean_unsigned_to_nat(1u);
x_596 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_593);
lean_ctor_set(x_596, 2, x_595);
x_597 = 0;
x_598 = lean_box(x_597);
x_599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_599, 0, x_3);
lean_ctor_set(x_599, 1, x_598);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_600 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_592, x_596, x_596, x_599, x_594, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_591);
lean_dec(x_596);
lean_dec(x_592);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
x_604 = lean_unbox(x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_602);
lean_dec(x_2);
x_605 = lean_ctor_get(x_600, 1);
lean_inc(x_605);
lean_dec(x_600);
x_606 = lean_ctor_get(x_601, 1);
lean_inc(x_606);
lean_dec(x_601);
lean_inc(x_1);
x_607 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_606, x_7, x_8, x_9, x_10, x_605);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_607;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_608 = lean_ctor_get(x_600, 1);
lean_inc(x_608);
lean_dec(x_600);
x_609 = lean_ctor_get(x_601, 1);
lean_inc(x_609);
lean_dec(x_601);
x_610 = lean_ctor_get(x_602, 0);
lean_inc(x_610);
lean_dec(x_602);
x_611 = l_Lean_mkAppN(x_2, x_610);
lean_dec(x_610);
x_612 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_611, x_5, x_609, x_7, x_8, x_9, x_10, x_608);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_612;
}
}
else
{
uint8_t x_613; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_613 = !lean_is_exclusive(x_600);
if (x_613 == 0)
{
return x_600;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_600, 0);
x_615 = lean_ctor_get(x_600, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_600);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
else
{
uint8_t x_617; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_617 = !lean_is_exclusive(x_589);
if (x_617 == 0)
{
return x_589;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_589, 0);
x_619 = lean_ctor_get(x_589, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_589);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
}
case 9:
{
lean_object* x_634; lean_object* x_665; lean_object* x_699; uint8_t x_700; 
lean_dec(x_4);
x_699 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_700 = l_Lean_Expr_isConstOf(x_2, x_699);
if (x_700 == 0)
{
lean_object* x_701; 
x_701 = lean_box(0);
x_665 = x_701;
goto block_698;
}
else
{
lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_702 = lean_array_get_size(x_3);
x_703 = lean_unsigned_to_nat(2u);
x_704 = lean_nat_dec_eq(x_702, x_703);
if (x_704 == 0)
{
lean_object* x_705; 
lean_dec(x_702);
x_705 = lean_box(0);
x_665 = x_705;
goto block_698;
}
else
{
lean_object* x_706; uint8_t x_707; 
x_706 = lean_unsigned_to_nat(0u);
x_707 = lean_nat_dec_lt(x_706, x_702);
lean_dec(x_702);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; 
x_708 = l_Lean_instInhabitedExpr;
x_709 = l_outOfBounds___rarg(x_708);
x_634 = x_709;
goto block_664;
}
else
{
lean_object* x_710; 
x_710 = lean_array_fget(x_3, x_706);
x_634 = x_710;
goto block_664;
}
}
}
block_664:
{
lean_object* x_635; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_634);
x_635 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_634, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_ctor_get(x_636, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
lean_dec(x_636);
x_640 = lean_ctor_get(x_639, 2);
lean_inc(x_640);
lean_inc(x_640);
x_641 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_640, x_638);
if (lean_obj_tag(x_641) == 0)
{
size_t x_642; size_t x_643; uint8_t x_644; 
x_642 = lean_ptr_addr(x_634);
lean_dec(x_634);
x_643 = lean_ptr_addr(x_638);
x_644 = lean_usize_dec_eq(x_642, x_643);
if (x_644 == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_645 = lean_unsigned_to_nat(0u);
lean_inc(x_638);
x_646 = lean_array_set(x_3, x_645, x_638);
x_647 = l_Lean_mkAppN(x_2, x_646);
lean_dec(x_646);
x_648 = lean_ctor_get(x_639, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_639, 1);
lean_inc(x_649);
lean_dec(x_639);
lean_inc(x_647);
x_650 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_640, x_638, x_647);
x_651 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
lean_ctor_set(x_651, 2, x_650);
x_652 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_647, x_5, x_651, x_7, x_8, x_9, x_10, x_637);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_652;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_3);
lean_dec(x_2);
x_653 = lean_ctor_get(x_639, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_639, 1);
lean_inc(x_654);
lean_dec(x_639);
lean_inc(x_1);
x_655 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_640, x_638, x_1);
x_656 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
lean_ctor_set(x_656, 2, x_655);
lean_inc(x_1);
x_657 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_656, x_7, x_8, x_9, x_10, x_637);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_657;
}
}
else
{
lean_object* x_658; lean_object* x_659; 
lean_dec(x_640);
lean_dec(x_638);
lean_dec(x_634);
lean_dec(x_3);
lean_dec(x_2);
x_658 = lean_ctor_get(x_641, 0);
lean_inc(x_658);
lean_dec(x_641);
x_659 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_658, x_5, x_639, x_7, x_8, x_9, x_10, x_637);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_659;
}
}
else
{
uint8_t x_660; 
lean_dec(x_634);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_660 = !lean_is_exclusive(x_635);
if (x_660 == 0)
{
return x_635;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_661 = lean_ctor_get(x_635, 0);
x_662 = lean_ctor_get(x_635, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_635);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
}
block_698:
{
lean_object* x_666; 
lean_dec(x_665);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_666 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec(x_666);
x_669 = lean_ctor_get(x_667, 0);
lean_inc(x_669);
lean_dec(x_667);
x_670 = lean_array_get_size(x_3);
x_671 = lean_unsigned_to_nat(0u);
x_672 = lean_unsigned_to_nat(1u);
x_673 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_673, 0, x_671);
lean_ctor_set(x_673, 1, x_670);
lean_ctor_set(x_673, 2, x_672);
x_674 = 0;
x_675 = lean_box(x_674);
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_3);
lean_ctor_set(x_676, 1, x_675);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_677 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_669, x_673, x_673, x_676, x_671, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_668);
lean_dec(x_673);
lean_dec(x_669);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_679, 1);
lean_inc(x_680);
x_681 = lean_unbox(x_680);
lean_dec(x_680);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_679);
lean_dec(x_2);
x_682 = lean_ctor_get(x_677, 1);
lean_inc(x_682);
lean_dec(x_677);
x_683 = lean_ctor_get(x_678, 1);
lean_inc(x_683);
lean_dec(x_678);
lean_inc(x_1);
x_684 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_683, x_7, x_8, x_9, x_10, x_682);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_684;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_685 = lean_ctor_get(x_677, 1);
lean_inc(x_685);
lean_dec(x_677);
x_686 = lean_ctor_get(x_678, 1);
lean_inc(x_686);
lean_dec(x_678);
x_687 = lean_ctor_get(x_679, 0);
lean_inc(x_687);
lean_dec(x_679);
x_688 = l_Lean_mkAppN(x_2, x_687);
lean_dec(x_687);
x_689 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_688, x_5, x_686, x_7, x_8, x_9, x_10, x_685);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_689;
}
}
else
{
uint8_t x_690; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_690 = !lean_is_exclusive(x_677);
if (x_690 == 0)
{
return x_677;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_677, 0);
x_692 = lean_ctor_get(x_677, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_677);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
return x_693;
}
}
}
else
{
uint8_t x_694; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_694 = !lean_is_exclusive(x_666);
if (x_694 == 0)
{
return x_666;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_666, 0);
x_696 = lean_ctor_get(x_666, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_666);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
return x_697;
}
}
}
}
case 10:
{
lean_object* x_711; lean_object* x_742; lean_object* x_776; uint8_t x_777; 
lean_dec(x_4);
x_776 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_777 = l_Lean_Expr_isConstOf(x_2, x_776);
if (x_777 == 0)
{
lean_object* x_778; 
x_778 = lean_box(0);
x_742 = x_778;
goto block_775;
}
else
{
lean_object* x_779; lean_object* x_780; uint8_t x_781; 
x_779 = lean_array_get_size(x_3);
x_780 = lean_unsigned_to_nat(2u);
x_781 = lean_nat_dec_eq(x_779, x_780);
if (x_781 == 0)
{
lean_object* x_782; 
lean_dec(x_779);
x_782 = lean_box(0);
x_742 = x_782;
goto block_775;
}
else
{
lean_object* x_783; uint8_t x_784; 
x_783 = lean_unsigned_to_nat(0u);
x_784 = lean_nat_dec_lt(x_783, x_779);
lean_dec(x_779);
if (x_784 == 0)
{
lean_object* x_785; lean_object* x_786; 
x_785 = l_Lean_instInhabitedExpr;
x_786 = l_outOfBounds___rarg(x_785);
x_711 = x_786;
goto block_741;
}
else
{
lean_object* x_787; 
x_787 = lean_array_fget(x_3, x_783);
x_711 = x_787;
goto block_741;
}
}
}
block_741:
{
lean_object* x_712; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_711);
x_712 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_711, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_ctor_get(x_713, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_713, 1);
lean_inc(x_716);
lean_dec(x_713);
x_717 = lean_ctor_get(x_716, 2);
lean_inc(x_717);
lean_inc(x_717);
x_718 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_717, x_715);
if (lean_obj_tag(x_718) == 0)
{
size_t x_719; size_t x_720; uint8_t x_721; 
x_719 = lean_ptr_addr(x_711);
lean_dec(x_711);
x_720 = lean_ptr_addr(x_715);
x_721 = lean_usize_dec_eq(x_719, x_720);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_722 = lean_unsigned_to_nat(0u);
lean_inc(x_715);
x_723 = lean_array_set(x_3, x_722, x_715);
x_724 = l_Lean_mkAppN(x_2, x_723);
lean_dec(x_723);
x_725 = lean_ctor_get(x_716, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_716, 1);
lean_inc(x_726);
lean_dec(x_716);
lean_inc(x_724);
x_727 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_717, x_715, x_724);
x_728 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_728, 0, x_725);
lean_ctor_set(x_728, 1, x_726);
lean_ctor_set(x_728, 2, x_727);
x_729 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_724, x_5, x_728, x_7, x_8, x_9, x_10, x_714);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_729;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_3);
lean_dec(x_2);
x_730 = lean_ctor_get(x_716, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_716, 1);
lean_inc(x_731);
lean_dec(x_716);
lean_inc(x_1);
x_732 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_717, x_715, x_1);
x_733 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_733, 0, x_730);
lean_ctor_set(x_733, 1, x_731);
lean_ctor_set(x_733, 2, x_732);
lean_inc(x_1);
x_734 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_733, x_7, x_8, x_9, x_10, x_714);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_734;
}
}
else
{
lean_object* x_735; lean_object* x_736; 
lean_dec(x_717);
lean_dec(x_715);
lean_dec(x_711);
lean_dec(x_3);
lean_dec(x_2);
x_735 = lean_ctor_get(x_718, 0);
lean_inc(x_735);
lean_dec(x_718);
x_736 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_735, x_5, x_716, x_7, x_8, x_9, x_10, x_714);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_736;
}
}
else
{
uint8_t x_737; 
lean_dec(x_711);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_737 = !lean_is_exclusive(x_712);
if (x_737 == 0)
{
return x_712;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_712, 0);
x_739 = lean_ctor_get(x_712, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_712);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
}
block_775:
{
lean_object* x_743; 
lean_dec(x_742);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_743 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_ctor_get(x_744, 0);
lean_inc(x_746);
lean_dec(x_744);
x_747 = lean_array_get_size(x_3);
x_748 = lean_unsigned_to_nat(0u);
x_749 = lean_unsigned_to_nat(1u);
x_750 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_750, 0, x_748);
lean_ctor_set(x_750, 1, x_747);
lean_ctor_set(x_750, 2, x_749);
x_751 = 0;
x_752 = lean_box(x_751);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_3);
lean_ctor_set(x_753, 1, x_752);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_754 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_746, x_750, x_750, x_753, x_748, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_745);
lean_dec(x_750);
lean_dec(x_746);
if (lean_obj_tag(x_754) == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; 
x_755 = lean_ctor_get(x_754, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_756, 1);
lean_inc(x_757);
x_758 = lean_unbox(x_757);
lean_dec(x_757);
if (x_758 == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_756);
lean_dec(x_2);
x_759 = lean_ctor_get(x_754, 1);
lean_inc(x_759);
lean_dec(x_754);
x_760 = lean_ctor_get(x_755, 1);
lean_inc(x_760);
lean_dec(x_755);
lean_inc(x_1);
x_761 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_760, x_7, x_8, x_9, x_10, x_759);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_761;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_762 = lean_ctor_get(x_754, 1);
lean_inc(x_762);
lean_dec(x_754);
x_763 = lean_ctor_get(x_755, 1);
lean_inc(x_763);
lean_dec(x_755);
x_764 = lean_ctor_get(x_756, 0);
lean_inc(x_764);
lean_dec(x_756);
x_765 = l_Lean_mkAppN(x_2, x_764);
lean_dec(x_764);
x_766 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_765, x_5, x_763, x_7, x_8, x_9, x_10, x_762);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_766;
}
}
else
{
uint8_t x_767; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_767 = !lean_is_exclusive(x_754);
if (x_767 == 0)
{
return x_754;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_754, 0);
x_769 = lean_ctor_get(x_754, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_754);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
}
}
}
else
{
uint8_t x_771; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_771 = !lean_is_exclusive(x_743);
if (x_771 == 0)
{
return x_743;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_743, 0);
x_773 = lean_ctor_get(x_743, 1);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_743);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
return x_774;
}
}
}
}
default: 
{
lean_object* x_788; lean_object* x_819; lean_object* x_853; uint8_t x_854; 
lean_dec(x_4);
x_853 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4;
x_854 = l_Lean_Expr_isConstOf(x_2, x_853);
if (x_854 == 0)
{
lean_object* x_855; 
x_855 = lean_box(0);
x_819 = x_855;
goto block_852;
}
else
{
lean_object* x_856; lean_object* x_857; uint8_t x_858; 
x_856 = lean_array_get_size(x_3);
x_857 = lean_unsigned_to_nat(2u);
x_858 = lean_nat_dec_eq(x_856, x_857);
if (x_858 == 0)
{
lean_object* x_859; 
lean_dec(x_856);
x_859 = lean_box(0);
x_819 = x_859;
goto block_852;
}
else
{
lean_object* x_860; uint8_t x_861; 
x_860 = lean_unsigned_to_nat(0u);
x_861 = lean_nat_dec_lt(x_860, x_856);
lean_dec(x_856);
if (x_861 == 0)
{
lean_object* x_862; lean_object* x_863; 
x_862 = l_Lean_instInhabitedExpr;
x_863 = l_outOfBounds___rarg(x_862);
x_788 = x_863;
goto block_818;
}
else
{
lean_object* x_864; 
x_864 = lean_array_fget(x_3, x_860);
x_788 = x_864;
goto block_818;
}
}
}
block_818:
{
lean_object* x_789; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_788);
x_789 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_788, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = lean_ctor_get(x_790, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_790, 1);
lean_inc(x_793);
lean_dec(x_790);
x_794 = lean_ctor_get(x_793, 2);
lean_inc(x_794);
lean_inc(x_794);
x_795 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_794, x_792);
if (lean_obj_tag(x_795) == 0)
{
size_t x_796; size_t x_797; uint8_t x_798; 
x_796 = lean_ptr_addr(x_788);
lean_dec(x_788);
x_797 = lean_ptr_addr(x_792);
x_798 = lean_usize_dec_eq(x_796, x_797);
if (x_798 == 0)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_799 = lean_unsigned_to_nat(0u);
lean_inc(x_792);
x_800 = lean_array_set(x_3, x_799, x_792);
x_801 = l_Lean_mkAppN(x_2, x_800);
lean_dec(x_800);
x_802 = lean_ctor_get(x_793, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_793, 1);
lean_inc(x_803);
lean_dec(x_793);
lean_inc(x_801);
x_804 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_794, x_792, x_801);
x_805 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_805, 0, x_802);
lean_ctor_set(x_805, 1, x_803);
lean_ctor_set(x_805, 2, x_804);
x_806 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_801, x_5, x_805, x_7, x_8, x_9, x_10, x_791);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_806;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_3);
lean_dec(x_2);
x_807 = lean_ctor_get(x_793, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_793, 1);
lean_inc(x_808);
lean_dec(x_793);
lean_inc(x_1);
x_809 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_794, x_792, x_1);
x_810 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_808);
lean_ctor_set(x_810, 2, x_809);
lean_inc(x_1);
x_811 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_810, x_7, x_8, x_9, x_10, x_791);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_811;
}
}
else
{
lean_object* x_812; lean_object* x_813; 
lean_dec(x_794);
lean_dec(x_792);
lean_dec(x_788);
lean_dec(x_3);
lean_dec(x_2);
x_812 = lean_ctor_get(x_795, 0);
lean_inc(x_812);
lean_dec(x_795);
x_813 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_812, x_5, x_793, x_7, x_8, x_9, x_10, x_791);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_813;
}
}
else
{
uint8_t x_814; 
lean_dec(x_788);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_814 = !lean_is_exclusive(x_789);
if (x_814 == 0)
{
return x_789;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_789, 0);
x_816 = lean_ctor_get(x_789, 1);
lean_inc(x_816);
lean_inc(x_815);
lean_dec(x_789);
x_817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
return x_817;
}
}
}
block_852:
{
lean_object* x_820; 
lean_dec(x_819);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_820 = l_Lean_Meta_getFunInfo(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; uint8_t x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
lean_dec(x_820);
x_823 = lean_ctor_get(x_821, 0);
lean_inc(x_823);
lean_dec(x_821);
x_824 = lean_array_get_size(x_3);
x_825 = lean_unsigned_to_nat(0u);
x_826 = lean_unsigned_to_nat(1u);
x_827 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set(x_827, 1, x_824);
lean_ctor_set(x_827, 2, x_826);
x_828 = 0;
x_829 = lean_box(x_828);
x_830 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_830, 0, x_3);
lean_ctor_set(x_830, 1, x_829);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_831 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_2, x_823, x_827, x_827, x_830, x_825, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_822);
lean_dec(x_827);
lean_dec(x_823);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; 
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_833, 1);
lean_inc(x_834);
x_835 = lean_unbox(x_834);
lean_dec(x_834);
if (x_835 == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_833);
lean_dec(x_2);
x_836 = lean_ctor_get(x_831, 1);
lean_inc(x_836);
lean_dec(x_831);
x_837 = lean_ctor_get(x_832, 1);
lean_inc(x_837);
lean_dec(x_832);
lean_inc(x_1);
x_838 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_1, x_5, x_837, x_7, x_8, x_9, x_10, x_836);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_838;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_839 = lean_ctor_get(x_831, 1);
lean_inc(x_839);
lean_dec(x_831);
x_840 = lean_ctor_get(x_832, 1);
lean_inc(x_840);
lean_dec(x_832);
x_841 = lean_ctor_get(x_833, 0);
lean_inc(x_841);
lean_dec(x_833);
x_842 = l_Lean_mkAppN(x_2, x_841);
lean_dec(x_841);
x_843 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_842, x_5, x_840, x_7, x_8, x_9, x_10, x_839);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_843;
}
}
else
{
uint8_t x_844; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_844 = !lean_is_exclusive(x_831);
if (x_844 == 0)
{
return x_831;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_831, 0);
x_846 = lean_ctor_get(x_831, 1);
lean_inc(x_846);
lean_inc(x_845);
lean_dec(x_831);
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
return x_847;
}
}
}
else
{
uint8_t x_848; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_848 = !lean_is_exclusive(x_820);
if (x_848 == 0)
{
return x_820;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_820, 0);
x_850 = lean_ctor_get(x_820, 1);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_820);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
return x_851;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_1);
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(x_1, x_1, x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Canon", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Canon.canonImpl.visit", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__1;
x_2 = l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__2;
x_3 = lean_unsigned_to_nat(115u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__4;
x_10 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
case 5:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_2, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_array_get_size(x_16);
x_19 = lean_ptr_addr(x_1);
x_20 = lean_usize_to_uint64(x_19);
x_21 = 11;
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_23 = 32;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = 16;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_31 = 1;
x_32 = lean_usize_sub(x_30, x_31);
x_33 = lean_usize_land(x_29, x_32);
x_34 = lean_array_uget(x_16, x_33);
lean_dec(x_16);
x_35 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_13);
lean_free_object(x_11);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 0, x_38);
return x_11;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get(x_11, 1);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_dec(x_13);
x_41 = lean_array_get_size(x_40);
x_42 = lean_ptr_addr(x_1);
x_43 = lean_usize_to_uint64(x_42);
x_44 = 11;
x_45 = lean_uint64_mix_hash(x_43, x_44);
x_46 = 32;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = 16;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = lean_uint64_to_usize(x_51);
x_53 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_54 = 1;
x_55 = lean_usize_sub(x_53, x_54);
x_56 = lean_usize_land(x_52, x_55);
x_57 = lean_array_uget(x_40, x_56);
lean_dec(x_40);
x_58 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_11);
x_59 = lean_box(0);
x_60 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_39);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_11, 0, x_62);
return x_11;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; size_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; 
x_63 = lean_ctor_get(x_11, 0);
x_64 = lean_ctor_get(x_11, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_11);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_array_get_size(x_65);
x_68 = lean_ptr_addr(x_1);
x_69 = lean_usize_to_uint64(x_68);
x_70 = 11;
x_71 = lean_uint64_mix_hash(x_69, x_70);
x_72 = 32;
x_73 = lean_uint64_shift_right(x_71, x_72);
x_74 = lean_uint64_xor(x_71, x_73);
x_75 = 16;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = lean_uint64_to_usize(x_77);
x_79 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_80 = 1;
x_81 = lean_usize_sub(x_79, x_80);
x_82 = lean_usize_land(x_78, x_81);
x_83 = lean_array_uget(x_65, x_82);
lean_dec(x_65);
x_84 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_83);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_66);
x_85 = lean_box(0);
x_86 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_64);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
if (lean_is_scalar(x_66)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_66;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_3);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_64);
return x_89;
}
}
}
default: 
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_3);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_8);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrMap___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_Grind_Canon_canonImpl___closed__1;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FVarSubset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FVarSubset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Canon_instInhabitedState___closed__1 = _init_l_Lean_Meta_Grind_Canon_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instInhabitedState___closed__1);
l_Lean_Meta_Grind_Canon_instInhabitedState___closed__2 = _init_l_Lean_Meta_Grind_Canon_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instInhabitedState___closed__2);
l_Lean_Meta_Grind_Canon_instInhabitedState___closed__3 = _init_l_Lean_Meta_Grind_Canon_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instInhabitedState___closed__3);
l_Lean_Meta_Grind_Canon_instInhabitedState = _init_l_Lean_Meta_Grind_Canon_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instInhabitedState);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2();
l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1();
l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2);
l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3 = _init_l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3);
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__2);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__4);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__6 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__6);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9();
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1);
l_Lean_Meta_Grind_Canon_canonInst___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonInst___closed__1();
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___closed__1);
l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult = _init_l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult();
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__1);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__2 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__2);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__3 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___closed__4);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___closed__1);
l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__1);
l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__2 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__2);
l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__3 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__3);
l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__4 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___closed__4);
l_Lean_Meta_Grind_Canon_canonImpl___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

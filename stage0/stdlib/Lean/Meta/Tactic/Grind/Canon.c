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
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_explain(uint8_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_toCtorIdx___boxed(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl___closed__1;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_beqCanonElemKind____x40_Lean_Meta_Tactic_Grind_Canon___hyg_87____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__11(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__1;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__16(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instBEqCanonElemKind___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2;
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__4;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrMap___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3;
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3;
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_ReaderT_instMonadLift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_toCtorIdx(uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__7___closed__1;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6;
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4;
static lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___closed__1;
lean_object* l_StateT_lift___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_Canon_canonElemCore___spec__13(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__3;
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3;
static uint64_t l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_explain___boxed(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3;
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__1;
static lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__6;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static uint64_t l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__2;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instBEqCanonElemKind;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
static uint64_t l_Lean_Meta_Grind_Canon_canonInst___closed__1;
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_beqCanonElemKind____x40_Lean_Meta_Tactic_Grind_Canon___hyg_87_(uint8_t, uint8_t);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState;
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__6;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_Canon_instInhabitedState___closed__3;
static lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5;
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__2;
static lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Grind_Canon_canonElemCore___spec__2___closed__2;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Grind_Canon_CanonElemKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_beqCanonElemKind____x40_Lean_Meta_Tactic_Grind_Canon___hyg_87_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Canon_CanonElemKind_toCtorIdx(x_1);
x_4 = l_Lean_Meta_Grind_Canon_CanonElemKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_beqCanonElemKind____x40_Lean_Meta_Tactic_Grind_Canon___hyg_87____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_beqCanonElemKind____x40_Lean_Meta_Tactic_Grind_Canon___hyg_87_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instBEqCanonElemKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_beqCanonElemKind____x40_Lean_Meta_Tactic_Grind_Canon___hyg_87____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instBEqCanonElemKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Canon_instBEqCanonElemKind___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type class instances", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("types (or type formers)", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("implicit arguments (which are not type class instances or types)", 64, 64);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_explain(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__3;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_CanonElemKind_explain___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Grind_Canon_CanonElemKind_explain(x_2);
return x_3;
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
x_1 = lean_mk_string_unchecked("the following ", 14, 14);
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
x_1 = lean_mk_string_unchecked(" are definitionally equal with `default` transparency but not with a more restrictive transparency", 98, 98);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nand", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static uint64_t _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11() {
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
uint8_t x_12; uint8_t x_13; 
x_12 = 1;
x_13 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_beqCanonElemKind____x40_Lean_Meta_Tactic_Grind_Canon___hyg_87_(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3;
x_80 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_79, x_6, x_7, x_8, x_9, x_10, x_11);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_81, 0);
lean_dec(x_86);
x_14 = x_81;
x_15 = x_84;
goto block_78;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
x_14 = x_88;
x_15 = x_84;
goto block_78;
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_82);
x_89 = lean_ctor_get(x_7, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 1);
lean_inc(x_90);
lean_dec(x_80);
x_91 = !lean_is_exclusive(x_81);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint64_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_92 = lean_ctor_get(x_81, 1);
x_93 = lean_ctor_get(x_81, 0);
lean_dec(x_93);
x_94 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_95 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_96 = lean_ctor_get(x_7, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_7, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_7, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_7, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_7, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_7, 6);
lean_inc(x_101);
x_102 = !lean_is_exclusive(x_89);
if (x_102 == 0)
{
uint8_t x_103; uint8_t x_104; uint8_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; lean_object* x_111; lean_object* x_112; 
x_103 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_104 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_105 = 1;
lean_ctor_set_uint8(x_89, 9, x_105);
x_106 = 2;
x_107 = lean_uint64_shift_right(x_94, x_106);
x_108 = lean_uint64_shift_left(x_107, x_106);
x_109 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
x_110 = lean_uint64_lor(x_108, x_109);
x_111 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_111, 0, x_89);
lean_ctor_set(x_111, 1, x_96);
lean_ctor_set(x_111, 2, x_97);
lean_ctor_set(x_111, 3, x_98);
lean_ctor_set(x_111, 4, x_99);
lean_ctor_set(x_111, 5, x_100);
lean_ctor_set(x_111, 6, x_101);
lean_ctor_set_uint64(x_111, sizeof(void*)*7, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*7 + 8, x_95);
lean_ctor_set_uint8(x_111, sizeof(void*)*7 + 9, x_103);
lean_ctor_set_uint8(x_111, sizeof(void*)*7 + 10, x_104);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_112 = l_Lean_Meta_isExprDefEq(x_3, x_4, x_111, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_ctor_set(x_81, 0, x_113);
x_14 = x_81;
x_15 = x_114;
goto block_78;
}
else
{
uint8_t x_115; 
lean_free_object(x_81);
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_112);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; lean_object* x_144; lean_object* x_145; 
x_119 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_120 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_121 = lean_ctor_get_uint8(x_89, 0);
x_122 = lean_ctor_get_uint8(x_89, 1);
x_123 = lean_ctor_get_uint8(x_89, 2);
x_124 = lean_ctor_get_uint8(x_89, 3);
x_125 = lean_ctor_get_uint8(x_89, 4);
x_126 = lean_ctor_get_uint8(x_89, 5);
x_127 = lean_ctor_get_uint8(x_89, 6);
x_128 = lean_ctor_get_uint8(x_89, 7);
x_129 = lean_ctor_get_uint8(x_89, 8);
x_130 = lean_ctor_get_uint8(x_89, 10);
x_131 = lean_ctor_get_uint8(x_89, 11);
x_132 = lean_ctor_get_uint8(x_89, 12);
x_133 = lean_ctor_get_uint8(x_89, 13);
x_134 = lean_ctor_get_uint8(x_89, 14);
x_135 = lean_ctor_get_uint8(x_89, 15);
x_136 = lean_ctor_get_uint8(x_89, 16);
lean_dec(x_89);
x_137 = 1;
x_138 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_138, 0, x_121);
lean_ctor_set_uint8(x_138, 1, x_122);
lean_ctor_set_uint8(x_138, 2, x_123);
lean_ctor_set_uint8(x_138, 3, x_124);
lean_ctor_set_uint8(x_138, 4, x_125);
lean_ctor_set_uint8(x_138, 5, x_126);
lean_ctor_set_uint8(x_138, 6, x_127);
lean_ctor_set_uint8(x_138, 7, x_128);
lean_ctor_set_uint8(x_138, 8, x_129);
lean_ctor_set_uint8(x_138, 9, x_137);
lean_ctor_set_uint8(x_138, 10, x_130);
lean_ctor_set_uint8(x_138, 11, x_131);
lean_ctor_set_uint8(x_138, 12, x_132);
lean_ctor_set_uint8(x_138, 13, x_133);
lean_ctor_set_uint8(x_138, 14, x_134);
lean_ctor_set_uint8(x_138, 15, x_135);
lean_ctor_set_uint8(x_138, 16, x_136);
x_139 = 2;
x_140 = lean_uint64_shift_right(x_94, x_139);
x_141 = lean_uint64_shift_left(x_140, x_139);
x_142 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
x_143 = lean_uint64_lor(x_141, x_142);
x_144 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_96);
lean_ctor_set(x_144, 2, x_97);
lean_ctor_set(x_144, 3, x_98);
lean_ctor_set(x_144, 4, x_99);
lean_ctor_set(x_144, 5, x_100);
lean_ctor_set(x_144, 6, x_101);
lean_ctor_set_uint64(x_144, sizeof(void*)*7, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 8, x_95);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 9, x_119);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 10, x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_145 = l_Lean_Meta_isExprDefEq(x_3, x_4, x_144, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
lean_ctor_set(x_81, 0, x_146);
x_14 = x_81;
x_15 = x_147;
goto block_78;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_free_object(x_81);
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_150 = x_145;
} else {
 lean_dec_ref(x_145);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
lean_object* x_152; uint64_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; lean_object* x_187; lean_object* x_188; 
x_152 = lean_ctor_get(x_81, 1);
lean_inc(x_152);
lean_dec(x_81);
x_153 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_154 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_155 = lean_ctor_get(x_7, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_7, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_7, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_7, 4);
lean_inc(x_158);
x_159 = lean_ctor_get(x_7, 5);
lean_inc(x_159);
x_160 = lean_ctor_get(x_7, 6);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_162 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_163 = lean_ctor_get_uint8(x_89, 0);
x_164 = lean_ctor_get_uint8(x_89, 1);
x_165 = lean_ctor_get_uint8(x_89, 2);
x_166 = lean_ctor_get_uint8(x_89, 3);
x_167 = lean_ctor_get_uint8(x_89, 4);
x_168 = lean_ctor_get_uint8(x_89, 5);
x_169 = lean_ctor_get_uint8(x_89, 6);
x_170 = lean_ctor_get_uint8(x_89, 7);
x_171 = lean_ctor_get_uint8(x_89, 8);
x_172 = lean_ctor_get_uint8(x_89, 10);
x_173 = lean_ctor_get_uint8(x_89, 11);
x_174 = lean_ctor_get_uint8(x_89, 12);
x_175 = lean_ctor_get_uint8(x_89, 13);
x_176 = lean_ctor_get_uint8(x_89, 14);
x_177 = lean_ctor_get_uint8(x_89, 15);
x_178 = lean_ctor_get_uint8(x_89, 16);
if (lean_is_exclusive(x_89)) {
 x_179 = x_89;
} else {
 lean_dec_ref(x_89);
 x_179 = lean_box(0);
}
x_180 = 1;
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 0, 17);
} else {
 x_181 = x_179;
}
lean_ctor_set_uint8(x_181, 0, x_163);
lean_ctor_set_uint8(x_181, 1, x_164);
lean_ctor_set_uint8(x_181, 2, x_165);
lean_ctor_set_uint8(x_181, 3, x_166);
lean_ctor_set_uint8(x_181, 4, x_167);
lean_ctor_set_uint8(x_181, 5, x_168);
lean_ctor_set_uint8(x_181, 6, x_169);
lean_ctor_set_uint8(x_181, 7, x_170);
lean_ctor_set_uint8(x_181, 8, x_171);
lean_ctor_set_uint8(x_181, 9, x_180);
lean_ctor_set_uint8(x_181, 10, x_172);
lean_ctor_set_uint8(x_181, 11, x_173);
lean_ctor_set_uint8(x_181, 12, x_174);
lean_ctor_set_uint8(x_181, 13, x_175);
lean_ctor_set_uint8(x_181, 14, x_176);
lean_ctor_set_uint8(x_181, 15, x_177);
lean_ctor_set_uint8(x_181, 16, x_178);
x_182 = 2;
x_183 = lean_uint64_shift_right(x_153, x_182);
x_184 = lean_uint64_shift_left(x_183, x_182);
x_185 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
x_186 = lean_uint64_lor(x_184, x_185);
x_187 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_155);
lean_ctor_set(x_187, 2, x_156);
lean_ctor_set(x_187, 3, x_157);
lean_ctor_set(x_187, 4, x_158);
lean_ctor_set(x_187, 5, x_159);
lean_ctor_set(x_187, 6, x_160);
lean_ctor_set_uint64(x_187, sizeof(void*)*7, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 8, x_154);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 9, x_161);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 10, x_162);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_188 = l_Lean_Meta_isExprDefEq(x_3, x_4, x_187, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_152);
x_14 = x_191;
x_15 = x_190;
goto block_78;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_152);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_194 = x_188;
} else {
 lean_dec_ref(x_188);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
block_78:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__3;
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_27, x_26, x_7, x_8, x_9, x_10, x_15);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
lean_dec(x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_29, 0, x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_42 = x_29;
} else {
 lean_dec_ref(x_29);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_dec(x_28);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_dec(x_29);
x_48 = l_Lean_Meta_Grind_Canon_CanonElemKind_explain(x_1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__5;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__7;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_3);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_indentExpr(x_4);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_27, x_61, x_47, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_2);
lean_ctor_set(x_64, 0, x_67);
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_2);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_62, 0, x_70);
return x_62;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_2);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_2);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_6);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_11);
return x_198;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canon", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__1;
x_2 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__1;
x_3 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ===> ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_36; 
lean_dec(x_8);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_20 = x_7;
} else {
 lean_dec_ref(x_7);
 x_20 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
lean_inc(x_1);
x_36 = l_Lean_Meta_isExprDefEq(x_1, x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_4);
x_41 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1(x_2, x_4, x_1, x_18, x_40, x_10, x_11, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_21 = x_42;
x_22 = x_43;
goto block_35;
}
else
{
uint8_t x_44; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_1);
x_51 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_50, x_1, x_18);
lean_ctor_set(x_10, 1, x_51);
x_52 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3;
x_53 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_52, x_10, x_11, x_12, x_13, x_14, x_48);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(0);
x_60 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(x_18, x_59, x_58, x_11, x_12, x_13, x_14, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_21 = x_61;
x_22 = x_62;
goto block_35;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_53);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_53, 1);
x_65 = lean_ctor_get(x_53, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_54);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_54, 1);
x_68 = lean_ctor_get(x_54, 0);
lean_dec(x_68);
lean_inc(x_1);
x_69 = l_Lean_MessageData_ofExpr(x_1);
x_70 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5;
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_69);
lean_ctor_set(x_54, 0, x_70);
x_71 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7;
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_71);
lean_inc(x_18);
x_72 = l_Lean_MessageData_ofExpr(x_18);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_52, x_75, x_67, x_11, x_12, x_13, x_14, x_64);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(x_18, x_79, x_80, x_11, x_12, x_13, x_14, x_78);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_21 = x_82;
x_22 = x_83;
goto block_35;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_84 = lean_ctor_get(x_54, 1);
lean_inc(x_84);
lean_dec(x_54);
lean_inc(x_1);
x_85 = l_Lean_MessageData_ofExpr(x_1);
x_86 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7;
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_88);
lean_ctor_set(x_53, 0, x_87);
lean_inc(x_18);
x_89 = l_Lean_MessageData_ofExpr(x_18);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_53);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_52, x_92, x_84, x_11, x_12, x_13, x_14, x_64);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(x_18, x_96, x_97, x_11, x_12, x_13, x_14, x_95);
lean_dec(x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_21 = x_99;
x_22 = x_100;
goto block_35;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_101 = lean_ctor_get(x_53, 1);
lean_inc(x_101);
lean_dec(x_53);
x_102 = lean_ctor_get(x_54, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_103 = x_54;
} else {
 lean_dec_ref(x_54);
 x_103 = lean_box(0);
}
lean_inc(x_1);
x_104 = l_Lean_MessageData_ofExpr(x_1);
x_105 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5;
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(7, 2, 0);
} else {
 x_106 = x_103;
 lean_ctor_set_tag(x_106, 7);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_18);
x_109 = l_Lean_MessageData_ofExpr(x_18);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_52, x_112, x_102, x_11, x_12, x_13, x_14, x_101);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(x_18, x_116, x_117, x_11, x_12, x_13, x_14, x_115);
lean_dec(x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_21 = x_119;
x_22 = x_120;
goto block_35;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_121 = lean_ctor_get(x_10, 0);
x_122 = lean_ctor_get(x_10, 1);
x_123 = lean_ctor_get(x_10, 2);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_10);
lean_inc(x_18);
lean_inc(x_1);
x_124 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_122, x_1, x_18);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_123);
x_126 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3;
x_127 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_126, x_125, x_11, x_12, x_13, x_14, x_48);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_dec(x_127);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_box(0);
x_134 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(x_18, x_133, x_132, x_11, x_12, x_13, x_14, x_131);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_21 = x_135;
x_22 = x_136;
goto block_35;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_137 = lean_ctor_get(x_127, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_138 = x_127;
} else {
 lean_dec_ref(x_127);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_128, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_140 = x_128;
} else {
 lean_dec_ref(x_128);
 x_140 = lean_box(0);
}
lean_inc(x_1);
x_141 = l_Lean_MessageData_ofExpr(x_1);
x_142 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5;
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(7, 2, 0);
} else {
 x_143 = x_140;
 lean_ctor_set_tag(x_143, 7);
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7;
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(7, 2, 0);
} else {
 x_145 = x_138;
 lean_ctor_set_tag(x_145, 7);
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_18);
x_146 = l_Lean_MessageData_ofExpr(x_18);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_126, x_149, x_139, x_11, x_12, x_13, x_14, x_137);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(x_18, x_153, x_154, x_11, x_12, x_13, x_14, x_152);
lean_dec(x_153);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_21 = x_156;
x_22 = x_157;
goto block_35;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_36);
if (x_158 == 0)
{
return x_36;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_36, 0);
x_160 = lean_ctor_get(x_36, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_36);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
block_35:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_26);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_20;
 lean_ctor_set_tag(x_27, 0);
}
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
if (lean_is_scalar(x_20)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_20;
 lean_ctor_set_tag(x_31, 0);
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_7 = x_19;
x_8 = x_33;
x_9 = lean_box(0);
x_10 = x_32;
x_15 = x_22;
goto _start;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") ↦ ", 6, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3;
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_13, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_20, x_19, x_8, x_9, x_10, x_11, x_18);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = l_Lean_MessageData_ofExpr(x_4);
x_29 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_29);
x_30 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_30);
x_31 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_MessageData_ofFormat(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_1);
x_37 = l_Lean_MessageData_ofExpr(x_1);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_13, x_40, x_26, x_8, x_9, x_10, x_11, x_23);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_44, x_45, x_8, x_9, x_10, x_11, x_43);
lean_dec(x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_dec(x_15);
x_48 = l_Lean_MessageData_ofExpr(x_4);
x_49 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_51);
lean_ctor_set(x_14, 0, x_50);
x_52 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_14);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_1);
x_58 = l_Lean_MessageData_ofExpr(x_1);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_13, x_61, x_47, x_8, x_9, x_10, x_11, x_23);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_65, x_66, x_8, x_9, x_10, x_11, x_64);
lean_dec(x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_68 = lean_ctor_get(x_14, 1);
lean_inc(x_68);
lean_dec(x_14);
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_70 = x_15;
} else {
 lean_dec_ref(x_15);
 x_70 = lean_box(0);
}
x_71 = l_Lean_MessageData_ofExpr(x_4);
x_72 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2;
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(7, 2, 0);
} else {
 x_73 = x_70;
 lean_ctor_set_tag(x_73, 7);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_MessageData_ofFormat(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_1);
x_82 = l_Lean_MessageData_ofExpr(x_1);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_13, x_85, x_69, x_8, x_9, x_10, x_11, x_68);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__1(x_1, x_2, x_3, x_89, x_90, x_8, x_9, x_10, x_11, x_88);
lean_dec(x_89);
return x_91;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
lean_inc(x_1);
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
x_18 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1;
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
x_26 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(x_4, x_17, x_13, x_1, x_2, x_25, x_24, x_8, x_9, x_10, x_11, x_23);
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
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_2);
lean_dec(x_1);
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
x_14 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(x_1, x_2, x_5, x_3, x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
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
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_18 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
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
x_61 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
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
x_110 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
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
static uint64_t _init_l_Lean_Meta_Grind_Canon_canonImplicit___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = 2;
lean_ctor_set_uint8(x_11, 9, x_14);
x_15 = 2;
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_shift_left(x_16, x_15);
x_18 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_19 = lean_uint64_lor(x_17, x_18);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_19);
x_20 = 2;
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
x_56 = 2;
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
x_61 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_62 = lean_uint64_lor(x_60, x_61);
lean_ctor_set(x_5, 0, x_57);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_62);
x_63 = 2;
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
x_105 = 2;
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
x_110 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
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
x_113 = 2;
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___closed__1;
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
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canonType", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canonInst", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("canonImplicit", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("visit", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2;
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4;
return x_4;
}
case 2:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6;
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_isProp(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_isTypeFormer(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 3;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 3;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
lean_dec(x_36);
x_37 = 3;
x_38 = lean_box(x_37);
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_dec(x_8);
x_40 = 3;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
return x_8;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Meta_ParamInfo_isImplicit(x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_Canon_shouldCanon___lambda__1(x_3, x_17, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Meta_isTypeFormer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = 2;
x_25 = lean_box(x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = 2;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
lean_dec(x_31);
x_32 = 0;
x_33 = lean_box(x_32);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = 3;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
return x_47;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__4___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_8);
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
x_19 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_15);
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
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_StateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_Lean_isTracingEnabledForCore(x_1, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_st_ref_take(x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_16, 3);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; double x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_26 = 0;
x_27 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_28 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_float(x_28, sizeof(void*)*2, x_25);
lean_ctor_set_float(x_28, sizeof(void*)*2 + 8, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 16, x_26);
x_29 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_30 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_13);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_10);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_10);
x_31 = l_Lean_PersistentArray_push___rarg(x_24, x_15);
lean_ctor_set(x_17, 0, x_31);
x_32 = lean_st_ref_set(x_8, x_16, x_19);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 0, x_35);
lean_ctor_set(x_32, 0, x_11);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint64_t x_39; lean_object* x_40; double x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
x_41 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_42 = 0;
x_43 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_44 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_float(x_44, sizeof(void*)*2, x_41);
lean_ctor_set_float(x_44, sizeof(void*)*2 + 8, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*2 + 16, x_42);
x_45 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_46 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_10);
lean_ctor_set(x_15, 1, x_46);
lean_ctor_set(x_15, 0, x_10);
x_47 = l_Lean_PersistentArray_push___rarg(x_40, x_15);
x_48 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint64(x_48, sizeof(void*)*1, x_39);
lean_ctor_set(x_16, 3, x_48);
x_49 = lean_st_ref_set(x_8, x_16, x_19);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_11);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; double x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
x_56 = lean_ctor_get(x_16, 2);
x_57 = lean_ctor_get(x_16, 4);
x_58 = lean_ctor_get(x_16, 5);
x_59 = lean_ctor_get(x_16, 6);
x_60 = lean_ctor_get(x_16, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_61 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_62 = lean_ctor_get(x_17, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_63 = x_17;
} else {
 lean_dec_ref(x_17);
 x_63 = lean_box(0);
}
x_64 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_65 = 0;
x_66 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_67 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_float(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_float(x_67, sizeof(void*)*2 + 8, x_64);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 16, x_65);
x_68 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_69 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_68);
lean_inc(x_10);
lean_ctor_set(x_15, 1, x_69);
lean_ctor_set(x_15, 0, x_10);
x_70 = l_Lean_PersistentArray_push___rarg(x_62, x_15);
if (lean_is_scalar(x_63)) {
 x_71 = lean_alloc_ctor(0, 1, 8);
} else {
 x_71 = x_63;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_uint64(x_71, sizeof(void*)*1, x_61);
x_72 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_55);
lean_ctor_set(x_72, 2, x_56);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_57);
lean_ctor_set(x_72, 5, x_58);
lean_ctor_set(x_72, 6, x_59);
lean_ctor_set(x_72, 7, x_60);
x_73 = lean_st_ref_set(x_8, x_72, x_19);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 0, x_76);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_11);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint64_t x_87; lean_object* x_88; lean_object* x_89; double x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_dec(x_15);
x_79 = lean_ctor_get(x_16, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_16, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_16, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_16, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_16, 6);
lean_inc(x_84);
x_85 = lean_ctor_get(x_16, 7);
lean_inc(x_85);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 lean_ctor_release(x_16, 6);
 lean_ctor_release(x_16, 7);
 x_86 = x_16;
} else {
 lean_dec_ref(x_16);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_88 = lean_ctor_get(x_17, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_89 = x_17;
} else {
 lean_dec_ref(x_17);
 x_89 = lean_box(0);
}
x_90 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_91 = 0;
x_92 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_93 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_float(x_93, sizeof(void*)*2, x_90);
lean_ctor_set_float(x_93, sizeof(void*)*2 + 8, x_90);
lean_ctor_set_uint8(x_93, sizeof(void*)*2 + 16, x_91);
x_94 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_95 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_13);
lean_ctor_set(x_95, 2, x_94);
lean_inc(x_10);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_10);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_PersistentArray_push___rarg(x_88, x_96);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 1, 8);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set_uint64(x_98, sizeof(void*)*1, x_87);
if (lean_is_scalar(x_86)) {
 x_99 = lean_alloc_ctor(0, 8, 0);
} else {
 x_99 = x_86;
}
lean_ctor_set(x_99, 0, x_79);
lean_ctor_set(x_99, 1, x_80);
lean_ctor_set(x_99, 2, x_81);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set(x_99, 4, x_82);
lean_ctor_set(x_99, 5, x_83);
lean_ctor_set(x_99, 6, x_84);
lean_ctor_set(x_99, 7, x_85);
x_100 = lean_st_ref_set(x_8, x_99, x_78);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 0, x_103);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_11);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; lean_object* x_122; double x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_105 = lean_ctor_get(x_11, 0);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_11);
x_107 = lean_st_ref_take(x_8, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 3);
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
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 6);
lean_inc(x_117);
x_118 = lean_ctor_get(x_108, 7);
lean_inc(x_118);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 lean_ctor_release(x_108, 5);
 lean_ctor_release(x_108, 6);
 lean_ctor_release(x_108, 7);
 x_119 = x_108;
} else {
 lean_dec_ref(x_108);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get_uint64(x_109, sizeof(void*)*1);
x_121 = lean_ctor_get(x_109, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_122 = x_109;
} else {
 lean_dec_ref(x_109);
 x_122 = lean_box(0);
}
x_123 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__1;
x_124 = 0;
x_125 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__2;
x_126 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set_float(x_126, sizeof(void*)*2, x_123);
lean_ctor_set_float(x_126, sizeof(void*)*2 + 8, x_123);
lean_ctor_set_uint8(x_126, sizeof(void*)*2 + 16, x_124);
x_127 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5___closed__3;
x_128 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_105);
lean_ctor_set(x_128, 2, x_127);
lean_inc(x_10);
if (lean_is_scalar(x_111)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_111;
}
lean_ctor_set(x_129, 0, x_10);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_PersistentArray_push___rarg(x_121, x_129);
if (lean_is_scalar(x_122)) {
 x_131 = lean_alloc_ctor(0, 1, 8);
} else {
 x_131 = x_122;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set_uint64(x_131, sizeof(void*)*1, x_120);
if (lean_is_scalar(x_119)) {
 x_132 = lean_alloc_ctor(0, 8, 0);
} else {
 x_132 = x_119;
}
lean_ctor_set(x_132, 0, x_112);
lean_ctor_set(x_132, 1, x_113);
lean_ctor_set(x_132, 2, x_114);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_115);
lean_ctor_set(x_132, 5, x_116);
lean_ctor_set(x_132, 6, x_117);
lean_ctor_set(x_132, 7, x_118);
x_133 = lean_st_ref_set(x_8, x_132, x_110);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_4);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_135;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
return x_138;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_1);
x_14 = lean_ptr_addr(x_5);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_fset(x_3, x_2, x_5);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
x_15 = l_Lean_Meta_Grind_Canon_shouldCanon(x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
switch (x_17) {
case 0:
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get_uint64(x_10, sizeof(void*)*7);
x_21 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 8);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_10, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_10, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_10, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_10, 6);
lean_inc(x_27);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_29 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 9);
x_30 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 10);
x_31 = 1;
lean_ctor_set_uint8(x_18, 9, x_31);
x_32 = 2;
x_33 = lean_uint64_shift_right(x_20, x_32);
x_34 = lean_uint64_shift_left(x_33, x_32);
x_35 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
x_36 = lean_uint64_lor(x_34, x_35);
x_37 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 2, x_23);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set(x_37, 4, x_25);
lean_ctor_set(x_37, 5, x_26);
lean_ctor_set(x_37, 6, x_27);
lean_ctor_set_uint64(x_37, sizeof(void*)*7, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 8, x_21);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 9, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 10, x_30);
x_38 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_2, x_3, x_38, x_9, x_37, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_5, x_6, x_42, x_8, x_43, x_10, x_11, x_12, x_13, x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_3);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_49 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 9);
x_50 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 10);
x_51 = lean_ctor_get_uint8(x_18, 0);
x_52 = lean_ctor_get_uint8(x_18, 1);
x_53 = lean_ctor_get_uint8(x_18, 2);
x_54 = lean_ctor_get_uint8(x_18, 3);
x_55 = lean_ctor_get_uint8(x_18, 4);
x_56 = lean_ctor_get_uint8(x_18, 5);
x_57 = lean_ctor_get_uint8(x_18, 6);
x_58 = lean_ctor_get_uint8(x_18, 7);
x_59 = lean_ctor_get_uint8(x_18, 8);
x_60 = lean_ctor_get_uint8(x_18, 10);
x_61 = lean_ctor_get_uint8(x_18, 11);
x_62 = lean_ctor_get_uint8(x_18, 12);
x_63 = lean_ctor_get_uint8(x_18, 13);
x_64 = lean_ctor_get_uint8(x_18, 14);
x_65 = lean_ctor_get_uint8(x_18, 15);
x_66 = lean_ctor_get_uint8(x_18, 16);
lean_dec(x_18);
x_67 = 1;
x_68 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_68, 0, x_51);
lean_ctor_set_uint8(x_68, 1, x_52);
lean_ctor_set_uint8(x_68, 2, x_53);
lean_ctor_set_uint8(x_68, 3, x_54);
lean_ctor_set_uint8(x_68, 4, x_55);
lean_ctor_set_uint8(x_68, 5, x_56);
lean_ctor_set_uint8(x_68, 6, x_57);
lean_ctor_set_uint8(x_68, 7, x_58);
lean_ctor_set_uint8(x_68, 8, x_59);
lean_ctor_set_uint8(x_68, 9, x_67);
lean_ctor_set_uint8(x_68, 10, x_60);
lean_ctor_set_uint8(x_68, 11, x_61);
lean_ctor_set_uint8(x_68, 12, x_62);
lean_ctor_set_uint8(x_68, 13, x_63);
lean_ctor_set_uint8(x_68, 14, x_64);
lean_ctor_set_uint8(x_68, 15, x_65);
lean_ctor_set_uint8(x_68, 16, x_66);
x_69 = 2;
x_70 = lean_uint64_shift_right(x_20, x_69);
x_71 = lean_uint64_shift_left(x_70, x_69);
x_72 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11;
x_73 = lean_uint64_lor(x_71, x_72);
x_74 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_22);
lean_ctor_set(x_74, 2, x_23);
lean_ctor_set(x_74, 3, x_24);
lean_ctor_set(x_74, 4, x_25);
lean_ctor_set(x_74, 5, x_26);
lean_ctor_set(x_74, 6, x_27);
lean_ctor_set_uint64(x_74, sizeof(void*)*7, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*7 + 8, x_21);
lean_ctor_set_uint8(x_74, sizeof(void*)*7 + 9, x_49);
lean_ctor_set_uint8(x_74, sizeof(void*)*7 + 10, x_50);
x_75 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_76 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_2, x_3, x_75, x_9, x_74, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_5, x_6, x_79, x_8, x_80, x_10, x_11, x_12, x_13, x_78);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_3);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_84 = x_76;
} else {
 lean_dec_ref(x_76);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
case 1:
{
lean_object* x_86; lean_object* x_87; uint64_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_86 = lean_ctor_get(x_10, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_dec(x_15);
x_88 = lean_ctor_get_uint64(x_10, sizeof(void*)*7);
x_89 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 8);
x_90 = lean_ctor_get(x_10, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_10, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_10, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_10, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_10, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_10, 6);
lean_inc(x_95);
x_96 = !lean_is_exclusive(x_86);
if (x_96 == 0)
{
uint8_t x_97; uint8_t x_98; uint8_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_97 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 9);
x_98 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 10);
x_99 = 3;
lean_ctor_set_uint8(x_86, 9, x_99);
x_100 = 2;
x_101 = lean_uint64_shift_right(x_88, x_100);
x_102 = lean_uint64_shift_left(x_101, x_100);
x_103 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_104 = lean_uint64_lor(x_102, x_103);
x_105 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_90);
lean_ctor_set(x_105, 2, x_91);
lean_ctor_set(x_105, 3, x_92);
lean_ctor_set(x_105, 4, x_93);
lean_ctor_set(x_105, 5, x_94);
lean_ctor_set(x_105, 6, x_95);
lean_ctor_set_uint64(x_105, sizeof(void*)*7, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 8, x_89);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 9, x_97);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 10, x_98);
x_106 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_107 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_2, x_3, x_106, x_9, x_105, x_11, x_12, x_13, x_87);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_5, x_6, x_110, x_8, x_111, x_10, x_11, x_12, x_13, x_109);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_3);
return x_112;
}
else
{
uint8_t x_113; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_107);
if (x_113 == 0)
{
return x_107;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_107, 0);
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_107);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_117 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 9);
x_118 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 10);
x_119 = lean_ctor_get_uint8(x_86, 0);
x_120 = lean_ctor_get_uint8(x_86, 1);
x_121 = lean_ctor_get_uint8(x_86, 2);
x_122 = lean_ctor_get_uint8(x_86, 3);
x_123 = lean_ctor_get_uint8(x_86, 4);
x_124 = lean_ctor_get_uint8(x_86, 5);
x_125 = lean_ctor_get_uint8(x_86, 6);
x_126 = lean_ctor_get_uint8(x_86, 7);
x_127 = lean_ctor_get_uint8(x_86, 8);
x_128 = lean_ctor_get_uint8(x_86, 10);
x_129 = lean_ctor_get_uint8(x_86, 11);
x_130 = lean_ctor_get_uint8(x_86, 12);
x_131 = lean_ctor_get_uint8(x_86, 13);
x_132 = lean_ctor_get_uint8(x_86, 14);
x_133 = lean_ctor_get_uint8(x_86, 15);
x_134 = lean_ctor_get_uint8(x_86, 16);
lean_dec(x_86);
x_135 = 3;
x_136 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_136, 0, x_119);
lean_ctor_set_uint8(x_136, 1, x_120);
lean_ctor_set_uint8(x_136, 2, x_121);
lean_ctor_set_uint8(x_136, 3, x_122);
lean_ctor_set_uint8(x_136, 4, x_123);
lean_ctor_set_uint8(x_136, 5, x_124);
lean_ctor_set_uint8(x_136, 6, x_125);
lean_ctor_set_uint8(x_136, 7, x_126);
lean_ctor_set_uint8(x_136, 8, x_127);
lean_ctor_set_uint8(x_136, 9, x_135);
lean_ctor_set_uint8(x_136, 10, x_128);
lean_ctor_set_uint8(x_136, 11, x_129);
lean_ctor_set_uint8(x_136, 12, x_130);
lean_ctor_set_uint8(x_136, 13, x_131);
lean_ctor_set_uint8(x_136, 14, x_132);
lean_ctor_set_uint8(x_136, 15, x_133);
lean_ctor_set_uint8(x_136, 16, x_134);
x_137 = 2;
x_138 = lean_uint64_shift_right(x_88, x_137);
x_139 = lean_uint64_shift_left(x_138, x_137);
x_140 = l_Lean_Meta_Grind_Canon_canonInst___closed__1;
x_141 = lean_uint64_lor(x_139, x_140);
x_142 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_90);
lean_ctor_set(x_142, 2, x_91);
lean_ctor_set(x_142, 3, x_92);
lean_ctor_set(x_142, 4, x_93);
lean_ctor_set(x_142, 5, x_94);
lean_ctor_set(x_142, 6, x_95);
lean_ctor_set_uint64(x_142, sizeof(void*)*7, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 8, x_89);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 9, x_117);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 10, x_118);
x_143 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_144 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_2, x_3, x_143, x_9, x_142, x_11, x_12, x_13, x_87);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_5, x_6, x_147, x_8, x_148, x_10, x_11, x_12, x_13, x_146);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_3);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_152 = x_144;
} else {
 lean_dec_ref(x_144);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
case 2:
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_15, 1);
lean_inc(x_154);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_3);
x_155 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint64_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_10, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
lean_dec(x_156);
x_161 = lean_ctor_get_uint64(x_10, sizeof(void*)*7);
x_162 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 8);
x_163 = lean_ctor_get(x_10, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_10, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_10, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_10, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_10, 5);
lean_inc(x_167);
x_168 = lean_ctor_get(x_10, 6);
lean_inc(x_168);
x_169 = !lean_is_exclusive(x_157);
if (x_169 == 0)
{
uint8_t x_170; uint8_t x_171; uint8_t x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; uint64_t x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_170 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 9);
x_171 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 10);
x_172 = 2;
lean_ctor_set_uint8(x_157, 9, x_172);
x_173 = 2;
x_174 = lean_uint64_shift_right(x_161, x_173);
x_175 = lean_uint64_shift_left(x_174, x_173);
x_176 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_177 = lean_uint64_lor(x_175, x_176);
x_178 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_178, 0, x_157);
lean_ctor_set(x_178, 1, x_163);
lean_ctor_set(x_178, 2, x_164);
lean_ctor_set(x_178, 3, x_165);
lean_ctor_set(x_178, 4, x_166);
lean_ctor_set(x_178, 5, x_167);
lean_ctor_set(x_178, 6, x_168);
lean_ctor_set_uint64(x_178, sizeof(void*)*7, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*7 + 8, x_162);
lean_ctor_set_uint8(x_178, sizeof(void*)*7 + 9, x_170);
lean_ctor_set_uint8(x_178, sizeof(void*)*7 + 10, x_171);
x_179 = 2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
x_180 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_2, x_159, x_179, x_160, x_178, x_11, x_12, x_13, x_158);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_185 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_5, x_6, x_183, x_8, x_184, x_10, x_11, x_12, x_13, x_182);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_3);
return x_185;
}
else
{
uint8_t x_186; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_180);
if (x_186 == 0)
{
return x_180;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_180, 0);
x_188 = lean_ctor_get(x_180, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_180);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; lean_object* x_209; uint64_t x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; uint64_t x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_190 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 9);
x_191 = lean_ctor_get_uint8(x_10, sizeof(void*)*7 + 10);
x_192 = lean_ctor_get_uint8(x_157, 0);
x_193 = lean_ctor_get_uint8(x_157, 1);
x_194 = lean_ctor_get_uint8(x_157, 2);
x_195 = lean_ctor_get_uint8(x_157, 3);
x_196 = lean_ctor_get_uint8(x_157, 4);
x_197 = lean_ctor_get_uint8(x_157, 5);
x_198 = lean_ctor_get_uint8(x_157, 6);
x_199 = lean_ctor_get_uint8(x_157, 7);
x_200 = lean_ctor_get_uint8(x_157, 8);
x_201 = lean_ctor_get_uint8(x_157, 10);
x_202 = lean_ctor_get_uint8(x_157, 11);
x_203 = lean_ctor_get_uint8(x_157, 12);
x_204 = lean_ctor_get_uint8(x_157, 13);
x_205 = lean_ctor_get_uint8(x_157, 14);
x_206 = lean_ctor_get_uint8(x_157, 15);
x_207 = lean_ctor_get_uint8(x_157, 16);
lean_dec(x_157);
x_208 = 2;
x_209 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_209, 0, x_192);
lean_ctor_set_uint8(x_209, 1, x_193);
lean_ctor_set_uint8(x_209, 2, x_194);
lean_ctor_set_uint8(x_209, 3, x_195);
lean_ctor_set_uint8(x_209, 4, x_196);
lean_ctor_set_uint8(x_209, 5, x_197);
lean_ctor_set_uint8(x_209, 6, x_198);
lean_ctor_set_uint8(x_209, 7, x_199);
lean_ctor_set_uint8(x_209, 8, x_200);
lean_ctor_set_uint8(x_209, 9, x_208);
lean_ctor_set_uint8(x_209, 10, x_201);
lean_ctor_set_uint8(x_209, 11, x_202);
lean_ctor_set_uint8(x_209, 12, x_203);
lean_ctor_set_uint8(x_209, 13, x_204);
lean_ctor_set_uint8(x_209, 14, x_205);
lean_ctor_set_uint8(x_209, 15, x_206);
lean_ctor_set_uint8(x_209, 16, x_207);
x_210 = 2;
x_211 = lean_uint64_shift_right(x_161, x_210);
x_212 = lean_uint64_shift_left(x_211, x_210);
x_213 = l_Lean_Meta_Grind_Canon_canonImplicit___closed__1;
x_214 = lean_uint64_lor(x_212, x_213);
x_215 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_215, 0, x_209);
lean_ctor_set(x_215, 1, x_163);
lean_ctor_set(x_215, 2, x_164);
lean_ctor_set(x_215, 3, x_165);
lean_ctor_set(x_215, 4, x_166);
lean_ctor_set(x_215, 5, x_167);
lean_ctor_set(x_215, 6, x_168);
lean_ctor_set_uint64(x_215, sizeof(void*)*7, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*7 + 8, x_162);
lean_ctor_set_uint8(x_215, sizeof(void*)*7 + 9, x_190);
lean_ctor_set_uint8(x_215, sizeof(void*)*7 + 10, x_191);
x_216 = 2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
x_217 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_2, x_159, x_216, x_160, x_215, x_11, x_12, x_13, x_158);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_5, x_6, x_220, x_8, x_221, x_10, x_11, x_12, x_13, x_219);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_3);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_223 = lean_ctor_get(x_217, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_225 = x_217;
} else {
 lean_dec_ref(x_217);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_227 = !lean_is_exclusive(x_155);
if (x_227 == 0)
{
return x_155;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_155, 0);
x_229 = lean_ctor_get(x_155, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_155);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
default: 
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_4);
x_231 = lean_ctor_get(x_15, 1);
lean_inc(x_231);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_3);
x_232 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_3, x_2, x_5, x_6, x_235, x_8, x_236, x_10, x_11, x_12, x_13, x_234);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_3);
return x_237;
}
else
{
uint8_t x_238; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_238 = !lean_is_exclusive(x_232);
if (x_238 == 0)
{
return x_232;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_232, 0);
x_240 = lean_ctor_get(x_232, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_232);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_15);
if (x_242 == 0)
{
return x_15;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_15, 0);
x_244 = lean_ctor_get(x_15, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_15);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_array_fget(x_12, x_2);
x_15 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_unbox(x_13);
lean_dec(x_13);
x_24 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(x_3, x_2, x_14, x_4, x_12, x_23, x_22, x_5, x_21, x_7, x_8, x_9, x_10, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_26 = x_16;
} else {
 lean_dec_ref(x_16);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_28 = x_17;
} else {
 lean_dec_ref(x_17);
 x_28 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_29 = l_Lean_Meta_Grind_Canon_shouldCanon(x_3, x_2, x_14, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_32 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_57; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_14);
x_35 = l_Lean_MessageData_ofExpr(x_14);
x_36 = l_Lean_MessageData_ofExpr(x_33);
x_57 = lean_unbox(x_30);
lean_dec(x_30);
switch (x_57) {
case 0:
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2;
x_37 = x_58;
goto block_56;
}
case 1:
{
lean_object* x_59; 
x_59 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4;
x_37 = x_59;
goto block_56;
}
case 2:
{
lean_object* x_60; 
x_60 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6;
x_37 = x_60;
goto block_56;
}
default: 
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8;
x_37 = x_61;
goto block_56;
}
}
block_56:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2;
if (lean_is_scalar(x_28)) {
 x_40 = lean_alloc_ctor(7, 2, 0);
} else {
 x_40 = x_28;
 lean_ctor_set_tag(x_40, 7);
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4;
if (lean_is_scalar(x_26)) {
 x_42 = lean_alloc_ctor(7, 2, 0);
} else {
 x_42 = x_26;
 lean_ctor_set_tag(x_42, 7);
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
x_44 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
x_47 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(x_15, x_48, x_5, x_27, x_7, x_8, x_9, x_10, x_34);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_unbox(x_13);
lean_dec(x_13);
x_55 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(x_3, x_2, x_14, x_4, x_12, x_54, x_52, x_5, x_53, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_52);
return x_55;
}
}
else
{
uint8_t x_62; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_32);
if (x_62 == 0)
{
return x_32;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_32, 0);
x_64 = lean_ctor_get(x_32, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_32);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_29);
if (x_66 == 0)
{
return x_29;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_29, 0);
x_68 = lean_ctor_get(x_29, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_29);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_9(x_23, lean_box(0), x_21, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_26);
x_28 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_2, x_25, x_27, lean_box(0), lean_box(0), x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_13, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_9(x_26, lean_box(0), x_12, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_13);
x_29 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___boxed), 11, 4);
lean_closure_set(x_29, 0, x_12);
lean_closure_set(x_29, 1, x_13);
lean_closure_set(x_29, 2, x_8);
lean_closure_set(x_29, 3, x_5);
x_30 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4___boxed), 20, 12);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_11);
lean_closure_set(x_30, 2, x_13);
lean_closure_set(x_30, 3, x_2);
lean_closure_set(x_30, 4, x_3);
lean_closure_set(x_30, 5, x_4);
lean_closure_set(x_30, 6, x_5);
lean_closure_set(x_30, 7, x_6);
lean_closure_set(x_30, 8, x_7);
lean_closure_set(x_30, 9, x_8);
lean_closure_set(x_30, 10, x_9);
lean_closure_set(x_30, 11, x_10);
x_31 = lean_apply_11(x_28, lean_box(0), lean_box(0), x_29, x_30, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nestedProof", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2;
x_2 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3;
x_3 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_16; lean_object* x_95; lean_object* x_150; uint8_t x_151; 
lean_dec(x_8);
x_150 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_151 = l_Lean_Expr_isConstOf(x_6, x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_95 = x_152;
goto block_149;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_array_get_size(x_7);
x_154 = lean_unsigned_to_nat(2u);
x_155 = lean_nat_dec_eq(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_153);
x_156 = lean_box(0);
x_95 = x_156;
goto block_149;
}
else
{
lean_object* x_157; uint8_t x_158; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_nat_dec_lt(x_157, x_153);
lean_dec(x_153);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Lean_instInhabitedExpr;
x_160 = l_outOfBounds___rarg(x_159);
x_16 = x_160;
goto block_94;
}
else
{
lean_object* x_161; 
x_161 = lean_array_fget(x_7, x_157);
x_16 = x_161;
goto block_94;
}
}
}
block_94:
{
lean_object* x_17; 
lean_inc(x_16);
x_17 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_inc(x_23);
x_24 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_23, x_21);
if (lean_obj_tag(x_24) == 0)
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_26 = lean_ptr_addr(x_21);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_21);
x_29 = lean_array_set(x_7, x_28, x_21);
x_30 = l_Lean_mkAppN(x_6, x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
lean_inc(x_30);
x_33 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_23, x_21, x_30);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_19, 1, x_34);
lean_ctor_set(x_19, 0, x_30);
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
lean_inc(x_1);
x_37 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_23, x_21, x_1);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_19, 0, x_1);
return x_17;
}
}
else
{
lean_object* x_39; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_39);
return x_17;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_inc(x_42);
x_43 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_42, x_40);
if (lean_obj_tag(x_43) == 0)
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_45 = lean_ptr_addr(x_40);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_47 = lean_unsigned_to_nat(0u);
lean_inc(x_40);
x_48 = lean_array_set(x_7, x_47, x_40);
x_49 = l_Lean_mkAppN(x_6, x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_dec(x_41);
lean_inc(x_49);
x_52 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_42, x_40, x_49);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_17, 0, x_54);
return x_17;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_6);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_dec(x_41);
lean_inc(x_1);
x_57 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_42, x_40, x_1);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_17, 0, x_59);
return x_17;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_ctor_get(x_43, 0);
lean_inc(x_60);
lean_dec(x_43);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_17, 0, x_61);
return x_17;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_17, 0);
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_17);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
lean_inc(x_67);
x_68 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_67, x_64);
if (lean_obj_tag(x_68) == 0)
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_70 = lean_ptr_addr(x_64);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_72 = lean_unsigned_to_nat(0u);
lean_inc(x_64);
x_73 = lean_array_set(x_7, x_72, x_64);
x_74 = l_Lean_mkAppN(x_6, x_73);
lean_dec(x_73);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_dec(x_65);
lean_inc(x_74);
x_77 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_67, x_64, x_74);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
if (lean_is_scalar(x_66)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_66;
}
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_63);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_7);
lean_dec(x_6);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_dec(x_65);
lean_inc(x_1);
x_83 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_67, x_64, x_1);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_83);
if (lean_is_scalar(x_66)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_66;
}
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_63);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_87 = lean_ctor_get(x_68, 0);
lean_inc(x_87);
lean_dec(x_68);
if (lean_is_scalar(x_66)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_66;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_65);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_63);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_17);
if (x_90 == 0)
{
return x_17;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_17, 0);
x_92 = lean_ctor_get(x_17, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_17);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
block_149:
{
lean_object* x_96; 
lean_dec(x_95);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_96 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_array_get_size(x_7);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_unsigned_to_nat(1u);
lean_inc(x_100);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_102);
x_104 = 0;
x_105 = lean_box(x_104);
lean_inc(x_7);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_7);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_103);
lean_inc(x_6);
x_108 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_107, x_99, x_100, x_103, x_103, x_106, x_101, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_98);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_110);
lean_dec(x_6);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_108, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_109);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_109, 0);
lean_dec(x_116);
lean_ctor_set(x_109, 0, x_1);
return x_108;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
lean_dec(x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_108, 0, x_118);
return x_108;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_108, 1);
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_ctor_get(x_109, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_121 = x_109;
} else {
 lean_dec_ref(x_109);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_108);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_108, 0);
lean_dec(x_125);
x_126 = !lean_is_exclusive(x_109);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_109, 0);
lean_dec(x_127);
x_128 = lean_ctor_get(x_110, 0);
lean_inc(x_128);
lean_dec(x_110);
x_129 = l_Lean_mkAppN(x_6, x_128);
lean_dec(x_128);
lean_ctor_set(x_109, 0, x_129);
return x_108;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_109, 1);
lean_inc(x_130);
lean_dec(x_109);
x_131 = lean_ctor_get(x_110, 0);
lean_inc(x_131);
lean_dec(x_110);
x_132 = l_Lean_mkAppN(x_6, x_131);
lean_dec(x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
lean_ctor_set(x_108, 0, x_133);
return x_108;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_108, 1);
lean_inc(x_134);
lean_dec(x_108);
x_135 = lean_ctor_get(x_109, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_136 = x_109;
} else {
 lean_dec_ref(x_109);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_110, 0);
lean_inc(x_137);
lean_dec(x_110);
x_138 = l_Lean_mkAppN(x_6, x_137);
lean_dec(x_137);
if (lean_is_scalar(x_136)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_136;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_135);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_6);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_108);
if (x_141 == 0)
{
return x_108;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_108, 0);
x_143 = lean_ctor_get(x_108, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_108);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_96);
if (x_145 == 0)
{
return x_96;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_96, 0);
x_147 = lean_ctor_get(x_96, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_96);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
case 1:
{
lean_object* x_162; lean_object* x_241; lean_object* x_296; uint8_t x_297; 
lean_dec(x_8);
x_296 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_297 = l_Lean_Expr_isConstOf(x_6, x_296);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_box(0);
x_241 = x_298;
goto block_295;
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = lean_array_get_size(x_7);
x_300 = lean_unsigned_to_nat(2u);
x_301 = lean_nat_dec_eq(x_299, x_300);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_299);
x_302 = lean_box(0);
x_241 = x_302;
goto block_295;
}
else
{
lean_object* x_303; uint8_t x_304; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_303 = lean_unsigned_to_nat(0u);
x_304 = lean_nat_dec_lt(x_303, x_299);
lean_dec(x_299);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = l_Lean_instInhabitedExpr;
x_306 = l_outOfBounds___rarg(x_305);
x_162 = x_306;
goto block_240;
}
else
{
lean_object* x_307; 
x_307 = lean_array_fget(x_7, x_303);
x_162 = x_307;
goto block_240;
}
}
}
block_240:
{
lean_object* x_163; 
lean_inc(x_162);
x_163 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_162, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
lean_inc(x_169);
x_170 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_169, x_167);
if (lean_obj_tag(x_170) == 0)
{
size_t x_171; size_t x_172; uint8_t x_173; 
x_171 = lean_ptr_addr(x_162);
lean_dec(x_162);
x_172 = lean_ptr_addr(x_167);
x_173 = lean_usize_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_1);
x_174 = lean_unsigned_to_nat(0u);
lean_inc(x_167);
x_175 = lean_array_set(x_7, x_174, x_167);
x_176 = l_Lean_mkAppN(x_6, x_175);
lean_dec(x_175);
x_177 = lean_ctor_get(x_168, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_168, 1);
lean_inc(x_178);
lean_dec(x_168);
lean_inc(x_176);
x_179 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_169, x_167, x_176);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set(x_180, 2, x_179);
lean_ctor_set(x_165, 1, x_180);
lean_ctor_set(x_165, 0, x_176);
return x_163;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_7);
lean_dec(x_6);
x_181 = lean_ctor_get(x_168, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_168, 1);
lean_inc(x_182);
lean_dec(x_168);
lean_inc(x_1);
x_183 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_169, x_167, x_1);
x_184 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
lean_ctor_set(x_184, 2, x_183);
lean_ctor_set(x_165, 1, x_184);
lean_ctor_set(x_165, 0, x_1);
return x_163;
}
}
else
{
lean_object* x_185; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_162);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_185 = lean_ctor_get(x_170, 0);
lean_inc(x_185);
lean_dec(x_170);
lean_ctor_set(x_165, 0, x_185);
return x_163;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_165, 0);
x_187 = lean_ctor_get(x_165, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_165);
x_188 = lean_ctor_get(x_187, 2);
lean_inc(x_188);
lean_inc(x_188);
x_189 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_188, x_186);
if (lean_obj_tag(x_189) == 0)
{
size_t x_190; size_t x_191; uint8_t x_192; 
x_190 = lean_ptr_addr(x_162);
lean_dec(x_162);
x_191 = lean_ptr_addr(x_186);
x_192 = lean_usize_dec_eq(x_190, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_1);
x_193 = lean_unsigned_to_nat(0u);
lean_inc(x_186);
x_194 = lean_array_set(x_7, x_193, x_186);
x_195 = l_Lean_mkAppN(x_6, x_194);
lean_dec(x_194);
x_196 = lean_ctor_get(x_187, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_187, 1);
lean_inc(x_197);
lean_dec(x_187);
lean_inc(x_195);
x_198 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_188, x_186, x_195);
x_199 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_163, 0, x_200);
return x_163;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_7);
lean_dec(x_6);
x_201 = lean_ctor_get(x_187, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_187, 1);
lean_inc(x_202);
lean_dec(x_187);
lean_inc(x_1);
x_203 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_188, x_186, x_1);
x_204 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_204, 2, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_1);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_163, 0, x_205);
return x_163;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_162);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_206 = lean_ctor_get(x_189, 0);
lean_inc(x_206);
lean_dec(x_189);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_187);
lean_ctor_set(x_163, 0, x_207);
return x_163;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_163, 0);
x_209 = lean_ctor_get(x_163, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_163);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_212 = x_208;
} else {
 lean_dec_ref(x_208);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_211, 2);
lean_inc(x_213);
lean_inc(x_213);
x_214 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_213, x_210);
if (lean_obj_tag(x_214) == 0)
{
size_t x_215; size_t x_216; uint8_t x_217; 
x_215 = lean_ptr_addr(x_162);
lean_dec(x_162);
x_216 = lean_ptr_addr(x_210);
x_217 = lean_usize_dec_eq(x_215, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_1);
x_218 = lean_unsigned_to_nat(0u);
lean_inc(x_210);
x_219 = lean_array_set(x_7, x_218, x_210);
x_220 = l_Lean_mkAppN(x_6, x_219);
lean_dec(x_219);
x_221 = lean_ctor_get(x_211, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_211, 1);
lean_inc(x_222);
lean_dec(x_211);
lean_inc(x_220);
x_223 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_213, x_210, x_220);
x_224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
lean_ctor_set(x_224, 2, x_223);
if (lean_is_scalar(x_212)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_212;
}
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_209);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_7);
lean_dec(x_6);
x_227 = lean_ctor_get(x_211, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_211, 1);
lean_inc(x_228);
lean_dec(x_211);
lean_inc(x_1);
x_229 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_213, x_210, x_1);
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
lean_ctor_set(x_230, 2, x_229);
if (lean_is_scalar(x_212)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_212;
}
lean_ctor_set(x_231, 0, x_1);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_209);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_162);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_233 = lean_ctor_get(x_214, 0);
lean_inc(x_233);
lean_dec(x_214);
if (lean_is_scalar(x_212)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_212;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_211);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_209);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_162);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_163);
if (x_236 == 0)
{
return x_163;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_163, 0);
x_238 = lean_ctor_get(x_163, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_163);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
block_295:
{
lean_object* x_242; 
lean_dec(x_241);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_242 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_array_get_size(x_7);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_unsigned_to_nat(1u);
lean_inc(x_246);
x_249 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_246);
lean_ctor_set(x_249, 2, x_248);
x_250 = 0;
x_251 = lean_box(x_250);
lean_inc(x_7);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_7);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_249);
lean_inc(x_6);
x_254 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_253, x_245, x_246, x_249, x_249, x_252, x_247, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_244);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
uint8_t x_259; 
lean_dec(x_256);
lean_dec(x_6);
x_259 = !lean_is_exclusive(x_254);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_254, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_255);
if (x_261 == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_255, 0);
lean_dec(x_262);
lean_ctor_set(x_255, 0, x_1);
return x_254;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_255, 1);
lean_inc(x_263);
lean_dec(x_255);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_1);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_254, 0, x_264);
return x_254;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_254, 1);
lean_inc(x_265);
lean_dec(x_254);
x_266 = lean_ctor_get(x_255, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_267 = x_255;
} else {
 lean_dec_ref(x_255);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_1);
lean_ctor_set(x_268, 1, x_266);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_265);
return x_269;
}
}
else
{
uint8_t x_270; 
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_254);
if (x_270 == 0)
{
lean_object* x_271; uint8_t x_272; 
x_271 = lean_ctor_get(x_254, 0);
lean_dec(x_271);
x_272 = !lean_is_exclusive(x_255);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_255, 0);
lean_dec(x_273);
x_274 = lean_ctor_get(x_256, 0);
lean_inc(x_274);
lean_dec(x_256);
x_275 = l_Lean_mkAppN(x_6, x_274);
lean_dec(x_274);
lean_ctor_set(x_255, 0, x_275);
return x_254;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_255, 1);
lean_inc(x_276);
lean_dec(x_255);
x_277 = lean_ctor_get(x_256, 0);
lean_inc(x_277);
lean_dec(x_256);
x_278 = l_Lean_mkAppN(x_6, x_277);
lean_dec(x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set(x_254, 0, x_279);
return x_254;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_280 = lean_ctor_get(x_254, 1);
lean_inc(x_280);
lean_dec(x_254);
x_281 = lean_ctor_get(x_255, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_282 = x_255;
} else {
 lean_dec_ref(x_255);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_256, 0);
lean_inc(x_283);
lean_dec(x_256);
x_284 = l_Lean_mkAppN(x_6, x_283);
lean_dec(x_283);
if (lean_is_scalar(x_282)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_282;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_281);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_280);
return x_286;
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_6);
lean_dec(x_1);
x_287 = !lean_is_exclusive(x_254);
if (x_287 == 0)
{
return x_254;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_254, 0);
x_289 = lean_ctor_get(x_254, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_254);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = !lean_is_exclusive(x_242);
if (x_291 == 0)
{
return x_242;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_242, 0);
x_293 = lean_ctor_get(x_242, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_242);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
}
case 2:
{
lean_object* x_308; lean_object* x_387; lean_object* x_442; uint8_t x_443; 
lean_dec(x_8);
x_442 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_443 = l_Lean_Expr_isConstOf(x_6, x_442);
if (x_443 == 0)
{
lean_object* x_444; 
x_444 = lean_box(0);
x_387 = x_444;
goto block_441;
}
else
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_445 = lean_array_get_size(x_7);
x_446 = lean_unsigned_to_nat(2u);
x_447 = lean_nat_dec_eq(x_445, x_446);
if (x_447 == 0)
{
lean_object* x_448; 
lean_dec(x_445);
x_448 = lean_box(0);
x_387 = x_448;
goto block_441;
}
else
{
lean_object* x_449; uint8_t x_450; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_449 = lean_unsigned_to_nat(0u);
x_450 = lean_nat_dec_lt(x_449, x_445);
lean_dec(x_445);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = l_Lean_instInhabitedExpr;
x_452 = l_outOfBounds___rarg(x_451);
x_308 = x_452;
goto block_386;
}
else
{
lean_object* x_453; 
x_453 = lean_array_fget(x_7, x_449);
x_308 = x_453;
goto block_386;
}
}
}
block_386:
{
lean_object* x_309; 
lean_inc(x_308);
x_309 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_308, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_309) == 0)
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_313 = lean_ctor_get(x_311, 0);
x_314 = lean_ctor_get(x_311, 1);
x_315 = lean_ctor_get(x_314, 2);
lean_inc(x_315);
lean_inc(x_315);
x_316 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_315, x_313);
if (lean_obj_tag(x_316) == 0)
{
size_t x_317; size_t x_318; uint8_t x_319; 
x_317 = lean_ptr_addr(x_308);
lean_dec(x_308);
x_318 = lean_ptr_addr(x_313);
x_319 = lean_usize_dec_eq(x_317, x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_1);
x_320 = lean_unsigned_to_nat(0u);
lean_inc(x_313);
x_321 = lean_array_set(x_7, x_320, x_313);
x_322 = l_Lean_mkAppN(x_6, x_321);
lean_dec(x_321);
x_323 = lean_ctor_get(x_314, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_314, 1);
lean_inc(x_324);
lean_dec(x_314);
lean_inc(x_322);
x_325 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_315, x_313, x_322);
x_326 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
lean_ctor_set(x_326, 2, x_325);
lean_ctor_set(x_311, 1, x_326);
lean_ctor_set(x_311, 0, x_322);
return x_309;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_7);
lean_dec(x_6);
x_327 = lean_ctor_get(x_314, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_314, 1);
lean_inc(x_328);
lean_dec(x_314);
lean_inc(x_1);
x_329 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_315, x_313, x_1);
x_330 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
lean_ctor_set(x_330, 2, x_329);
lean_ctor_set(x_311, 1, x_330);
lean_ctor_set(x_311, 0, x_1);
return x_309;
}
}
else
{
lean_object* x_331; 
lean_dec(x_315);
lean_dec(x_313);
lean_dec(x_308);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_331 = lean_ctor_get(x_316, 0);
lean_inc(x_331);
lean_dec(x_316);
lean_ctor_set(x_311, 0, x_331);
return x_309;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_311, 0);
x_333 = lean_ctor_get(x_311, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_311);
x_334 = lean_ctor_get(x_333, 2);
lean_inc(x_334);
lean_inc(x_334);
x_335 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_334, x_332);
if (lean_obj_tag(x_335) == 0)
{
size_t x_336; size_t x_337; uint8_t x_338; 
x_336 = lean_ptr_addr(x_308);
lean_dec(x_308);
x_337 = lean_ptr_addr(x_332);
x_338 = lean_usize_dec_eq(x_336, x_337);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_1);
x_339 = lean_unsigned_to_nat(0u);
lean_inc(x_332);
x_340 = lean_array_set(x_7, x_339, x_332);
x_341 = l_Lean_mkAppN(x_6, x_340);
lean_dec(x_340);
x_342 = lean_ctor_get(x_333, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_333, 1);
lean_inc(x_343);
lean_dec(x_333);
lean_inc(x_341);
x_344 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_334, x_332, x_341);
x_345 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
lean_ctor_set(x_345, 2, x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_341);
lean_ctor_set(x_346, 1, x_345);
lean_ctor_set(x_309, 0, x_346);
return x_309;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_7);
lean_dec(x_6);
x_347 = lean_ctor_get(x_333, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_333, 1);
lean_inc(x_348);
lean_dec(x_333);
lean_inc(x_1);
x_349 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_334, x_332, x_1);
x_350 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
lean_ctor_set(x_350, 2, x_349);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_1);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set(x_309, 0, x_351);
return x_309;
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_334);
lean_dec(x_332);
lean_dec(x_308);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_352 = lean_ctor_get(x_335, 0);
lean_inc(x_352);
lean_dec(x_335);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_333);
lean_ctor_set(x_309, 0, x_353);
return x_309;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_354 = lean_ctor_get(x_309, 0);
x_355 = lean_ctor_get(x_309, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_309);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_358 = x_354;
} else {
 lean_dec_ref(x_354);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_357, 2);
lean_inc(x_359);
lean_inc(x_359);
x_360 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_359, x_356);
if (lean_obj_tag(x_360) == 0)
{
size_t x_361; size_t x_362; uint8_t x_363; 
x_361 = lean_ptr_addr(x_308);
lean_dec(x_308);
x_362 = lean_ptr_addr(x_356);
x_363 = lean_usize_dec_eq(x_361, x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_1);
x_364 = lean_unsigned_to_nat(0u);
lean_inc(x_356);
x_365 = lean_array_set(x_7, x_364, x_356);
x_366 = l_Lean_mkAppN(x_6, x_365);
lean_dec(x_365);
x_367 = lean_ctor_get(x_357, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_357, 1);
lean_inc(x_368);
lean_dec(x_357);
lean_inc(x_366);
x_369 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_359, x_356, x_366);
x_370 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
lean_ctor_set(x_370, 2, x_369);
if (lean_is_scalar(x_358)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_358;
}
lean_ctor_set(x_371, 0, x_366);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_355);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_7);
lean_dec(x_6);
x_373 = lean_ctor_get(x_357, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_357, 1);
lean_inc(x_374);
lean_dec(x_357);
lean_inc(x_1);
x_375 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_359, x_356, x_1);
x_376 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
lean_ctor_set(x_376, 2, x_375);
if (lean_is_scalar(x_358)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_358;
}
lean_ctor_set(x_377, 0, x_1);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_355);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_359);
lean_dec(x_356);
lean_dec(x_308);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_379 = lean_ctor_get(x_360, 0);
lean_inc(x_379);
lean_dec(x_360);
if (lean_is_scalar(x_358)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_358;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_357);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_355);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_308);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_309);
if (x_382 == 0)
{
return x_309;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_309, 0);
x_384 = lean_ctor_get(x_309, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_309);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
block_441:
{
lean_object* x_388; 
lean_dec(x_387);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_388 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_ctor_get(x_389, 0);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_array_get_size(x_7);
x_393 = lean_unsigned_to_nat(0u);
x_394 = lean_unsigned_to_nat(1u);
lean_inc(x_392);
x_395 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_392);
lean_ctor_set(x_395, 2, x_394);
x_396 = 0;
x_397 = lean_box(x_396);
lean_inc(x_7);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_7);
lean_ctor_set(x_398, 1, x_397);
x_399 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_395);
lean_inc(x_6);
x_400 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_399, x_391, x_392, x_395, x_395, x_398, x_393, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_390);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 1);
lean_inc(x_403);
x_404 = lean_unbox(x_403);
lean_dec(x_403);
if (x_404 == 0)
{
uint8_t x_405; 
lean_dec(x_402);
lean_dec(x_6);
x_405 = !lean_is_exclusive(x_400);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_ctor_get(x_400, 0);
lean_dec(x_406);
x_407 = !lean_is_exclusive(x_401);
if (x_407 == 0)
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_401, 0);
lean_dec(x_408);
lean_ctor_set(x_401, 0, x_1);
return x_400;
}
else
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_401, 1);
lean_inc(x_409);
lean_dec(x_401);
x_410 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_410, 0, x_1);
lean_ctor_set(x_410, 1, x_409);
lean_ctor_set(x_400, 0, x_410);
return x_400;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_411 = lean_ctor_get(x_400, 1);
lean_inc(x_411);
lean_dec(x_400);
x_412 = lean_ctor_get(x_401, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_413 = x_401;
} else {
 lean_dec_ref(x_401);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_1);
lean_ctor_set(x_414, 1, x_412);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_411);
return x_415;
}
}
else
{
uint8_t x_416; 
lean_dec(x_1);
x_416 = !lean_is_exclusive(x_400);
if (x_416 == 0)
{
lean_object* x_417; uint8_t x_418; 
x_417 = lean_ctor_get(x_400, 0);
lean_dec(x_417);
x_418 = !lean_is_exclusive(x_401);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_401, 0);
lean_dec(x_419);
x_420 = lean_ctor_get(x_402, 0);
lean_inc(x_420);
lean_dec(x_402);
x_421 = l_Lean_mkAppN(x_6, x_420);
lean_dec(x_420);
lean_ctor_set(x_401, 0, x_421);
return x_400;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_401, 1);
lean_inc(x_422);
lean_dec(x_401);
x_423 = lean_ctor_get(x_402, 0);
lean_inc(x_423);
lean_dec(x_402);
x_424 = l_Lean_mkAppN(x_6, x_423);
lean_dec(x_423);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_422);
lean_ctor_set(x_400, 0, x_425);
return x_400;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_426 = lean_ctor_get(x_400, 1);
lean_inc(x_426);
lean_dec(x_400);
x_427 = lean_ctor_get(x_401, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_428 = x_401;
} else {
 lean_dec_ref(x_401);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_402, 0);
lean_inc(x_429);
lean_dec(x_402);
x_430 = l_Lean_mkAppN(x_6, x_429);
lean_dec(x_429);
if (lean_is_scalar(x_428)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_428;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_427);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_426);
return x_432;
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_6);
lean_dec(x_1);
x_433 = !lean_is_exclusive(x_400);
if (x_433 == 0)
{
return x_400;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_400, 0);
x_435 = lean_ctor_get(x_400, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_400);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_437 = !lean_is_exclusive(x_388);
if (x_437 == 0)
{
return x_388;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_388, 0);
x_439 = lean_ctor_get(x_388, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_388);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
}
case 3:
{
lean_object* x_454; lean_object* x_533; lean_object* x_588; uint8_t x_589; 
lean_dec(x_8);
x_588 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_589 = l_Lean_Expr_isConstOf(x_6, x_588);
if (x_589 == 0)
{
lean_object* x_590; 
x_590 = lean_box(0);
x_533 = x_590;
goto block_587;
}
else
{
lean_object* x_591; lean_object* x_592; uint8_t x_593; 
x_591 = lean_array_get_size(x_7);
x_592 = lean_unsigned_to_nat(2u);
x_593 = lean_nat_dec_eq(x_591, x_592);
if (x_593 == 0)
{
lean_object* x_594; 
lean_dec(x_591);
x_594 = lean_box(0);
x_533 = x_594;
goto block_587;
}
else
{
lean_object* x_595; uint8_t x_596; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_595 = lean_unsigned_to_nat(0u);
x_596 = lean_nat_dec_lt(x_595, x_591);
lean_dec(x_591);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; 
x_597 = l_Lean_instInhabitedExpr;
x_598 = l_outOfBounds___rarg(x_597);
x_454 = x_598;
goto block_532;
}
else
{
lean_object* x_599; 
x_599 = lean_array_fget(x_7, x_595);
x_454 = x_599;
goto block_532;
}
}
}
block_532:
{
lean_object* x_455; 
lean_inc(x_454);
x_455 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_454, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_455) == 0)
{
uint8_t x_456; 
x_456 = !lean_is_exclusive(x_455);
if (x_456 == 0)
{
lean_object* x_457; uint8_t x_458; 
x_457 = lean_ctor_get(x_455, 0);
x_458 = !lean_is_exclusive(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_459 = lean_ctor_get(x_457, 0);
x_460 = lean_ctor_get(x_457, 1);
x_461 = lean_ctor_get(x_460, 2);
lean_inc(x_461);
lean_inc(x_461);
x_462 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_461, x_459);
if (lean_obj_tag(x_462) == 0)
{
size_t x_463; size_t x_464; uint8_t x_465; 
x_463 = lean_ptr_addr(x_454);
lean_dec(x_454);
x_464 = lean_ptr_addr(x_459);
x_465 = lean_usize_dec_eq(x_463, x_464);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_1);
x_466 = lean_unsigned_to_nat(0u);
lean_inc(x_459);
x_467 = lean_array_set(x_7, x_466, x_459);
x_468 = l_Lean_mkAppN(x_6, x_467);
lean_dec(x_467);
x_469 = lean_ctor_get(x_460, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_460, 1);
lean_inc(x_470);
lean_dec(x_460);
lean_inc(x_468);
x_471 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_461, x_459, x_468);
x_472 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
lean_ctor_set(x_472, 2, x_471);
lean_ctor_set(x_457, 1, x_472);
lean_ctor_set(x_457, 0, x_468);
return x_455;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_7);
lean_dec(x_6);
x_473 = lean_ctor_get(x_460, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_460, 1);
lean_inc(x_474);
lean_dec(x_460);
lean_inc(x_1);
x_475 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_461, x_459, x_1);
x_476 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
lean_ctor_set(x_476, 2, x_475);
lean_ctor_set(x_457, 1, x_476);
lean_ctor_set(x_457, 0, x_1);
return x_455;
}
}
else
{
lean_object* x_477; 
lean_dec(x_461);
lean_dec(x_459);
lean_dec(x_454);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_477 = lean_ctor_get(x_462, 0);
lean_inc(x_477);
lean_dec(x_462);
lean_ctor_set(x_457, 0, x_477);
return x_455;
}
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_478 = lean_ctor_get(x_457, 0);
x_479 = lean_ctor_get(x_457, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_457);
x_480 = lean_ctor_get(x_479, 2);
lean_inc(x_480);
lean_inc(x_480);
x_481 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_480, x_478);
if (lean_obj_tag(x_481) == 0)
{
size_t x_482; size_t x_483; uint8_t x_484; 
x_482 = lean_ptr_addr(x_454);
lean_dec(x_454);
x_483 = lean_ptr_addr(x_478);
x_484 = lean_usize_dec_eq(x_482, x_483);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_1);
x_485 = lean_unsigned_to_nat(0u);
lean_inc(x_478);
x_486 = lean_array_set(x_7, x_485, x_478);
x_487 = l_Lean_mkAppN(x_6, x_486);
lean_dec(x_486);
x_488 = lean_ctor_get(x_479, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_479, 1);
lean_inc(x_489);
lean_dec(x_479);
lean_inc(x_487);
x_490 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_480, x_478, x_487);
x_491 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_489);
lean_ctor_set(x_491, 2, x_490);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_487);
lean_ctor_set(x_492, 1, x_491);
lean_ctor_set(x_455, 0, x_492);
return x_455;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_7);
lean_dec(x_6);
x_493 = lean_ctor_get(x_479, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_479, 1);
lean_inc(x_494);
lean_dec(x_479);
lean_inc(x_1);
x_495 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_480, x_478, x_1);
x_496 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
lean_ctor_set(x_496, 2, x_495);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_1);
lean_ctor_set(x_497, 1, x_496);
lean_ctor_set(x_455, 0, x_497);
return x_455;
}
}
else
{
lean_object* x_498; lean_object* x_499; 
lean_dec(x_480);
lean_dec(x_478);
lean_dec(x_454);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_498 = lean_ctor_get(x_481, 0);
lean_inc(x_498);
lean_dec(x_481);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_479);
lean_ctor_set(x_455, 0, x_499);
return x_455;
}
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_500 = lean_ctor_get(x_455, 0);
x_501 = lean_ctor_get(x_455, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_455);
x_502 = lean_ctor_get(x_500, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_500, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_504 = x_500;
} else {
 lean_dec_ref(x_500);
 x_504 = lean_box(0);
}
x_505 = lean_ctor_get(x_503, 2);
lean_inc(x_505);
lean_inc(x_505);
x_506 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_505, x_502);
if (lean_obj_tag(x_506) == 0)
{
size_t x_507; size_t x_508; uint8_t x_509; 
x_507 = lean_ptr_addr(x_454);
lean_dec(x_454);
x_508 = lean_ptr_addr(x_502);
x_509 = lean_usize_dec_eq(x_507, x_508);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_1);
x_510 = lean_unsigned_to_nat(0u);
lean_inc(x_502);
x_511 = lean_array_set(x_7, x_510, x_502);
x_512 = l_Lean_mkAppN(x_6, x_511);
lean_dec(x_511);
x_513 = lean_ctor_get(x_503, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_503, 1);
lean_inc(x_514);
lean_dec(x_503);
lean_inc(x_512);
x_515 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_505, x_502, x_512);
x_516 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
lean_ctor_set(x_516, 2, x_515);
if (lean_is_scalar(x_504)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_504;
}
lean_ctor_set(x_517, 0, x_512);
lean_ctor_set(x_517, 1, x_516);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_501);
return x_518;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_7);
lean_dec(x_6);
x_519 = lean_ctor_get(x_503, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_503, 1);
lean_inc(x_520);
lean_dec(x_503);
lean_inc(x_1);
x_521 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_505, x_502, x_1);
x_522 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_520);
lean_ctor_set(x_522, 2, x_521);
if (lean_is_scalar(x_504)) {
 x_523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_523 = x_504;
}
lean_ctor_set(x_523, 0, x_1);
lean_ctor_set(x_523, 1, x_522);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_501);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_505);
lean_dec(x_502);
lean_dec(x_454);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_525 = lean_ctor_get(x_506, 0);
lean_inc(x_525);
lean_dec(x_506);
if (lean_is_scalar(x_504)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_504;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_503);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_501);
return x_527;
}
}
}
else
{
uint8_t x_528; 
lean_dec(x_454);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_528 = !lean_is_exclusive(x_455);
if (x_528 == 0)
{
return x_455;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_455, 0);
x_530 = lean_ctor_get(x_455, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_455);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
block_587:
{
lean_object* x_534; 
lean_dec(x_533);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_534 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = lean_ctor_get(x_535, 0);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_array_get_size(x_7);
x_539 = lean_unsigned_to_nat(0u);
x_540 = lean_unsigned_to_nat(1u);
lean_inc(x_538);
x_541 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_538);
lean_ctor_set(x_541, 2, x_540);
x_542 = 0;
x_543 = lean_box(x_542);
lean_inc(x_7);
x_544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_544, 0, x_7);
lean_ctor_set(x_544, 1, x_543);
x_545 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_541);
lean_inc(x_6);
x_546 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_545, x_537, x_538, x_541, x_541, x_544, x_539, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_536);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_548, 1);
lean_inc(x_549);
x_550 = lean_unbox(x_549);
lean_dec(x_549);
if (x_550 == 0)
{
uint8_t x_551; 
lean_dec(x_548);
lean_dec(x_6);
x_551 = !lean_is_exclusive(x_546);
if (x_551 == 0)
{
lean_object* x_552; uint8_t x_553; 
x_552 = lean_ctor_get(x_546, 0);
lean_dec(x_552);
x_553 = !lean_is_exclusive(x_547);
if (x_553 == 0)
{
lean_object* x_554; 
x_554 = lean_ctor_get(x_547, 0);
lean_dec(x_554);
lean_ctor_set(x_547, 0, x_1);
return x_546;
}
else
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_547, 1);
lean_inc(x_555);
lean_dec(x_547);
x_556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_556, 0, x_1);
lean_ctor_set(x_556, 1, x_555);
lean_ctor_set(x_546, 0, x_556);
return x_546;
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_557 = lean_ctor_get(x_546, 1);
lean_inc(x_557);
lean_dec(x_546);
x_558 = lean_ctor_get(x_547, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_559 = x_547;
} else {
 lean_dec_ref(x_547);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_1);
lean_ctor_set(x_560, 1, x_558);
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_557);
return x_561;
}
}
else
{
uint8_t x_562; 
lean_dec(x_1);
x_562 = !lean_is_exclusive(x_546);
if (x_562 == 0)
{
lean_object* x_563; uint8_t x_564; 
x_563 = lean_ctor_get(x_546, 0);
lean_dec(x_563);
x_564 = !lean_is_exclusive(x_547);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_547, 0);
lean_dec(x_565);
x_566 = lean_ctor_get(x_548, 0);
lean_inc(x_566);
lean_dec(x_548);
x_567 = l_Lean_mkAppN(x_6, x_566);
lean_dec(x_566);
lean_ctor_set(x_547, 0, x_567);
return x_546;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_568 = lean_ctor_get(x_547, 1);
lean_inc(x_568);
lean_dec(x_547);
x_569 = lean_ctor_get(x_548, 0);
lean_inc(x_569);
lean_dec(x_548);
x_570 = l_Lean_mkAppN(x_6, x_569);
lean_dec(x_569);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_568);
lean_ctor_set(x_546, 0, x_571);
return x_546;
}
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_572 = lean_ctor_get(x_546, 1);
lean_inc(x_572);
lean_dec(x_546);
x_573 = lean_ctor_get(x_547, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_574 = x_547;
} else {
 lean_dec_ref(x_547);
 x_574 = lean_box(0);
}
x_575 = lean_ctor_get(x_548, 0);
lean_inc(x_575);
lean_dec(x_548);
x_576 = l_Lean_mkAppN(x_6, x_575);
lean_dec(x_575);
if (lean_is_scalar(x_574)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_574;
}
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_573);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_572);
return x_578;
}
}
}
else
{
uint8_t x_579; 
lean_dec(x_6);
lean_dec(x_1);
x_579 = !lean_is_exclusive(x_546);
if (x_579 == 0)
{
return x_546;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_546, 0);
x_581 = lean_ctor_get(x_546, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_546);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_534);
if (x_583 == 0)
{
return x_534;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_534, 0);
x_585 = lean_ctor_get(x_534, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_534);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
}
case 4:
{
lean_object* x_600; lean_object* x_679; lean_object* x_734; uint8_t x_735; 
lean_dec(x_8);
x_734 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_735 = l_Lean_Expr_isConstOf(x_6, x_734);
if (x_735 == 0)
{
lean_object* x_736; 
x_736 = lean_box(0);
x_679 = x_736;
goto block_733;
}
else
{
lean_object* x_737; lean_object* x_738; uint8_t x_739; 
x_737 = lean_array_get_size(x_7);
x_738 = lean_unsigned_to_nat(2u);
x_739 = lean_nat_dec_eq(x_737, x_738);
if (x_739 == 0)
{
lean_object* x_740; 
lean_dec(x_737);
x_740 = lean_box(0);
x_679 = x_740;
goto block_733;
}
else
{
lean_object* x_741; uint8_t x_742; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_741 = lean_unsigned_to_nat(0u);
x_742 = lean_nat_dec_lt(x_741, x_737);
lean_dec(x_737);
if (x_742 == 0)
{
lean_object* x_743; lean_object* x_744; 
x_743 = l_Lean_instInhabitedExpr;
x_744 = l_outOfBounds___rarg(x_743);
x_600 = x_744;
goto block_678;
}
else
{
lean_object* x_745; 
x_745 = lean_array_fget(x_7, x_741);
x_600 = x_745;
goto block_678;
}
}
}
block_678:
{
lean_object* x_601; 
lean_inc(x_600);
x_601 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_600, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_601) == 0)
{
uint8_t x_602; 
x_602 = !lean_is_exclusive(x_601);
if (x_602 == 0)
{
lean_object* x_603; uint8_t x_604; 
x_603 = lean_ctor_get(x_601, 0);
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_605 = lean_ctor_get(x_603, 0);
x_606 = lean_ctor_get(x_603, 1);
x_607 = lean_ctor_get(x_606, 2);
lean_inc(x_607);
lean_inc(x_607);
x_608 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_607, x_605);
if (lean_obj_tag(x_608) == 0)
{
size_t x_609; size_t x_610; uint8_t x_611; 
x_609 = lean_ptr_addr(x_600);
lean_dec(x_600);
x_610 = lean_ptr_addr(x_605);
x_611 = lean_usize_dec_eq(x_609, x_610);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_1);
x_612 = lean_unsigned_to_nat(0u);
lean_inc(x_605);
x_613 = lean_array_set(x_7, x_612, x_605);
x_614 = l_Lean_mkAppN(x_6, x_613);
lean_dec(x_613);
x_615 = lean_ctor_get(x_606, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_606, 1);
lean_inc(x_616);
lean_dec(x_606);
lean_inc(x_614);
x_617 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_607, x_605, x_614);
x_618 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_618, 0, x_615);
lean_ctor_set(x_618, 1, x_616);
lean_ctor_set(x_618, 2, x_617);
lean_ctor_set(x_603, 1, x_618);
lean_ctor_set(x_603, 0, x_614);
return x_601;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_7);
lean_dec(x_6);
x_619 = lean_ctor_get(x_606, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_606, 1);
lean_inc(x_620);
lean_dec(x_606);
lean_inc(x_1);
x_621 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_607, x_605, x_1);
x_622 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_622, 0, x_619);
lean_ctor_set(x_622, 1, x_620);
lean_ctor_set(x_622, 2, x_621);
lean_ctor_set(x_603, 1, x_622);
lean_ctor_set(x_603, 0, x_1);
return x_601;
}
}
else
{
lean_object* x_623; 
lean_dec(x_607);
lean_dec(x_605);
lean_dec(x_600);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_623 = lean_ctor_get(x_608, 0);
lean_inc(x_623);
lean_dec(x_608);
lean_ctor_set(x_603, 0, x_623);
return x_601;
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_624 = lean_ctor_get(x_603, 0);
x_625 = lean_ctor_get(x_603, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_603);
x_626 = lean_ctor_get(x_625, 2);
lean_inc(x_626);
lean_inc(x_626);
x_627 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_626, x_624);
if (lean_obj_tag(x_627) == 0)
{
size_t x_628; size_t x_629; uint8_t x_630; 
x_628 = lean_ptr_addr(x_600);
lean_dec(x_600);
x_629 = lean_ptr_addr(x_624);
x_630 = lean_usize_dec_eq(x_628, x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_1);
x_631 = lean_unsigned_to_nat(0u);
lean_inc(x_624);
x_632 = lean_array_set(x_7, x_631, x_624);
x_633 = l_Lean_mkAppN(x_6, x_632);
lean_dec(x_632);
x_634 = lean_ctor_get(x_625, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_625, 1);
lean_inc(x_635);
lean_dec(x_625);
lean_inc(x_633);
x_636 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_626, x_624, x_633);
x_637 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_637, 0, x_634);
lean_ctor_set(x_637, 1, x_635);
lean_ctor_set(x_637, 2, x_636);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_633);
lean_ctor_set(x_638, 1, x_637);
lean_ctor_set(x_601, 0, x_638);
return x_601;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_7);
lean_dec(x_6);
x_639 = lean_ctor_get(x_625, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_625, 1);
lean_inc(x_640);
lean_dec(x_625);
lean_inc(x_1);
x_641 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_626, x_624, x_1);
x_642 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
lean_ctor_set(x_642, 2, x_641);
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_1);
lean_ctor_set(x_643, 1, x_642);
lean_ctor_set(x_601, 0, x_643);
return x_601;
}
}
else
{
lean_object* x_644; lean_object* x_645; 
lean_dec(x_626);
lean_dec(x_624);
lean_dec(x_600);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_644 = lean_ctor_get(x_627, 0);
lean_inc(x_644);
lean_dec(x_627);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_625);
lean_ctor_set(x_601, 0, x_645);
return x_601;
}
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_646 = lean_ctor_get(x_601, 0);
x_647 = lean_ctor_get(x_601, 1);
lean_inc(x_647);
lean_inc(x_646);
lean_dec(x_601);
x_648 = lean_ctor_get(x_646, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_646, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_650 = x_646;
} else {
 lean_dec_ref(x_646);
 x_650 = lean_box(0);
}
x_651 = lean_ctor_get(x_649, 2);
lean_inc(x_651);
lean_inc(x_651);
x_652 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_651, x_648);
if (lean_obj_tag(x_652) == 0)
{
size_t x_653; size_t x_654; uint8_t x_655; 
x_653 = lean_ptr_addr(x_600);
lean_dec(x_600);
x_654 = lean_ptr_addr(x_648);
x_655 = lean_usize_dec_eq(x_653, x_654);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_1);
x_656 = lean_unsigned_to_nat(0u);
lean_inc(x_648);
x_657 = lean_array_set(x_7, x_656, x_648);
x_658 = l_Lean_mkAppN(x_6, x_657);
lean_dec(x_657);
x_659 = lean_ctor_get(x_649, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_649, 1);
lean_inc(x_660);
lean_dec(x_649);
lean_inc(x_658);
x_661 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_651, x_648, x_658);
x_662 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_662, 0, x_659);
lean_ctor_set(x_662, 1, x_660);
lean_ctor_set(x_662, 2, x_661);
if (lean_is_scalar(x_650)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_650;
}
lean_ctor_set(x_663, 0, x_658);
lean_ctor_set(x_663, 1, x_662);
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_647);
return x_664;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_7);
lean_dec(x_6);
x_665 = lean_ctor_get(x_649, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_649, 1);
lean_inc(x_666);
lean_dec(x_649);
lean_inc(x_1);
x_667 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_651, x_648, x_1);
x_668 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
lean_ctor_set(x_668, 2, x_667);
if (lean_is_scalar(x_650)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_650;
}
lean_ctor_set(x_669, 0, x_1);
lean_ctor_set(x_669, 1, x_668);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_647);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_651);
lean_dec(x_648);
lean_dec(x_600);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_671 = lean_ctor_get(x_652, 0);
lean_inc(x_671);
lean_dec(x_652);
if (lean_is_scalar(x_650)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_650;
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_649);
x_673 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_647);
return x_673;
}
}
}
else
{
uint8_t x_674; 
lean_dec(x_600);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_674 = !lean_is_exclusive(x_601);
if (x_674 == 0)
{
return x_601;
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_601, 0);
x_676 = lean_ctor_get(x_601, 1);
lean_inc(x_676);
lean_inc(x_675);
lean_dec(x_601);
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_675);
lean_ctor_set(x_677, 1, x_676);
return x_677;
}
}
}
block_733:
{
lean_object* x_680; 
lean_dec(x_679);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_680 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = lean_ctor_get(x_681, 0);
lean_inc(x_683);
lean_dec(x_681);
x_684 = lean_array_get_size(x_7);
x_685 = lean_unsigned_to_nat(0u);
x_686 = lean_unsigned_to_nat(1u);
lean_inc(x_684);
x_687 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_684);
lean_ctor_set(x_687, 2, x_686);
x_688 = 0;
x_689 = lean_box(x_688);
lean_inc(x_7);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_7);
lean_ctor_set(x_690, 1, x_689);
x_691 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_687);
lean_inc(x_6);
x_692 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_691, x_683, x_684, x_687, x_687, x_690, x_685, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_682);
if (lean_obj_tag(x_692) == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; 
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_694, 1);
lean_inc(x_695);
x_696 = lean_unbox(x_695);
lean_dec(x_695);
if (x_696 == 0)
{
uint8_t x_697; 
lean_dec(x_694);
lean_dec(x_6);
x_697 = !lean_is_exclusive(x_692);
if (x_697 == 0)
{
lean_object* x_698; uint8_t x_699; 
x_698 = lean_ctor_get(x_692, 0);
lean_dec(x_698);
x_699 = !lean_is_exclusive(x_693);
if (x_699 == 0)
{
lean_object* x_700; 
x_700 = lean_ctor_get(x_693, 0);
lean_dec(x_700);
lean_ctor_set(x_693, 0, x_1);
return x_692;
}
else
{
lean_object* x_701; lean_object* x_702; 
x_701 = lean_ctor_get(x_693, 1);
lean_inc(x_701);
lean_dec(x_693);
x_702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_702, 0, x_1);
lean_ctor_set(x_702, 1, x_701);
lean_ctor_set(x_692, 0, x_702);
return x_692;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_703 = lean_ctor_get(x_692, 1);
lean_inc(x_703);
lean_dec(x_692);
x_704 = lean_ctor_get(x_693, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_705 = x_693;
} else {
 lean_dec_ref(x_693);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_1);
lean_ctor_set(x_706, 1, x_704);
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_703);
return x_707;
}
}
else
{
uint8_t x_708; 
lean_dec(x_1);
x_708 = !lean_is_exclusive(x_692);
if (x_708 == 0)
{
lean_object* x_709; uint8_t x_710; 
x_709 = lean_ctor_get(x_692, 0);
lean_dec(x_709);
x_710 = !lean_is_exclusive(x_693);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_693, 0);
lean_dec(x_711);
x_712 = lean_ctor_get(x_694, 0);
lean_inc(x_712);
lean_dec(x_694);
x_713 = l_Lean_mkAppN(x_6, x_712);
lean_dec(x_712);
lean_ctor_set(x_693, 0, x_713);
return x_692;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_714 = lean_ctor_get(x_693, 1);
lean_inc(x_714);
lean_dec(x_693);
x_715 = lean_ctor_get(x_694, 0);
lean_inc(x_715);
lean_dec(x_694);
x_716 = l_Lean_mkAppN(x_6, x_715);
lean_dec(x_715);
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_714);
lean_ctor_set(x_692, 0, x_717);
return x_692;
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_718 = lean_ctor_get(x_692, 1);
lean_inc(x_718);
lean_dec(x_692);
x_719 = lean_ctor_get(x_693, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_720 = x_693;
} else {
 lean_dec_ref(x_693);
 x_720 = lean_box(0);
}
x_721 = lean_ctor_get(x_694, 0);
lean_inc(x_721);
lean_dec(x_694);
x_722 = l_Lean_mkAppN(x_6, x_721);
lean_dec(x_721);
if (lean_is_scalar(x_720)) {
 x_723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_723 = x_720;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_719);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_718);
return x_724;
}
}
}
else
{
uint8_t x_725; 
lean_dec(x_6);
lean_dec(x_1);
x_725 = !lean_is_exclusive(x_692);
if (x_725 == 0)
{
return x_692;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_692, 0);
x_727 = lean_ctor_get(x_692, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_692);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set(x_728, 1, x_727);
return x_728;
}
}
}
else
{
uint8_t x_729; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_729 = !lean_is_exclusive(x_680);
if (x_729 == 0)
{
return x_680;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_680, 0);
x_731 = lean_ctor_get(x_680, 1);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_680);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
}
}
case 5:
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_746 = lean_ctor_get(x_6, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_6, 1);
lean_inc(x_747);
lean_dec(x_6);
x_748 = lean_array_set(x_7, x_8, x_747);
x_749 = lean_unsigned_to_nat(1u);
x_750 = lean_nat_sub(x_8, x_749);
lean_dec(x_8);
x_6 = x_746;
x_7 = x_748;
x_8 = x_750;
goto _start;
}
case 6:
{
lean_object* x_752; lean_object* x_831; lean_object* x_886; uint8_t x_887; 
lean_dec(x_8);
x_886 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_887 = l_Lean_Expr_isConstOf(x_6, x_886);
if (x_887 == 0)
{
lean_object* x_888; 
x_888 = lean_box(0);
x_831 = x_888;
goto block_885;
}
else
{
lean_object* x_889; lean_object* x_890; uint8_t x_891; 
x_889 = lean_array_get_size(x_7);
x_890 = lean_unsigned_to_nat(2u);
x_891 = lean_nat_dec_eq(x_889, x_890);
if (x_891 == 0)
{
lean_object* x_892; 
lean_dec(x_889);
x_892 = lean_box(0);
x_831 = x_892;
goto block_885;
}
else
{
lean_object* x_893; uint8_t x_894; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_893 = lean_unsigned_to_nat(0u);
x_894 = lean_nat_dec_lt(x_893, x_889);
lean_dec(x_889);
if (x_894 == 0)
{
lean_object* x_895; lean_object* x_896; 
x_895 = l_Lean_instInhabitedExpr;
x_896 = l_outOfBounds___rarg(x_895);
x_752 = x_896;
goto block_830;
}
else
{
lean_object* x_897; 
x_897 = lean_array_fget(x_7, x_893);
x_752 = x_897;
goto block_830;
}
}
}
block_830:
{
lean_object* x_753; 
lean_inc(x_752);
x_753 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_752, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_753) == 0)
{
uint8_t x_754; 
x_754 = !lean_is_exclusive(x_753);
if (x_754 == 0)
{
lean_object* x_755; uint8_t x_756; 
x_755 = lean_ctor_get(x_753, 0);
x_756 = !lean_is_exclusive(x_755);
if (x_756 == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_757 = lean_ctor_get(x_755, 0);
x_758 = lean_ctor_get(x_755, 1);
x_759 = lean_ctor_get(x_758, 2);
lean_inc(x_759);
lean_inc(x_759);
x_760 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_759, x_757);
if (lean_obj_tag(x_760) == 0)
{
size_t x_761; size_t x_762; uint8_t x_763; 
x_761 = lean_ptr_addr(x_752);
lean_dec(x_752);
x_762 = lean_ptr_addr(x_757);
x_763 = lean_usize_dec_eq(x_761, x_762);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_1);
x_764 = lean_unsigned_to_nat(0u);
lean_inc(x_757);
x_765 = lean_array_set(x_7, x_764, x_757);
x_766 = l_Lean_mkAppN(x_6, x_765);
lean_dec(x_765);
x_767 = lean_ctor_get(x_758, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_758, 1);
lean_inc(x_768);
lean_dec(x_758);
lean_inc(x_766);
x_769 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_759, x_757, x_766);
x_770 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_770, 0, x_767);
lean_ctor_set(x_770, 1, x_768);
lean_ctor_set(x_770, 2, x_769);
lean_ctor_set(x_755, 1, x_770);
lean_ctor_set(x_755, 0, x_766);
return x_753;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_7);
lean_dec(x_6);
x_771 = lean_ctor_get(x_758, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_758, 1);
lean_inc(x_772);
lean_dec(x_758);
lean_inc(x_1);
x_773 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_759, x_757, x_1);
x_774 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_774, 0, x_771);
lean_ctor_set(x_774, 1, x_772);
lean_ctor_set(x_774, 2, x_773);
lean_ctor_set(x_755, 1, x_774);
lean_ctor_set(x_755, 0, x_1);
return x_753;
}
}
else
{
lean_object* x_775; 
lean_dec(x_759);
lean_dec(x_757);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_775 = lean_ctor_get(x_760, 0);
lean_inc(x_775);
lean_dec(x_760);
lean_ctor_set(x_755, 0, x_775);
return x_753;
}
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_776 = lean_ctor_get(x_755, 0);
x_777 = lean_ctor_get(x_755, 1);
lean_inc(x_777);
lean_inc(x_776);
lean_dec(x_755);
x_778 = lean_ctor_get(x_777, 2);
lean_inc(x_778);
lean_inc(x_778);
x_779 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_778, x_776);
if (lean_obj_tag(x_779) == 0)
{
size_t x_780; size_t x_781; uint8_t x_782; 
x_780 = lean_ptr_addr(x_752);
lean_dec(x_752);
x_781 = lean_ptr_addr(x_776);
x_782 = lean_usize_dec_eq(x_780, x_781);
if (x_782 == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_1);
x_783 = lean_unsigned_to_nat(0u);
lean_inc(x_776);
x_784 = lean_array_set(x_7, x_783, x_776);
x_785 = l_Lean_mkAppN(x_6, x_784);
lean_dec(x_784);
x_786 = lean_ctor_get(x_777, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_777, 1);
lean_inc(x_787);
lean_dec(x_777);
lean_inc(x_785);
x_788 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_778, x_776, x_785);
x_789 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_789, 0, x_786);
lean_ctor_set(x_789, 1, x_787);
lean_ctor_set(x_789, 2, x_788);
x_790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_790, 0, x_785);
lean_ctor_set(x_790, 1, x_789);
lean_ctor_set(x_753, 0, x_790);
return x_753;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_7);
lean_dec(x_6);
x_791 = lean_ctor_get(x_777, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_777, 1);
lean_inc(x_792);
lean_dec(x_777);
lean_inc(x_1);
x_793 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_778, x_776, x_1);
x_794 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
lean_ctor_set(x_794, 2, x_793);
x_795 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_795, 0, x_1);
lean_ctor_set(x_795, 1, x_794);
lean_ctor_set(x_753, 0, x_795);
return x_753;
}
}
else
{
lean_object* x_796; lean_object* x_797; 
lean_dec(x_778);
lean_dec(x_776);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_796 = lean_ctor_get(x_779, 0);
lean_inc(x_796);
lean_dec(x_779);
x_797 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_777);
lean_ctor_set(x_753, 0, x_797);
return x_753;
}
}
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_798 = lean_ctor_get(x_753, 0);
x_799 = lean_ctor_get(x_753, 1);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_753);
x_800 = lean_ctor_get(x_798, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_798, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 x_802 = x_798;
} else {
 lean_dec_ref(x_798);
 x_802 = lean_box(0);
}
x_803 = lean_ctor_get(x_801, 2);
lean_inc(x_803);
lean_inc(x_803);
x_804 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_803, x_800);
if (lean_obj_tag(x_804) == 0)
{
size_t x_805; size_t x_806; uint8_t x_807; 
x_805 = lean_ptr_addr(x_752);
lean_dec(x_752);
x_806 = lean_ptr_addr(x_800);
x_807 = lean_usize_dec_eq(x_805, x_806);
if (x_807 == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_1);
x_808 = lean_unsigned_to_nat(0u);
lean_inc(x_800);
x_809 = lean_array_set(x_7, x_808, x_800);
x_810 = l_Lean_mkAppN(x_6, x_809);
lean_dec(x_809);
x_811 = lean_ctor_get(x_801, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_801, 1);
lean_inc(x_812);
lean_dec(x_801);
lean_inc(x_810);
x_813 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_803, x_800, x_810);
x_814 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_812);
lean_ctor_set(x_814, 2, x_813);
if (lean_is_scalar(x_802)) {
 x_815 = lean_alloc_ctor(0, 2, 0);
} else {
 x_815 = x_802;
}
lean_ctor_set(x_815, 0, x_810);
lean_ctor_set(x_815, 1, x_814);
x_816 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_816, 0, x_815);
lean_ctor_set(x_816, 1, x_799);
return x_816;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
lean_dec(x_7);
lean_dec(x_6);
x_817 = lean_ctor_get(x_801, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_801, 1);
lean_inc(x_818);
lean_dec(x_801);
lean_inc(x_1);
x_819 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_803, x_800, x_1);
x_820 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_820, 0, x_817);
lean_ctor_set(x_820, 1, x_818);
lean_ctor_set(x_820, 2, x_819);
if (lean_is_scalar(x_802)) {
 x_821 = lean_alloc_ctor(0, 2, 0);
} else {
 x_821 = x_802;
}
lean_ctor_set(x_821, 0, x_1);
lean_ctor_set(x_821, 1, x_820);
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_799);
return x_822;
}
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
lean_dec(x_803);
lean_dec(x_800);
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_823 = lean_ctor_get(x_804, 0);
lean_inc(x_823);
lean_dec(x_804);
if (lean_is_scalar(x_802)) {
 x_824 = lean_alloc_ctor(0, 2, 0);
} else {
 x_824 = x_802;
}
lean_ctor_set(x_824, 0, x_823);
lean_ctor_set(x_824, 1, x_801);
x_825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_799);
return x_825;
}
}
}
else
{
uint8_t x_826; 
lean_dec(x_752);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_826 = !lean_is_exclusive(x_753);
if (x_826 == 0)
{
return x_753;
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_827 = lean_ctor_get(x_753, 0);
x_828 = lean_ctor_get(x_753, 1);
lean_inc(x_828);
lean_inc(x_827);
lean_dec(x_753);
x_829 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_829, 0, x_827);
lean_ctor_set(x_829, 1, x_828);
return x_829;
}
}
}
block_885:
{
lean_object* x_832; 
lean_dec(x_831);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_832 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; uint8_t x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = lean_ctor_get(x_833, 0);
lean_inc(x_835);
lean_dec(x_833);
x_836 = lean_array_get_size(x_7);
x_837 = lean_unsigned_to_nat(0u);
x_838 = lean_unsigned_to_nat(1u);
lean_inc(x_836);
x_839 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_839, 0, x_837);
lean_ctor_set(x_839, 1, x_836);
lean_ctor_set(x_839, 2, x_838);
x_840 = 0;
x_841 = lean_box(x_840);
lean_inc(x_7);
x_842 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_842, 0, x_7);
lean_ctor_set(x_842, 1, x_841);
x_843 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_839);
lean_inc(x_6);
x_844 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_843, x_835, x_836, x_839, x_839, x_842, x_837, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_834);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; 
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_846, 1);
lean_inc(x_847);
x_848 = lean_unbox(x_847);
lean_dec(x_847);
if (x_848 == 0)
{
uint8_t x_849; 
lean_dec(x_846);
lean_dec(x_6);
x_849 = !lean_is_exclusive(x_844);
if (x_849 == 0)
{
lean_object* x_850; uint8_t x_851; 
x_850 = lean_ctor_get(x_844, 0);
lean_dec(x_850);
x_851 = !lean_is_exclusive(x_845);
if (x_851 == 0)
{
lean_object* x_852; 
x_852 = lean_ctor_get(x_845, 0);
lean_dec(x_852);
lean_ctor_set(x_845, 0, x_1);
return x_844;
}
else
{
lean_object* x_853; lean_object* x_854; 
x_853 = lean_ctor_get(x_845, 1);
lean_inc(x_853);
lean_dec(x_845);
x_854 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_854, 0, x_1);
lean_ctor_set(x_854, 1, x_853);
lean_ctor_set(x_844, 0, x_854);
return x_844;
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_855 = lean_ctor_get(x_844, 1);
lean_inc(x_855);
lean_dec(x_844);
x_856 = lean_ctor_get(x_845, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_857 = x_845;
} else {
 lean_dec_ref(x_845);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_1);
lean_ctor_set(x_858, 1, x_856);
x_859 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_855);
return x_859;
}
}
else
{
uint8_t x_860; 
lean_dec(x_1);
x_860 = !lean_is_exclusive(x_844);
if (x_860 == 0)
{
lean_object* x_861; uint8_t x_862; 
x_861 = lean_ctor_get(x_844, 0);
lean_dec(x_861);
x_862 = !lean_is_exclusive(x_845);
if (x_862 == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_863 = lean_ctor_get(x_845, 0);
lean_dec(x_863);
x_864 = lean_ctor_get(x_846, 0);
lean_inc(x_864);
lean_dec(x_846);
x_865 = l_Lean_mkAppN(x_6, x_864);
lean_dec(x_864);
lean_ctor_set(x_845, 0, x_865);
return x_844;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_866 = lean_ctor_get(x_845, 1);
lean_inc(x_866);
lean_dec(x_845);
x_867 = lean_ctor_get(x_846, 0);
lean_inc(x_867);
lean_dec(x_846);
x_868 = l_Lean_mkAppN(x_6, x_867);
lean_dec(x_867);
x_869 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_869, 0, x_868);
lean_ctor_set(x_869, 1, x_866);
lean_ctor_set(x_844, 0, x_869);
return x_844;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_870 = lean_ctor_get(x_844, 1);
lean_inc(x_870);
lean_dec(x_844);
x_871 = lean_ctor_get(x_845, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_872 = x_845;
} else {
 lean_dec_ref(x_845);
 x_872 = lean_box(0);
}
x_873 = lean_ctor_get(x_846, 0);
lean_inc(x_873);
lean_dec(x_846);
x_874 = l_Lean_mkAppN(x_6, x_873);
lean_dec(x_873);
if (lean_is_scalar(x_872)) {
 x_875 = lean_alloc_ctor(0, 2, 0);
} else {
 x_875 = x_872;
}
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_871);
x_876 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_876, 0, x_875);
lean_ctor_set(x_876, 1, x_870);
return x_876;
}
}
}
else
{
uint8_t x_877; 
lean_dec(x_6);
lean_dec(x_1);
x_877 = !lean_is_exclusive(x_844);
if (x_877 == 0)
{
return x_844;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_878 = lean_ctor_get(x_844, 0);
x_879 = lean_ctor_get(x_844, 1);
lean_inc(x_879);
lean_inc(x_878);
lean_dec(x_844);
x_880 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_880, 0, x_878);
lean_ctor_set(x_880, 1, x_879);
return x_880;
}
}
}
else
{
uint8_t x_881; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_881 = !lean_is_exclusive(x_832);
if (x_881 == 0)
{
return x_832;
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_832, 0);
x_883 = lean_ctor_get(x_832, 1);
lean_inc(x_883);
lean_inc(x_882);
lean_dec(x_832);
x_884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_884, 0, x_882);
lean_ctor_set(x_884, 1, x_883);
return x_884;
}
}
}
}
case 7:
{
lean_object* x_898; lean_object* x_977; lean_object* x_1032; uint8_t x_1033; 
lean_dec(x_8);
x_1032 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1033 = l_Lean_Expr_isConstOf(x_6, x_1032);
if (x_1033 == 0)
{
lean_object* x_1034; 
x_1034 = lean_box(0);
x_977 = x_1034;
goto block_1031;
}
else
{
lean_object* x_1035; lean_object* x_1036; uint8_t x_1037; 
x_1035 = lean_array_get_size(x_7);
x_1036 = lean_unsigned_to_nat(2u);
x_1037 = lean_nat_dec_eq(x_1035, x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; 
lean_dec(x_1035);
x_1038 = lean_box(0);
x_977 = x_1038;
goto block_1031;
}
else
{
lean_object* x_1039; uint8_t x_1040; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1039 = lean_unsigned_to_nat(0u);
x_1040 = lean_nat_dec_lt(x_1039, x_1035);
lean_dec(x_1035);
if (x_1040 == 0)
{
lean_object* x_1041; lean_object* x_1042; 
x_1041 = l_Lean_instInhabitedExpr;
x_1042 = l_outOfBounds___rarg(x_1041);
x_898 = x_1042;
goto block_976;
}
else
{
lean_object* x_1043; 
x_1043 = lean_array_fget(x_7, x_1039);
x_898 = x_1043;
goto block_976;
}
}
}
block_976:
{
lean_object* x_899; 
lean_inc(x_898);
x_899 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_898, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_899) == 0)
{
uint8_t x_900; 
x_900 = !lean_is_exclusive(x_899);
if (x_900 == 0)
{
lean_object* x_901; uint8_t x_902; 
x_901 = lean_ctor_get(x_899, 0);
x_902 = !lean_is_exclusive(x_901);
if (x_902 == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_903 = lean_ctor_get(x_901, 0);
x_904 = lean_ctor_get(x_901, 1);
x_905 = lean_ctor_get(x_904, 2);
lean_inc(x_905);
lean_inc(x_905);
x_906 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_905, x_903);
if (lean_obj_tag(x_906) == 0)
{
size_t x_907; size_t x_908; uint8_t x_909; 
x_907 = lean_ptr_addr(x_898);
lean_dec(x_898);
x_908 = lean_ptr_addr(x_903);
x_909 = lean_usize_dec_eq(x_907, x_908);
if (x_909 == 0)
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_1);
x_910 = lean_unsigned_to_nat(0u);
lean_inc(x_903);
x_911 = lean_array_set(x_7, x_910, x_903);
x_912 = l_Lean_mkAppN(x_6, x_911);
lean_dec(x_911);
x_913 = lean_ctor_get(x_904, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_904, 1);
lean_inc(x_914);
lean_dec(x_904);
lean_inc(x_912);
x_915 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_905, x_903, x_912);
x_916 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_916, 0, x_913);
lean_ctor_set(x_916, 1, x_914);
lean_ctor_set(x_916, 2, x_915);
lean_ctor_set(x_901, 1, x_916);
lean_ctor_set(x_901, 0, x_912);
return x_899;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
lean_dec(x_7);
lean_dec(x_6);
x_917 = lean_ctor_get(x_904, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_904, 1);
lean_inc(x_918);
lean_dec(x_904);
lean_inc(x_1);
x_919 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_905, x_903, x_1);
x_920 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_920, 0, x_917);
lean_ctor_set(x_920, 1, x_918);
lean_ctor_set(x_920, 2, x_919);
lean_ctor_set(x_901, 1, x_920);
lean_ctor_set(x_901, 0, x_1);
return x_899;
}
}
else
{
lean_object* x_921; 
lean_dec(x_905);
lean_dec(x_903);
lean_dec(x_898);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_921 = lean_ctor_get(x_906, 0);
lean_inc(x_921);
lean_dec(x_906);
lean_ctor_set(x_901, 0, x_921);
return x_899;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_922 = lean_ctor_get(x_901, 0);
x_923 = lean_ctor_get(x_901, 1);
lean_inc(x_923);
lean_inc(x_922);
lean_dec(x_901);
x_924 = lean_ctor_get(x_923, 2);
lean_inc(x_924);
lean_inc(x_924);
x_925 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_924, x_922);
if (lean_obj_tag(x_925) == 0)
{
size_t x_926; size_t x_927; uint8_t x_928; 
x_926 = lean_ptr_addr(x_898);
lean_dec(x_898);
x_927 = lean_ptr_addr(x_922);
x_928 = lean_usize_dec_eq(x_926, x_927);
if (x_928 == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
lean_dec(x_1);
x_929 = lean_unsigned_to_nat(0u);
lean_inc(x_922);
x_930 = lean_array_set(x_7, x_929, x_922);
x_931 = l_Lean_mkAppN(x_6, x_930);
lean_dec(x_930);
x_932 = lean_ctor_get(x_923, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_923, 1);
lean_inc(x_933);
lean_dec(x_923);
lean_inc(x_931);
x_934 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_924, x_922, x_931);
x_935 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_935, 0, x_932);
lean_ctor_set(x_935, 1, x_933);
lean_ctor_set(x_935, 2, x_934);
x_936 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_936, 0, x_931);
lean_ctor_set(x_936, 1, x_935);
lean_ctor_set(x_899, 0, x_936);
return x_899;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_7);
lean_dec(x_6);
x_937 = lean_ctor_get(x_923, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_923, 1);
lean_inc(x_938);
lean_dec(x_923);
lean_inc(x_1);
x_939 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_924, x_922, x_1);
x_940 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_940, 0, x_937);
lean_ctor_set(x_940, 1, x_938);
lean_ctor_set(x_940, 2, x_939);
x_941 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_941, 0, x_1);
lean_ctor_set(x_941, 1, x_940);
lean_ctor_set(x_899, 0, x_941);
return x_899;
}
}
else
{
lean_object* x_942; lean_object* x_943; 
lean_dec(x_924);
lean_dec(x_922);
lean_dec(x_898);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_942 = lean_ctor_get(x_925, 0);
lean_inc(x_942);
lean_dec(x_925);
x_943 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_943, 0, x_942);
lean_ctor_set(x_943, 1, x_923);
lean_ctor_set(x_899, 0, x_943);
return x_899;
}
}
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_944 = lean_ctor_get(x_899, 0);
x_945 = lean_ctor_get(x_899, 1);
lean_inc(x_945);
lean_inc(x_944);
lean_dec(x_899);
x_946 = lean_ctor_get(x_944, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_944, 1);
lean_inc(x_947);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 lean_ctor_release(x_944, 1);
 x_948 = x_944;
} else {
 lean_dec_ref(x_944);
 x_948 = lean_box(0);
}
x_949 = lean_ctor_get(x_947, 2);
lean_inc(x_949);
lean_inc(x_949);
x_950 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_949, x_946);
if (lean_obj_tag(x_950) == 0)
{
size_t x_951; size_t x_952; uint8_t x_953; 
x_951 = lean_ptr_addr(x_898);
lean_dec(x_898);
x_952 = lean_ptr_addr(x_946);
x_953 = lean_usize_dec_eq(x_951, x_952);
if (x_953 == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_1);
x_954 = lean_unsigned_to_nat(0u);
lean_inc(x_946);
x_955 = lean_array_set(x_7, x_954, x_946);
x_956 = l_Lean_mkAppN(x_6, x_955);
lean_dec(x_955);
x_957 = lean_ctor_get(x_947, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_947, 1);
lean_inc(x_958);
lean_dec(x_947);
lean_inc(x_956);
x_959 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_949, x_946, x_956);
x_960 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_960, 0, x_957);
lean_ctor_set(x_960, 1, x_958);
lean_ctor_set(x_960, 2, x_959);
if (lean_is_scalar(x_948)) {
 x_961 = lean_alloc_ctor(0, 2, 0);
} else {
 x_961 = x_948;
}
lean_ctor_set(x_961, 0, x_956);
lean_ctor_set(x_961, 1, x_960);
x_962 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_962, 0, x_961);
lean_ctor_set(x_962, 1, x_945);
return x_962;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_7);
lean_dec(x_6);
x_963 = lean_ctor_get(x_947, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_947, 1);
lean_inc(x_964);
lean_dec(x_947);
lean_inc(x_1);
x_965 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_949, x_946, x_1);
x_966 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_964);
lean_ctor_set(x_966, 2, x_965);
if (lean_is_scalar(x_948)) {
 x_967 = lean_alloc_ctor(0, 2, 0);
} else {
 x_967 = x_948;
}
lean_ctor_set(x_967, 0, x_1);
lean_ctor_set(x_967, 1, x_966);
x_968 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_968, 0, x_967);
lean_ctor_set(x_968, 1, x_945);
return x_968;
}
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_949);
lean_dec(x_946);
lean_dec(x_898);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_969 = lean_ctor_get(x_950, 0);
lean_inc(x_969);
lean_dec(x_950);
if (lean_is_scalar(x_948)) {
 x_970 = lean_alloc_ctor(0, 2, 0);
} else {
 x_970 = x_948;
}
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_947);
x_971 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_971, 0, x_970);
lean_ctor_set(x_971, 1, x_945);
return x_971;
}
}
}
else
{
uint8_t x_972; 
lean_dec(x_898);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_972 = !lean_is_exclusive(x_899);
if (x_972 == 0)
{
return x_899;
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_973 = lean_ctor_get(x_899, 0);
x_974 = lean_ctor_get(x_899, 1);
lean_inc(x_974);
lean_inc(x_973);
lean_dec(x_899);
x_975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_975, 0, x_973);
lean_ctor_set(x_975, 1, x_974);
return x_975;
}
}
}
block_1031:
{
lean_object* x_978; 
lean_dec(x_977);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_978 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; uint8_t x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec(x_978);
x_981 = lean_ctor_get(x_979, 0);
lean_inc(x_981);
lean_dec(x_979);
x_982 = lean_array_get_size(x_7);
x_983 = lean_unsigned_to_nat(0u);
x_984 = lean_unsigned_to_nat(1u);
lean_inc(x_982);
x_985 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_985, 0, x_983);
lean_ctor_set(x_985, 1, x_982);
lean_ctor_set(x_985, 2, x_984);
x_986 = 0;
x_987 = lean_box(x_986);
lean_inc(x_7);
x_988 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_988, 0, x_7);
lean_ctor_set(x_988, 1, x_987);
x_989 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_985);
lean_inc(x_6);
x_990 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_989, x_981, x_982, x_985, x_985, x_988, x_983, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_980);
if (lean_obj_tag(x_990) == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; uint8_t x_994; 
x_991 = lean_ctor_get(x_990, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_992, 1);
lean_inc(x_993);
x_994 = lean_unbox(x_993);
lean_dec(x_993);
if (x_994 == 0)
{
uint8_t x_995; 
lean_dec(x_992);
lean_dec(x_6);
x_995 = !lean_is_exclusive(x_990);
if (x_995 == 0)
{
lean_object* x_996; uint8_t x_997; 
x_996 = lean_ctor_get(x_990, 0);
lean_dec(x_996);
x_997 = !lean_is_exclusive(x_991);
if (x_997 == 0)
{
lean_object* x_998; 
x_998 = lean_ctor_get(x_991, 0);
lean_dec(x_998);
lean_ctor_set(x_991, 0, x_1);
return x_990;
}
else
{
lean_object* x_999; lean_object* x_1000; 
x_999 = lean_ctor_get(x_991, 1);
lean_inc(x_999);
lean_dec(x_991);
x_1000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1000, 0, x_1);
lean_ctor_set(x_1000, 1, x_999);
lean_ctor_set(x_990, 0, x_1000);
return x_990;
}
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_1001 = lean_ctor_get(x_990, 1);
lean_inc(x_1001);
lean_dec(x_990);
x_1002 = lean_ctor_get(x_991, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1003 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1003 = lean_box(0);
}
if (lean_is_scalar(x_1003)) {
 x_1004 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1004 = x_1003;
}
lean_ctor_set(x_1004, 0, x_1);
lean_ctor_set(x_1004, 1, x_1002);
x_1005 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_1001);
return x_1005;
}
}
else
{
uint8_t x_1006; 
lean_dec(x_1);
x_1006 = !lean_is_exclusive(x_990);
if (x_1006 == 0)
{
lean_object* x_1007; uint8_t x_1008; 
x_1007 = lean_ctor_get(x_990, 0);
lean_dec(x_1007);
x_1008 = !lean_is_exclusive(x_991);
if (x_1008 == 0)
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1009 = lean_ctor_get(x_991, 0);
lean_dec(x_1009);
x_1010 = lean_ctor_get(x_992, 0);
lean_inc(x_1010);
lean_dec(x_992);
x_1011 = l_Lean_mkAppN(x_6, x_1010);
lean_dec(x_1010);
lean_ctor_set(x_991, 0, x_1011);
return x_990;
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1012 = lean_ctor_get(x_991, 1);
lean_inc(x_1012);
lean_dec(x_991);
x_1013 = lean_ctor_get(x_992, 0);
lean_inc(x_1013);
lean_dec(x_992);
x_1014 = l_Lean_mkAppN(x_6, x_1013);
lean_dec(x_1013);
x_1015 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1015, 0, x_1014);
lean_ctor_set(x_1015, 1, x_1012);
lean_ctor_set(x_990, 0, x_1015);
return x_990;
}
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1016 = lean_ctor_get(x_990, 1);
lean_inc(x_1016);
lean_dec(x_990);
x_1017 = lean_ctor_get(x_991, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1018 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1018 = lean_box(0);
}
x_1019 = lean_ctor_get(x_992, 0);
lean_inc(x_1019);
lean_dec(x_992);
x_1020 = l_Lean_mkAppN(x_6, x_1019);
lean_dec(x_1019);
if (lean_is_scalar(x_1018)) {
 x_1021 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1021 = x_1018;
}
lean_ctor_set(x_1021, 0, x_1020);
lean_ctor_set(x_1021, 1, x_1017);
x_1022 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_1016);
return x_1022;
}
}
}
else
{
uint8_t x_1023; 
lean_dec(x_6);
lean_dec(x_1);
x_1023 = !lean_is_exclusive(x_990);
if (x_1023 == 0)
{
return x_990;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1024 = lean_ctor_get(x_990, 0);
x_1025 = lean_ctor_get(x_990, 1);
lean_inc(x_1025);
lean_inc(x_1024);
lean_dec(x_990);
x_1026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1026, 0, x_1024);
lean_ctor_set(x_1026, 1, x_1025);
return x_1026;
}
}
}
else
{
uint8_t x_1027; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1027 = !lean_is_exclusive(x_978);
if (x_1027 == 0)
{
return x_978;
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1028 = lean_ctor_get(x_978, 0);
x_1029 = lean_ctor_get(x_978, 1);
lean_inc(x_1029);
lean_inc(x_1028);
lean_dec(x_978);
x_1030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set(x_1030, 1, x_1029);
return x_1030;
}
}
}
}
case 8:
{
lean_object* x_1044; lean_object* x_1123; lean_object* x_1178; uint8_t x_1179; 
lean_dec(x_8);
x_1178 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1179 = l_Lean_Expr_isConstOf(x_6, x_1178);
if (x_1179 == 0)
{
lean_object* x_1180; 
x_1180 = lean_box(0);
x_1123 = x_1180;
goto block_1177;
}
else
{
lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; 
x_1181 = lean_array_get_size(x_7);
x_1182 = lean_unsigned_to_nat(2u);
x_1183 = lean_nat_dec_eq(x_1181, x_1182);
if (x_1183 == 0)
{
lean_object* x_1184; 
lean_dec(x_1181);
x_1184 = lean_box(0);
x_1123 = x_1184;
goto block_1177;
}
else
{
lean_object* x_1185; uint8_t x_1186; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1185 = lean_unsigned_to_nat(0u);
x_1186 = lean_nat_dec_lt(x_1185, x_1181);
lean_dec(x_1181);
if (x_1186 == 0)
{
lean_object* x_1187; lean_object* x_1188; 
x_1187 = l_Lean_instInhabitedExpr;
x_1188 = l_outOfBounds___rarg(x_1187);
x_1044 = x_1188;
goto block_1122;
}
else
{
lean_object* x_1189; 
x_1189 = lean_array_fget(x_7, x_1185);
x_1044 = x_1189;
goto block_1122;
}
}
}
block_1122:
{
lean_object* x_1045; 
lean_inc(x_1044);
x_1045 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1044, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1045) == 0)
{
uint8_t x_1046; 
x_1046 = !lean_is_exclusive(x_1045);
if (x_1046 == 0)
{
lean_object* x_1047; uint8_t x_1048; 
x_1047 = lean_ctor_get(x_1045, 0);
x_1048 = !lean_is_exclusive(x_1047);
if (x_1048 == 0)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1049 = lean_ctor_get(x_1047, 0);
x_1050 = lean_ctor_get(x_1047, 1);
x_1051 = lean_ctor_get(x_1050, 2);
lean_inc(x_1051);
lean_inc(x_1051);
x_1052 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1051, x_1049);
if (lean_obj_tag(x_1052) == 0)
{
size_t x_1053; size_t x_1054; uint8_t x_1055; 
x_1053 = lean_ptr_addr(x_1044);
lean_dec(x_1044);
x_1054 = lean_ptr_addr(x_1049);
x_1055 = lean_usize_dec_eq(x_1053, x_1054);
if (x_1055 == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_1);
x_1056 = lean_unsigned_to_nat(0u);
lean_inc(x_1049);
x_1057 = lean_array_set(x_7, x_1056, x_1049);
x_1058 = l_Lean_mkAppN(x_6, x_1057);
lean_dec(x_1057);
x_1059 = lean_ctor_get(x_1050, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1050, 1);
lean_inc(x_1060);
lean_dec(x_1050);
lean_inc(x_1058);
x_1061 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1051, x_1049, x_1058);
x_1062 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1062, 0, x_1059);
lean_ctor_set(x_1062, 1, x_1060);
lean_ctor_set(x_1062, 2, x_1061);
lean_ctor_set(x_1047, 1, x_1062);
lean_ctor_set(x_1047, 0, x_1058);
return x_1045;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_7);
lean_dec(x_6);
x_1063 = lean_ctor_get(x_1050, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1050, 1);
lean_inc(x_1064);
lean_dec(x_1050);
lean_inc(x_1);
x_1065 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1051, x_1049, x_1);
x_1066 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1066, 0, x_1063);
lean_ctor_set(x_1066, 1, x_1064);
lean_ctor_set(x_1066, 2, x_1065);
lean_ctor_set(x_1047, 1, x_1066);
lean_ctor_set(x_1047, 0, x_1);
return x_1045;
}
}
else
{
lean_object* x_1067; 
lean_dec(x_1051);
lean_dec(x_1049);
lean_dec(x_1044);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1067 = lean_ctor_get(x_1052, 0);
lean_inc(x_1067);
lean_dec(x_1052);
lean_ctor_set(x_1047, 0, x_1067);
return x_1045;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
x_1068 = lean_ctor_get(x_1047, 0);
x_1069 = lean_ctor_get(x_1047, 1);
lean_inc(x_1069);
lean_inc(x_1068);
lean_dec(x_1047);
x_1070 = lean_ctor_get(x_1069, 2);
lean_inc(x_1070);
lean_inc(x_1070);
x_1071 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1070, x_1068);
if (lean_obj_tag(x_1071) == 0)
{
size_t x_1072; size_t x_1073; uint8_t x_1074; 
x_1072 = lean_ptr_addr(x_1044);
lean_dec(x_1044);
x_1073 = lean_ptr_addr(x_1068);
x_1074 = lean_usize_dec_eq(x_1072, x_1073);
if (x_1074 == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_1);
x_1075 = lean_unsigned_to_nat(0u);
lean_inc(x_1068);
x_1076 = lean_array_set(x_7, x_1075, x_1068);
x_1077 = l_Lean_mkAppN(x_6, x_1076);
lean_dec(x_1076);
x_1078 = lean_ctor_get(x_1069, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1069, 1);
lean_inc(x_1079);
lean_dec(x_1069);
lean_inc(x_1077);
x_1080 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1070, x_1068, x_1077);
x_1081 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1081, 0, x_1078);
lean_ctor_set(x_1081, 1, x_1079);
lean_ctor_set(x_1081, 2, x_1080);
x_1082 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1082, 0, x_1077);
lean_ctor_set(x_1082, 1, x_1081);
lean_ctor_set(x_1045, 0, x_1082);
return x_1045;
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_7);
lean_dec(x_6);
x_1083 = lean_ctor_get(x_1069, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1069, 1);
lean_inc(x_1084);
lean_dec(x_1069);
lean_inc(x_1);
x_1085 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1070, x_1068, x_1);
x_1086 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1086, 0, x_1083);
lean_ctor_set(x_1086, 1, x_1084);
lean_ctor_set(x_1086, 2, x_1085);
x_1087 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1087, 0, x_1);
lean_ctor_set(x_1087, 1, x_1086);
lean_ctor_set(x_1045, 0, x_1087);
return x_1045;
}
}
else
{
lean_object* x_1088; lean_object* x_1089; 
lean_dec(x_1070);
lean_dec(x_1068);
lean_dec(x_1044);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1088 = lean_ctor_get(x_1071, 0);
lean_inc(x_1088);
lean_dec(x_1071);
x_1089 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1089, 0, x_1088);
lean_ctor_set(x_1089, 1, x_1069);
lean_ctor_set(x_1045, 0, x_1089);
return x_1045;
}
}
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1090 = lean_ctor_get(x_1045, 0);
x_1091 = lean_ctor_get(x_1045, 1);
lean_inc(x_1091);
lean_inc(x_1090);
lean_dec(x_1045);
x_1092 = lean_ctor_get(x_1090, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1090, 1);
lean_inc(x_1093);
if (lean_is_exclusive(x_1090)) {
 lean_ctor_release(x_1090, 0);
 lean_ctor_release(x_1090, 1);
 x_1094 = x_1090;
} else {
 lean_dec_ref(x_1090);
 x_1094 = lean_box(0);
}
x_1095 = lean_ctor_get(x_1093, 2);
lean_inc(x_1095);
lean_inc(x_1095);
x_1096 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1095, x_1092);
if (lean_obj_tag(x_1096) == 0)
{
size_t x_1097; size_t x_1098; uint8_t x_1099; 
x_1097 = lean_ptr_addr(x_1044);
lean_dec(x_1044);
x_1098 = lean_ptr_addr(x_1092);
x_1099 = lean_usize_dec_eq(x_1097, x_1098);
if (x_1099 == 0)
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_1);
x_1100 = lean_unsigned_to_nat(0u);
lean_inc(x_1092);
x_1101 = lean_array_set(x_7, x_1100, x_1092);
x_1102 = l_Lean_mkAppN(x_6, x_1101);
lean_dec(x_1101);
x_1103 = lean_ctor_get(x_1093, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1093, 1);
lean_inc(x_1104);
lean_dec(x_1093);
lean_inc(x_1102);
x_1105 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1095, x_1092, x_1102);
x_1106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1106, 0, x_1103);
lean_ctor_set(x_1106, 1, x_1104);
lean_ctor_set(x_1106, 2, x_1105);
if (lean_is_scalar(x_1094)) {
 x_1107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1107 = x_1094;
}
lean_ctor_set(x_1107, 0, x_1102);
lean_ctor_set(x_1107, 1, x_1106);
x_1108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_1091);
return x_1108;
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_7);
lean_dec(x_6);
x_1109 = lean_ctor_get(x_1093, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1093, 1);
lean_inc(x_1110);
lean_dec(x_1093);
lean_inc(x_1);
x_1111 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1095, x_1092, x_1);
x_1112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1112, 0, x_1109);
lean_ctor_set(x_1112, 1, x_1110);
lean_ctor_set(x_1112, 2, x_1111);
if (lean_is_scalar(x_1094)) {
 x_1113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1113 = x_1094;
}
lean_ctor_set(x_1113, 0, x_1);
lean_ctor_set(x_1113, 1, x_1112);
x_1114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1114, 0, x_1113);
lean_ctor_set(x_1114, 1, x_1091);
return x_1114;
}
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_1095);
lean_dec(x_1092);
lean_dec(x_1044);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1115 = lean_ctor_get(x_1096, 0);
lean_inc(x_1115);
lean_dec(x_1096);
if (lean_is_scalar(x_1094)) {
 x_1116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1116 = x_1094;
}
lean_ctor_set(x_1116, 0, x_1115);
lean_ctor_set(x_1116, 1, x_1093);
x_1117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_1091);
return x_1117;
}
}
}
else
{
uint8_t x_1118; 
lean_dec(x_1044);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1118 = !lean_is_exclusive(x_1045);
if (x_1118 == 0)
{
return x_1045;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_1045, 0);
x_1120 = lean_ctor_get(x_1045, 1);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_1045);
x_1121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1121, 0, x_1119);
lean_ctor_set(x_1121, 1, x_1120);
return x_1121;
}
}
}
block_1177:
{
lean_object* x_1124; 
lean_dec(x_1123);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_1124 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1124) == 0)
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; uint8_t x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1125 = lean_ctor_get(x_1124, 0);
lean_inc(x_1125);
x_1126 = lean_ctor_get(x_1124, 1);
lean_inc(x_1126);
lean_dec(x_1124);
x_1127 = lean_ctor_get(x_1125, 0);
lean_inc(x_1127);
lean_dec(x_1125);
x_1128 = lean_array_get_size(x_7);
x_1129 = lean_unsigned_to_nat(0u);
x_1130 = lean_unsigned_to_nat(1u);
lean_inc(x_1128);
x_1131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1131, 0, x_1129);
lean_ctor_set(x_1131, 1, x_1128);
lean_ctor_set(x_1131, 2, x_1130);
x_1132 = 0;
x_1133 = lean_box(x_1132);
lean_inc(x_7);
x_1134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1134, 0, x_7);
lean_ctor_set(x_1134, 1, x_1133);
x_1135 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1131);
lean_inc(x_6);
x_1136 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_1135, x_1127, x_1128, x_1131, x_1131, x_1134, x_1129, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_1126);
if (lean_obj_tag(x_1136) == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; uint8_t x_1140; 
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1138, 1);
lean_inc(x_1139);
x_1140 = lean_unbox(x_1139);
lean_dec(x_1139);
if (x_1140 == 0)
{
uint8_t x_1141; 
lean_dec(x_1138);
lean_dec(x_6);
x_1141 = !lean_is_exclusive(x_1136);
if (x_1141 == 0)
{
lean_object* x_1142; uint8_t x_1143; 
x_1142 = lean_ctor_get(x_1136, 0);
lean_dec(x_1142);
x_1143 = !lean_is_exclusive(x_1137);
if (x_1143 == 0)
{
lean_object* x_1144; 
x_1144 = lean_ctor_get(x_1137, 0);
lean_dec(x_1144);
lean_ctor_set(x_1137, 0, x_1);
return x_1136;
}
else
{
lean_object* x_1145; lean_object* x_1146; 
x_1145 = lean_ctor_get(x_1137, 1);
lean_inc(x_1145);
lean_dec(x_1137);
x_1146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1146, 0, x_1);
lean_ctor_set(x_1146, 1, x_1145);
lean_ctor_set(x_1136, 0, x_1146);
return x_1136;
}
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1147 = lean_ctor_get(x_1136, 1);
lean_inc(x_1147);
lean_dec(x_1136);
x_1148 = lean_ctor_get(x_1137, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 lean_ctor_release(x_1137, 1);
 x_1149 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1149 = lean_box(0);
}
if (lean_is_scalar(x_1149)) {
 x_1150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1150 = x_1149;
}
lean_ctor_set(x_1150, 0, x_1);
lean_ctor_set(x_1150, 1, x_1148);
x_1151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1151, 0, x_1150);
lean_ctor_set(x_1151, 1, x_1147);
return x_1151;
}
}
else
{
uint8_t x_1152; 
lean_dec(x_1);
x_1152 = !lean_is_exclusive(x_1136);
if (x_1152 == 0)
{
lean_object* x_1153; uint8_t x_1154; 
x_1153 = lean_ctor_get(x_1136, 0);
lean_dec(x_1153);
x_1154 = !lean_is_exclusive(x_1137);
if (x_1154 == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1155 = lean_ctor_get(x_1137, 0);
lean_dec(x_1155);
x_1156 = lean_ctor_get(x_1138, 0);
lean_inc(x_1156);
lean_dec(x_1138);
x_1157 = l_Lean_mkAppN(x_6, x_1156);
lean_dec(x_1156);
lean_ctor_set(x_1137, 0, x_1157);
return x_1136;
}
else
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1158 = lean_ctor_get(x_1137, 1);
lean_inc(x_1158);
lean_dec(x_1137);
x_1159 = lean_ctor_get(x_1138, 0);
lean_inc(x_1159);
lean_dec(x_1138);
x_1160 = l_Lean_mkAppN(x_6, x_1159);
lean_dec(x_1159);
x_1161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1161, 0, x_1160);
lean_ctor_set(x_1161, 1, x_1158);
lean_ctor_set(x_1136, 0, x_1161);
return x_1136;
}
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1162 = lean_ctor_get(x_1136, 1);
lean_inc(x_1162);
lean_dec(x_1136);
x_1163 = lean_ctor_get(x_1137, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 lean_ctor_release(x_1137, 1);
 x_1164 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1164 = lean_box(0);
}
x_1165 = lean_ctor_get(x_1138, 0);
lean_inc(x_1165);
lean_dec(x_1138);
x_1166 = l_Lean_mkAppN(x_6, x_1165);
lean_dec(x_1165);
if (lean_is_scalar(x_1164)) {
 x_1167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1167 = x_1164;
}
lean_ctor_set(x_1167, 0, x_1166);
lean_ctor_set(x_1167, 1, x_1163);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_1167);
lean_ctor_set(x_1168, 1, x_1162);
return x_1168;
}
}
}
else
{
uint8_t x_1169; 
lean_dec(x_6);
lean_dec(x_1);
x_1169 = !lean_is_exclusive(x_1136);
if (x_1169 == 0)
{
return x_1136;
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1170 = lean_ctor_get(x_1136, 0);
x_1171 = lean_ctor_get(x_1136, 1);
lean_inc(x_1171);
lean_inc(x_1170);
lean_dec(x_1136);
x_1172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set(x_1172, 1, x_1171);
return x_1172;
}
}
}
else
{
uint8_t x_1173; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1173 = !lean_is_exclusive(x_1124);
if (x_1173 == 0)
{
return x_1124;
}
else
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1174 = lean_ctor_get(x_1124, 0);
x_1175 = lean_ctor_get(x_1124, 1);
lean_inc(x_1175);
lean_inc(x_1174);
lean_dec(x_1124);
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_1174);
lean_ctor_set(x_1176, 1, x_1175);
return x_1176;
}
}
}
}
case 9:
{
lean_object* x_1190; lean_object* x_1269; lean_object* x_1324; uint8_t x_1325; 
lean_dec(x_8);
x_1324 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1325 = l_Lean_Expr_isConstOf(x_6, x_1324);
if (x_1325 == 0)
{
lean_object* x_1326; 
x_1326 = lean_box(0);
x_1269 = x_1326;
goto block_1323;
}
else
{
lean_object* x_1327; lean_object* x_1328; uint8_t x_1329; 
x_1327 = lean_array_get_size(x_7);
x_1328 = lean_unsigned_to_nat(2u);
x_1329 = lean_nat_dec_eq(x_1327, x_1328);
if (x_1329 == 0)
{
lean_object* x_1330; 
lean_dec(x_1327);
x_1330 = lean_box(0);
x_1269 = x_1330;
goto block_1323;
}
else
{
lean_object* x_1331; uint8_t x_1332; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1331 = lean_unsigned_to_nat(0u);
x_1332 = lean_nat_dec_lt(x_1331, x_1327);
lean_dec(x_1327);
if (x_1332 == 0)
{
lean_object* x_1333; lean_object* x_1334; 
x_1333 = l_Lean_instInhabitedExpr;
x_1334 = l_outOfBounds___rarg(x_1333);
x_1190 = x_1334;
goto block_1268;
}
else
{
lean_object* x_1335; 
x_1335 = lean_array_fget(x_7, x_1331);
x_1190 = x_1335;
goto block_1268;
}
}
}
block_1268:
{
lean_object* x_1191; 
lean_inc(x_1190);
x_1191 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1190, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1191) == 0)
{
uint8_t x_1192; 
x_1192 = !lean_is_exclusive(x_1191);
if (x_1192 == 0)
{
lean_object* x_1193; uint8_t x_1194; 
x_1193 = lean_ctor_get(x_1191, 0);
x_1194 = !lean_is_exclusive(x_1193);
if (x_1194 == 0)
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1195 = lean_ctor_get(x_1193, 0);
x_1196 = lean_ctor_get(x_1193, 1);
x_1197 = lean_ctor_get(x_1196, 2);
lean_inc(x_1197);
lean_inc(x_1197);
x_1198 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1197, x_1195);
if (lean_obj_tag(x_1198) == 0)
{
size_t x_1199; size_t x_1200; uint8_t x_1201; 
x_1199 = lean_ptr_addr(x_1190);
lean_dec(x_1190);
x_1200 = lean_ptr_addr(x_1195);
x_1201 = lean_usize_dec_eq(x_1199, x_1200);
if (x_1201 == 0)
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1);
x_1202 = lean_unsigned_to_nat(0u);
lean_inc(x_1195);
x_1203 = lean_array_set(x_7, x_1202, x_1195);
x_1204 = l_Lean_mkAppN(x_6, x_1203);
lean_dec(x_1203);
x_1205 = lean_ctor_get(x_1196, 0);
lean_inc(x_1205);
x_1206 = lean_ctor_get(x_1196, 1);
lean_inc(x_1206);
lean_dec(x_1196);
lean_inc(x_1204);
x_1207 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1197, x_1195, x_1204);
x_1208 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1208, 0, x_1205);
lean_ctor_set(x_1208, 1, x_1206);
lean_ctor_set(x_1208, 2, x_1207);
lean_ctor_set(x_1193, 1, x_1208);
lean_ctor_set(x_1193, 0, x_1204);
return x_1191;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
lean_dec(x_7);
lean_dec(x_6);
x_1209 = lean_ctor_get(x_1196, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1196, 1);
lean_inc(x_1210);
lean_dec(x_1196);
lean_inc(x_1);
x_1211 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1197, x_1195, x_1);
x_1212 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1212, 0, x_1209);
lean_ctor_set(x_1212, 1, x_1210);
lean_ctor_set(x_1212, 2, x_1211);
lean_ctor_set(x_1193, 1, x_1212);
lean_ctor_set(x_1193, 0, x_1);
return x_1191;
}
}
else
{
lean_object* x_1213; 
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1190);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1213 = lean_ctor_get(x_1198, 0);
lean_inc(x_1213);
lean_dec(x_1198);
lean_ctor_set(x_1193, 0, x_1213);
return x_1191;
}
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
x_1214 = lean_ctor_get(x_1193, 0);
x_1215 = lean_ctor_get(x_1193, 1);
lean_inc(x_1215);
lean_inc(x_1214);
lean_dec(x_1193);
x_1216 = lean_ctor_get(x_1215, 2);
lean_inc(x_1216);
lean_inc(x_1216);
x_1217 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1216, x_1214);
if (lean_obj_tag(x_1217) == 0)
{
size_t x_1218; size_t x_1219; uint8_t x_1220; 
x_1218 = lean_ptr_addr(x_1190);
lean_dec(x_1190);
x_1219 = lean_ptr_addr(x_1214);
x_1220 = lean_usize_dec_eq(x_1218, x_1219);
if (x_1220 == 0)
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1);
x_1221 = lean_unsigned_to_nat(0u);
lean_inc(x_1214);
x_1222 = lean_array_set(x_7, x_1221, x_1214);
x_1223 = l_Lean_mkAppN(x_6, x_1222);
lean_dec(x_1222);
x_1224 = lean_ctor_get(x_1215, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1215, 1);
lean_inc(x_1225);
lean_dec(x_1215);
lean_inc(x_1223);
x_1226 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1216, x_1214, x_1223);
x_1227 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1227, 0, x_1224);
lean_ctor_set(x_1227, 1, x_1225);
lean_ctor_set(x_1227, 2, x_1226);
x_1228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1228, 0, x_1223);
lean_ctor_set(x_1228, 1, x_1227);
lean_ctor_set(x_1191, 0, x_1228);
return x_1191;
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
lean_dec(x_7);
lean_dec(x_6);
x_1229 = lean_ctor_get(x_1215, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1215, 1);
lean_inc(x_1230);
lean_dec(x_1215);
lean_inc(x_1);
x_1231 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1216, x_1214, x_1);
x_1232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1232, 0, x_1229);
lean_ctor_set(x_1232, 1, x_1230);
lean_ctor_set(x_1232, 2, x_1231);
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_1);
lean_ctor_set(x_1233, 1, x_1232);
lean_ctor_set(x_1191, 0, x_1233);
return x_1191;
}
}
else
{
lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1216);
lean_dec(x_1214);
lean_dec(x_1190);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1234 = lean_ctor_get(x_1217, 0);
lean_inc(x_1234);
lean_dec(x_1217);
x_1235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1215);
lean_ctor_set(x_1191, 0, x_1235);
return x_1191;
}
}
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
x_1236 = lean_ctor_get(x_1191, 0);
x_1237 = lean_ctor_get(x_1191, 1);
lean_inc(x_1237);
lean_inc(x_1236);
lean_dec(x_1191);
x_1238 = lean_ctor_get(x_1236, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1236, 1);
lean_inc(x_1239);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 lean_ctor_release(x_1236, 1);
 x_1240 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1240 = lean_box(0);
}
x_1241 = lean_ctor_get(x_1239, 2);
lean_inc(x_1241);
lean_inc(x_1241);
x_1242 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1241, x_1238);
if (lean_obj_tag(x_1242) == 0)
{
size_t x_1243; size_t x_1244; uint8_t x_1245; 
x_1243 = lean_ptr_addr(x_1190);
lean_dec(x_1190);
x_1244 = lean_ptr_addr(x_1238);
x_1245 = lean_usize_dec_eq(x_1243, x_1244);
if (x_1245 == 0)
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1);
x_1246 = lean_unsigned_to_nat(0u);
lean_inc(x_1238);
x_1247 = lean_array_set(x_7, x_1246, x_1238);
x_1248 = l_Lean_mkAppN(x_6, x_1247);
lean_dec(x_1247);
x_1249 = lean_ctor_get(x_1239, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1239, 1);
lean_inc(x_1250);
lean_dec(x_1239);
lean_inc(x_1248);
x_1251 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1241, x_1238, x_1248);
x_1252 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1252, 0, x_1249);
lean_ctor_set(x_1252, 1, x_1250);
lean_ctor_set(x_1252, 2, x_1251);
if (lean_is_scalar(x_1240)) {
 x_1253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1253 = x_1240;
}
lean_ctor_set(x_1253, 0, x_1248);
lean_ctor_set(x_1253, 1, x_1252);
x_1254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1254, 0, x_1253);
lean_ctor_set(x_1254, 1, x_1237);
return x_1254;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_7);
lean_dec(x_6);
x_1255 = lean_ctor_get(x_1239, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1239, 1);
lean_inc(x_1256);
lean_dec(x_1239);
lean_inc(x_1);
x_1257 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1241, x_1238, x_1);
x_1258 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1258, 0, x_1255);
lean_ctor_set(x_1258, 1, x_1256);
lean_ctor_set(x_1258, 2, x_1257);
if (lean_is_scalar(x_1240)) {
 x_1259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1259 = x_1240;
}
lean_ctor_set(x_1259, 0, x_1);
lean_ctor_set(x_1259, 1, x_1258);
x_1260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1260, 0, x_1259);
lean_ctor_set(x_1260, 1, x_1237);
return x_1260;
}
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
lean_dec(x_1241);
lean_dec(x_1238);
lean_dec(x_1190);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1261 = lean_ctor_get(x_1242, 0);
lean_inc(x_1261);
lean_dec(x_1242);
if (lean_is_scalar(x_1240)) {
 x_1262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1262 = x_1240;
}
lean_ctor_set(x_1262, 0, x_1261);
lean_ctor_set(x_1262, 1, x_1239);
x_1263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1263, 0, x_1262);
lean_ctor_set(x_1263, 1, x_1237);
return x_1263;
}
}
}
else
{
uint8_t x_1264; 
lean_dec(x_1190);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1264 = !lean_is_exclusive(x_1191);
if (x_1264 == 0)
{
return x_1191;
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1265 = lean_ctor_get(x_1191, 0);
x_1266 = lean_ctor_get(x_1191, 1);
lean_inc(x_1266);
lean_inc(x_1265);
lean_dec(x_1191);
x_1267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1267, 0, x_1265);
lean_ctor_set(x_1267, 1, x_1266);
return x_1267;
}
}
}
block_1323:
{
lean_object* x_1270; 
lean_dec(x_1269);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_1270 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1270) == 0)
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; uint8_t x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
x_1271 = lean_ctor_get(x_1270, 0);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1270, 1);
lean_inc(x_1272);
lean_dec(x_1270);
x_1273 = lean_ctor_get(x_1271, 0);
lean_inc(x_1273);
lean_dec(x_1271);
x_1274 = lean_array_get_size(x_7);
x_1275 = lean_unsigned_to_nat(0u);
x_1276 = lean_unsigned_to_nat(1u);
lean_inc(x_1274);
x_1277 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1277, 0, x_1275);
lean_ctor_set(x_1277, 1, x_1274);
lean_ctor_set(x_1277, 2, x_1276);
x_1278 = 0;
x_1279 = lean_box(x_1278);
lean_inc(x_7);
x_1280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1280, 0, x_7);
lean_ctor_set(x_1280, 1, x_1279);
x_1281 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1277);
lean_inc(x_6);
x_1282 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_1281, x_1273, x_1274, x_1277, x_1277, x_1280, x_1275, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_1272);
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; uint8_t x_1286; 
x_1283 = lean_ctor_get(x_1282, 0);
lean_inc(x_1283);
x_1284 = lean_ctor_get(x_1283, 0);
lean_inc(x_1284);
x_1285 = lean_ctor_get(x_1284, 1);
lean_inc(x_1285);
x_1286 = lean_unbox(x_1285);
lean_dec(x_1285);
if (x_1286 == 0)
{
uint8_t x_1287; 
lean_dec(x_1284);
lean_dec(x_6);
x_1287 = !lean_is_exclusive(x_1282);
if (x_1287 == 0)
{
lean_object* x_1288; uint8_t x_1289; 
x_1288 = lean_ctor_get(x_1282, 0);
lean_dec(x_1288);
x_1289 = !lean_is_exclusive(x_1283);
if (x_1289 == 0)
{
lean_object* x_1290; 
x_1290 = lean_ctor_get(x_1283, 0);
lean_dec(x_1290);
lean_ctor_set(x_1283, 0, x_1);
return x_1282;
}
else
{
lean_object* x_1291; lean_object* x_1292; 
x_1291 = lean_ctor_get(x_1283, 1);
lean_inc(x_1291);
lean_dec(x_1283);
x_1292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1292, 0, x_1);
lean_ctor_set(x_1292, 1, x_1291);
lean_ctor_set(x_1282, 0, x_1292);
return x_1282;
}
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1293 = lean_ctor_get(x_1282, 1);
lean_inc(x_1293);
lean_dec(x_1282);
x_1294 = lean_ctor_get(x_1283, 1);
lean_inc(x_1294);
if (lean_is_exclusive(x_1283)) {
 lean_ctor_release(x_1283, 0);
 lean_ctor_release(x_1283, 1);
 x_1295 = x_1283;
} else {
 lean_dec_ref(x_1283);
 x_1295 = lean_box(0);
}
if (lean_is_scalar(x_1295)) {
 x_1296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1296 = x_1295;
}
lean_ctor_set(x_1296, 0, x_1);
lean_ctor_set(x_1296, 1, x_1294);
x_1297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1297, 0, x_1296);
lean_ctor_set(x_1297, 1, x_1293);
return x_1297;
}
}
else
{
uint8_t x_1298; 
lean_dec(x_1);
x_1298 = !lean_is_exclusive(x_1282);
if (x_1298 == 0)
{
lean_object* x_1299; uint8_t x_1300; 
x_1299 = lean_ctor_get(x_1282, 0);
lean_dec(x_1299);
x_1300 = !lean_is_exclusive(x_1283);
if (x_1300 == 0)
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1301 = lean_ctor_get(x_1283, 0);
lean_dec(x_1301);
x_1302 = lean_ctor_get(x_1284, 0);
lean_inc(x_1302);
lean_dec(x_1284);
x_1303 = l_Lean_mkAppN(x_6, x_1302);
lean_dec(x_1302);
lean_ctor_set(x_1283, 0, x_1303);
return x_1282;
}
else
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
x_1304 = lean_ctor_get(x_1283, 1);
lean_inc(x_1304);
lean_dec(x_1283);
x_1305 = lean_ctor_get(x_1284, 0);
lean_inc(x_1305);
lean_dec(x_1284);
x_1306 = l_Lean_mkAppN(x_6, x_1305);
lean_dec(x_1305);
x_1307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1307, 0, x_1306);
lean_ctor_set(x_1307, 1, x_1304);
lean_ctor_set(x_1282, 0, x_1307);
return x_1282;
}
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1308 = lean_ctor_get(x_1282, 1);
lean_inc(x_1308);
lean_dec(x_1282);
x_1309 = lean_ctor_get(x_1283, 1);
lean_inc(x_1309);
if (lean_is_exclusive(x_1283)) {
 lean_ctor_release(x_1283, 0);
 lean_ctor_release(x_1283, 1);
 x_1310 = x_1283;
} else {
 lean_dec_ref(x_1283);
 x_1310 = lean_box(0);
}
x_1311 = lean_ctor_get(x_1284, 0);
lean_inc(x_1311);
lean_dec(x_1284);
x_1312 = l_Lean_mkAppN(x_6, x_1311);
lean_dec(x_1311);
if (lean_is_scalar(x_1310)) {
 x_1313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1313 = x_1310;
}
lean_ctor_set(x_1313, 0, x_1312);
lean_ctor_set(x_1313, 1, x_1309);
x_1314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1314, 0, x_1313);
lean_ctor_set(x_1314, 1, x_1308);
return x_1314;
}
}
}
else
{
uint8_t x_1315; 
lean_dec(x_6);
lean_dec(x_1);
x_1315 = !lean_is_exclusive(x_1282);
if (x_1315 == 0)
{
return x_1282;
}
else
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
x_1316 = lean_ctor_get(x_1282, 0);
x_1317 = lean_ctor_get(x_1282, 1);
lean_inc(x_1317);
lean_inc(x_1316);
lean_dec(x_1282);
x_1318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1318, 0, x_1316);
lean_ctor_set(x_1318, 1, x_1317);
return x_1318;
}
}
}
else
{
uint8_t x_1319; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1319 = !lean_is_exclusive(x_1270);
if (x_1319 == 0)
{
return x_1270;
}
else
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1320 = lean_ctor_get(x_1270, 0);
x_1321 = lean_ctor_get(x_1270, 1);
lean_inc(x_1321);
lean_inc(x_1320);
lean_dec(x_1270);
x_1322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1322, 0, x_1320);
lean_ctor_set(x_1322, 1, x_1321);
return x_1322;
}
}
}
}
case 10:
{
lean_object* x_1336; lean_object* x_1415; lean_object* x_1470; uint8_t x_1471; 
lean_dec(x_8);
x_1470 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1471 = l_Lean_Expr_isConstOf(x_6, x_1470);
if (x_1471 == 0)
{
lean_object* x_1472; 
x_1472 = lean_box(0);
x_1415 = x_1472;
goto block_1469;
}
else
{
lean_object* x_1473; lean_object* x_1474; uint8_t x_1475; 
x_1473 = lean_array_get_size(x_7);
x_1474 = lean_unsigned_to_nat(2u);
x_1475 = lean_nat_dec_eq(x_1473, x_1474);
if (x_1475 == 0)
{
lean_object* x_1476; 
lean_dec(x_1473);
x_1476 = lean_box(0);
x_1415 = x_1476;
goto block_1469;
}
else
{
lean_object* x_1477; uint8_t x_1478; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1477 = lean_unsigned_to_nat(0u);
x_1478 = lean_nat_dec_lt(x_1477, x_1473);
lean_dec(x_1473);
if (x_1478 == 0)
{
lean_object* x_1479; lean_object* x_1480; 
x_1479 = l_Lean_instInhabitedExpr;
x_1480 = l_outOfBounds___rarg(x_1479);
x_1336 = x_1480;
goto block_1414;
}
else
{
lean_object* x_1481; 
x_1481 = lean_array_fget(x_7, x_1477);
x_1336 = x_1481;
goto block_1414;
}
}
}
block_1414:
{
lean_object* x_1337; 
lean_inc(x_1336);
x_1337 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1336, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1337) == 0)
{
uint8_t x_1338; 
x_1338 = !lean_is_exclusive(x_1337);
if (x_1338 == 0)
{
lean_object* x_1339; uint8_t x_1340; 
x_1339 = lean_ctor_get(x_1337, 0);
x_1340 = !lean_is_exclusive(x_1339);
if (x_1340 == 0)
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1341 = lean_ctor_get(x_1339, 0);
x_1342 = lean_ctor_get(x_1339, 1);
x_1343 = lean_ctor_get(x_1342, 2);
lean_inc(x_1343);
lean_inc(x_1343);
x_1344 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1343, x_1341);
if (lean_obj_tag(x_1344) == 0)
{
size_t x_1345; size_t x_1346; uint8_t x_1347; 
x_1345 = lean_ptr_addr(x_1336);
lean_dec(x_1336);
x_1346 = lean_ptr_addr(x_1341);
x_1347 = lean_usize_dec_eq(x_1345, x_1346);
if (x_1347 == 0)
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
lean_dec(x_1);
x_1348 = lean_unsigned_to_nat(0u);
lean_inc(x_1341);
x_1349 = lean_array_set(x_7, x_1348, x_1341);
x_1350 = l_Lean_mkAppN(x_6, x_1349);
lean_dec(x_1349);
x_1351 = lean_ctor_get(x_1342, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1342, 1);
lean_inc(x_1352);
lean_dec(x_1342);
lean_inc(x_1350);
x_1353 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1343, x_1341, x_1350);
x_1354 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1354, 0, x_1351);
lean_ctor_set(x_1354, 1, x_1352);
lean_ctor_set(x_1354, 2, x_1353);
lean_ctor_set(x_1339, 1, x_1354);
lean_ctor_set(x_1339, 0, x_1350);
return x_1337;
}
else
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
lean_dec(x_7);
lean_dec(x_6);
x_1355 = lean_ctor_get(x_1342, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1342, 1);
lean_inc(x_1356);
lean_dec(x_1342);
lean_inc(x_1);
x_1357 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1343, x_1341, x_1);
x_1358 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1358, 0, x_1355);
lean_ctor_set(x_1358, 1, x_1356);
lean_ctor_set(x_1358, 2, x_1357);
lean_ctor_set(x_1339, 1, x_1358);
lean_ctor_set(x_1339, 0, x_1);
return x_1337;
}
}
else
{
lean_object* x_1359; 
lean_dec(x_1343);
lean_dec(x_1341);
lean_dec(x_1336);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1359 = lean_ctor_get(x_1344, 0);
lean_inc(x_1359);
lean_dec(x_1344);
lean_ctor_set(x_1339, 0, x_1359);
return x_1337;
}
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1360 = lean_ctor_get(x_1339, 0);
x_1361 = lean_ctor_get(x_1339, 1);
lean_inc(x_1361);
lean_inc(x_1360);
lean_dec(x_1339);
x_1362 = lean_ctor_get(x_1361, 2);
lean_inc(x_1362);
lean_inc(x_1362);
x_1363 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1362, x_1360);
if (lean_obj_tag(x_1363) == 0)
{
size_t x_1364; size_t x_1365; uint8_t x_1366; 
x_1364 = lean_ptr_addr(x_1336);
lean_dec(x_1336);
x_1365 = lean_ptr_addr(x_1360);
x_1366 = lean_usize_dec_eq(x_1364, x_1365);
if (x_1366 == 0)
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_1);
x_1367 = lean_unsigned_to_nat(0u);
lean_inc(x_1360);
x_1368 = lean_array_set(x_7, x_1367, x_1360);
x_1369 = l_Lean_mkAppN(x_6, x_1368);
lean_dec(x_1368);
x_1370 = lean_ctor_get(x_1361, 0);
lean_inc(x_1370);
x_1371 = lean_ctor_get(x_1361, 1);
lean_inc(x_1371);
lean_dec(x_1361);
lean_inc(x_1369);
x_1372 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1362, x_1360, x_1369);
x_1373 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1373, 0, x_1370);
lean_ctor_set(x_1373, 1, x_1371);
lean_ctor_set(x_1373, 2, x_1372);
x_1374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1374, 0, x_1369);
lean_ctor_set(x_1374, 1, x_1373);
lean_ctor_set(x_1337, 0, x_1374);
return x_1337;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
lean_dec(x_7);
lean_dec(x_6);
x_1375 = lean_ctor_get(x_1361, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1361, 1);
lean_inc(x_1376);
lean_dec(x_1361);
lean_inc(x_1);
x_1377 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1362, x_1360, x_1);
x_1378 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1378, 0, x_1375);
lean_ctor_set(x_1378, 1, x_1376);
lean_ctor_set(x_1378, 2, x_1377);
x_1379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1379, 0, x_1);
lean_ctor_set(x_1379, 1, x_1378);
lean_ctor_set(x_1337, 0, x_1379);
return x_1337;
}
}
else
{
lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1362);
lean_dec(x_1360);
lean_dec(x_1336);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1380 = lean_ctor_get(x_1363, 0);
lean_inc(x_1380);
lean_dec(x_1363);
x_1381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1381, 0, x_1380);
lean_ctor_set(x_1381, 1, x_1361);
lean_ctor_set(x_1337, 0, x_1381);
return x_1337;
}
}
}
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
x_1382 = lean_ctor_get(x_1337, 0);
x_1383 = lean_ctor_get(x_1337, 1);
lean_inc(x_1383);
lean_inc(x_1382);
lean_dec(x_1337);
x_1384 = lean_ctor_get(x_1382, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1382, 1);
lean_inc(x_1385);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 x_1386 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1386 = lean_box(0);
}
x_1387 = lean_ctor_get(x_1385, 2);
lean_inc(x_1387);
lean_inc(x_1387);
x_1388 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1387, x_1384);
if (lean_obj_tag(x_1388) == 0)
{
size_t x_1389; size_t x_1390; uint8_t x_1391; 
x_1389 = lean_ptr_addr(x_1336);
lean_dec(x_1336);
x_1390 = lean_ptr_addr(x_1384);
x_1391 = lean_usize_dec_eq(x_1389, x_1390);
if (x_1391 == 0)
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
lean_dec(x_1);
x_1392 = lean_unsigned_to_nat(0u);
lean_inc(x_1384);
x_1393 = lean_array_set(x_7, x_1392, x_1384);
x_1394 = l_Lean_mkAppN(x_6, x_1393);
lean_dec(x_1393);
x_1395 = lean_ctor_get(x_1385, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1385, 1);
lean_inc(x_1396);
lean_dec(x_1385);
lean_inc(x_1394);
x_1397 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1387, x_1384, x_1394);
x_1398 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1398, 0, x_1395);
lean_ctor_set(x_1398, 1, x_1396);
lean_ctor_set(x_1398, 2, x_1397);
if (lean_is_scalar(x_1386)) {
 x_1399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1399 = x_1386;
}
lean_ctor_set(x_1399, 0, x_1394);
lean_ctor_set(x_1399, 1, x_1398);
x_1400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1400, 0, x_1399);
lean_ctor_set(x_1400, 1, x_1383);
return x_1400;
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
lean_dec(x_7);
lean_dec(x_6);
x_1401 = lean_ctor_get(x_1385, 0);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1385, 1);
lean_inc(x_1402);
lean_dec(x_1385);
lean_inc(x_1);
x_1403 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1387, x_1384, x_1);
x_1404 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1404, 0, x_1401);
lean_ctor_set(x_1404, 1, x_1402);
lean_ctor_set(x_1404, 2, x_1403);
if (lean_is_scalar(x_1386)) {
 x_1405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1405 = x_1386;
}
lean_ctor_set(x_1405, 0, x_1);
lean_ctor_set(x_1405, 1, x_1404);
x_1406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1406, 0, x_1405);
lean_ctor_set(x_1406, 1, x_1383);
return x_1406;
}
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
lean_dec(x_1387);
lean_dec(x_1384);
lean_dec(x_1336);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1407 = lean_ctor_get(x_1388, 0);
lean_inc(x_1407);
lean_dec(x_1388);
if (lean_is_scalar(x_1386)) {
 x_1408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1408 = x_1386;
}
lean_ctor_set(x_1408, 0, x_1407);
lean_ctor_set(x_1408, 1, x_1385);
x_1409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1409, 0, x_1408);
lean_ctor_set(x_1409, 1, x_1383);
return x_1409;
}
}
}
else
{
uint8_t x_1410; 
lean_dec(x_1336);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1410 = !lean_is_exclusive(x_1337);
if (x_1410 == 0)
{
return x_1337;
}
else
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1411 = lean_ctor_get(x_1337, 0);
x_1412 = lean_ctor_get(x_1337, 1);
lean_inc(x_1412);
lean_inc(x_1411);
lean_dec(x_1337);
x_1413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1413, 0, x_1411);
lean_ctor_set(x_1413, 1, x_1412);
return x_1413;
}
}
}
block_1469:
{
lean_object* x_1416; 
lean_dec(x_1415);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_1416 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1416) == 0)
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; uint8_t x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
x_1417 = lean_ctor_get(x_1416, 0);
lean_inc(x_1417);
x_1418 = lean_ctor_get(x_1416, 1);
lean_inc(x_1418);
lean_dec(x_1416);
x_1419 = lean_ctor_get(x_1417, 0);
lean_inc(x_1419);
lean_dec(x_1417);
x_1420 = lean_array_get_size(x_7);
x_1421 = lean_unsigned_to_nat(0u);
x_1422 = lean_unsigned_to_nat(1u);
lean_inc(x_1420);
x_1423 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1423, 0, x_1421);
lean_ctor_set(x_1423, 1, x_1420);
lean_ctor_set(x_1423, 2, x_1422);
x_1424 = 0;
x_1425 = lean_box(x_1424);
lean_inc(x_7);
x_1426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1426, 0, x_7);
lean_ctor_set(x_1426, 1, x_1425);
x_1427 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1423);
lean_inc(x_6);
x_1428 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_1427, x_1419, x_1420, x_1423, x_1423, x_1426, x_1421, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_1418);
if (lean_obj_tag(x_1428) == 0)
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; uint8_t x_1432; 
x_1429 = lean_ctor_get(x_1428, 0);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1429, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1430, 1);
lean_inc(x_1431);
x_1432 = lean_unbox(x_1431);
lean_dec(x_1431);
if (x_1432 == 0)
{
uint8_t x_1433; 
lean_dec(x_1430);
lean_dec(x_6);
x_1433 = !lean_is_exclusive(x_1428);
if (x_1433 == 0)
{
lean_object* x_1434; uint8_t x_1435; 
x_1434 = lean_ctor_get(x_1428, 0);
lean_dec(x_1434);
x_1435 = !lean_is_exclusive(x_1429);
if (x_1435 == 0)
{
lean_object* x_1436; 
x_1436 = lean_ctor_get(x_1429, 0);
lean_dec(x_1436);
lean_ctor_set(x_1429, 0, x_1);
return x_1428;
}
else
{
lean_object* x_1437; lean_object* x_1438; 
x_1437 = lean_ctor_get(x_1429, 1);
lean_inc(x_1437);
lean_dec(x_1429);
x_1438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1438, 0, x_1);
lean_ctor_set(x_1438, 1, x_1437);
lean_ctor_set(x_1428, 0, x_1438);
return x_1428;
}
}
else
{
lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; 
x_1439 = lean_ctor_get(x_1428, 1);
lean_inc(x_1439);
lean_dec(x_1428);
x_1440 = lean_ctor_get(x_1429, 1);
lean_inc(x_1440);
if (lean_is_exclusive(x_1429)) {
 lean_ctor_release(x_1429, 0);
 lean_ctor_release(x_1429, 1);
 x_1441 = x_1429;
} else {
 lean_dec_ref(x_1429);
 x_1441 = lean_box(0);
}
if (lean_is_scalar(x_1441)) {
 x_1442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1442 = x_1441;
}
lean_ctor_set(x_1442, 0, x_1);
lean_ctor_set(x_1442, 1, x_1440);
x_1443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1443, 0, x_1442);
lean_ctor_set(x_1443, 1, x_1439);
return x_1443;
}
}
else
{
uint8_t x_1444; 
lean_dec(x_1);
x_1444 = !lean_is_exclusive(x_1428);
if (x_1444 == 0)
{
lean_object* x_1445; uint8_t x_1446; 
x_1445 = lean_ctor_get(x_1428, 0);
lean_dec(x_1445);
x_1446 = !lean_is_exclusive(x_1429);
if (x_1446 == 0)
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
x_1447 = lean_ctor_get(x_1429, 0);
lean_dec(x_1447);
x_1448 = lean_ctor_get(x_1430, 0);
lean_inc(x_1448);
lean_dec(x_1430);
x_1449 = l_Lean_mkAppN(x_6, x_1448);
lean_dec(x_1448);
lean_ctor_set(x_1429, 0, x_1449);
return x_1428;
}
else
{
lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
x_1450 = lean_ctor_get(x_1429, 1);
lean_inc(x_1450);
lean_dec(x_1429);
x_1451 = lean_ctor_get(x_1430, 0);
lean_inc(x_1451);
lean_dec(x_1430);
x_1452 = l_Lean_mkAppN(x_6, x_1451);
lean_dec(x_1451);
x_1453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1453, 0, x_1452);
lean_ctor_set(x_1453, 1, x_1450);
lean_ctor_set(x_1428, 0, x_1453);
return x_1428;
}
}
else
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1454 = lean_ctor_get(x_1428, 1);
lean_inc(x_1454);
lean_dec(x_1428);
x_1455 = lean_ctor_get(x_1429, 1);
lean_inc(x_1455);
if (lean_is_exclusive(x_1429)) {
 lean_ctor_release(x_1429, 0);
 lean_ctor_release(x_1429, 1);
 x_1456 = x_1429;
} else {
 lean_dec_ref(x_1429);
 x_1456 = lean_box(0);
}
x_1457 = lean_ctor_get(x_1430, 0);
lean_inc(x_1457);
lean_dec(x_1430);
x_1458 = l_Lean_mkAppN(x_6, x_1457);
lean_dec(x_1457);
if (lean_is_scalar(x_1456)) {
 x_1459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1459 = x_1456;
}
lean_ctor_set(x_1459, 0, x_1458);
lean_ctor_set(x_1459, 1, x_1455);
x_1460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1460, 0, x_1459);
lean_ctor_set(x_1460, 1, x_1454);
return x_1460;
}
}
}
else
{
uint8_t x_1461; 
lean_dec(x_6);
lean_dec(x_1);
x_1461 = !lean_is_exclusive(x_1428);
if (x_1461 == 0)
{
return x_1428;
}
else
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; 
x_1462 = lean_ctor_get(x_1428, 0);
x_1463 = lean_ctor_get(x_1428, 1);
lean_inc(x_1463);
lean_inc(x_1462);
lean_dec(x_1428);
x_1464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1464, 0, x_1462);
lean_ctor_set(x_1464, 1, x_1463);
return x_1464;
}
}
}
else
{
uint8_t x_1465; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1465 = !lean_is_exclusive(x_1416);
if (x_1465 == 0)
{
return x_1416;
}
else
{
lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; 
x_1466 = lean_ctor_get(x_1416, 0);
x_1467 = lean_ctor_get(x_1416, 1);
lean_inc(x_1467);
lean_inc(x_1466);
lean_dec(x_1416);
x_1468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1468, 0, x_1466);
lean_ctor_set(x_1468, 1, x_1467);
return x_1468;
}
}
}
}
default: 
{
lean_object* x_1482; lean_object* x_1561; lean_object* x_1616; uint8_t x_1617; 
lean_dec(x_8);
x_1616 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5;
x_1617 = l_Lean_Expr_isConstOf(x_6, x_1616);
if (x_1617 == 0)
{
lean_object* x_1618; 
x_1618 = lean_box(0);
x_1561 = x_1618;
goto block_1615;
}
else
{
lean_object* x_1619; lean_object* x_1620; uint8_t x_1621; 
x_1619 = lean_array_get_size(x_7);
x_1620 = lean_unsigned_to_nat(2u);
x_1621 = lean_nat_dec_eq(x_1619, x_1620);
if (x_1621 == 0)
{
lean_object* x_1622; 
lean_dec(x_1619);
x_1622 = lean_box(0);
x_1561 = x_1622;
goto block_1615;
}
else
{
lean_object* x_1623; uint8_t x_1624; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1623 = lean_unsigned_to_nat(0u);
x_1624 = lean_nat_dec_lt(x_1623, x_1619);
lean_dec(x_1619);
if (x_1624 == 0)
{
lean_object* x_1625; lean_object* x_1626; 
x_1625 = l_Lean_instInhabitedExpr;
x_1626 = l_outOfBounds___rarg(x_1625);
x_1482 = x_1626;
goto block_1560;
}
else
{
lean_object* x_1627; 
x_1627 = lean_array_fget(x_7, x_1623);
x_1482 = x_1627;
goto block_1560;
}
}
}
block_1560:
{
lean_object* x_1483; 
lean_inc(x_1482);
x_1483 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1482, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1483) == 0)
{
uint8_t x_1484; 
x_1484 = !lean_is_exclusive(x_1483);
if (x_1484 == 0)
{
lean_object* x_1485; uint8_t x_1486; 
x_1485 = lean_ctor_get(x_1483, 0);
x_1486 = !lean_is_exclusive(x_1485);
if (x_1486 == 0)
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
x_1487 = lean_ctor_get(x_1485, 0);
x_1488 = lean_ctor_get(x_1485, 1);
x_1489 = lean_ctor_get(x_1488, 2);
lean_inc(x_1489);
lean_inc(x_1489);
x_1490 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1489, x_1487);
if (lean_obj_tag(x_1490) == 0)
{
size_t x_1491; size_t x_1492; uint8_t x_1493; 
x_1491 = lean_ptr_addr(x_1482);
lean_dec(x_1482);
x_1492 = lean_ptr_addr(x_1487);
x_1493 = lean_usize_dec_eq(x_1491, x_1492);
if (x_1493 == 0)
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
lean_dec(x_1);
x_1494 = lean_unsigned_to_nat(0u);
lean_inc(x_1487);
x_1495 = lean_array_set(x_7, x_1494, x_1487);
x_1496 = l_Lean_mkAppN(x_6, x_1495);
lean_dec(x_1495);
x_1497 = lean_ctor_get(x_1488, 0);
lean_inc(x_1497);
x_1498 = lean_ctor_get(x_1488, 1);
lean_inc(x_1498);
lean_dec(x_1488);
lean_inc(x_1496);
x_1499 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1489, x_1487, x_1496);
x_1500 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1500, 0, x_1497);
lean_ctor_set(x_1500, 1, x_1498);
lean_ctor_set(x_1500, 2, x_1499);
lean_ctor_set(x_1485, 1, x_1500);
lean_ctor_set(x_1485, 0, x_1496);
return x_1483;
}
else
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; 
lean_dec(x_7);
lean_dec(x_6);
x_1501 = lean_ctor_get(x_1488, 0);
lean_inc(x_1501);
x_1502 = lean_ctor_get(x_1488, 1);
lean_inc(x_1502);
lean_dec(x_1488);
lean_inc(x_1);
x_1503 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1489, x_1487, x_1);
x_1504 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1504, 0, x_1501);
lean_ctor_set(x_1504, 1, x_1502);
lean_ctor_set(x_1504, 2, x_1503);
lean_ctor_set(x_1485, 1, x_1504);
lean_ctor_set(x_1485, 0, x_1);
return x_1483;
}
}
else
{
lean_object* x_1505; 
lean_dec(x_1489);
lean_dec(x_1487);
lean_dec(x_1482);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1505 = lean_ctor_get(x_1490, 0);
lean_inc(x_1505);
lean_dec(x_1490);
lean_ctor_set(x_1485, 0, x_1505);
return x_1483;
}
}
else
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
x_1506 = lean_ctor_get(x_1485, 0);
x_1507 = lean_ctor_get(x_1485, 1);
lean_inc(x_1507);
lean_inc(x_1506);
lean_dec(x_1485);
x_1508 = lean_ctor_get(x_1507, 2);
lean_inc(x_1508);
lean_inc(x_1508);
x_1509 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1508, x_1506);
if (lean_obj_tag(x_1509) == 0)
{
size_t x_1510; size_t x_1511; uint8_t x_1512; 
x_1510 = lean_ptr_addr(x_1482);
lean_dec(x_1482);
x_1511 = lean_ptr_addr(x_1506);
x_1512 = lean_usize_dec_eq(x_1510, x_1511);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
lean_dec(x_1);
x_1513 = lean_unsigned_to_nat(0u);
lean_inc(x_1506);
x_1514 = lean_array_set(x_7, x_1513, x_1506);
x_1515 = l_Lean_mkAppN(x_6, x_1514);
lean_dec(x_1514);
x_1516 = lean_ctor_get(x_1507, 0);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1507, 1);
lean_inc(x_1517);
lean_dec(x_1507);
lean_inc(x_1515);
x_1518 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1508, x_1506, x_1515);
x_1519 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1519, 0, x_1516);
lean_ctor_set(x_1519, 1, x_1517);
lean_ctor_set(x_1519, 2, x_1518);
x_1520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1520, 0, x_1515);
lean_ctor_set(x_1520, 1, x_1519);
lean_ctor_set(x_1483, 0, x_1520);
return x_1483;
}
else
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
lean_dec(x_7);
lean_dec(x_6);
x_1521 = lean_ctor_get(x_1507, 0);
lean_inc(x_1521);
x_1522 = lean_ctor_get(x_1507, 1);
lean_inc(x_1522);
lean_dec(x_1507);
lean_inc(x_1);
x_1523 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1508, x_1506, x_1);
x_1524 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1524, 0, x_1521);
lean_ctor_set(x_1524, 1, x_1522);
lean_ctor_set(x_1524, 2, x_1523);
x_1525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1525, 0, x_1);
lean_ctor_set(x_1525, 1, x_1524);
lean_ctor_set(x_1483, 0, x_1525);
return x_1483;
}
}
else
{
lean_object* x_1526; lean_object* x_1527; 
lean_dec(x_1508);
lean_dec(x_1506);
lean_dec(x_1482);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1526 = lean_ctor_get(x_1509, 0);
lean_inc(x_1526);
lean_dec(x_1509);
x_1527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1527, 0, x_1526);
lean_ctor_set(x_1527, 1, x_1507);
lean_ctor_set(x_1483, 0, x_1527);
return x_1483;
}
}
}
else
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
x_1528 = lean_ctor_get(x_1483, 0);
x_1529 = lean_ctor_get(x_1483, 1);
lean_inc(x_1529);
lean_inc(x_1528);
lean_dec(x_1483);
x_1530 = lean_ctor_get(x_1528, 0);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_1528, 1);
lean_inc(x_1531);
if (lean_is_exclusive(x_1528)) {
 lean_ctor_release(x_1528, 0);
 lean_ctor_release(x_1528, 1);
 x_1532 = x_1528;
} else {
 lean_dec_ref(x_1528);
 x_1532 = lean_box(0);
}
x_1533 = lean_ctor_get(x_1531, 2);
lean_inc(x_1533);
lean_inc(x_1533);
x_1534 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_Canon_canonElemCore___spec__15(x_1533, x_1530);
if (lean_obj_tag(x_1534) == 0)
{
size_t x_1535; size_t x_1536; uint8_t x_1537; 
x_1535 = lean_ptr_addr(x_1482);
lean_dec(x_1482);
x_1536 = lean_ptr_addr(x_1530);
x_1537 = lean_usize_dec_eq(x_1535, x_1536);
if (x_1537 == 0)
{
lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
lean_dec(x_1);
x_1538 = lean_unsigned_to_nat(0u);
lean_inc(x_1530);
x_1539 = lean_array_set(x_7, x_1538, x_1530);
x_1540 = l_Lean_mkAppN(x_6, x_1539);
lean_dec(x_1539);
x_1541 = lean_ctor_get(x_1531, 0);
lean_inc(x_1541);
x_1542 = lean_ctor_get(x_1531, 1);
lean_inc(x_1542);
lean_dec(x_1531);
lean_inc(x_1540);
x_1543 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1533, x_1530, x_1540);
x_1544 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1544, 0, x_1541);
lean_ctor_set(x_1544, 1, x_1542);
lean_ctor_set(x_1544, 2, x_1543);
if (lean_is_scalar(x_1532)) {
 x_1545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1545 = x_1532;
}
lean_ctor_set(x_1545, 0, x_1540);
lean_ctor_set(x_1545, 1, x_1544);
x_1546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1546, 0, x_1545);
lean_ctor_set(x_1546, 1, x_1529);
return x_1546;
}
else
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; 
lean_dec(x_7);
lean_dec(x_6);
x_1547 = lean_ctor_get(x_1531, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1531, 1);
lean_inc(x_1548);
lean_dec(x_1531);
lean_inc(x_1);
x_1549 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_Canon_canonElemCore___spec__6(x_1533, x_1530, x_1);
x_1550 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1550, 0, x_1547);
lean_ctor_set(x_1550, 1, x_1548);
lean_ctor_set(x_1550, 2, x_1549);
if (lean_is_scalar(x_1532)) {
 x_1551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1551 = x_1532;
}
lean_ctor_set(x_1551, 0, x_1);
lean_ctor_set(x_1551, 1, x_1550);
x_1552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1552, 0, x_1551);
lean_ctor_set(x_1552, 1, x_1529);
return x_1552;
}
}
else
{
lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
lean_dec(x_1533);
lean_dec(x_1530);
lean_dec(x_1482);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1553 = lean_ctor_get(x_1534, 0);
lean_inc(x_1553);
lean_dec(x_1534);
if (lean_is_scalar(x_1532)) {
 x_1554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1554 = x_1532;
}
lean_ctor_set(x_1554, 0, x_1553);
lean_ctor_set(x_1554, 1, x_1531);
x_1555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1555, 0, x_1554);
lean_ctor_set(x_1555, 1, x_1529);
return x_1555;
}
}
}
else
{
uint8_t x_1556; 
lean_dec(x_1482);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_1556 = !lean_is_exclusive(x_1483);
if (x_1556 == 0)
{
return x_1483;
}
else
{
lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; 
x_1557 = lean_ctor_get(x_1483, 0);
x_1558 = lean_ctor_get(x_1483, 1);
lean_inc(x_1558);
lean_inc(x_1557);
lean_dec(x_1483);
x_1559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1559, 0, x_1557);
lean_ctor_set(x_1559, 1, x_1558);
return x_1559;
}
}
}
block_1615:
{
lean_object* x_1562; 
lean_dec(x_1561);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_6);
x_1562 = l_Lean_Meta_getFunInfo(x_6, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1562) == 0)
{
lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; uint8_t x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; 
x_1563 = lean_ctor_get(x_1562, 0);
lean_inc(x_1563);
x_1564 = lean_ctor_get(x_1562, 1);
lean_inc(x_1564);
lean_dec(x_1562);
x_1565 = lean_ctor_get(x_1563, 0);
lean_inc(x_1565);
lean_dec(x_1563);
x_1566 = lean_array_get_size(x_7);
x_1567 = lean_unsigned_to_nat(0u);
x_1568 = lean_unsigned_to_nat(1u);
lean_inc(x_1566);
x_1569 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1569, 0, x_1567);
lean_ctor_set(x_1569, 1, x_1566);
lean_ctor_set(x_1569, 2, x_1568);
x_1570 = 0;
x_1571 = lean_box(x_1570);
lean_inc(x_7);
x_1572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1572, 0, x_7);
lean_ctor_set(x_1572, 1, x_1571);
x_1573 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
lean_inc(x_1569);
lean_inc(x_6);
x_1574 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_1573, x_1565, x_1566, x_1569, x_1569, x_1572, x_1567, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_1564);
if (lean_obj_tag(x_1574) == 0)
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; uint8_t x_1578; 
x_1575 = lean_ctor_get(x_1574, 0);
lean_inc(x_1575);
x_1576 = lean_ctor_get(x_1575, 0);
lean_inc(x_1576);
x_1577 = lean_ctor_get(x_1576, 1);
lean_inc(x_1577);
x_1578 = lean_unbox(x_1577);
lean_dec(x_1577);
if (x_1578 == 0)
{
uint8_t x_1579; 
lean_dec(x_1576);
lean_dec(x_6);
x_1579 = !lean_is_exclusive(x_1574);
if (x_1579 == 0)
{
lean_object* x_1580; uint8_t x_1581; 
x_1580 = lean_ctor_get(x_1574, 0);
lean_dec(x_1580);
x_1581 = !lean_is_exclusive(x_1575);
if (x_1581 == 0)
{
lean_object* x_1582; 
x_1582 = lean_ctor_get(x_1575, 0);
lean_dec(x_1582);
lean_ctor_set(x_1575, 0, x_1);
return x_1574;
}
else
{
lean_object* x_1583; lean_object* x_1584; 
x_1583 = lean_ctor_get(x_1575, 1);
lean_inc(x_1583);
lean_dec(x_1575);
x_1584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1584, 0, x_1);
lean_ctor_set(x_1584, 1, x_1583);
lean_ctor_set(x_1574, 0, x_1584);
return x_1574;
}
}
else
{
lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; 
x_1585 = lean_ctor_get(x_1574, 1);
lean_inc(x_1585);
lean_dec(x_1574);
x_1586 = lean_ctor_get(x_1575, 1);
lean_inc(x_1586);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1587 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1587 = lean_box(0);
}
if (lean_is_scalar(x_1587)) {
 x_1588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1588 = x_1587;
}
lean_ctor_set(x_1588, 0, x_1);
lean_ctor_set(x_1588, 1, x_1586);
x_1589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1589, 0, x_1588);
lean_ctor_set(x_1589, 1, x_1585);
return x_1589;
}
}
else
{
uint8_t x_1590; 
lean_dec(x_1);
x_1590 = !lean_is_exclusive(x_1574);
if (x_1590 == 0)
{
lean_object* x_1591; uint8_t x_1592; 
x_1591 = lean_ctor_get(x_1574, 0);
lean_dec(x_1591);
x_1592 = !lean_is_exclusive(x_1575);
if (x_1592 == 0)
{
lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
x_1593 = lean_ctor_get(x_1575, 0);
lean_dec(x_1593);
x_1594 = lean_ctor_get(x_1576, 0);
lean_inc(x_1594);
lean_dec(x_1576);
x_1595 = l_Lean_mkAppN(x_6, x_1594);
lean_dec(x_1594);
lean_ctor_set(x_1575, 0, x_1595);
return x_1574;
}
else
{
lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1596 = lean_ctor_get(x_1575, 1);
lean_inc(x_1596);
lean_dec(x_1575);
x_1597 = lean_ctor_get(x_1576, 0);
lean_inc(x_1597);
lean_dec(x_1576);
x_1598 = l_Lean_mkAppN(x_6, x_1597);
lean_dec(x_1597);
x_1599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1599, 0, x_1598);
lean_ctor_set(x_1599, 1, x_1596);
lean_ctor_set(x_1574, 0, x_1599);
return x_1574;
}
}
else
{
lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
x_1600 = lean_ctor_get(x_1574, 1);
lean_inc(x_1600);
lean_dec(x_1574);
x_1601 = lean_ctor_get(x_1575, 1);
lean_inc(x_1601);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1602 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1602 = lean_box(0);
}
x_1603 = lean_ctor_get(x_1576, 0);
lean_inc(x_1603);
lean_dec(x_1576);
x_1604 = l_Lean_mkAppN(x_6, x_1603);
lean_dec(x_1603);
if (lean_is_scalar(x_1602)) {
 x_1605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1605 = x_1602;
}
lean_ctor_set(x_1605, 0, x_1604);
lean_ctor_set(x_1605, 1, x_1601);
x_1606 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1606, 0, x_1605);
lean_ctor_set(x_1606, 1, x_1600);
return x_1606;
}
}
}
else
{
uint8_t x_1607; 
lean_dec(x_6);
lean_dec(x_1);
x_1607 = !lean_is_exclusive(x_1574);
if (x_1607 == 0)
{
return x_1574;
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; 
x_1608 = lean_ctor_get(x_1574, 0);
x_1609 = lean_ctor_get(x_1574, 1);
lean_inc(x_1609);
lean_inc(x_1608);
lean_dec(x_1574);
x_1610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1610, 0, x_1608);
lean_ctor_set(x_1610, 1, x_1609);
return x_1610;
}
}
}
else
{
uint8_t x_1611; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1611 = !lean_is_exclusive(x_1562);
if (x_1611 == 0)
{
return x_1562;
}
else
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; 
x_1612 = lean_ctor_get(x_1562, 0);
x_1613 = lean_ctor_get(x_1562, 1);
lean_inc(x_1613);
lean_inc(x_1612);
lean_dec(x_1562);
x_1614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1614, 0, x_1612);
lean_ctor_set(x_1614, 1, x_1613);
return x_1614;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_1, x_33);
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
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_38);
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
x_58 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_33);
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
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_1, x_84);
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
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_89);
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
x_109 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_84);
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
x_138 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_1, x_137);
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
x_149 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__2(x_142);
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
x_164 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__6(x_1, x_2, x_137);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_4);
x_16 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_17 = lean_ptr_addr(x_5);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_3);
x_19 = l_Lean_Expr_forallE___override(x_1, x_5, x_7, x_4);
x_20 = lean_apply_8(x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_22 = lean_ptr_addr(x_7);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = l_Lean_Expr_forallE___override(x_1, x_5, x_7, x_4);
x_25 = lean_apply_8(x_6, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_4, x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_27 = l_Lean_Expr_forallE___override(x_1, x_5, x_7, x_4);
x_28 = lean_apply_8(x_6, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_29 = lean_apply_8(x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Canon", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.Canon.canonImpl.visit", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1;
x_2 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(192u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_14);
x_16 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc_n(x_1, 2);
x_20 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11(x_1, x_2, x_3, x_4, x_5, x_1, x_17, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_23, x_7, x_24, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1___boxed), 9, 1);
lean_closure_set(x_34, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_31);
x_35 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_40 == 0)
{
lean_object* x_41; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_32);
x_41 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_32, x_7, x_39, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(x_30, x_31, x_32, x_33, x_38, x_34, x_44, x_7, x_45, x_9, x_10, x_11, x_12, x_43);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_inc(x_32);
x_51 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(x_30, x_31, x_32, x_33, x_38, x_34, x_32, x_7, x_39, x_9, x_10, x_11, x_12, x_37);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
return x_35;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_35, 0);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_35);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
default: 
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_57 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7(x_56, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__1(x_1, x_60, x_7, x_61, x_9, x_10, x_11, x_12, x_59);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = lean_alloc_closure((void*)(l_StateT_lift___rarg), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_array_get_size(x_15);
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
x_33 = lean_array_uget(x_15, x_32);
lean_dec(x_15);
x_34 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(x_1, x_33);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_12);
lean_free_object(x_10);
x_35 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2;
x_36 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1;
x_37 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2;
x_38 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
x_39 = lean_box(0);
x_40 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(x_1, x_35, x_36, x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 0, x_41);
return x_10;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_10, 1);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_dec(x_12);
x_44 = lean_array_get_size(x_43);
x_45 = lean_ptr_addr(x_1);
x_46 = lean_usize_to_uint64(x_45);
x_47 = 11;
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 32;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = 16;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = lean_uint64_to_usize(x_54);
x_56 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_57 = 1;
x_58 = lean_usize_sub(x_56, x_57);
x_59 = lean_usize_land(x_55, x_58);
x_60 = lean_array_uget(x_43, x_59);
lean_dec(x_43);
x_61 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(x_1, x_60);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_10);
x_62 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2;
x_63 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1;
x_64 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2;
x_65 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
x_66 = lean_box(0);
x_67 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(x_1, x_62, x_63, x_64, x_65, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
lean_ctor_set(x_10, 0, x_69);
return x_10;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_70 = lean_ctor_get(x_10, 0);
x_71 = lean_ctor_get(x_10, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_10);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_array_get_size(x_72);
x_75 = lean_ptr_addr(x_1);
x_76 = lean_usize_to_uint64(x_75);
x_77 = 11;
x_78 = lean_uint64_mix_hash(x_76, x_77);
x_79 = 32;
x_80 = lean_uint64_shift_right(x_78, x_79);
x_81 = lean_uint64_xor(x_78, x_80);
x_82 = 16;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_87 = 1;
x_88 = lean_usize_sub(x_86, x_87);
x_89 = lean_usize_land(x_85, x_88);
x_90 = lean_array_uget(x_72, x_89);
lean_dec(x_72);
x_91 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(x_1, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_73);
x_92 = l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2;
x_93 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1;
x_94 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2;
x_95 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1;
x_96 = lean_box(0);
x_97 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(x_1, x_92, x_93, x_94, x_95, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_71);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
lean_dec(x_91);
if (lean_is_scalar(x_73)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_73;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_4);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_71);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isApp(x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isForall(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__2(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
lean_object* x_23; 
x_23 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__12(x_1, x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3;
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_Canon_canonElemCore___spec__4(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_14, x_3, x_4, x_5, x_6, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
lean_inc(x_1);
x_22 = l_Lean_MessageData_ofExpr(x_1);
x_23 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_23);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_23);
x_24 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_8, x_9, x_20, x_3, x_4, x_5, x_6, x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_27, x_3, x_4, x_5, x_6, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
lean_inc(x_1);
x_30 = l_Lean_MessageData_ofExpr(x_1);
x_31 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_31);
lean_ctor_set(x_9, 0, x_32);
x_33 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_8, x_9, x_29, x_3, x_4, x_5, x_6, x_17);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_36, x_3, x_4, x_5, x_6, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_40 = x_10;
} else {
 lean_dec_ref(x_10);
 x_40 = lean_box(0);
}
lean_inc(x_1);
x_41 = l_Lean_MessageData_ofExpr(x_1);
x_42 = l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10;
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(7, 2, 0);
} else {
 x_43 = x_40;
 lean_ctor_set_tag(x_43, 7);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_addTrace___at_Lean_Meta_Grind_Canon_canonElemCore___spec__5(x_8, x_44, x_39, x_3, x_4, x_5, x_6, x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_48, x_3, x_4, x_5, x_6, x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canon___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Canon_canon___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
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
l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___closed__1 = _init_l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_CanonElemKind_noConfusion___rarg___closed__1);
l_Lean_Meta_Grind_Canon_instBEqCanonElemKind___closed__1 = _init_l_Lean_Meta_Grind_Canon_instBEqCanonElemKind___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instBEqCanonElemKind___closed__1);
l_Lean_Meta_Grind_Canon_instBEqCanonElemKind = _init_l_Lean_Meta_Grind_Canon_instBEqCanonElemKind();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instBEqCanonElemKind);
l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__1 = _init_l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__1);
l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__2 = _init_l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__2);
l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__3 = _init_l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_CanonElemKind_explain___closed__3);
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
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__9);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__10);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___lambda__1___closed__11();
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__1);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__2);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__3);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__4);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__5);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__6 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__6);
l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7 = _init_l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonElemCore___spec__10___closed__7);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__1);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__2);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__3);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__4);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__5);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__2___closed__6);
l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonElemCore___lambda__3___closed__1);
l_Lean_Meta_Grind_Canon_canonInst___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonInst___closed__1();
l_Lean_Meta_Grind_Canon_canonImplicit___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImplicit___closed__1();
l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult = _init_l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult();
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__1);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__2);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__3);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__4);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__5);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__6);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__7);
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8 = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__8);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__1);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__2);
l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3 = _init_l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__7___closed__3);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__2);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__3);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__4);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__5);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__10___lambda__3___closed__6);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_Canon_canonImpl_visit___spec__11___closed__5);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__1);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__2);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__3);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__4);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__3___closed__5);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__1);
l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2 = _init_l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl_visit___lambda__4___closed__2);
l_Lean_Meta_Grind_Canon_canonImpl___closed__1 = _init_l_Lean_Meta_Grind_Canon_canonImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_canonImpl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

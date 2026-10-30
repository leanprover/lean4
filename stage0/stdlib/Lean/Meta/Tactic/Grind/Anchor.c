// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Anchor
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_instDecidableEqUInt64___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_anchorPrefixToString(lean_object*, uint64_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_anchorsEnabled___redArg(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_sub(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0;
static const lean_array_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_getAnchor___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_getAnchor___boxed__const__1 = (const lean_object*)&l_Lean_Meta_Grind_getAnchor___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor = (const lean_object*)&l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "anchor"};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(168, 155, 228, 98, 168, 72, 115, 174)}};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(lean_object* v_n_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = l_Lean_Name_hasMacroScopes(v_n_1_);
if (v___x_2_ == 0)
{
uint8_t v___x_3_; 
lean_inc(v_n_1_);
v___x_3_ = l_Lean_Name_isInaccessibleUserName(v_n_1_);
if (v___x_3_ == 0)
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Name_isImplementationDetail(v_n_1_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = l_Lean_isPrivateName(v_n_1_);
if (v___x_5_ == 0)
{
uint8_t v___x_6_; 
v___x_6_ = l_Lean_Name_isInternal(v_n_1_);
if (v___x_6_ == 0)
{
if (lean_obj_tag(v_n_1_) == 0)
{
uint64_t v___x_7_; 
v___x_7_ = 1723ULL;
return v___x_7_;
}
else
{
uint64_t v_hash_8_; 
v_hash_8_ = lean_ctor_get_uint64(v_n_1_, sizeof(void*)*2);
lean_dec(v_n_1_);
return v_hash_8_;
}
}
else
{
uint64_t v___x_9_; 
lean_dec(v_n_1_);
v___x_9_ = 0ULL;
return v___x_9_;
}
}
else
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_privateToUserName(v_n_1_);
if (lean_obj_tag(v___x_10_) == 0)
{
uint64_t v___x_11_; 
v___x_11_ = 1723ULL;
return v___x_11_;
}
else
{
uint64_t v_hash_12_; 
v_hash_12_ = lean_ctor_get_uint64(v___x_10_, sizeof(void*)*2);
lean_dec(v___x_10_);
return v_hash_12_;
}
}
}
else
{
uint64_t v___x_13_; 
lean_dec(v_n_1_);
v___x_13_ = 0ULL;
return v___x_13_;
}
}
else
{
uint64_t v___x_14_; 
lean_dec(v_n_1_);
v___x_14_ = 0ULL;
return v___x_14_;
}
}
else
{
uint64_t v___x_15_; 
lean_dec(v_n_1_);
v___x_15_ = 0ULL;
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(lean_object* v_n_16_){
_start:
{
uint64_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_16_);
v_r_18_ = lean_box_uint64(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t v_a_19_, uint64_t v_b_20_){
_start:
{
uint64_t v___x_21_; uint8_t v___x_22_; 
v___x_21_ = 0ULL;
v___x_22_ = lean_uint64_dec_eq(v_a_19_, v___x_21_);
if (v___x_22_ == 0)
{
uint8_t v___x_23_; 
v___x_23_ = lean_uint64_dec_eq(v_b_20_, v___x_21_);
if (v___x_23_ == 0)
{
uint64_t v___x_24_; 
v___x_24_ = lean_uint64_mix_hash(v_a_19_, v_b_20_);
return v___x_24_;
}
else
{
return v_a_19_;
}
}
else
{
return v_b_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
uint64_t v_a_boxed_27_; uint64_t v_b_boxed_28_; uint64_t v_res_29_; lean_object* v_r_30_; 
v_a_boxed_27_ = lean_unbox_uint64(v_a_25_);
lean_dec_ref(v_a_25_);
v_b_boxed_28_ = lean_unbox_uint64(v_b_26_);
lean_dec_ref(v_b_26_);
v_res_29_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_a_boxed_27_, v_b_boxed_28_);
v_r_30_ = lean_box_uint64(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg(lean_object* v_declName_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; lean_object* v_env_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_34_ = lean_st_ref_get(v___y_32_);
v_env_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc_ref(v_env_35_);
lean_dec(v___x_34_);
v___x_36_ = l_Lean_Meta_isMatcherCore(v_env_35_, v_declName_31_);
v___x_37_ = lean_box(v___x_36_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg___boxed(lean_object* v_declName_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg(v_declName_39_, v___y_40_);
lean_dec(v___y_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4(lean_object* v_declName_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg(v_declName_43_, v___y_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___boxed(lean_object* v_declName_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4(v_declName_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_ks_71_; lean_object* v_vs_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_98_; 
v_ks_71_ = lean_ctor_get(v_x_67_, 0);
v_vs_72_ = lean_ctor_get(v_x_67_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_98_ == 0)
{
v___x_74_ = v_x_67_;
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_vs_72_);
lean_inc(v_ks_71_);
lean_dec(v_x_67_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = lean_array_get_size(v_ks_71_);
v___x_77_ = lean_nat_dec_lt(v_x_68_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
lean_dec(v_x_68_);
v___x_78_ = lean_array_push(v_ks_71_, v_x_69_);
v___x_79_ = lean_array_push(v_vs_72_, v_x_70_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v___x_79_);
lean_ctor_set(v___x_74_, 0, v___x_78_);
v___x_81_ = v___x_74_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
else
{
lean_object* v_k_x27_83_; size_t v___x_84_; size_t v___x_85_; uint8_t v___x_86_; 
v_k_x27_83_ = lean_array_fget_borrowed(v_ks_71_, v_x_68_);
v___x_84_ = lean_ptr_addr(v_x_69_);
v___x_85_ = lean_ptr_addr(v_k_x27_83_);
v___x_86_ = lean_usize_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_88_; 
if (v_isShared_75_ == 0)
{
v___x_88_ = v___x_74_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_ks_71_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_vs_72_);
v___x_88_ = v_reuseFailAlloc_92_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = lean_nat_add(v_x_68_, v___x_89_);
lean_dec(v_x_68_);
v_x_67_ = v___x_88_;
v_x_68_ = v___x_90_;
goto _start;
}
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_93_ = lean_array_fset(v_ks_71_, v_x_68_, v_x_69_);
v___x_94_ = lean_array_fset(v_vs_72_, v_x_68_, v_x_70_);
lean_dec(v_x_68_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v___x_94_);
lean_ctor_set(v___x_74_, 0, v___x_93_);
v___x_96_ = v___x_74_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2___redArg(lean_object* v_n_99_, lean_object* v_k_100_, lean_object* v_v_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7___redArg(v_n_99_, v___x_102_, v_k_100_, v_v_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(lean_object* v_x_105_, size_t v_x_106_, size_t v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v_es_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v_j_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_es_110_ = lean_ctor_get(v_x_105_, 0);
v___x_111_ = ((size_t)31ULL);
v___x_112_ = lean_usize_land(v_x_106_, v___x_111_);
v_j_113_ = lean_usize_to_nat(v___x_112_);
v___x_114_ = lean_array_get_size(v_es_110_);
v___x_115_ = lean_nat_dec_lt(v_j_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_dec(v_j_113_);
lean_dec(v_x_109_);
lean_dec_ref(v_x_108_);
return v_x_105_;
}
else
{
lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_156_; 
lean_inc_ref(v_es_110_);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v_x_105_, 0);
lean_dec(v_unused_157_);
v___x_117_ = v_x_105_;
v_isShared_118_ = v_isSharedCheck_156_;
goto v_resetjp_116_;
}
else
{
lean_dec(v_x_105_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_156_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_v_119_; lean_object* v___x_120_; lean_object* v_xs_x27_121_; lean_object* v___y_123_; 
v_v_119_ = lean_array_fget(v_es_110_, v_j_113_);
v___x_120_ = lean_box(0);
v_xs_x27_121_ = lean_array_fset(v_es_110_, v_j_113_, v___x_120_);
switch(lean_obj_tag(v_v_119_))
{
case 0:
{
lean_object* v_key_128_; lean_object* v_val_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_141_; 
v_key_128_ = lean_ctor_get(v_v_119_, 0);
v_val_129_ = lean_ctor_get(v_v_119_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_v_119_);
if (v_isSharedCheck_141_ == 0)
{
v___x_131_ = v_v_119_;
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_val_129_);
lean_inc(v_key_128_);
lean_dec(v_v_119_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_141_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
size_t v___x_133_; size_t v___x_134_; uint8_t v___x_135_; 
v___x_133_ = lean_ptr_addr(v_x_108_);
v___x_134_ = lean_ptr_addr(v_key_128_);
v___x_135_ = lean_usize_dec_eq(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_del_object(v___x_131_);
v___x_136_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_128_, v_val_129_, v_x_108_, v_x_109_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
v___y_123_ = v___x_137_;
goto v___jp_122_;
}
else
{
lean_object* v___x_139_; 
lean_dec(v_val_129_);
lean_dec(v_key_128_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_x_109_);
lean_ctor_set(v___x_131_, 0, v_x_108_);
v___x_139_ = v___x_131_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_x_108_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_x_109_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
v___y_123_ = v___x_139_;
goto v___jp_122_;
}
}
}
}
case 1:
{
lean_object* v_node_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_154_; 
v_node_142_ = lean_ctor_get(v_v_119_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_v_119_);
if (v_isSharedCheck_154_ == 0)
{
v___x_144_ = v_v_119_;
v_isShared_145_ = v_isSharedCheck_154_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_node_142_);
lean_dec(v_v_119_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_154_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_146_ = ((size_t)5ULL);
v___x_147_ = lean_usize_shift_right(v_x_106_, v___x_146_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_x_107_, v___x_148_);
v___x_150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(v_node_142_, v___x_147_, v___x_149_, v_x_108_, v_x_109_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_150_);
v___x_152_ = v___x_144_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v___y_123_ = v___x_152_;
goto v___jp_122_;
}
}
}
default: 
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_x_108_);
lean_ctor_set(v___x_155_, 1, v_x_109_);
v___y_123_ = v___x_155_;
goto v___jp_122_;
}
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_array_fset(v_xs_x27_121_, v_j_113_, v___y_123_);
lean_dec(v_j_113_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_124_);
v___x_126_ = v___x_117_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
else
{
lean_object* v_ks_158_; lean_object* v_vs_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_177_; 
v_ks_158_ = lean_ctor_get(v_x_105_, 0);
v_vs_159_ = lean_ctor_get(v_x_105_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_177_ == 0)
{
v___x_161_ = v_x_105_;
v_isShared_162_ = v_isSharedCheck_177_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_vs_159_);
lean_inc(v_ks_158_);
lean_dec(v_x_105_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_177_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_ks_158_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_vs_159_);
v___x_164_ = v_reuseFailAlloc_176_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v_newNode_165_; size_t v___x_166_; uint8_t v___x_167_; 
v_newNode_165_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2___redArg(v___x_164_, v_x_108_, v_x_109_);
v___x_166_ = ((size_t)7ULL);
v___x_167_ = lean_usize_dec_le(v___x_166_, v_x_107_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_168_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_165_);
v___x_169_ = lean_unsigned_to_nat(4u);
v___x_170_ = lean_nat_dec_lt(v___x_168_, v___x_169_);
lean_dec(v___x_168_);
if (v___x_170_ == 0)
{
lean_object* v_ks_171_; lean_object* v_vs_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_ks_171_ = lean_ctor_get(v_newNode_165_, 0);
lean_inc_ref(v_ks_171_);
v_vs_172_ = lean_ctor_get(v_newNode_165_, 1);
lean_inc_ref(v_vs_172_);
lean_dec_ref(v_newNode_165_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___closed__0);
v___x_175_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg(v_x_107_, v_ks_171_, v_vs_172_, v___x_173_, v___x_174_);
lean_dec_ref(v_vs_172_);
lean_dec_ref(v_ks_171_);
return v___x_175_;
}
else
{
return v_newNode_165_;
}
}
else
{
return v_newNode_165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg(size_t v_depth_178_, lean_object* v_keys_179_, lean_object* v_vals_180_, lean_object* v_i_181_, lean_object* v_entries_182_){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_array_get_size(v_keys_179_);
v___x_184_ = lean_nat_dec_lt(v_i_181_, v___x_183_);
if (v___x_184_ == 0)
{
lean_dec(v_i_181_);
return v_entries_182_;
}
else
{
lean_object* v_k_185_; lean_object* v_v_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; uint64_t v___x_190_; size_t v_h_191_; size_t v___x_192_; lean_object* v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v_h_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_k_185_ = lean_array_fget_borrowed(v_keys_179_, v_i_181_);
v_v_186_ = lean_array_fget_borrowed(v_vals_180_, v_i_181_);
v___x_187_ = lean_ptr_addr(v_k_185_);
v___x_188_ = ((size_t)3ULL);
v___x_189_ = lean_usize_shift_right(v___x_187_, v___x_188_);
v___x_190_ = lean_usize_to_uint64(v___x_189_);
v_h_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = ((size_t)5ULL);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v_depth_178_, v___x_194_);
v___x_196_ = lean_usize_mul(v___x_192_, v___x_195_);
v_h_197_ = lean_usize_shift_right(v_h_191_, v___x_196_);
v___x_198_ = lean_nat_add(v_i_181_, v___x_193_);
lean_dec(v_i_181_);
lean_inc(v_v_186_);
lean_inc(v_k_185_);
v___x_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(v_entries_182_, v_h_197_, v_depth_178_, v_k_185_, v_v_186_);
v_i_181_ = v___x_198_;
v_entries_182_ = v___x_199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_201_, lean_object* v_keys_202_, lean_object* v_vals_203_, lean_object* v_i_204_, lean_object* v_entries_205_){
_start:
{
size_t v_depth_boxed_206_; lean_object* v_res_207_; 
v_depth_boxed_206_ = lean_unbox_usize(v_depth_201_);
lean_dec(v_depth_201_);
v_res_207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg(v_depth_boxed_206_, v_keys_202_, v_vals_203_, v_i_204_, v_entries_205_);
lean_dec_ref(v_vals_203_);
lean_dec_ref(v_keys_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
size_t v_x_34973__boxed_213_; size_t v_x_34974__boxed_214_; lean_object* v_res_215_; 
v_x_34973__boxed_213_ = lean_unbox_usize(v_x_209_);
lean_dec(v_x_209_);
v_x_34974__boxed_214_ = lean_unbox_usize(v_x_210_);
lean_dec(v_x_210_);
v_res_215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(v_x_208_, v_x_34973__boxed_213_, v_x_34974__boxed_214_, v_x_211_, v_x_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0___redArg(lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; uint64_t v___x_222_; size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v___x_219_ = lean_ptr_addr(v_x_217_);
v___x_220_ = ((size_t)3ULL);
v___x_221_ = lean_usize_shift_right(v___x_219_, v___x_220_);
v___x_222_ = lean_usize_to_uint64(v___x_221_);
v___x_223_ = lean_uint64_to_usize(v___x_222_);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(v_x_216_, v___x_223_, v___x_224_, v_x_217_, v_x_218_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg(lean_object* v_keys_226_, lean_object* v_vals_227_, lean_object* v_i_228_, lean_object* v_k_229_){
_start:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_get_size(v_keys_226_);
v___x_231_ = lean_nat_dec_lt(v_i_228_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec(v_i_228_);
v___x_232_ = lean_box(0);
return v___x_232_;
}
else
{
lean_object* v_k_x27_233_; size_t v___x_234_; size_t v___x_235_; uint8_t v___x_236_; 
v_k_x27_233_ = lean_array_fget_borrowed(v_keys_226_, v_i_228_);
v___x_234_ = lean_ptr_addr(v_k_229_);
v___x_235_ = lean_ptr_addr(v_k_x27_233_);
v___x_236_ = lean_usize_dec_eq(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_i_228_, v___x_237_);
lean_dec(v_i_228_);
v_i_228_ = v___x_238_;
goto _start;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_array_fget_borrowed(v_vals_227_, v_i_228_);
lean_dec(v_i_228_);
lean_inc(v___x_240_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_keys_242_, lean_object* v_vals_243_, lean_object* v_i_244_, lean_object* v_k_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg(v_keys_242_, v_vals_243_, v_i_244_, v_k_245_);
lean_dec_ref(v_k_245_);
lean_dec_ref(v_vals_243_);
lean_dec_ref(v_keys_242_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg(lean_object* v_x_247_, size_t v_x_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_object* v_es_250_; lean_object* v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v_j_254_; lean_object* v___x_255_; 
v_es_250_ = lean_ctor_get(v_x_247_, 0);
v___x_251_ = lean_box(2);
v___x_252_ = ((size_t)31ULL);
v___x_253_ = lean_usize_land(v_x_248_, v___x_252_);
v_j_254_ = lean_usize_to_nat(v___x_253_);
v___x_255_ = lean_array_get_borrowed(v___x_251_, v_es_250_, v_j_254_);
lean_dec(v_j_254_);
switch(lean_obj_tag(v___x_255_))
{
case 0:
{
lean_object* v_key_256_; lean_object* v_val_257_; size_t v___x_258_; size_t v___x_259_; uint8_t v___x_260_; 
v_key_256_ = lean_ctor_get(v___x_255_, 0);
v_val_257_ = lean_ctor_get(v___x_255_, 1);
v___x_258_ = lean_ptr_addr(v_x_249_);
v___x_259_ = lean_ptr_addr(v_key_256_);
v___x_260_ = lean_usize_dec_eq(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v___x_262_; 
lean_inc(v_val_257_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v_val_257_);
return v___x_262_;
}
}
case 1:
{
lean_object* v_node_263_; size_t v___x_264_; size_t v___x_265_; 
v_node_263_ = lean_ctor_get(v___x_255_, 0);
v___x_264_ = ((size_t)5ULL);
v___x_265_ = lean_usize_shift_right(v_x_248_, v___x_264_);
v_x_247_ = v_node_263_;
v_x_248_ = v___x_265_;
goto _start;
}
default: 
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
}
else
{
lean_object* v_ks_268_; lean_object* v_vs_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_ks_268_ = lean_ctor_get(v_x_247_, 0);
v_vs_269_ = lean_ctor_get(v_x_247_, 1);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg(v_ks_268_, v_vs_269_, v___x_270_, v_x_249_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg___boxed(lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
size_t v_x_35174__boxed_275_; lean_object* v_res_276_; 
v_x_35174__boxed_275_ = lean_unbox_usize(v_x_273_);
lean_dec(v_x_273_);
v_res_276_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg(v_x_272_, v_x_35174__boxed_275_, v_x_274_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; uint64_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; 
v___x_279_ = lean_ptr_addr(v_x_278_);
v___x_280_ = ((size_t)3ULL);
v___x_281_ = lean_usize_shift_right(v___x_279_, v___x_280_);
v___x_282_ = lean_usize_to_uint64(v___x_281_);
v___x_283_ = lean_uint64_to_usize(v___x_282_);
v___x_284_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg(v_x_277_, v___x_283_, v_x_278_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg___boxed(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg(v_x_285_, v_x_286_);
lean_dec_ref(v_x_286_);
lean_dec_ref(v_x_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg(lean_object* v_keys_288_, lean_object* v_vals_289_, lean_object* v_i_290_, lean_object* v_k_291_){
_start:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_array_get_size(v_keys_288_);
v___x_293_ = lean_nat_dec_lt(v_i_290_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec(v_i_290_);
v___x_294_ = lean_box(0);
return v___x_294_;
}
else
{
lean_object* v_k_x27_295_; uint8_t v___x_296_; 
v_k_x27_295_ = lean_array_fget_borrowed(v_keys_288_, v_i_290_);
v___x_296_ = l_Lean_instBEqFVarId_beq(v_k_291_, v_k_x27_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_i_290_, v___x_297_);
lean_dec(v_i_290_);
v_i_290_ = v___x_298_;
goto _start;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_array_fget_borrowed(v_vals_289_, v_i_290_);
lean_dec(v_i_290_);
lean_inc(v___x_300_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_keys_302_, lean_object* v_vals_303_, lean_object* v_i_304_, lean_object* v_k_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg(v_keys_302_, v_vals_303_, v_i_304_, v_k_305_);
lean_dec(v_k_305_);
lean_dec_ref(v_vals_303_);
lean_dec_ref(v_keys_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg(lean_object* v_x_307_, size_t v_x_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_es_310_; lean_object* v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v_j_314_; lean_object* v___x_315_; 
v_es_310_ = lean_ctor_get(v_x_307_, 0);
v___x_311_ = lean_box(2);
v___x_312_ = ((size_t)31ULL);
v___x_313_ = lean_usize_land(v_x_308_, v___x_312_);
v_j_314_ = lean_usize_to_nat(v___x_313_);
v___x_315_ = lean_array_get_borrowed(v___x_311_, v_es_310_, v_j_314_);
lean_dec(v_j_314_);
switch(lean_obj_tag(v___x_315_))
{
case 0:
{
lean_object* v_key_316_; lean_object* v_val_317_; uint8_t v___x_318_; 
v_key_316_ = lean_ctor_get(v___x_315_, 0);
v_val_317_ = lean_ctor_get(v___x_315_, 1);
v___x_318_ = l_Lean_instBEqFVarId_beq(v_x_309_, v_key_316_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
return v___x_319_;
}
else
{
lean_object* v___x_320_; 
lean_inc(v_val_317_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_val_317_);
return v___x_320_;
}
}
case 1:
{
lean_object* v_node_321_; size_t v___x_322_; size_t v___x_323_; 
v_node_321_ = lean_ctor_get(v___x_315_, 0);
v___x_322_ = ((size_t)5ULL);
v___x_323_ = lean_usize_shift_right(v_x_308_, v___x_322_);
v_x_307_ = v_node_321_;
v_x_308_ = v___x_323_;
goto _start;
}
default: 
{
lean_object* v___x_325_; 
v___x_325_ = lean_box(0);
return v___x_325_;
}
}
}
else
{
lean_object* v_ks_326_; lean_object* v_vs_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_ks_326_ = lean_ctor_get(v_x_307_, 0);
v_vs_327_ = lean_ctor_get(v_x_307_, 1);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg(v_ks_326_, v_vs_327_, v___x_328_, v_x_309_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg___boxed(lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
size_t v_x_35261__boxed_333_; lean_object* v_res_334_; 
v_x_35261__boxed_333_ = lean_unbox_usize(v_x_331_);
lean_dec(v_x_331_);
v_res_334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg(v_x_330_, v_x_35261__boxed_333_, v_x_332_);
lean_dec(v_x_332_);
lean_dec_ref(v_x_330_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg(lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
uint64_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = l_Lean_instHashableFVarId_hash(v_x_336_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg(v_x_335_, v___x_338_, v_x_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg___boxed(lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg(v_x_340_, v_x_341_);
lean_dec(v_x_341_);
lean_dec_ref(v_x_340_);
return v_res_342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v_dummy_344_; 
v___x_343_ = lean_box(0);
v_dummy_344_ = l_Lean_Expr_sort___override(v___x_343_);
return v_dummy_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_pinfos_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; 
if (lean_obj_tag(v_x_347_) == 5)
{
lean_object* v_fn_392_; lean_object* v_arg_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_fn_392_ = lean_ctor_get(v_x_347_, 0);
lean_inc_ref(v_fn_392_);
v_arg_393_ = lean_ctor_get(v_x_347_, 1);
lean_inc_ref(v_arg_393_);
lean_dec_ref_known(v_x_347_, 2);
v___x_394_ = lean_array_set(v_x_348_, v_x_349_, v_arg_393_);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_sub(v_x_349_, v___x_395_);
lean_dec(v_x_349_);
v_x_347_ = v_fn_392_;
v_x_348_ = v___x_394_;
v_x_349_ = v___x_396_;
goto _start;
}
else
{
uint8_t v___x_398_; 
lean_dec(v_x_349_);
v___x_398_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_347_);
if (v___x_398_ == 0)
{
goto v___jp_377_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = lean_array_get_size(v_x_348_);
v___x_400_ = lean_unsigned_to_nat(2u);
v___x_401_ = lean_nat_dec_eq(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
goto v___jp_377_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_x_347_);
v___x_402_ = l_Lean_instInhabitedExpr;
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_array_get(v___x_402_, v_x_348_, v___x_403_);
lean_dec_ref(v_x_348_);
v___x_405_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v___x_404_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
return v___x_405_;
}
}
}
v___jp_360_:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_x_347_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint64_t v___x_375_; lean_object* v___x_376_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_array_get_size(v_x_348_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_unbox_uint64(v_a_372_);
lean_dec(v_a_372_);
v___x_376_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(v___x_373_, v_x_348_, v_pinfos_361_, v___x_374_, v___x_375_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec_ref(v_pinfos_361_);
lean_dec_ref(v_x_348_);
return v___x_376_;
}
else
{
lean_dec_ref(v_pinfos_361_);
lean_dec_ref(v_x_348_);
return v___x_371_;
}
}
v___jp_377_:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_Expr_hasLooseBVars(v_x_347_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_box(0);
lean_inc_ref(v_x_347_);
v___x_380_ = l_Lean_Meta_getFunInfo(v_x_347_, v___x_379_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v_paramInfo_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v_paramInfo_382_ = lean_ctor_get(v_a_381_, 0);
lean_inc_ref(v_paramInfo_382_);
lean_dec(v_a_381_);
v_pinfos_361_ = v_paramInfo_382_;
v___y_362_ = v___y_350_;
v___y_363_ = v___y_351_;
v___y_364_ = v___y_352_;
v___y_365_ = v___y_353_;
v___y_366_ = v___y_354_;
v___y_367_ = v___y_355_;
v___y_368_ = v___y_356_;
v___y_369_ = v___y_357_;
v___y_370_ = v___y_358_;
goto v___jp_360_;
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref(v_x_348_);
lean_dec_ref(v_x_347_);
v_a_383_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_380_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_380_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v___x_391_; 
v___x_391_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5___closed__0));
v_pinfos_361_ = v___x_391_;
v___y_362_ = v___y_350_;
v___y_363_ = v___y_351_;
v___y_364_ = v___y_352_;
v___y_365_ = v___y_353_;
v___y_366_ = v___y_354_;
v___y_367_ = v___y_355_;
v___y_368_ = v___y_356_;
v___y_369_ = v___y_357_;
v___y_370_ = v___y_358_;
goto v___jp_360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
uint64_t v_a_418_; lean_object* v___y_419_; lean_object* v_n_448_; lean_object* v_d_449_; lean_object* v_b_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___x_469_; lean_object* v_anchors_470_; lean_object* v___x_471_; 
v___x_469_ = lean_st_ref_get(v_a_409_);
v_anchors_470_ = lean_ctor_get(v___x_469_, 10);
lean_inc_ref(v_anchors_470_);
lean_dec(v___x_469_);
v___x_471_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg(v_anchors_470_, v_e_406_);
lean_dec_ref(v_anchors_470_);
if (lean_obj_tag(v___x_471_) == 1)
{
lean_object* v_val_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_e_406_);
v_val_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_val_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 0);
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_val_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_dec(v___x_471_);
switch(lean_obj_tag(v_e_406_))
{
case 0:
{
lean_object* v_deBruijnIndex_480_; uint64_t v___x_481_; 
v_deBruijnIndex_480_ = lean_ctor_get(v_e_406_, 0);
v___x_481_ = lean_uint64_of_nat(v_deBruijnIndex_480_);
v_a_418_ = v___x_481_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
case 1:
{
lean_object* v_fvarId_482_; lean_object* v___x_483_; lean_object* v_fvarAnchors_484_; lean_object* v___x_485_; 
v_fvarId_482_ = lean_ctor_get(v_e_406_, 0);
v___x_483_ = lean_st_ref_get(v_a_409_);
v_fvarAnchors_484_ = lean_ctor_get(v___x_483_, 11);
lean_inc_ref(v_fvarAnchors_484_);
lean_dec(v___x_483_);
v___x_485_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg(v_fvarAnchors_484_, v_fvarId_482_);
lean_dec_ref(v_fvarAnchors_484_);
if (lean_obj_tag(v___x_485_) == 1)
{
lean_object* v_val_486_; uint64_t v___x_487_; 
v_val_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = lean_unbox_uint64(v_val_486_);
lean_dec(v_val_486_);
v_a_418_ = v___x_487_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v___x_485_);
lean_inc(v_fvarId_482_);
v___x_488_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_482_, v_a_412_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = l_Lean_LocalDecl_userName(v_a_489_);
lean_dec(v_a_489_);
v___x_491_ = l_Lean_Name_eraseMacroScopes(v___x_490_);
lean_dec(v___x_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
uint64_t v___x_492_; 
v___x_492_ = 1723ULL;
v_a_418_ = v___x_492_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
uint64_t v_hash_493_; 
v_hash_493_ = lean_ctor_get_uint64(v___x_491_, sizeof(void*)*2);
lean_dec(v___x_491_);
v_a_418_ = v_hash_493_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref_known(v_e_406_, 1);
v_a_494_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_488_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_488_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
case 4:
{
lean_object* v_declName_502_; lean_object* v___x_503_; 
v_declName_502_ = lean_ctor_get(v_e_406_, 0);
lean_inc(v_declName_502_);
v___x_503_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg(v_declName_502_, v_a_415_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; uint8_t v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = lean_unbox(v_a_504_);
lean_dec(v_a_504_);
if (v___x_505_ == 0)
{
uint64_t v___x_506_; 
lean_inc(v_declName_502_);
v___x_506_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_502_);
v_a_418_ = v___x_506_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
uint64_t v___x_507_; 
v___x_507_ = 0ULL;
v_a_418_ = v___x_507_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref_known(v_e_406_, 2);
v_a_508_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_503_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_503_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
case 5:
{
lean_object* v_dummy_516_; lean_object* v_nargs_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_dummy_516_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0);
v_nargs_517_ = l_Lean_Expr_getAppNumArgs(v_e_406_);
lean_inc(v_nargs_517_);
v___x_518_ = lean_mk_array(v_nargs_517_, v_dummy_516_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_sub(v_nargs_517_, v___x_519_);
lean_dec(v_nargs_517_);
lean_inc_ref(v_e_406_);
v___x_521_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5(v_e_406_, v___x_518_, v___x_520_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; uint64_t v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = lean_unbox_uint64(v_a_522_);
lean_dec(v_a_522_);
v_a_418_ = v___x_523_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec_ref_known(v_e_406_, 2);
return v___x_521_;
}
}
case 6:
{
lean_object* v_binderName_524_; lean_object* v_binderType_525_; lean_object* v_body_526_; 
v_binderName_524_ = lean_ctor_get(v_e_406_, 0);
v_binderType_525_ = lean_ctor_get(v_e_406_, 1);
v_body_526_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_body_526_);
lean_inc_ref(v_binderType_525_);
lean_inc(v_binderName_524_);
v_n_448_ = v_binderName_524_;
v_d_449_ = v_binderType_525_;
v_b_450_ = v_body_526_;
v___y_451_ = v_a_407_;
v___y_452_ = v_a_408_;
v___y_453_ = v_a_409_;
v___y_454_ = v_a_410_;
v___y_455_ = v_a_411_;
v___y_456_ = v_a_412_;
v___y_457_ = v_a_413_;
v___y_458_ = v_a_414_;
v___y_459_ = v_a_415_;
goto v___jp_447_;
}
case 7:
{
lean_object* v_binderName_527_; lean_object* v_binderType_528_; lean_object* v_body_529_; 
v_binderName_527_ = lean_ctor_get(v_e_406_, 0);
v_binderType_528_ = lean_ctor_get(v_e_406_, 1);
v_body_529_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_body_529_);
lean_inc_ref(v_binderType_528_);
lean_inc(v_binderName_527_);
v_n_448_ = v_binderName_527_;
v_d_449_ = v_binderType_528_;
v_b_450_ = v_body_529_;
v___y_451_ = v_a_407_;
v___y_452_ = v_a_408_;
v___y_453_ = v_a_409_;
v___y_454_ = v_a_410_;
v___y_455_ = v_a_411_;
v___y_456_ = v_a_412_;
v___y_457_ = v_a_413_;
v___y_458_ = v_a_414_;
v___y_459_ = v_a_415_;
goto v___jp_447_;
}
case 8:
{
lean_object* v_declName_530_; lean_object* v_type_531_; lean_object* v_value_532_; lean_object* v_body_533_; lean_object* v___x_534_; 
v_declName_530_ = lean_ctor_get(v_e_406_, 0);
v_type_531_ = lean_ctor_get(v_e_406_, 1);
v_value_532_ = lean_ctor_get(v_e_406_, 2);
v_body_533_ = lean_ctor_get(v_e_406_, 3);
lean_inc_ref(v_value_532_);
v___x_534_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_value_532_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
lean_inc_ref(v_type_531_);
v___x_536_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_type_531_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
lean_inc_ref(v_body_533_);
v___x_538_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_body_533_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; uint64_t v___x_540_; uint64_t v___x_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v___x_546_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
lean_inc(v_declName_530_);
v___x_540_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_530_);
v___x_541_ = lean_unbox_uint64(v_a_537_);
lean_dec(v_a_537_);
v___x_542_ = lean_unbox_uint64(v_a_539_);
lean_dec(v_a_539_);
v___x_543_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_541_, v___x_542_);
v___x_544_ = lean_unbox_uint64(v_a_535_);
lean_dec(v_a_535_);
v___x_545_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_544_, v___x_543_);
v___x_546_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_540_, v___x_545_);
v_a_418_ = v___x_546_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec(v_a_537_);
lean_dec(v_a_535_);
lean_dec_ref_known(v_e_406_, 4);
return v___x_538_;
}
}
else
{
lean_dec(v_a_535_);
lean_dec_ref_known(v_e_406_, 4);
return v___x_536_;
}
}
else
{
lean_dec_ref_known(v_e_406_, 4);
return v___x_534_;
}
}
case 9:
{
lean_object* v_a_547_; uint64_t v___x_548_; 
v_a_547_ = lean_ctor_get(v_e_406_, 0);
v___x_548_ = l_Lean_Literal_hash(v_a_547_);
v_a_418_ = v___x_548_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
case 10:
{
lean_object* v_expr_549_; lean_object* v___x_550_; 
v_expr_549_ = lean_ctor_get(v_e_406_, 1);
lean_inc_ref(v_expr_549_);
v___x_550_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_expr_549_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; uint64_t v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = lean_unbox_uint64(v_a_551_);
lean_dec(v_a_551_);
v_a_418_ = v___x_552_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec_ref_known(v_e_406_, 2);
return v___x_550_;
}
}
case 11:
{
lean_object* v_idx_553_; lean_object* v_struct_554_; lean_object* v___x_555_; 
v_idx_553_ = lean_ctor_get(v_e_406_, 1);
v_struct_554_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_struct_554_);
v___x_555_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_struct_554_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; uint64_t v___x_557_; uint64_t v___x_558_; uint64_t v___x_559_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = lean_uint64_of_nat(v_idx_553_);
v___x_558_ = lean_unbox_uint64(v_a_556_);
lean_dec(v_a_556_);
v___x_559_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_557_, v___x_558_);
v_a_418_ = v___x_559_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec_ref_known(v_e_406_, 3);
return v___x_555_;
}
}
default: 
{
uint64_t v___x_560_; 
v___x_560_ = 0ULL;
v_a_418_ = v___x_560_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
}
}
v___jp_417_:
{
lean_object* v___x_420_; lean_object* v_congrThms_421_; lean_object* v_simp_422_; lean_object* v_symSimp_423_; lean_object* v_symDSimp_424_; lean_object* v_lastTag_425_; lean_object* v_counters_426_; lean_object* v_splitDiags_427_; lean_object* v_ematchDiags_428_; lean_object* v_lawfulEqCmpMap_429_; lean_object* v_reflCmpMap_430_; lean_object* v_anchors_431_; lean_object* v_fvarAnchors_432_; lean_object* v_instanceMap_433_; lean_object* v_hoistedDecls_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_446_; 
v___x_420_ = lean_st_ref_take(v___y_419_);
v_congrThms_421_ = lean_ctor_get(v___x_420_, 0);
v_simp_422_ = lean_ctor_get(v___x_420_, 1);
v_symSimp_423_ = lean_ctor_get(v___x_420_, 2);
v_symDSimp_424_ = lean_ctor_get(v___x_420_, 3);
v_lastTag_425_ = lean_ctor_get(v___x_420_, 4);
v_counters_426_ = lean_ctor_get(v___x_420_, 5);
v_splitDiags_427_ = lean_ctor_get(v___x_420_, 6);
v_ematchDiags_428_ = lean_ctor_get(v___x_420_, 7);
v_lawfulEqCmpMap_429_ = lean_ctor_get(v___x_420_, 8);
v_reflCmpMap_430_ = lean_ctor_get(v___x_420_, 9);
v_anchors_431_ = lean_ctor_get(v___x_420_, 10);
v_fvarAnchors_432_ = lean_ctor_get(v___x_420_, 11);
v_instanceMap_433_ = lean_ctor_get(v___x_420_, 12);
v_hoistedDecls_434_ = lean_ctor_get(v___x_420_, 13);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_446_ == 0)
{
v___x_436_ = v___x_420_;
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_hoistedDecls_434_);
lean_inc(v_instanceMap_433_);
lean_inc(v_fvarAnchors_432_);
lean_inc(v_anchors_431_);
lean_inc(v_reflCmpMap_430_);
lean_inc(v_lawfulEqCmpMap_429_);
lean_inc(v_ematchDiags_428_);
lean_inc(v_splitDiags_427_);
lean_inc(v_counters_426_);
lean_inc(v_lastTag_425_);
lean_inc(v_symDSimp_424_);
lean_inc(v_symSimp_423_);
lean_inc(v_simp_422_);
lean_inc(v_congrThms_421_);
lean_dec(v___x_420_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_box_uint64(v_a_418_);
v___x_439_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0___redArg(v_anchors_431_, v_e_406_, v___x_438_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 10, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_congrThms_421_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_simp_422_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_symSimp_423_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_symDSimp_424_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_lastTag_425_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v_counters_426_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_splitDiags_427_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_ematchDiags_428_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_lawfulEqCmpMap_429_);
lean_ctor_set(v_reuseFailAlloc_445_, 9, v_reflCmpMap_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 10, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_445_, 11, v_fvarAnchors_432_);
lean_ctor_set(v_reuseFailAlloc_445_, 12, v_instanceMap_433_);
lean_ctor_set(v_reuseFailAlloc_445_, 13, v_hoistedDecls_434_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_st_ref_put(v___y_419_, v___x_441_);
v___x_443_ = lean_box_uint64(v_a_418_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
}
v___jp_447_:
{
lean_object* v___x_460_; 
v___x_460_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_d_449_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_b_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_448_);
v___x_465_ = lean_unbox_uint64(v_a_461_);
lean_dec(v_a_461_);
v___x_466_ = lean_unbox_uint64(v_a_463_);
lean_dec(v_a_463_);
v___x_467_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_465_, v___x_466_);
v___x_468_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_464_, v___x_467_);
v_a_418_ = v___x_468_;
v___y_419_ = v___y_453_;
goto v___jp_417_;
}
else
{
lean_dec(v_a_461_);
lean_dec(v_n_448_);
lean_dec_ref(v_e_406_);
return v___x_462_;
}
}
else
{
lean_dec_ref(v_b_450_);
lean_dec(v_n_448_);
lean_dec_ref(v_e_406_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(lean_object* v_upperBound_561_, lean_object* v_args_562_, lean_object* v_pinfos_563_, lean_object* v_a_564_, uint64_t v_b_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint64_t v_a_577_; uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_lt(v_a_564_, v_upperBound_561_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_a_564_);
v___x_582_ = lean_box_uint64(v_b_565_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_array_fget_borrowed(v_args_562_, v_a_564_);
v___x_585_ = lean_array_get_size(v_pinfos_563_);
v___x_586_ = lean_nat_dec_lt(v_a_564_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_inc(v___x_584_);
v___x_587_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v___x_584_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; uint64_t v___x_589_; uint64_t v___x_590_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = lean_unbox_uint64(v_a_588_);
lean_dec(v_a_588_);
v___x_590_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_565_, v___x_589_);
v_a_577_ = v___x_590_;
goto v___jp_576_;
}
else
{
lean_dec(v_a_564_);
return v___x_587_;
}
}
else
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_array_fget_borrowed(v_pinfos_563_, v_a_564_);
v___x_592_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_inc(v___x_584_);
v___x_593_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v___x_584_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; uint64_t v___x_595_; uint64_t v___x_596_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_unbox_uint64(v_a_594_);
lean_dec(v_a_594_);
v___x_596_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_565_, v___x_595_);
v_a_577_ = v___x_596_;
goto v___jp_576_;
}
else
{
lean_dec(v_a_564_);
return v___x_593_;
}
}
else
{
v_a_577_ = v_b_565_;
goto v___jp_576_;
}
}
}
v___jp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_a_564_, v___x_578_);
lean_dec(v_a_564_);
v_a_564_ = v___x_579_;
v_b_565_ = v_a_577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg___boxed(lean_object* v_upperBound_597_, lean_object* v_args_598_, lean_object* v_pinfos_599_, lean_object* v_a_600_, lean_object* v_b_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint64_t v_b_boxed_612_; lean_object* v_res_613_; 
v_b_boxed_612_ = lean_unbox_uint64(v_b_601_);
lean_dec_ref(v_b_601_);
v_res_613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(v_upperBound_597_, v_args_598_, v_pinfos_599_, v_a_600_, v_b_boxed_612_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v_pinfos_599_);
lean_dec_ref(v_args_598_);
lean_dec(v_upperBound_597_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5___boxed(lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5(v_x_614_, v_x_615_, v_x_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___boxed(lean_object* v_e_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_e_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0(lean_object* v_00_u03b2_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0___redArg(v_x_641_, v_x_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1(lean_object* v_upperBound_645_, lean_object* v_args_646_, lean_object* v_pinfos_647_, lean_object* v_inst_648_, lean_object* v_R_649_, lean_object* v_a_650_, uint64_t v_b_651_, lean_object* v_c_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(v_upperBound_645_, v_args_646_, v_pinfos_647_, v_a_650_, v_b_651_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_664_ = _args[0];
lean_object* v_args_665_ = _args[1];
lean_object* v_pinfos_666_ = _args[2];
lean_object* v_inst_667_ = _args[3];
lean_object* v_R_668_ = _args[4];
lean_object* v_a_669_ = _args[5];
lean_object* v_b_670_ = _args[6];
lean_object* v_c_671_ = _args[7];
lean_object* v___y_672_ = _args[8];
lean_object* v___y_673_ = _args[9];
lean_object* v___y_674_ = _args[10];
lean_object* v___y_675_ = _args[11];
lean_object* v___y_676_ = _args[12];
lean_object* v___y_677_ = _args[13];
lean_object* v___y_678_ = _args[14];
lean_object* v___y_679_ = _args[15];
lean_object* v___y_680_ = _args[16];
lean_object* v___y_681_ = _args[17];
_start:
{
uint64_t v_b_boxed_682_; lean_object* v_res_683_; 
v_b_boxed_682_ = lean_unbox_uint64(v_b_670_);
lean_dec_ref(v_b_670_);
v_res_683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1(v_upperBound_664_, v_args_665_, v_pinfos_666_, v_inst_667_, v_R_668_, v_a_669_, v_b_boxed_682_, v_c_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_pinfos_666_);
lean_dec_ref(v_args_665_);
lean_dec(v_upperBound_664_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2(lean_object* v_00_u03b2_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg(v_x_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___boxed(lean_object* v_00_u03b2_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2(v_00_u03b2_688_, v_x_689_, v_x_690_);
lean_dec_ref(v_x_690_);
lean_dec_ref(v_x_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3(lean_object* v_00_u03b2_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg(v_x_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___boxed(lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3(v_00_u03b2_696_, v_x_697_, v_x_698_);
lean_dec(v_x_698_);
lean_dec_ref(v_x_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0(lean_object* v_00_u03b2_700_, lean_object* v_x_701_, size_t v_x_702_, size_t v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(v_x_701_, v_x_702_, v_x_703_, v_x_704_, v_x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
size_t v_x_35857__boxed_713_; size_t v_x_35858__boxed_714_; lean_object* v_res_715_; 
v_x_35857__boxed_713_ = lean_unbox_usize(v_x_709_);
lean_dec(v_x_709_);
v_x_35858__boxed_714_ = lean_unbox_usize(v_x_710_);
lean_dec(v_x_710_);
v_res_715_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0(v_00_u03b2_707_, v_x_708_, v_x_35857__boxed_713_, v_x_35858__boxed_714_, v_x_711_, v_x_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3(lean_object* v_00_u03b2_716_, lean_object* v_x_717_, size_t v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg(v_x_717_, v_x_718_, v_x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___boxed(lean_object* v_00_u03b2_721_, lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
size_t v_x_35874__boxed_725_; lean_object* v_res_726_; 
v_x_35874__boxed_725_ = lean_unbox_usize(v_x_723_);
lean_dec(v_x_723_);
v_res_726_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3(v_00_u03b2_721_, v_x_722_, v_x_35874__boxed_725_, v_x_724_);
lean_dec_ref(v_x_724_);
lean_dec_ref(v_x_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5(lean_object* v_00_u03b2_727_, lean_object* v_x_728_, size_t v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg(v_x_728_, v_x_729_, v_x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
size_t v_x_35885__boxed_736_; lean_object* v_res_737_; 
v_x_35885__boxed_736_ = lean_unbox_usize(v_x_734_);
lean_dec(v_x_734_);
v_res_737_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5(v_00_u03b2_732_, v_x_733_, v_x_35885__boxed_736_, v_x_735_);
lean_dec(v_x_735_);
lean_dec_ref(v_x_733_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_738_, lean_object* v_n_739_, lean_object* v_k_740_, lean_object* v_v_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2___redArg(v_n_739_, v_k_740_, v_v_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_743_, size_t v_depth_744_, lean_object* v_keys_745_, lean_object* v_vals_746_, lean_object* v_heq_747_, lean_object* v_i_748_, lean_object* v_entries_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg(v_depth_744_, v_keys_745_, v_vals_746_, v_i_748_, v_entries_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_751_, lean_object* v_depth_752_, lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_heq_755_, lean_object* v_i_756_, lean_object* v_entries_757_){
_start:
{
size_t v_depth_boxed_758_; lean_object* v_res_759_; 
v_depth_boxed_758_ = lean_unbox_usize(v_depth_752_);
lean_dec(v_depth_752_);
v_res_759_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3(v_00_u03b2_751_, v_depth_boxed_758_, v_keys_753_, v_vals_754_, v_heq_755_, v_i_756_, v_entries_757_);
lean_dec_ref(v_vals_754_);
lean_dec_ref(v_keys_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_760_, lean_object* v_keys_761_, lean_object* v_vals_762_, lean_object* v_heq_763_, lean_object* v_i_764_, lean_object* v_k_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg(v_keys_761_, v_vals_762_, v_i_764_, v_k_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_767_, lean_object* v_keys_768_, lean_object* v_vals_769_, lean_object* v_heq_770_, lean_object* v_i_771_, lean_object* v_k_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7(v_00_u03b2_767_, v_keys_768_, v_vals_769_, v_heq_770_, v_i_771_, v_k_772_);
lean_dec_ref(v_k_772_);
lean_dec_ref(v_vals_769_);
lean_dec_ref(v_keys_768_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_774_, lean_object* v_keys_775_, lean_object* v_vals_776_, lean_object* v_heq_777_, lean_object* v_i_778_, lean_object* v_k_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg(v_keys_775_, v_vals_776_, v_i_778_, v_k_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_781_, lean_object* v_keys_782_, lean_object* v_vals_783_, lean_object* v_heq_784_, lean_object* v_i_785_, lean_object* v_k_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10(v_00_u03b2_781_, v_keys_782_, v_vals_783_, v_heq_784_, v_i_785_, v_k_786_);
lean_dec(v_k_786_);
lean_dec_ref(v_vals_783_);
lean_dec_ref(v_keys_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7___redArg(v_x_789_, v_x_790_, v_x_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_anchorsEnabled___redArg(v_a_798_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_818_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_818_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_818_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_818_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = lean_unbox(v_a_808_);
lean_dec(v_a_808_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_815_; 
lean_dec_ref(v_e_796_);
v___x_813_ = ((lean_object*)(l_Lean_Meta_Grind_getAnchor___boxed__const__1));
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_813_);
v___x_815_ = v___x_810_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
lean_object* v___x_817_; 
lean_del_object(v___x_810_);
v___x_817_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_e_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_817_;
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_e_796_);
v_a_819_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_807_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_807_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Meta_Grind_getAnchor(v_e_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
return v_res_838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_839_, uint64_t v_anchor_840_){
_start:
{
lean_object* v_numDigits_841_; uint64_t v_anchorPrefix_842_; uint64_t v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v_shift_847_; uint64_t v___x_848_; uint8_t v___x_849_; 
v_numDigits_841_ = lean_ctor_get(v_anchorRef_839_, 0);
v_anchorPrefix_842_ = lean_ctor_get_uint64(v_anchorRef_839_, sizeof(void*)*1);
v___x_843_ = 64ULL;
v___x_844_ = lean_uint64_of_nat(v_numDigits_841_);
v___x_845_ = 2ULL;
v___x_846_ = lean_uint64_shift_left(v___x_844_, v___x_845_);
v_shift_847_ = lean_uint64_sub(v___x_843_, v___x_846_);
v___x_848_ = lean_uint64_shift_right(v_anchor_840_, v_shift_847_);
v___x_849_ = lean_uint64_dec_eq(v_anchorPrefix_842_, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_850_, lean_object* v_anchor_851_){
_start:
{
uint64_t v_anchor_boxed_852_; uint8_t v_res_853_; lean_object* v_r_854_; 
v_anchor_boxed_852_ = lean_unbox_uint64(v_anchor_851_);
lean_dec_ref(v_anchor_851_);
v_res_853_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_850_, v_anchor_boxed_852_);
lean_dec_ref(v_anchorRef_850_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10(void){
_start:
{
lean_object* v___x_874_; lean_object* v___f_875_; 
v___x_874_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_875_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_875_, 0, v___x_874_);
return v___f_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_877_, lean_object* v_shift_878_, lean_object* v___f_879_, lean_object* v___f_880_, lean_object* v_numDigits_881_, lean_object* v_es_882_, lean_object* v___x_883_, lean_object* v_a_884_, lean_object* v_x_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_877_, v_shift_878_, v___f_879_, v___f_880_, v_numDigits_881_, v_es_882_, v___x_883_, v_a_884_, v_x_885_, v___y_886_);
lean_dec(v_numDigits_881_);
lean_dec(v_shift_878_);
return v_res_887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
v___x_889_ = lean_unsigned_to_nat(16u);
v___x_890_ = lean_mk_array(v___x_889_, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_found_893_; 
v___x_891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12);
v___x_892_ = lean_unsigned_to_nat(0u);
v_found_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_893_, 0, v___x_892_);
lean_ctor_set(v_found_893_, 1, v___x_891_);
return v_found_893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_found_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13);
v___x_895_ = lean_box(0);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v_found_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_897_, lean_object* v_es_898_, lean_object* v_numDigits_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9));
v___x_901_ = lean_unsigned_to_nat(4u);
v___x_902_ = lean_nat_mul(v___x_901_, v_numDigits_899_);
v___x_903_ = lean_unsigned_to_nat(64u);
v___x_904_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_dec(v___x_902_);
lean_dec_ref(v_es_898_);
lean_dec_ref(v_inst_897_);
return v_numDigits_899_;
}
else
{
lean_object* v___f_905_; lean_object* v___f_906_; lean_object* v_shift_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; size_t v_sz_911_; size_t v___x_912_; lean_object* v___x_913_; lean_object* v_fst_914_; 
v___f_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10);
v___f_906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11));
v_shift_907_ = lean_nat_sub(v___x_903_, v___x_902_);
lean_dec(v___x_902_);
v___x_908_ = lean_box(0);
lean_inc_ref(v_es_898_);
lean_inc(v_numDigits_899_);
v___f_909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_909_, 0, v_inst_897_);
lean_closure_set(v___f_909_, 1, v_shift_907_);
lean_closure_set(v___f_909_, 2, v___f_905_);
lean_closure_set(v___f_909_, 3, v___f_906_);
lean_closure_set(v___f_909_, 4, v_numDigits_899_);
lean_closure_set(v___f_909_, 5, v_es_898_);
lean_closure_set(v___f_909_, 6, v___x_908_);
v___x_910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_911_ = lean_array_size(v_es_898_);
v___x_912_ = ((size_t)0ULL);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_900_, v_es_898_, v___f_909_, v_sz_911_, v___x_912_, v___x_910_);
v_fst_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_fst_914_);
lean_dec(v___x_913_);
if (lean_obj_tag(v_fst_914_) == 0)
{
return v_numDigits_899_;
}
else
{
lean_object* v_val_915_; 
lean_dec(v_numDigits_899_);
v_val_915_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v_fst_914_, 1);
return v_val_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_916_, lean_object* v_shift_917_, lean_object* v___f_918_, lean_object* v___f_919_, lean_object* v_numDigits_920_, lean_object* v_es_921_, lean_object* v___x_922_, lean_object* v_a_923_, lean_object* v_x_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_snd_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_964_; 
v_snd_926_ = lean_ctor_get(v___y_925_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v___y_925_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v___y_925_, 0);
lean_dec(v_unused_965_);
v___x_928_ = v___y_925_;
v_isShared_929_ = v_isSharedCheck_964_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_snd_926_);
lean_dec(v___y_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_964_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; uint64_t v___x_931_; uint64_t v___x_932_; uint64_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_inc_ref(v_inst_916_);
v___x_930_ = lean_apply_1(v_inst_916_, v_a_923_);
v___x_931_ = lean_uint64_of_nat(v_shift_917_);
v___x_932_ = lean_unbox_uint64(v___x_930_);
v___x_933_ = lean_uint64_shift_right(v___x_932_, v___x_931_);
v___x_934_ = lean_box_uint64(v___x_933_);
lean_inc_ref(v___f_919_);
lean_inc_ref(v___f_918_);
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_918_, v___f_919_, v_snd_926_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___f_919_);
lean_dec_ref(v___f_918_);
v_val_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_957_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_957_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_val_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_957_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint64_t v___x_940_; uint64_t v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_unbox_uint64(v_val_936_);
lean_dec(v_val_936_);
v___x_941_ = lean_unbox_uint64(v___x_930_);
lean_dec_ref(v___x_930_);
v___x_942_ = lean_uint64_dec_eq(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
lean_dec(v___x_922_);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_numDigits_920_, v___x_943_);
v___x_945_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_916_, v_es_921_, v___x_944_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_945_);
v___x_947_ = v___x_938_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_952_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_947_);
v___x_949_ = v___x_928_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_snd_926_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
else
{
lean_object* v___x_954_; 
lean_del_object(v___x_938_);
lean_dec_ref(v_es_921_);
lean_dec_ref(v_inst_916_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_922_);
v___x_954_ = v___x_928_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_snd_926_);
v___x_954_ = v_reuseFailAlloc_956_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
lean_dec(v___x_935_);
lean_dec_ref(v_es_921_);
lean_dec_ref(v_inst_916_);
v___x_958_ = lean_box_uint64(v___x_933_);
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_918_, v___f_919_, v_snd_926_, v___x_958_, v___x_930_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_959_);
lean_ctor_set(v___x_928_, 0, v___x_922_);
v___x_961_ = v___x_928_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_959_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_966_, lean_object* v_inst_967_, lean_object* v_es_968_, lean_object* v_numDigits_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_967_, v_es_968_, v_numDigits_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_match__1_splitter___redArg(lean_object* v_x_971_, lean_object* v_h__1_972_, lean_object* v_h__2_973_){
_start:
{
if (lean_obj_tag(v_x_971_) == 1)
{
lean_object* v_val_974_; lean_object* v___x_975_; 
lean_dec(v_h__2_973_);
v_val_974_ = lean_ctor_get(v_x_971_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v_x_971_, 1);
v___x_975_ = lean_apply_1(v_h__1_972_, v_val_974_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; 
lean_dec(v_h__1_972_);
v___x_976_ = lean_apply_2(v_h__2_973_, v_x_971_, lean_box(0));
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_match__1_splitter(lean_object* v_motive_977_, lean_object* v_x_978_, lean_object* v_h__1_979_, lean_object* v_h__2_980_){
_start:
{
if (lean_obj_tag(v_x_978_) == 1)
{
lean_object* v_val_981_; lean_object* v___x_982_; 
lean_dec(v_h__2_980_);
v_val_981_ = lean_ctor_get(v_x_978_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v_x_978_, 1);
v___x_982_ = lean_apply_1(v_h__1_979_, v_val_981_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
lean_dec(v_h__1_979_);
v___x_983_ = lean_apply_2(v_h__2_980_, v_x_978_, lean_box(0));
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_984_, lean_object* v_h__1_985_, lean_object* v_h__2_986_){
_start:
{
if (lean_obj_tag(v_x_984_) == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec(v_h__1_985_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_apply_1(v_h__2_986_, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v_val_989_; lean_object* v___x_990_; 
lean_dec(v_h__2_986_);
v_val_989_ = lean_ctor_get(v_x_984_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v_x_984_, 1);
v___x_990_ = lean_apply_1(v_h__1_985_, v_val_989_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_991_, lean_object* v_motive_992_, lean_object* v_x_993_, lean_object* v_h__1_994_, lean_object* v_h__2_995_){
_start:
{
if (lean_obj_tag(v_x_993_) == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v_h__1_994_);
v___x_996_ = lean_box(0);
v___x_997_ = lean_apply_1(v_h__2_995_, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v_val_998_; lean_object* v___x_999_; 
lean_dec(v_h__2_995_);
v_val_998_ = lean_ctor_get(v_x_993_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_x_993_, 1);
v___x_999_ = lean_apply_1(v_h__1_994_, v_val_998_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_1000_, lean_object* v_es_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(4u);
v___x_1003_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1000_, v_es_1001_, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_1004_, lean_object* v_inst_1005_, lean_object* v_es_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_1005_, v_es_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_1008_){
_start:
{
uint64_t v_anchor_1009_; 
v_anchor_1009_ = lean_ctor_get_uint64(v_e_1008_, sizeof(void*)*1);
return v_anchor_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_1010_){
_start:
{
uint64_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_1010_);
lean_dec_ref(v_e_1010_);
v_r_1012_ = lean_box_uint64(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_1028_, uint64_t v_anchorPrefix_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_ref_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_ref_1032_ = lean_ctor_get(v_a_1030_, 2);
v___x_1033_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_1034_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_1028_, v_anchorPrefix_1029_);
v___x_1035_ = l_Lean_mkAtom(v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_mk_empty_array_with_capacity(v___x_1036_);
v___x_1038_ = lean_array_push(v___x_1037_, v___x_1035_);
v___x_1039_ = lean_box(2);
v___x_1040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_1033_);
lean_ctor_set(v___x_1040_, 2, v___x_1038_);
v___x_1041_ = 0;
v___x_1042_ = l_Lean_SourceInfo_fromRef(v_ref_1032_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_1042_);
v___x_1045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1042_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node2(v___x_1042_, v___x_1043_, v___x_1045_, v___x_1040_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_1048_, lean_object* v_anchorPrefix_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
uint64_t v_anchorPrefix_boxed_1052_; lean_object* v_res_1053_; 
v_anchorPrefix_boxed_1052_ = lean_unbox_uint64(v_anchorPrefix_1049_);
lean_dec_ref(v_anchorPrefix_1049_);
v_res_1053_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1048_, v_anchorPrefix_boxed_1052_, v_a_1050_);
lean_dec_ref(v_a_1050_);
lean_dec(v_numDigits_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_1054_, uint64_t v_anchorPrefix_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1054_, v_anchorPrefix_1055_, v_a_1056_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_1060_, lean_object* v_anchorPrefix_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
uint64_t v_anchorPrefix_boxed_1065_; lean_object* v_res_1066_; 
v_anchorPrefix_boxed_1065_ = lean_unbox_uint64(v_anchorPrefix_1061_);
lean_dec_ref(v_anchorPrefix_1061_);
v_res_1066_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_1060_, v_anchorPrefix_boxed_1065_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_numDigits_1060_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_1067_, uint64_t v_anchor_1068_, lean_object* v_a_1069_){
_start:
{
uint64_t v___x_1071_; uint64_t v___x_1072_; uint64_t v___x_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v_anchorPrefix_1076_; lean_object* v___x_1077_; 
v___x_1071_ = 64ULL;
v___x_1072_ = lean_uint64_of_nat(v_numDigits_1067_);
v___x_1073_ = 2ULL;
v___x_1074_ = lean_uint64_shift_left(v___x_1072_, v___x_1073_);
v___x_1075_ = lean_uint64_sub(v___x_1071_, v___x_1074_);
v_anchorPrefix_1076_ = lean_uint64_shift_right(v_anchor_1068_, v___x_1075_);
v___x_1077_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1067_, v_anchorPrefix_1076_, v_a_1069_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_1078_, lean_object* v_anchor_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
uint64_t v_anchor_boxed_1082_; lean_object* v_res_1083_; 
v_anchor_boxed_1082_ = lean_unbox_uint64(v_anchor_1079_);
lean_dec_ref(v_anchor_1079_);
v_res_1083_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1078_, v_anchor_boxed_1082_, v_a_1080_);
lean_dec_ref(v_a_1080_);
lean_dec(v_numDigits_1078_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_1084_, uint64_t v_anchor_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1084_, v_anchor_1085_, v_a_1086_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_1090_, lean_object* v_anchor_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
uint64_t v_anchor_boxed_1095_; lean_object* v_res_1096_; 
v_anchor_boxed_1095_ = lean_unbox_uint64(v_anchor_1091_);
lean_dec_ref(v_anchor_1091_);
v_res_1096_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_1090_, v_anchor_boxed_1095_, v_a_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_numDigits_1090_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_1097_);
v___x_1109_ = l_Lean_Meta_Grind_getAnchor(v___x_1108_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_s_1110_);
return v_res_1121_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
}
#ifdef __cplusplus
}
#endif

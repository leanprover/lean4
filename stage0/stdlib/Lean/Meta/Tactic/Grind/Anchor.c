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
size_t v_x_35022__boxed_213_; size_t v_x_35023__boxed_214_; lean_object* v_res_215_; 
v_x_35022__boxed_213_ = lean_unbox_usize(v_x_209_);
lean_dec(v_x_209_);
v_x_35023__boxed_214_ = lean_unbox_usize(v_x_210_);
lean_dec(v_x_210_);
v_res_215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(v_x_208_, v_x_35022__boxed_213_, v_x_35023__boxed_214_, v_x_211_, v_x_212_);
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
size_t v_x_35223__boxed_275_; lean_object* v_res_276_; 
v_x_35223__boxed_275_ = lean_unbox_usize(v_x_273_);
lean_dec(v_x_273_);
v_res_276_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg(v_x_272_, v_x_35223__boxed_275_, v_x_274_);
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
size_t v_x_35310__boxed_333_; lean_object* v_res_334_; 
v_x_35310__boxed_333_ = lean_unbox_usize(v_x_331_);
lean_dec(v_x_331_);
v_res_334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg(v_x_330_, v_x_35310__boxed_333_, v_x_332_);
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
uint64_t v_a_418_; lean_object* v___y_419_; lean_object* v_n_450_; lean_object* v_d_451_; lean_object* v_b_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___x_471_; lean_object* v_anchors_472_; lean_object* v___x_473_; 
v___x_471_ = lean_st_ref_get(v_a_409_);
v_anchors_472_ = lean_ctor_get(v___x_471_, 10);
lean_inc_ref(v_anchors_472_);
lean_dec(v___x_471_);
v___x_473_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg(v_anchors_472_, v_e_406_);
lean_dec_ref(v_anchors_472_);
if (lean_obj_tag(v___x_473_) == 1)
{
lean_object* v_val_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_e_406_);
v_val_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_val_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 0);
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_val_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_dec(v___x_473_);
switch(lean_obj_tag(v_e_406_))
{
case 0:
{
lean_object* v_deBruijnIndex_482_; uint64_t v___x_483_; 
v_deBruijnIndex_482_ = lean_ctor_get(v_e_406_, 0);
v___x_483_ = lean_uint64_of_nat(v_deBruijnIndex_482_);
v_a_418_ = v___x_483_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
case 1:
{
lean_object* v_fvarId_484_; lean_object* v___x_485_; lean_object* v_fvarAnchors_486_; lean_object* v___x_487_; 
v_fvarId_484_ = lean_ctor_get(v_e_406_, 0);
v___x_485_ = lean_st_ref_get(v_a_409_);
v_fvarAnchors_486_ = lean_ctor_get(v___x_485_, 11);
lean_inc_ref(v_fvarAnchors_486_);
lean_dec(v___x_485_);
v___x_487_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg(v_fvarAnchors_486_, v_fvarId_484_);
lean_dec_ref(v_fvarAnchors_486_);
if (lean_obj_tag(v___x_487_) == 1)
{
lean_object* v_val_488_; uint64_t v___x_489_; 
v_val_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = lean_unbox_uint64(v_val_488_);
lean_dec(v_val_488_);
v_a_418_ = v___x_489_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v___x_487_);
lean_inc(v_fvarId_484_);
v___x_490_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_484_, v_a_412_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = l_Lean_LocalDecl_userName(v_a_491_);
lean_dec(v_a_491_);
v___x_493_ = l_Lean_Name_eraseMacroScopes(v___x_492_);
lean_dec(v___x_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
uint64_t v___x_494_; 
v___x_494_ = 1723ULL;
v_a_418_ = v___x_494_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
uint64_t v_hash_495_; 
v_hash_495_ = lean_ctor_get_uint64(v___x_493_, sizeof(void*)*2);
lean_dec(v___x_493_);
v_a_418_ = v_hash_495_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref_known(v_e_406_, 1);
v_a_496_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_490_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_490_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
case 4:
{
lean_object* v_declName_504_; lean_object* v___x_505_; 
v_declName_504_ = lean_ctor_get(v_e_406_, 0);
lean_inc(v_declName_504_);
v___x_505_ = l_Lean_Meta_isMatcher___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__4___redArg(v_declName_504_, v_a_415_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; uint8_t v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
if (v___x_507_ == 0)
{
uint64_t v___x_508_; 
lean_inc(v_declName_504_);
v___x_508_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_504_);
v_a_418_ = v___x_508_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
uint64_t v___x_509_; 
v___x_509_ = 0ULL;
v_a_418_ = v___x_509_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref_known(v_e_406_, 2);
v_a_510_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_505_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
case 5:
{
lean_object* v_dummy_518_; lean_object* v_nargs_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_dummy_518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___closed__0);
v_nargs_519_ = l_Lean_Expr_getAppNumArgs(v_e_406_);
lean_inc(v_nargs_519_);
v___x_520_ = lean_mk_array(v_nargs_519_, v_dummy_518_);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_sub(v_nargs_519_, v___x_521_);
lean_dec(v_nargs_519_);
lean_inc_ref(v_e_406_);
v___x_523_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5(v_e_406_, v___x_520_, v___x_522_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; uint64_t v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_unbox_uint64(v_a_524_);
lean_dec(v_a_524_);
v_a_418_ = v___x_525_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec_ref_known(v_e_406_, 2);
return v___x_523_;
}
}
case 6:
{
lean_object* v_binderName_526_; lean_object* v_binderType_527_; lean_object* v_body_528_; 
v_binderName_526_ = lean_ctor_get(v_e_406_, 0);
v_binderType_527_ = lean_ctor_get(v_e_406_, 1);
v_body_528_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_body_528_);
lean_inc_ref(v_binderType_527_);
lean_inc(v_binderName_526_);
v_n_450_ = v_binderName_526_;
v_d_451_ = v_binderType_527_;
v_b_452_ = v_body_528_;
v___y_453_ = v_a_407_;
v___y_454_ = v_a_408_;
v___y_455_ = v_a_409_;
v___y_456_ = v_a_410_;
v___y_457_ = v_a_411_;
v___y_458_ = v_a_412_;
v___y_459_ = v_a_413_;
v___y_460_ = v_a_414_;
v___y_461_ = v_a_415_;
goto v___jp_449_;
}
case 7:
{
lean_object* v_binderName_529_; lean_object* v_binderType_530_; lean_object* v_body_531_; 
v_binderName_529_ = lean_ctor_get(v_e_406_, 0);
v_binderType_530_ = lean_ctor_get(v_e_406_, 1);
v_body_531_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_body_531_);
lean_inc_ref(v_binderType_530_);
lean_inc(v_binderName_529_);
v_n_450_ = v_binderName_529_;
v_d_451_ = v_binderType_530_;
v_b_452_ = v_body_531_;
v___y_453_ = v_a_407_;
v___y_454_ = v_a_408_;
v___y_455_ = v_a_409_;
v___y_456_ = v_a_410_;
v___y_457_ = v_a_411_;
v___y_458_ = v_a_412_;
v___y_459_ = v_a_413_;
v___y_460_ = v_a_414_;
v___y_461_ = v_a_415_;
goto v___jp_449_;
}
case 8:
{
lean_object* v_declName_532_; lean_object* v_type_533_; lean_object* v_value_534_; lean_object* v_body_535_; lean_object* v___x_536_; 
v_declName_532_ = lean_ctor_get(v_e_406_, 0);
v_type_533_ = lean_ctor_get(v_e_406_, 1);
v_value_534_ = lean_ctor_get(v_e_406_, 2);
v_body_535_ = lean_ctor_get(v_e_406_, 3);
lean_inc_ref(v_value_534_);
v___x_536_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_value_534_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_538_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
lean_inc_ref(v_type_533_);
v___x_538_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_type_533_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
lean_inc_ref(v_body_535_);
v___x_540_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_body_535_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
lean_inc(v_declName_532_);
v___x_542_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_532_);
v___x_543_ = lean_unbox_uint64(v_a_539_);
lean_dec(v_a_539_);
v___x_544_ = lean_unbox_uint64(v_a_541_);
lean_dec(v_a_541_);
v___x_545_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_543_, v___x_544_);
v___x_546_ = lean_unbox_uint64(v_a_537_);
lean_dec(v_a_537_);
v___x_547_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_546_, v___x_545_);
v___x_548_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_542_, v___x_547_);
v_a_418_ = v___x_548_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec(v_a_539_);
lean_dec(v_a_537_);
lean_dec_ref_known(v_e_406_, 4);
return v___x_540_;
}
}
else
{
lean_dec(v_a_537_);
lean_dec_ref_known(v_e_406_, 4);
return v___x_538_;
}
}
else
{
lean_dec_ref_known(v_e_406_, 4);
return v___x_536_;
}
}
case 9:
{
lean_object* v_a_549_; uint64_t v___x_550_; 
v_a_549_ = lean_ctor_get(v_e_406_, 0);
v___x_550_ = l_Lean_Literal_hash(v_a_549_);
v_a_418_ = v___x_550_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
case 10:
{
lean_object* v_expr_551_; lean_object* v___x_552_; 
v_expr_551_ = lean_ctor_get(v_e_406_, 1);
lean_inc_ref(v_expr_551_);
v___x_552_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_expr_551_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; uint64_t v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = lean_unbox_uint64(v_a_553_);
lean_dec(v_a_553_);
v_a_418_ = v___x_554_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec_ref_known(v_e_406_, 2);
return v___x_552_;
}
}
case 11:
{
lean_object* v_idx_555_; lean_object* v_struct_556_; lean_object* v___x_557_; 
v_idx_555_ = lean_ctor_get(v_e_406_, 1);
v_struct_556_ = lean_ctor_get(v_e_406_, 2);
lean_inc_ref(v_struct_556_);
v___x_557_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_struct_556_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; uint64_t v___x_559_; uint64_t v___x_560_; uint64_t v___x_561_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = lean_uint64_of_nat(v_idx_555_);
v___x_560_ = lean_unbox_uint64(v_a_558_);
lean_dec(v_a_558_);
v___x_561_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_559_, v___x_560_);
v_a_418_ = v___x_561_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
else
{
lean_dec_ref_known(v_e_406_, 3);
return v___x_557_;
}
}
default: 
{
uint64_t v___x_562_; 
v___x_562_ = 0ULL;
v_a_418_ = v___x_562_;
v___y_419_ = v_a_409_;
goto v___jp_417_;
}
}
}
v___jp_417_:
{
lean_object* v___x_420_; lean_object* v_congrThms_421_; lean_object* v_simp_422_; lean_object* v_symSimp_423_; lean_object* v_symDSimp_424_; lean_object* v_lastTag_425_; lean_object* v_counters_426_; lean_object* v_splitDiags_427_; lean_object* v_ematchDiags_428_; lean_object* v_lawfulEqCmpMap_429_; lean_object* v_reflCmpMap_430_; lean_object* v_anchors_431_; lean_object* v_fvarAnchors_432_; lean_object* v_instanceMap_433_; lean_object* v_hoistedDecls_434_; lean_object* v_proofInfos_435_; lean_object* v_numBranches_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_448_; 
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
v_proofInfos_435_ = lean_ctor_get(v___x_420_, 14);
v_numBranches_436_ = lean_ctor_get(v___x_420_, 15);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_448_ == 0)
{
v___x_438_ = v___x_420_;
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_numBranches_436_);
lean_inc(v_proofInfos_435_);
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
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_box_uint64(v_a_418_);
v___x_441_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0___redArg(v_anchors_431_, v_e_406_, v___x_440_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 10, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_congrThms_421_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_simp_422_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_symSimp_423_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_symDSimp_424_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_lastTag_425_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v_counters_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_splitDiags_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_ematchDiags_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v_lawfulEqCmpMap_429_);
lean_ctor_set(v_reuseFailAlloc_447_, 9, v_reflCmpMap_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 10, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_447_, 11, v_fvarAnchors_432_);
lean_ctor_set(v_reuseFailAlloc_447_, 12, v_instanceMap_433_);
lean_ctor_set(v_reuseFailAlloc_447_, 13, v_hoistedDecls_434_);
lean_ctor_set(v_reuseFailAlloc_447_, 14, v_proofInfos_435_);
lean_ctor_set(v_reuseFailAlloc_447_, 15, v_numBranches_436_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_st_ref_put(v___y_419_, v___x_443_);
v___x_445_ = lean_box_uint64(v_a_418_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
}
v___jp_449_:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_d_451_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_b_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_450_);
v___x_467_ = lean_unbox_uint64(v_a_463_);
lean_dec(v_a_463_);
v___x_468_ = lean_unbox_uint64(v_a_465_);
lean_dec(v_a_465_);
v___x_469_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_467_, v___x_468_);
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_466_, v___x_469_);
v_a_418_ = v___x_470_;
v___y_419_ = v___y_455_;
goto v___jp_417_;
}
else
{
lean_dec(v_a_463_);
lean_dec(v_n_450_);
lean_dec_ref(v_e_406_);
return v___x_464_;
}
}
else
{
lean_dec_ref(v_b_452_);
lean_dec(v_n_450_);
lean_dec_ref(v_e_406_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(lean_object* v_upperBound_563_, lean_object* v_args_564_, lean_object* v_pinfos_565_, lean_object* v_a_566_, uint64_t v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint64_t v_a_579_; uint8_t v___x_583_; 
v___x_583_ = lean_nat_dec_lt(v_a_566_, v_upperBound_563_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_a_566_);
v___x_584_ = lean_box_uint64(v_b_567_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_array_fget_borrowed(v_args_564_, v_a_566_);
v___x_587_ = lean_array_get_size(v_pinfos_565_);
v___x_588_ = lean_nat_dec_lt(v_a_566_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_inc(v___x_586_);
v___x_589_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v___x_586_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; uint64_t v___x_591_; uint64_t v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_unbox_uint64(v_a_590_);
lean_dec(v_a_590_);
v___x_592_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_567_, v___x_591_);
v_a_579_ = v___x_592_;
goto v___jp_578_;
}
else
{
lean_dec(v_a_566_);
return v___x_589_;
}
}
else
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_fget_borrowed(v_pinfos_565_, v_a_566_);
v___x_594_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_inc(v___x_586_);
v___x_595_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v___x_586_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; uint64_t v___x_597_; uint64_t v___x_598_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = lean_unbox_uint64(v_a_596_);
lean_dec(v_a_596_);
v___x_598_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_567_, v___x_597_);
v_a_579_ = v___x_598_;
goto v___jp_578_;
}
else
{
lean_dec(v_a_566_);
return v___x_595_;
}
}
else
{
v_a_579_ = v_b_567_;
goto v___jp_578_;
}
}
}
v___jp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_a_566_, v___x_580_);
lean_dec(v_a_566_);
v_a_566_ = v___x_581_;
v_b_567_ = v_a_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg___boxed(lean_object* v_upperBound_599_, lean_object* v_args_600_, lean_object* v_pinfos_601_, lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint64_t v_b_boxed_614_; lean_object* v_res_615_; 
v_b_boxed_614_ = lean_unbox_uint64(v_b_603_);
lean_dec_ref(v_b_603_);
v_res_615_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(v_upperBound_599_, v_args_600_, v_pinfos_601_, v_a_602_, v_b_boxed_614_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v_pinfos_601_);
lean_dec_ref(v_args_600_);
lean_dec(v_upperBound_599_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5___boxed(lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__5(v_x_616_, v_x_617_, v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore___boxed(lean_object* v_e_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_e_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0(lean_object* v_00_u03b2_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0___redArg(v_x_643_, v_x_644_, v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1(lean_object* v_upperBound_647_, lean_object* v_args_648_, lean_object* v_pinfos_649_, lean_object* v_inst_650_, lean_object* v_R_651_, lean_object* v_a_652_, uint64_t v_b_653_, lean_object* v_c_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___redArg(v_upperBound_647_, v_args_648_, v_pinfos_649_, v_a_652_, v_b_653_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_666_ = _args[0];
lean_object* v_args_667_ = _args[1];
lean_object* v_pinfos_668_ = _args[2];
lean_object* v_inst_669_ = _args[3];
lean_object* v_R_670_ = _args[4];
lean_object* v_a_671_ = _args[5];
lean_object* v_b_672_ = _args[6];
lean_object* v_c_673_ = _args[7];
lean_object* v___y_674_ = _args[8];
lean_object* v___y_675_ = _args[9];
lean_object* v___y_676_ = _args[10];
lean_object* v___y_677_ = _args[11];
lean_object* v___y_678_ = _args[12];
lean_object* v___y_679_ = _args[13];
lean_object* v___y_680_ = _args[14];
lean_object* v___y_681_ = _args[15];
lean_object* v___y_682_ = _args[16];
lean_object* v___y_683_ = _args[17];
_start:
{
uint64_t v_b_boxed_684_; lean_object* v_res_685_; 
v_b_boxed_684_ = lean_unbox_uint64(v_b_672_);
lean_dec_ref(v_b_672_);
v_res_685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__1(v_upperBound_666_, v_args_667_, v_pinfos_668_, v_inst_669_, v_R_670_, v_a_671_, v_b_boxed_684_, v_c_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v_pinfos_668_);
lean_dec_ref(v_args_667_);
lean_dec(v_upperBound_666_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2(lean_object* v_00_u03b2_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___redArg(v_x_687_, v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2___boxed(lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2(v_00_u03b2_690_, v_x_691_, v_x_692_);
lean_dec_ref(v_x_692_);
lean_dec_ref(v_x_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___redArg(v_x_695_, v_x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3___boxed(lean_object* v_00_u03b2_698_, lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3(v_00_u03b2_698_, v_x_699_, v_x_700_);
lean_dec(v_x_700_);
lean_dec_ref(v_x_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0(lean_object* v_00_u03b2_702_, lean_object* v_x_703_, size_t v_x_704_, size_t v_x_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___redArg(v_x_703_, v_x_704_, v_x_705_, v_x_706_, v_x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
size_t v_x_35906__boxed_715_; size_t v_x_35907__boxed_716_; lean_object* v_res_717_; 
v_x_35906__boxed_715_ = lean_unbox_usize(v_x_711_);
lean_dec(v_x_711_);
v_x_35907__boxed_716_ = lean_unbox_usize(v_x_712_);
lean_dec(v_x_712_);
v_res_717_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0(v_00_u03b2_709_, v_x_710_, v_x_35906__boxed_715_, v_x_35907__boxed_716_, v_x_713_, v_x_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, size_t v_x_720_, lean_object* v_x_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___redArg(v_x_719_, v_x_720_, v_x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3___boxed(lean_object* v_00_u03b2_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
size_t v_x_35923__boxed_727_; lean_object* v_res_728_; 
v_x_35923__boxed_727_ = lean_unbox_usize(v_x_725_);
lean_dec(v_x_725_);
v_res_728_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3(v_00_u03b2_723_, v_x_724_, v_x_35923__boxed_727_, v_x_726_);
lean_dec_ref(v_x_726_);
lean_dec_ref(v_x_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5(lean_object* v_00_u03b2_729_, lean_object* v_x_730_, size_t v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___redArg(v_x_730_, v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5___boxed(lean_object* v_00_u03b2_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
size_t v_x_35934__boxed_738_; lean_object* v_res_739_; 
v_x_35934__boxed_738_ = lean_unbox_usize(v_x_736_);
lean_dec(v_x_736_);
v_res_739_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5(v_00_u03b2_734_, v_x_735_, v_x_35934__boxed_738_, v_x_737_);
lean_dec(v_x_737_);
lean_dec_ref(v_x_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_740_, lean_object* v_n_741_, lean_object* v_k_742_, lean_object* v_v_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2___redArg(v_n_741_, v_k_742_, v_v_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_745_, size_t v_depth_746_, lean_object* v_keys_747_, lean_object* v_vals_748_, lean_object* v_heq_749_, lean_object* v_i_750_, lean_object* v_entries_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___redArg(v_depth_746_, v_keys_747_, v_vals_748_, v_i_750_, v_entries_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_753_, lean_object* v_depth_754_, lean_object* v_keys_755_, lean_object* v_vals_756_, lean_object* v_heq_757_, lean_object* v_i_758_, lean_object* v_entries_759_){
_start:
{
size_t v_depth_boxed_760_; lean_object* v_res_761_; 
v_depth_boxed_760_ = lean_unbox_usize(v_depth_754_);
lean_dec(v_depth_754_);
v_res_761_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__3(v_00_u03b2_753_, v_depth_boxed_760_, v_keys_755_, v_vals_756_, v_heq_757_, v_i_758_, v_entries_759_);
lean_dec_ref(v_vals_756_);
lean_dec_ref(v_keys_755_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_762_, lean_object* v_keys_763_, lean_object* v_vals_764_, lean_object* v_heq_765_, lean_object* v_i_766_, lean_object* v_k_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___redArg(v_keys_763_, v_vals_764_, v_i_766_, v_k_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_769_, lean_object* v_keys_770_, lean_object* v_vals_771_, lean_object* v_heq_772_, lean_object* v_i_773_, lean_object* v_k_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__2_spec__3_spec__7(v_00_u03b2_769_, v_keys_770_, v_vals_771_, v_heq_772_, v_i_773_, v_k_774_);
lean_dec_ref(v_k_774_);
lean_dec_ref(v_vals_771_);
lean_dec_ref(v_keys_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_776_, lean_object* v_keys_777_, lean_object* v_vals_778_, lean_object* v_heq_779_, lean_object* v_i_780_, lean_object* v_k_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___redArg(v_keys_777_, v_vals_778_, v_i_780_, v_k_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_783_, lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_heq_786_, lean_object* v_i_787_, lean_object* v_k_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__3_spec__5_spec__10(v_00_u03b2_783_, v_keys_784_, v_vals_785_, v_heq_786_, v_i_787_, v_k_788_);
lean_dec(v_k_788_);
lean_dec_ref(v_vals_785_);
lean_dec_ref(v_keys_784_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_spec__0_spec__0_spec__2_spec__7___redArg(v_x_791_, v_x_792_, v_x_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Meta_Grind_anchorsEnabled___redArg(v_a_800_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_820_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_820_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_820_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_820_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
uint8_t v___x_814_; 
v___x_814_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref(v_e_798_);
v___x_815_ = ((lean_object*)(l_Lean_Meta_Grind_getAnchor___boxed__const__1));
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_815_);
v___x_817_ = v___x_812_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v___x_819_; 
lean_del_object(v___x_812_);
v___x_819_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore(v_e_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
return v___x_819_;
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v_e_798_);
v_a_821_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_809_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_809_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_Grind_getAnchor(v_e_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
return v_res_840_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_841_, uint64_t v_anchor_842_){
_start:
{
lean_object* v_numDigits_843_; uint64_t v_anchorPrefix_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v_shift_849_; uint64_t v___x_850_; uint8_t v___x_851_; 
v_numDigits_843_ = lean_ctor_get(v_anchorRef_841_, 0);
v_anchorPrefix_844_ = lean_ctor_get_uint64(v_anchorRef_841_, sizeof(void*)*1);
v___x_845_ = 64ULL;
v___x_846_ = lean_uint64_of_nat(v_numDigits_843_);
v___x_847_ = 2ULL;
v___x_848_ = lean_uint64_shift_left(v___x_846_, v___x_847_);
v_shift_849_ = lean_uint64_sub(v___x_845_, v___x_848_);
v___x_850_ = lean_uint64_shift_right(v_anchor_842_, v_shift_849_);
v___x_851_ = lean_uint64_dec_eq(v_anchorPrefix_844_, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_852_, lean_object* v_anchor_853_){
_start:
{
uint64_t v_anchor_boxed_854_; uint8_t v_res_855_; lean_object* v_r_856_; 
v_anchor_boxed_854_ = lean_unbox_uint64(v_anchor_853_);
lean_dec_ref(v_anchor_853_);
v_res_855_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_852_, v_anchor_boxed_854_);
lean_dec_ref(v_anchorRef_852_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10(void){
_start:
{
lean_object* v___x_876_; lean_object* v___f_877_; 
v___x_876_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_877_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_877_, 0, v___x_876_);
return v___f_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_879_, lean_object* v_shift_880_, lean_object* v___f_881_, lean_object* v___f_882_, lean_object* v_numDigits_883_, lean_object* v_es_884_, lean_object* v___x_885_, lean_object* v_a_886_, lean_object* v_x_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_879_, v_shift_880_, v___f_881_, v___f_882_, v_numDigits_883_, v_es_884_, v___x_885_, v_a_886_, v_x_887_, v___y_888_);
lean_dec(v_numDigits_883_);
lean_dec(v_shift_880_);
return v_res_889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
v___x_891_ = lean_unsigned_to_nat(16u);
v___x_892_ = lean_mk_array(v___x_891_, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_found_895_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12);
v___x_894_ = lean_unsigned_to_nat(0u);
v_found_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_895_, 0, v___x_894_);
lean_ctor_set(v_found_895_, 1, v___x_893_);
return v_found_895_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_found_896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13);
v___x_897_ = lean_box(0);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_found_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_899_, lean_object* v_es_900_, lean_object* v_numDigits_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9));
v___x_903_ = lean_unsigned_to_nat(4u);
v___x_904_ = lean_nat_mul(v___x_903_, v_numDigits_901_);
v___x_905_ = lean_unsigned_to_nat(64u);
v___x_906_ = lean_nat_dec_lt(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_dec(v___x_904_);
lean_dec_ref(v_es_900_);
lean_dec_ref(v_inst_899_);
return v_numDigits_901_;
}
else
{
lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v_shift_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___x_912_; size_t v_sz_913_; size_t v___x_914_; lean_object* v___x_915_; lean_object* v_fst_916_; 
v___f_907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10);
v___f_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11));
v_shift_909_ = lean_nat_sub(v___x_905_, v___x_904_);
lean_dec(v___x_904_);
v___x_910_ = lean_box(0);
lean_inc_ref(v_es_900_);
lean_inc(v_numDigits_901_);
v___f_911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_911_, 0, v_inst_899_);
lean_closure_set(v___f_911_, 1, v_shift_909_);
lean_closure_set(v___f_911_, 2, v___f_907_);
lean_closure_set(v___f_911_, 3, v___f_908_);
lean_closure_set(v___f_911_, 4, v_numDigits_901_);
lean_closure_set(v___f_911_, 5, v_es_900_);
lean_closure_set(v___f_911_, 6, v___x_910_);
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_913_ = lean_array_size(v_es_900_);
v___x_914_ = ((size_t)0ULL);
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_902_, v_es_900_, v___f_911_, v_sz_913_, v___x_914_, v___x_912_);
v_fst_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_fst_916_);
lean_dec(v___x_915_);
if (lean_obj_tag(v_fst_916_) == 0)
{
return v_numDigits_901_;
}
else
{
lean_object* v_val_917_; 
lean_dec(v_numDigits_901_);
v_val_917_ = lean_ctor_get(v_fst_916_, 0);
lean_inc(v_val_917_);
lean_dec_ref_known(v_fst_916_, 1);
return v_val_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_918_, lean_object* v_shift_919_, lean_object* v___f_920_, lean_object* v___f_921_, lean_object* v_numDigits_922_, lean_object* v_es_923_, lean_object* v___x_924_, lean_object* v_a_925_, lean_object* v_x_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_snd_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_966_; 
v_snd_928_ = lean_ctor_get(v___y_927_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v___y_927_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___y_927_, 0);
lean_dec(v_unused_967_);
v___x_930_ = v___y_927_;
v_isShared_931_ = v_isSharedCheck_966_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_snd_928_);
lean_dec(v___y_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_966_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc_ref(v_inst_918_);
v___x_932_ = lean_apply_1(v_inst_918_, v_a_925_);
v___x_933_ = lean_uint64_of_nat(v_shift_919_);
v___x_934_ = lean_unbox_uint64(v___x_932_);
v___x_935_ = lean_uint64_shift_right(v___x_934_, v___x_933_);
v___x_936_ = lean_box_uint64(v___x_935_);
lean_inc_ref(v___f_921_);
lean_inc_ref(v___f_920_);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_920_, v___f_921_, v_snd_928_, v___x_936_);
if (lean_obj_tag(v___x_937_) == 1)
{
lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v___f_921_);
lean_dec_ref(v___f_920_);
v_val_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_959_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_959_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_959_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
uint64_t v___x_942_; uint64_t v___x_943_; uint8_t v___x_944_; 
v___x_942_ = lean_unbox_uint64(v_val_938_);
lean_dec(v_val_938_);
v___x_943_ = lean_unbox_uint64(v___x_932_);
lean_dec_ref(v___x_932_);
v___x_944_ = lean_uint64_dec_eq(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec(v___x_924_);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_add(v_numDigits_922_, v___x_945_);
v___x_947_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_918_, v_es_923_, v___x_946_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_947_);
v___x_949_ = v___x_940_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_954_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_949_);
v___x_951_ = v___x_930_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_snd_928_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
else
{
lean_object* v___x_956_; 
lean_del_object(v___x_940_);
lean_dec_ref(v_es_923_);
lean_dec_ref(v_inst_918_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_924_);
v___x_956_ = v___x_930_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_snd_928_);
v___x_956_ = v_reuseFailAlloc_958_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
lean_dec(v___x_937_);
lean_dec_ref(v_es_923_);
lean_dec_ref(v_inst_918_);
v___x_960_ = lean_box_uint64(v___x_935_);
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_920_, v___f_921_, v_snd_928_, v___x_960_, v___x_932_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_961_);
lean_ctor_set(v___x_930_, 0, v___x_924_);
v___x_963_ = v___x_930_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_968_, lean_object* v_inst_969_, lean_object* v_es_970_, lean_object* v_numDigits_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_969_, v_es_970_, v_numDigits_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_match__1_splitter___redArg(lean_object* v_x_973_, lean_object* v_h__1_974_, lean_object* v_h__2_975_){
_start:
{
if (lean_obj_tag(v_x_973_) == 1)
{
lean_object* v_val_976_; lean_object* v___x_977_; 
lean_dec(v_h__2_975_);
v_val_976_ = lean_ctor_get(v_x_973_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v_x_973_, 1);
v___x_977_ = lean_apply_1(v_h__1_974_, v_val_976_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; 
lean_dec(v_h__1_974_);
v___x_978_ = lean_apply_2(v_h__2_975_, v_x_973_, lean_box(0));
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchorCore_match__1_splitter(lean_object* v_motive_979_, lean_object* v_x_980_, lean_object* v_h__1_981_, lean_object* v_h__2_982_){
_start:
{
if (lean_obj_tag(v_x_980_) == 1)
{
lean_object* v_val_983_; lean_object* v___x_984_; 
lean_dec(v_h__2_982_);
v_val_983_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v_x_980_, 1);
v___x_984_ = lean_apply_1(v_h__1_981_, v_val_983_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; 
lean_dec(v_h__1_981_);
v___x_985_ = lean_apply_2(v_h__2_982_, v_x_980_, lean_box(0));
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_986_, lean_object* v_h__1_987_, lean_object* v_h__2_988_){
_start:
{
if (lean_obj_tag(v_x_986_) == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_h__1_987_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_apply_1(v_h__2_988_, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_992_; 
lean_dec(v_h__2_988_);
v_val_991_ = lean_ctor_get(v_x_986_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_x_986_, 1);
v___x_992_ = lean_apply_1(v_h__1_987_, v_val_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_993_, lean_object* v_motive_994_, lean_object* v_x_995_, lean_object* v_h__1_996_, lean_object* v_h__2_997_){
_start:
{
if (lean_obj_tag(v_x_995_) == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_h__1_996_);
v___x_998_ = lean_box(0);
v___x_999_ = lean_apply_1(v_h__2_997_, v___x_998_);
return v___x_999_;
}
else
{
lean_object* v_val_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__2_997_);
v_val_1000_ = lean_ctor_get(v_x_995_, 0);
lean_inc(v_val_1000_);
lean_dec_ref_known(v_x_995_, 1);
v___x_1001_ = lean_apply_1(v_h__1_996_, v_val_1000_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_1002_, lean_object* v_es_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(4u);
v___x_1005_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1002_, v_es_1003_, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_1006_, lean_object* v_inst_1007_, lean_object* v_es_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_1007_, v_es_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_1010_){
_start:
{
uint64_t v_anchor_1011_; 
v_anchor_1011_ = lean_ctor_get_uint64(v_e_1010_, sizeof(void*)*1);
return v_anchor_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_1012_){
_start:
{
uint64_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_1012_);
lean_dec_ref(v_e_1012_);
v_r_1014_ = lean_box_uint64(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_1030_, uint64_t v_anchorPrefix_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_ref_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_ref_1034_ = lean_ctor_get(v_a_1032_, 2);
v___x_1035_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_1036_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_1030_, v_anchorPrefix_1031_);
v___x_1037_ = l_Lean_mkAtom(v___x_1036_);
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = lean_mk_empty_array_with_capacity(v___x_1038_);
v___x_1040_ = lean_array_push(v___x_1039_, v___x_1037_);
v___x_1041_ = lean_box(2);
v___x_1042_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1035_);
lean_ctor_set(v___x_1042_, 2, v___x_1040_);
v___x_1043_ = 0;
v___x_1044_ = l_Lean_SourceInfo_fromRef(v_ref_1034_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_1046_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_1044_);
v___x_1047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1044_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_Syntax_node2(v___x_1044_, v___x_1045_, v___x_1047_, v___x_1042_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_1050_, lean_object* v_anchorPrefix_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
uint64_t v_anchorPrefix_boxed_1054_; lean_object* v_res_1055_; 
v_anchorPrefix_boxed_1054_ = lean_unbox_uint64(v_anchorPrefix_1051_);
lean_dec_ref(v_anchorPrefix_1051_);
v_res_1055_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1050_, v_anchorPrefix_boxed_1054_, v_a_1052_);
lean_dec_ref(v_a_1052_);
lean_dec(v_numDigits_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_1056_, uint64_t v_anchorPrefix_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1056_, v_anchorPrefix_1057_, v_a_1058_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_1062_, lean_object* v_anchorPrefix_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
uint64_t v_anchorPrefix_boxed_1067_; lean_object* v_res_1068_; 
v_anchorPrefix_boxed_1067_ = lean_unbox_uint64(v_anchorPrefix_1063_);
lean_dec_ref(v_anchorPrefix_1063_);
v_res_1068_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_1062_, v_anchorPrefix_boxed_1067_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_numDigits_1062_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_1069_, uint64_t v_anchor_1070_, lean_object* v_a_1071_){
_start:
{
uint64_t v___x_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v___x_1076_; uint64_t v___x_1077_; uint64_t v_anchorPrefix_1078_; lean_object* v___x_1079_; 
v___x_1073_ = 64ULL;
v___x_1074_ = lean_uint64_of_nat(v_numDigits_1069_);
v___x_1075_ = 2ULL;
v___x_1076_ = lean_uint64_shift_left(v___x_1074_, v___x_1075_);
v___x_1077_ = lean_uint64_sub(v___x_1073_, v___x_1076_);
v_anchorPrefix_1078_ = lean_uint64_shift_right(v_anchor_1070_, v___x_1077_);
v___x_1079_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1069_, v_anchorPrefix_1078_, v_a_1071_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_1080_, lean_object* v_anchor_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
uint64_t v_anchor_boxed_1084_; lean_object* v_res_1085_; 
v_anchor_boxed_1084_ = lean_unbox_uint64(v_anchor_1081_);
lean_dec_ref(v_anchor_1081_);
v_res_1085_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1080_, v_anchor_boxed_1084_, v_a_1082_);
lean_dec_ref(v_a_1082_);
lean_dec(v_numDigits_1080_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_1086_, uint64_t v_anchor_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1086_, v_anchor_1087_, v_a_1088_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_1092_, lean_object* v_anchor_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
uint64_t v_anchor_boxed_1097_; lean_object* v_res_1098_; 
v_anchor_boxed_1097_ = lean_unbox_uint64(v_anchor_1093_);
lean_dec_ref(v_anchor_1093_);
v_res_1098_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_1092_, v_anchor_boxed_1097_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_numDigits_1092_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_1099_);
v___x_1111_ = l_Lean_Meta_Grind_getAnchor(v___x_1110_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_s_1112_);
return v_res_1123_;
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

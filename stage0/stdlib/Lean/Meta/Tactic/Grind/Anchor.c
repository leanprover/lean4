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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instDecidableEqUInt64___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_anchorPrefixToString(lean_object*, uint64_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SplitInfo_getExpr(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_sub(uint64_t, uint64_t);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0;
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_getAnchor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAnchor___closed__0;
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0(void){
_start:
{
lean_object* v___x_1_; uint64_t v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1723u);
v___x_2_ = lean_uint64_of_nat(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(lean_object* v_n_3_){
_start:
{
uint8_t v___y_5_; uint8_t v___x_17_; 
v___x_17_ = l_Lean_Name_hasMacroScopes(v_n_3_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; 
lean_inc(v_n_3_);
v___x_18_ = l_Lean_Name_isInaccessibleUserName(v_n_3_);
v___y_5_ = v___x_18_;
goto v___jp_4_;
}
else
{
v___y_5_ = v___x_17_;
goto v___jp_4_;
}
v___jp_4_:
{
if (v___y_5_ == 0)
{
uint8_t v___x_6_; 
v___x_6_ = l_Lean_Name_isImplementationDetail(v_n_3_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
v___x_7_ = l_Lean_isPrivateName(v_n_3_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; 
v___x_8_ = l_Lean_Name_isInternal(v_n_3_);
if (v___x_8_ == 0)
{
if (lean_obj_tag(v_n_3_) == 0)
{
uint64_t v___x_9_; 
v___x_9_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0);
return v___x_9_;
}
else
{
uint64_t v_hash_10_; 
v_hash_10_ = lean_ctor_get_uint64(v_n_3_, sizeof(void*)*2);
lean_dec(v_n_3_);
return v_hash_10_;
}
}
else
{
uint64_t v___x_11_; 
lean_dec(v_n_3_);
v___x_11_ = 0ULL;
return v___x_11_;
}
}
else
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_privateToUserName(v_n_3_);
if (lean_obj_tag(v___x_12_) == 0)
{
uint64_t v___x_13_; 
v___x_13_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0);
return v___x_13_;
}
else
{
uint64_t v_hash_14_; 
v_hash_14_ = lean_ctor_get_uint64(v___x_12_, sizeof(void*)*2);
lean_dec(v___x_12_);
return v_hash_14_;
}
}
}
else
{
uint64_t v___x_15_; 
lean_dec(v_n_3_);
v___x_15_ = 0ULL;
return v___x_15_;
}
}
else
{
uint64_t v___x_16_; 
lean_dec(v_n_3_);
v___x_16_ = 0ULL;
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(lean_object* v_n_19_){
_start:
{
uint64_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_19_);
v_r_21_ = lean_box_uint64(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t v_a_22_, uint64_t v_b_23_){
_start:
{
uint64_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = 0ULL;
v___x_25_ = lean_uint64_dec_eq(v_a_22_, v___x_24_);
if (v___x_25_ == 0)
{
uint8_t v___x_26_; 
v___x_26_ = lean_uint64_dec_eq(v_b_23_, v___x_24_);
if (v___x_26_ == 0)
{
uint64_t v___x_27_; 
v___x_27_ = lean_uint64_mix_hash(v_a_22_, v_b_23_);
return v___x_27_;
}
else
{
return v_a_22_;
}
}
else
{
return v_b_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(lean_object* v_a_28_, lean_object* v_b_29_){
_start:
{
uint64_t v_a_boxed_30_; uint64_t v_b_boxed_31_; uint64_t v_res_32_; lean_object* v_r_33_; 
v_a_boxed_30_ = lean_unbox_uint64(v_a_28_);
lean_dec_ref(v_a_28_);
v_b_boxed_31_ = lean_unbox_uint64(v_b_29_);
lean_dec_ref(v_b_29_);
v_res_32_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_a_boxed_30_, v_b_boxed_31_);
v_r_33_ = lean_box_uint64(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(lean_object* v_declName_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; lean_object* v_env_38_; uint8_t v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_37_ = lean_st_ref_get(v___y_35_);
v_env_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc_ref(v_env_38_);
lean_dec(v___x_37_);
v___x_39_ = l_Lean_Meta_isMatcherCore(v_env_38_, v_declName_34_);
v___x_40_ = lean_box(v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(lean_object* v_declName_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_42_, v___y_43_);
lean_dec(v___y_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(lean_object* v_declName_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_46_, v___y_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(lean_object* v_declName_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(v_declName_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_ks_74_; lean_object* v_vs_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_101_; 
v_ks_74_ = lean_ctor_get(v_x_70_, 0);
v_vs_75_ = lean_ctor_get(v_x_70_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_101_ == 0)
{
v___x_77_ = v_x_70_;
v_isShared_78_ = v_isSharedCheck_101_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_vs_75_);
lean_inc(v_ks_74_);
lean_dec(v_x_70_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_101_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_array_get_size(v_ks_74_);
v___x_80_ = lean_nat_dec_lt(v_x_71_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_dec(v_x_71_);
v___x_81_ = lean_array_push(v_ks_74_, v_x_72_);
v___x_82_ = lean_array_push(v_vs_75_, v_x_73_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_82_);
lean_ctor_set(v___x_77_, 0, v___x_81_);
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v_k_x27_86_; size_t v___x_87_; size_t v___x_88_; uint8_t v___x_89_; 
v_k_x27_86_ = lean_array_fget_borrowed(v_ks_74_, v_x_71_);
v___x_87_ = lean_ptr_addr(v_x_72_);
v___x_88_ = lean_ptr_addr(v_k_x27_86_);
v___x_89_ = lean_usize_dec_eq(v___x_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_91_; 
if (v_isShared_78_ == 0)
{
v___x_91_ = v___x_77_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_ks_74_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_vs_75_);
v___x_91_ = v_reuseFailAlloc_95_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_add(v_x_71_, v___x_92_);
lean_dec(v_x_71_);
v_x_70_ = v___x_91_;
v_x_71_ = v___x_93_;
goto _start;
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_96_ = lean_array_fset(v_ks_74_, v_x_71_, v_x_72_);
v___x_97_ = lean_array_fset(v_vs_75_, v_x_71_, v_x_73_);
lean_dec(v_x_71_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_97_);
lean_ctor_set(v___x_77_, 0, v___x_96_);
v___x_99_ = v___x_77_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(lean_object* v_n_102_, lean_object* v_k_103_, lean_object* v_v_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_n_102_, v___x_105_, v_k_103_, v_v_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(lean_object* v_x_108_, size_t v_x_109_, size_t v_x_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v_es_113_; size_t v___x_114_; size_t v___x_115_; lean_object* v_j_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_es_113_ = lean_ctor_get(v_x_108_, 0);
v___x_114_ = ((size_t)31ULL);
v___x_115_ = lean_usize_land(v_x_109_, v___x_114_);
v_j_116_ = lean_usize_to_nat(v___x_115_);
v___x_117_ = lean_array_get_size(v_es_113_);
v___x_118_ = lean_nat_dec_lt(v_j_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec(v_j_116_);
lean_dec(v_x_112_);
lean_dec_ref(v_x_111_);
return v_x_108_;
}
else
{
lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_159_; 
lean_inc_ref(v_es_113_);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_x_108_, 0);
lean_dec(v_unused_160_);
v___x_120_ = v_x_108_;
v_isShared_121_ = v_isSharedCheck_159_;
goto v_resetjp_119_;
}
else
{
lean_dec(v_x_108_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_159_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_v_122_; lean_object* v___x_123_; lean_object* v_xs_x27_124_; lean_object* v___y_126_; 
v_v_122_ = lean_array_fget(v_es_113_, v_j_116_);
v___x_123_ = lean_box(0);
v_xs_x27_124_ = lean_array_fset(v_es_113_, v_j_116_, v___x_123_);
switch(lean_obj_tag(v_v_122_))
{
case 0:
{
lean_object* v_key_131_; lean_object* v_val_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_144_; 
v_key_131_ = lean_ctor_get(v_v_122_, 0);
v_val_132_ = lean_ctor_get(v_v_122_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_v_122_);
if (v_isSharedCheck_144_ == 0)
{
v___x_134_ = v_v_122_;
v_isShared_135_ = v_isSharedCheck_144_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_val_132_);
lean_inc(v_key_131_);
lean_dec(v_v_122_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_144_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
size_t v___x_136_; size_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_ptr_addr(v_x_111_);
v___x_137_ = lean_ptr_addr(v_key_131_);
v___x_138_ = lean_usize_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_del_object(v___x_134_);
v___x_139_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_131_, v_val_132_, v_x_111_, v_x_112_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___y_126_ = v___x_140_;
goto v___jp_125_;
}
else
{
lean_object* v___x_142_; 
lean_dec(v_val_132_);
lean_dec(v_key_131_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_x_112_);
lean_ctor_set(v___x_134_, 0, v_x_111_);
v___x_142_ = v___x_134_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_x_111_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_x_112_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
v___y_126_ = v___x_142_;
goto v___jp_125_;
}
}
}
}
case 1:
{
lean_object* v_node_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_157_; 
v_node_145_ = lean_ctor_get(v_v_122_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v_v_122_);
if (v_isSharedCheck_157_ == 0)
{
v___x_147_ = v_v_122_;
v_isShared_148_ = v_isSharedCheck_157_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_node_145_);
lean_dec(v_v_122_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_157_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_149_ = ((size_t)5ULL);
v___x_150_ = lean_usize_shift_right(v_x_109_, v___x_149_);
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_add(v_x_110_, v___x_151_);
v___x_153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_node_145_, v___x_150_, v___x_152_, v_x_111_, v_x_112_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_153_);
v___x_155_ = v___x_147_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
v___y_126_ = v___x_155_;
goto v___jp_125_;
}
}
}
default: 
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_x_111_);
lean_ctor_set(v___x_158_, 1, v_x_112_);
v___y_126_ = v___x_158_;
goto v___jp_125_;
}
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_array_fset(v_xs_x27_124_, v_j_116_, v___y_126_);
lean_dec(v_j_116_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_127_);
v___x_129_ = v___x_120_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
else
{
lean_object* v_ks_161_; lean_object* v_vs_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_182_; 
v_ks_161_ = lean_ctor_get(v_x_108_, 0);
v_vs_162_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_182_ == 0)
{
v___x_164_ = v_x_108_;
v_isShared_165_ = v_isSharedCheck_182_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_vs_162_);
lean_inc(v_ks_161_);
lean_dec(v_x_108_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_182_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_ks_161_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_vs_162_);
v___x_167_ = v_reuseFailAlloc_181_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v_newNode_168_; uint8_t v___y_170_; size_t v___x_176_; uint8_t v___x_177_; 
v_newNode_168_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v___x_167_, v_x_111_, v_x_112_);
v___x_176_ = ((size_t)7ULL);
v___x_177_ = lean_usize_dec_le(v___x_176_, v_x_110_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_168_);
v___x_179_ = lean_unsigned_to_nat(4u);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
lean_dec(v___x_178_);
v___y_170_ = v___x_180_;
goto v___jp_169_;
}
else
{
v___y_170_ = v___x_177_;
goto v___jp_169_;
}
v___jp_169_:
{
if (v___y_170_ == 0)
{
lean_object* v_ks_171_; lean_object* v_vs_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_ks_171_ = lean_ctor_get(v_newNode_168_, 0);
lean_inc_ref(v_ks_171_);
v_vs_172_ = lean_ctor_get(v_newNode_168_, 1);
lean_inc_ref(v_vs_172_);
lean_dec_ref(v_newNode_168_);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0);
v___x_175_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_x_110_, v_ks_171_, v_vs_172_, v___x_173_, v___x_174_);
lean_dec_ref(v_vs_172_);
lean_dec_ref(v_ks_171_);
return v___x_175_;
}
else
{
return v_newNode_168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(size_t v_depth_183_, lean_object* v_keys_184_, lean_object* v_vals_185_, lean_object* v_i_186_, lean_object* v_entries_187_){
_start:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_array_get_size(v_keys_184_);
v___x_189_ = lean_nat_dec_lt(v_i_186_, v___x_188_);
if (v___x_189_ == 0)
{
lean_dec(v_i_186_);
return v_entries_187_;
}
else
{
lean_object* v_k_190_; lean_object* v_v_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; uint64_t v___x_195_; size_t v_h_196_; size_t v___x_197_; lean_object* v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v_h_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_k_190_ = lean_array_fget_borrowed(v_keys_184_, v_i_186_);
v_v_191_ = lean_array_fget_borrowed(v_vals_185_, v_i_186_);
v___x_192_ = lean_ptr_addr(v_k_190_);
v___x_193_ = ((size_t)3ULL);
v___x_194_ = lean_usize_shift_right(v___x_192_, v___x_193_);
v___x_195_ = lean_usize_to_uint64(v___x_194_);
v_h_196_ = lean_uint64_to_usize(v___x_195_);
v___x_197_ = ((size_t)5ULL);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_sub(v_depth_183_, v___x_199_);
v___x_201_ = lean_usize_mul(v___x_197_, v___x_200_);
v_h_202_ = lean_usize_shift_right(v_h_196_, v___x_201_);
v___x_203_ = lean_nat_add(v_i_186_, v___x_198_);
lean_dec(v_i_186_);
lean_inc(v_v_191_);
lean_inc(v_k_190_);
v___x_204_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_entries_187_, v_h_202_, v_depth_183_, v_k_190_, v_v_191_);
v_i_186_ = v___x_203_;
v_entries_187_ = v___x_204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_depth_206_, lean_object* v_keys_207_, lean_object* v_vals_208_, lean_object* v_i_209_, lean_object* v_entries_210_){
_start:
{
size_t v_depth_boxed_211_; lean_object* v_res_212_; 
v_depth_boxed_211_ = lean_unbox_usize(v_depth_206_);
lean_dec(v_depth_206_);
v_res_212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_boxed_211_, v_keys_207_, v_vals_208_, v_i_209_, v_entries_210_);
lean_dec_ref(v_vals_208_);
lean_dec_ref(v_keys_207_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___boxed(lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
size_t v_x_32520__boxed_218_; size_t v_x_32521__boxed_219_; lean_object* v_res_220_; 
v_x_32520__boxed_218_ = lean_unbox_usize(v_x_214_);
lean_dec(v_x_214_);
v_x_32521__boxed_219_ = lean_unbox_usize(v_x_215_);
lean_dec(v_x_215_);
v_res_220_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_213_, v_x_32520__boxed_218_, v_x_32521__boxed_219_, v_x_216_, v_x_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; uint64_t v___x_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; 
v___x_224_ = lean_ptr_addr(v_x_222_);
v___x_225_ = ((size_t)3ULL);
v___x_226_ = lean_usize_shift_right(v___x_224_, v___x_225_);
v___x_227_ = lean_usize_to_uint64(v___x_226_);
v___x_228_ = lean_uint64_to_usize(v___x_227_);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_221_, v___x_228_, v___x_229_, v_x_222_, v_x_223_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object* v_keys_231_, lean_object* v_vals_232_, lean_object* v_i_233_, lean_object* v_k_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_get_size(v_keys_231_);
v___x_236_ = lean_nat_dec_lt(v_i_233_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_i_233_);
v___x_237_ = lean_box(0);
return v___x_237_;
}
else
{
lean_object* v_k_x27_238_; size_t v___x_239_; size_t v___x_240_; uint8_t v___x_241_; 
v_k_x27_238_ = lean_array_fget_borrowed(v_keys_231_, v_i_233_);
v___x_239_ = lean_ptr_addr(v_k_234_);
v___x_240_ = lean_ptr_addr(v_k_x27_238_);
v___x_241_ = lean_usize_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_i_233_, v___x_242_);
lean_dec(v_i_233_);
v_i_233_ = v___x_243_;
goto _start;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_array_fget_borrowed(v_vals_232_, v_i_233_);
lean_dec(v_i_233_);
lean_inc(v___x_245_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_keys_247_, lean_object* v_vals_248_, lean_object* v_i_249_, lean_object* v_k_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_247_, v_vals_248_, v_i_249_, v_k_250_);
lean_dec_ref(v_k_250_);
lean_dec_ref(v_vals_248_);
lean_dec_ref(v_keys_247_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object* v_x_252_, size_t v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v_es_255_; lean_object* v___x_256_; size_t v___x_257_; size_t v___x_258_; lean_object* v_j_259_; lean_object* v___x_260_; 
v_es_255_ = lean_ctor_get(v_x_252_, 0);
v___x_256_ = lean_box(2);
v___x_257_ = ((size_t)31ULL);
v___x_258_ = lean_usize_land(v_x_253_, v___x_257_);
v_j_259_ = lean_usize_to_nat(v___x_258_);
v___x_260_ = lean_array_get_borrowed(v___x_256_, v_es_255_, v_j_259_);
lean_dec(v_j_259_);
switch(lean_obj_tag(v___x_260_))
{
case 0:
{
lean_object* v_key_261_; lean_object* v_val_262_; size_t v___x_263_; size_t v___x_264_; uint8_t v___x_265_; 
v_key_261_ = lean_ctor_get(v___x_260_, 0);
v_val_262_ = lean_ctor_get(v___x_260_, 1);
v___x_263_ = lean_ptr_addr(v_x_254_);
v___x_264_ = lean_ptr_addr(v_key_261_);
v___x_265_ = lean_usize_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
else
{
lean_object* v___x_267_; 
lean_inc(v_val_262_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_val_262_);
return v___x_267_;
}
}
case 1:
{
lean_object* v_node_268_; size_t v___x_269_; size_t v___x_270_; 
v_node_268_ = lean_ctor_get(v___x_260_, 0);
v___x_269_ = ((size_t)5ULL);
v___x_270_ = lean_usize_shift_right(v_x_253_, v___x_269_);
v_x_252_ = v_node_268_;
v_x_253_ = v___x_270_;
goto _start;
}
default: 
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
else
{
lean_object* v_ks_273_; lean_object* v_vs_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_ks_273_ = lean_ctor_get(v_x_252_, 0);
v_vs_274_ = lean_ctor_get(v_x_252_, 1);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_273_, v_vs_274_, v___x_275_, v_x_254_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
size_t v_x_32725__boxed_280_; lean_object* v_res_281_; 
v_x_32725__boxed_280_ = lean_unbox_usize(v_x_278_);
lean_dec(v_x_278_);
v_res_281_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_277_, v_x_32725__boxed_280_, v_x_279_);
lean_dec_ref(v_x_279_);
lean_dec_ref(v_x_277_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; uint64_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_284_ = lean_ptr_addr(v_x_283_);
v___x_285_ = ((size_t)3ULL);
v___x_286_ = lean_usize_shift_right(v___x_284_, v___x_285_);
v___x_287_ = lean_usize_to_uint64(v___x_286_);
v___x_288_ = lean_uint64_to_usize(v___x_287_);
v___x_289_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_282_, v___x_288_, v_x_283_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_290_, v_x_291_);
lean_dec_ref(v_x_291_);
lean_dec_ref(v_x_290_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAnchor___closed__0(void){
_start:
{
lean_object* v___x_293_; lean_object* v_dummy_294_; 
v___x_293_ = lean_box(0);
v_dummy_294_ = l_Lean_Expr_sort___override(v___x_293_);
return v_dummy_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_pinfos_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; uint8_t v___y_328_; 
if (lean_obj_tag(v_x_297_) == 5)
{
lean_object* v_fn_347_; lean_object* v_arg_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_fn_347_ = lean_ctor_get(v_x_297_, 0);
lean_inc_ref(v_fn_347_);
v_arg_348_ = lean_ctor_get(v_x_297_, 1);
lean_inc_ref(v_arg_348_);
lean_dec_ref_known(v_x_297_, 2);
v___x_349_ = lean_array_set(v_x_298_, v_x_299_, v_arg_348_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_sub(v_x_299_, v___x_350_);
lean_dec(v_x_299_);
v_x_297_ = v_fn_347_;
v_x_298_ = v___x_349_;
v_x_299_ = v___x_351_;
goto _start;
}
else
{
uint8_t v___x_353_; 
lean_dec(v_x_299_);
v___x_353_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_297_);
if (v___x_353_ == 0)
{
v___y_328_ = v___x_353_;
goto v___jp_327_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = lean_array_get_size(v_x_298_);
v___x_355_ = lean_unsigned_to_nat(2u);
v___x_356_ = lean_nat_dec_eq(v___x_354_, v___x_355_);
v___y_328_ = v___x_356_;
goto v___jp_327_;
}
}
v___jp_310_:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Grind_getAnchor(v_x_297_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint64_t v___x_325_; lean_object* v___x_326_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_array_get_size(v_x_298_);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_unbox_uint64(v_a_322_);
lean_dec(v_a_322_);
v___x_326_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v___x_323_, v_x_298_, v_pinfos_311_, v___x_324_, v___x_325_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec_ref(v_pinfos_311_);
lean_dec_ref(v_x_298_);
return v___x_326_;
}
else
{
lean_dec_ref(v_pinfos_311_);
lean_dec_ref(v_x_298_);
return v___x_321_;
}
}
v___jp_327_:
{
if (v___y_328_ == 0)
{
uint8_t v___x_329_; 
v___x_329_ = l_Lean_Expr_hasLooseBVars(v_x_297_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_box(0);
lean_inc_ref(v_x_297_);
v___x_331_ = l_Lean_Meta_getFunInfo(v_x_297_, v___x_330_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_paramInfo_333_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v_paramInfo_333_ = lean_ctor_get(v_a_332_, 0);
lean_inc_ref(v_paramInfo_333_);
lean_dec(v_a_332_);
v_pinfos_311_ = v_paramInfo_333_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
v___y_319_ = v___y_307_;
v___y_320_ = v___y_308_;
goto v___jp_310_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_x_298_);
lean_dec_ref(v_x_297_);
v_a_334_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_331_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_331_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v___x_342_; 
v___x_342_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0));
v_pinfos_311_ = v___x_342_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
v___y_319_ = v___y_307_;
v___y_320_ = v___y_308_;
goto v___jp_310_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref(v_x_297_);
v___x_343_ = l_Lean_instInhabitedExpr;
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_array_get(v___x_343_, v_x_298_, v___x_344_);
lean_dec_ref(v_x_298_);
v___x_346_ = l_Lean_Meta_Grind_getAnchor(v___x_345_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
uint64_t v_a_369_; lean_object* v___y_370_; lean_object* v_n_395_; lean_object* v_d_396_; lean_object* v_b_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___x_416_; lean_object* v_anchors_417_; lean_object* v___x_418_; 
v___x_416_ = lean_st_ref_get(v_a_360_);
v_anchors_417_ = lean_ctor_get(v___x_416_, 8);
lean_inc_ref(v_anchors_417_);
lean_dec(v___x_416_);
v___x_418_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_417_, v_e_357_);
lean_dec_ref(v_anchors_417_);
if (lean_obj_tag(v___x_418_) == 1)
{
lean_object* v_val_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_e_357_);
v_val_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_val_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 0);
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_val_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_dec(v___x_418_);
switch(lean_obj_tag(v_e_357_))
{
case 0:
{
lean_object* v_deBruijnIndex_427_; uint64_t v___x_428_; 
v_deBruijnIndex_427_ = lean_ctor_get(v_e_357_, 0);
v___x_428_ = lean_uint64_of_nat(v_deBruijnIndex_427_);
v_a_369_ = v___x_428_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
case 1:
{
lean_object* v_fvarId_429_; lean_object* v___x_430_; 
v_fvarId_429_ = lean_ctor_get(v_e_357_, 0);
lean_inc(v_fvarId_429_);
v___x_430_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_429_, v_a_363_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; uint64_t v___x_433_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v___x_432_ = l_Lean_LocalDecl_userName(v_a_431_);
lean_dec(v_a_431_);
v___x_433_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_432_);
v_a_369_ = v___x_433_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref_known(v_e_357_, 1);
v_a_434_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_430_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_430_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
case 4:
{
lean_object* v_declName_442_; lean_object* v___x_443_; 
v_declName_442_ = lean_ctor_get(v_e_357_, 0);
lean_inc(v_declName_442_);
v___x_443_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_442_, v_a_366_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; uint8_t v___x_445_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = lean_unbox(v_a_444_);
lean_dec(v_a_444_);
if (v___x_445_ == 0)
{
uint64_t v___x_446_; 
lean_inc(v_declName_442_);
v___x_446_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_442_);
v_a_369_ = v___x_446_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
else
{
uint64_t v___x_447_; 
v___x_447_ = 0ULL;
v_a_369_ = v___x_447_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref_known(v_e_357_, 2);
v_a_448_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_443_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_443_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
case 5:
{
lean_object* v_dummy_456_; lean_object* v_nargs_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_dummy_456_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_457_ = l_Lean_Expr_getAppNumArgs(v_e_357_);
lean_inc(v_nargs_457_);
v___x_458_ = lean_mk_array(v_nargs_457_, v_dummy_456_);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_sub(v_nargs_457_, v___x_459_);
lean_dec(v_nargs_457_);
lean_inc_ref(v_e_357_);
v___x_461_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_357_, v___x_458_, v___x_460_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; uint64_t v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = lean_unbox_uint64(v_a_462_);
lean_dec(v_a_462_);
v_a_369_ = v___x_463_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
else
{
lean_dec_ref_known(v_e_357_, 2);
return v___x_461_;
}
}
case 6:
{
lean_object* v_binderName_464_; lean_object* v_binderType_465_; lean_object* v_body_466_; 
v_binderName_464_ = lean_ctor_get(v_e_357_, 0);
v_binderType_465_ = lean_ctor_get(v_e_357_, 1);
v_body_466_ = lean_ctor_get(v_e_357_, 2);
lean_inc_ref(v_body_466_);
lean_inc_ref(v_binderType_465_);
lean_inc(v_binderName_464_);
v_n_395_ = v_binderName_464_;
v_d_396_ = v_binderType_465_;
v_b_397_ = v_body_466_;
v___y_398_ = v_a_358_;
v___y_399_ = v_a_359_;
v___y_400_ = v_a_360_;
v___y_401_ = v_a_361_;
v___y_402_ = v_a_362_;
v___y_403_ = v_a_363_;
v___y_404_ = v_a_364_;
v___y_405_ = v_a_365_;
v___y_406_ = v_a_366_;
goto v___jp_394_;
}
case 7:
{
lean_object* v_binderName_467_; lean_object* v_binderType_468_; lean_object* v_body_469_; 
v_binderName_467_ = lean_ctor_get(v_e_357_, 0);
v_binderType_468_ = lean_ctor_get(v_e_357_, 1);
v_body_469_ = lean_ctor_get(v_e_357_, 2);
lean_inc_ref(v_body_469_);
lean_inc_ref(v_binderType_468_);
lean_inc(v_binderName_467_);
v_n_395_ = v_binderName_467_;
v_d_396_ = v_binderType_468_;
v_b_397_ = v_body_469_;
v___y_398_ = v_a_358_;
v___y_399_ = v_a_359_;
v___y_400_ = v_a_360_;
v___y_401_ = v_a_361_;
v___y_402_ = v_a_362_;
v___y_403_ = v_a_363_;
v___y_404_ = v_a_364_;
v___y_405_ = v_a_365_;
v___y_406_ = v_a_366_;
goto v___jp_394_;
}
case 8:
{
lean_object* v_declName_470_; lean_object* v_type_471_; lean_object* v_value_472_; lean_object* v_body_473_; lean_object* v___x_474_; 
v_declName_470_ = lean_ctor_get(v_e_357_, 0);
v_type_471_ = lean_ctor_get(v_e_357_, 1);
v_value_472_ = lean_ctor_get(v_e_357_, 2);
v_body_473_ = lean_ctor_get(v_e_357_, 3);
lean_inc_ref(v_value_472_);
v___x_474_ = l_Lean_Meta_Grind_getAnchor(v_value_472_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
lean_inc_ref(v_type_471_);
v___x_476_ = l_Lean_Meta_Grind_getAnchor(v_type_471_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
lean_inc_ref(v_body_473_);
v___x_478_ = l_Lean_Meta_Grind_getAnchor(v_body_473_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
lean_inc(v_declName_470_);
v___x_480_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_470_);
v___x_481_ = lean_unbox_uint64(v_a_477_);
lean_dec(v_a_477_);
v___x_482_ = lean_unbox_uint64(v_a_479_);
lean_dec(v_a_479_);
v___x_483_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_481_, v___x_482_);
v___x_484_ = lean_unbox_uint64(v_a_475_);
lean_dec(v_a_475_);
v___x_485_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_484_, v___x_483_);
v___x_486_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_480_, v___x_485_);
v_a_369_ = v___x_486_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
else
{
lean_dec(v_a_477_);
lean_dec(v_a_475_);
lean_dec_ref_known(v_e_357_, 4);
return v___x_478_;
}
}
else
{
lean_dec(v_a_475_);
lean_dec_ref_known(v_e_357_, 4);
return v___x_476_;
}
}
else
{
lean_dec_ref_known(v_e_357_, 4);
return v___x_474_;
}
}
case 9:
{
lean_object* v_a_487_; uint64_t v___x_488_; 
v_a_487_ = lean_ctor_get(v_e_357_, 0);
v___x_488_ = l_Lean_Literal_hash(v_a_487_);
v_a_369_ = v___x_488_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
case 10:
{
lean_object* v_expr_489_; lean_object* v___x_490_; 
v_expr_489_ = lean_ctor_get(v_e_357_, 1);
lean_inc_ref(v_expr_489_);
v___x_490_ = l_Lean_Meta_Grind_getAnchor(v_expr_489_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint64_t v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_unbox_uint64(v_a_491_);
lean_dec(v_a_491_);
v_a_369_ = v___x_492_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
else
{
lean_dec_ref_known(v_e_357_, 2);
return v___x_490_;
}
}
case 11:
{
lean_object* v_idx_493_; lean_object* v_struct_494_; lean_object* v___x_495_; 
v_idx_493_ = lean_ctor_get(v_e_357_, 1);
v_struct_494_ = lean_ctor_get(v_e_357_, 2);
lean_inc_ref(v_struct_494_);
v___x_495_ = l_Lean_Meta_Grind_getAnchor(v_struct_494_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = lean_uint64_of_nat(v_idx_493_);
v___x_498_ = lean_unbox_uint64(v_a_496_);
lean_dec(v_a_496_);
v___x_499_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_497_, v___x_498_);
v_a_369_ = v___x_499_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
else
{
lean_dec_ref_known(v_e_357_, 3);
return v___x_495_;
}
}
default: 
{
uint64_t v___x_500_; 
v___x_500_ = 0ULL;
v_a_369_ = v___x_500_;
v___y_370_ = v_a_360_;
goto v___jp_368_;
}
}
}
v___jp_368_:
{
lean_object* v___x_371_; lean_object* v_congrThms_372_; lean_object* v_simp_373_; lean_object* v_lastTag_374_; lean_object* v_counters_375_; lean_object* v_splitDiags_376_; lean_object* v_ematchDiags_377_; lean_object* v_lawfulEqCmpMap_378_; lean_object* v_reflCmpMap_379_; lean_object* v_anchors_380_; lean_object* v_instanceMap_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_393_; 
v___x_371_ = lean_st_ref_take(v___y_370_);
v_congrThms_372_ = lean_ctor_get(v___x_371_, 0);
v_simp_373_ = lean_ctor_get(v___x_371_, 1);
v_lastTag_374_ = lean_ctor_get(v___x_371_, 2);
v_counters_375_ = lean_ctor_get(v___x_371_, 3);
v_splitDiags_376_ = lean_ctor_get(v___x_371_, 4);
v_ematchDiags_377_ = lean_ctor_get(v___x_371_, 5);
v_lawfulEqCmpMap_378_ = lean_ctor_get(v___x_371_, 6);
v_reflCmpMap_379_ = lean_ctor_get(v___x_371_, 7);
v_anchors_380_ = lean_ctor_get(v___x_371_, 8);
v_instanceMap_381_ = lean_ctor_get(v___x_371_, 9);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_393_ == 0)
{
v___x_383_ = v___x_371_;
v_isShared_384_ = v_isSharedCheck_393_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_instanceMap_381_);
lean_inc(v_anchors_380_);
lean_inc(v_reflCmpMap_379_);
lean_inc(v_lawfulEqCmpMap_378_);
lean_inc(v_ematchDiags_377_);
lean_inc(v_splitDiags_376_);
lean_inc(v_counters_375_);
lean_inc(v_lastTag_374_);
lean_inc(v_simp_373_);
lean_inc(v_congrThms_372_);
lean_dec(v___x_371_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_393_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = lean_box_uint64(v_a_369_);
v___x_386_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_anchors_380_, v_e_357_, v___x_385_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 8, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_congrThms_372_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_simp_373_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_lastTag_374_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_counters_375_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_splitDiags_376_);
lean_ctor_set(v_reuseFailAlloc_392_, 5, v_ematchDiags_377_);
lean_ctor_set(v_reuseFailAlloc_392_, 6, v_lawfulEqCmpMap_378_);
lean_ctor_set(v_reuseFailAlloc_392_, 7, v_reflCmpMap_379_);
lean_ctor_set(v_reuseFailAlloc_392_, 8, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_392_, 9, v_instanceMap_381_);
v___x_388_ = v_reuseFailAlloc_392_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_st_ref_set(v___y_370_, v___x_388_);
v___x_390_ = lean_box_uint64(v_a_369_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
}
v___jp_394_:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Grind_getAnchor(v_d_396_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l_Lean_Meta_Grind_getAnchor(v_b_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_395_);
v___x_412_ = lean_unbox_uint64(v_a_408_);
lean_dec(v_a_408_);
v___x_413_ = lean_unbox_uint64(v_a_410_);
lean_dec(v_a_410_);
v___x_414_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_412_, v___x_413_);
v___x_415_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_411_, v___x_414_);
v_a_369_ = v___x_415_;
v___y_370_ = v___y_400_;
goto v___jp_368_;
}
else
{
lean_dec(v_a_408_);
lean_dec(v_n_395_);
lean_dec_ref(v_e_357_);
return v___x_409_;
}
}
else
{
lean_dec_ref(v_b_397_);
lean_dec(v_n_395_);
lean_dec_ref(v_e_357_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_upperBound_501_, lean_object* v_args_502_, lean_object* v_pinfos_503_, lean_object* v_a_504_, uint64_t v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
uint64_t v_a_517_; uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_lt(v_a_504_, v_upperBound_501_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_a_504_);
v___x_522_ = lean_box_uint64(v_b_505_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_array_fget_borrowed(v_args_502_, v_a_504_);
v___x_525_ = lean_array_get_size(v_pinfos_503_);
v___x_526_ = lean_nat_dec_lt(v_a_504_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_inc(v___x_524_);
v___x_527_ = l_Lean_Meta_Grind_getAnchor(v___x_524_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; uint64_t v___x_529_; uint64_t v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = lean_unbox_uint64(v_a_528_);
lean_dec(v_a_528_);
v___x_530_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_505_, v___x_529_);
v_a_517_ = v___x_530_;
goto v___jp_516_;
}
else
{
lean_dec(v_a_504_);
return v___x_527_;
}
}
else
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_array_fget_borrowed(v_pinfos_503_, v_a_504_);
v___x_532_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; 
lean_inc(v___x_524_);
v___x_533_ = l_Lean_Meta_Grind_getAnchor(v___x_524_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; uint64_t v___x_535_; uint64_t v___x_536_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = lean_unbox_uint64(v_a_534_);
lean_dec(v_a_534_);
v___x_536_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_505_, v___x_535_);
v_a_517_ = v___x_536_;
goto v___jp_516_;
}
else
{
lean_dec(v_a_504_);
return v___x_533_;
}
}
else
{
v_a_517_ = v_b_505_;
goto v___jp_516_;
}
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_a_504_, v___x_518_);
lean_dec(v_a_504_);
v_a_504_ = v___x_519_;
v_b_505_ = v_a_517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg___boxed(lean_object* v_upperBound_537_, lean_object* v_args_538_, lean_object* v_pinfos_539_, lean_object* v_a_540_, lean_object* v_b_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
uint64_t v_b_boxed_552_; lean_object* v_res_553_; 
v_b_boxed_552_ = lean_unbox_uint64(v_b_541_);
lean_dec_ref(v_b_541_);
v_res_553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_537_, v_args_538_, v_pinfos_539_, v_a_540_, v_b_boxed_552_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v_pinfos_539_);
lean_dec_ref(v_args_538_);
lean_dec(v_upperBound_537_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_554_, v_x_555_, v_x_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_Grind_getAnchor(v_e_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_upperBound_580_, lean_object* v_args_581_, lean_object* v_pinfos_582_, lean_object* v_inst_583_, lean_object* v_R_584_, lean_object* v_a_585_, uint64_t v_b_586_, lean_object* v_c_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_580_, v_args_581_, v_pinfos_582_, v_a_585_, v_b_586_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_599_ = _args[0];
lean_object* v_args_600_ = _args[1];
lean_object* v_pinfos_601_ = _args[2];
lean_object* v_inst_602_ = _args[3];
lean_object* v_R_603_ = _args[4];
lean_object* v_a_604_ = _args[5];
lean_object* v_b_605_ = _args[6];
lean_object* v_c_606_ = _args[7];
lean_object* v___y_607_ = _args[8];
lean_object* v___y_608_ = _args[9];
lean_object* v___y_609_ = _args[10];
lean_object* v___y_610_ = _args[11];
lean_object* v___y_611_ = _args[12];
lean_object* v___y_612_ = _args[13];
lean_object* v___y_613_ = _args[14];
lean_object* v___y_614_ = _args[15];
lean_object* v___y_615_ = _args[16];
lean_object* v___y_616_ = _args[17];
_start:
{
uint64_t v_b_boxed_617_; lean_object* v_res_618_; 
v_b_boxed_617_ = lean_unbox_uint64(v_b_605_);
lean_dec_ref(v_b_605_);
v_res_618_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(v_upperBound_599_, v_args_600_, v_pinfos_601_, v_inst_602_, v_R_603_, v_a_604_, v_b_boxed_617_, v_c_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v_pinfos_601_);
lean_dec_ref(v_args_600_);
lean_dec(v_upperBound_599_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_00_u03b2_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_x_620_, v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_628_, v_x_629_, v_x_630_);
lean_dec_ref(v_x_630_);
lean_dec_ref(v_x_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, size_t v_x_634_, size_t v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_633_, v_x_634_, v_x_635_, v_x_636_, v_x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(lean_object* v_00_u03b2_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
size_t v_x_33315__boxed_645_; size_t v_x_33316__boxed_646_; lean_object* v_res_647_; 
v_x_33315__boxed_645_ = lean_unbox_usize(v_x_641_);
lean_dec(v_x_641_);
v_x_33316__boxed_646_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_res_647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(v_00_u03b2_639_, v_x_640_, v_x_33315__boxed_645_, v_x_33316__boxed_646_, v_x_643_, v_x_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_648_, lean_object* v_x_649_, size_t v_x_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_649_, v_x_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
size_t v_x_33332__boxed_657_; lean_object* v_res_658_; 
v_x_33332__boxed_657_ = lean_unbox_usize(v_x_655_);
lean_dec(v_x_655_);
v_res_658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_653_, v_x_654_, v_x_33332__boxed_657_, v_x_656_);
lean_dec_ref(v_x_656_);
lean_dec_ref(v_x_654_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_659_, lean_object* v_n_660_, lean_object* v_k_661_, lean_object* v_v_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v_n_660_, v_k_661_, v_v_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_664_, size_t v_depth_665_, lean_object* v_keys_666_, lean_object* v_vals_667_, lean_object* v_heq_668_, lean_object* v_i_669_, lean_object* v_entries_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_665_, v_keys_666_, v_vals_667_, v_i_669_, v_entries_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_672_, lean_object* v_depth_673_, lean_object* v_keys_674_, lean_object* v_vals_675_, lean_object* v_heq_676_, lean_object* v_i_677_, lean_object* v_entries_678_){
_start:
{
size_t v_depth_boxed_679_; lean_object* v_res_680_; 
v_depth_boxed_679_ = lean_unbox_usize(v_depth_673_);
lean_dec(v_depth_673_);
v_res_680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(v_00_u03b2_672_, v_depth_boxed_679_, v_keys_674_, v_vals_675_, v_heq_676_, v_i_677_, v_entries_678_);
lean_dec_ref(v_vals_675_);
lean_dec_ref(v_keys_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_681_, lean_object* v_keys_682_, lean_object* v_vals_683_, lean_object* v_heq_684_, lean_object* v_i_685_, lean_object* v_k_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_682_, v_vals_683_, v_i_685_, v_k_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_688_, lean_object* v_keys_689_, lean_object* v_vals_690_, lean_object* v_heq_691_, lean_object* v_i_692_, lean_object* v_k_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_688_, v_keys_689_, v_vals_690_, v_heq_691_, v_i_692_, v_k_693_);
lean_dec_ref(v_k_693_);
lean_dec_ref(v_vals_690_);
lean_dec_ref(v_keys_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_695_, lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_x_696_, v_x_697_, v_x_698_, v_x_699_);
return v___x_700_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_701_, uint64_t v_anchor_702_){
_start:
{
lean_object* v_numDigits_703_; uint64_t v_anchorPrefix_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v_shift_709_; uint64_t v___x_710_; uint8_t v___x_711_; 
v_numDigits_703_ = lean_ctor_get(v_anchorRef_701_, 0);
v_anchorPrefix_704_ = lean_ctor_get_uint64(v_anchorRef_701_, sizeof(void*)*1);
v___x_705_ = 64ULL;
v___x_706_ = lean_uint64_of_nat(v_numDigits_703_);
v___x_707_ = 2ULL;
v___x_708_ = lean_uint64_shift_left(v___x_706_, v___x_707_);
v_shift_709_ = lean_uint64_sub(v___x_705_, v___x_708_);
v___x_710_ = lean_uint64_shift_right(v_anchor_702_, v_shift_709_);
v___x_711_ = lean_uint64_dec_eq(v_anchorPrefix_704_, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_712_, lean_object* v_anchor_713_){
_start:
{
uint64_t v_anchor_boxed_714_; uint8_t v_res_715_; lean_object* v_r_716_; 
v_anchor_boxed_714_ = lean_unbox_uint64(v_anchor_713_);
lean_dec_ref(v_anchor_713_);
v_res_715_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_712_, v_anchor_boxed_714_);
lean_dec_ref(v_anchorRef_712_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_717_; lean_object* v___f_718_; 
v___x_717_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_718_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_718_, 0, v___x_717_);
return v___f_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_739_, lean_object* v_shift_740_, lean_object* v___f_741_, lean_object* v___f_742_, lean_object* v_numDigits_743_, lean_object* v_es_744_, lean_object* v___x_745_, lean_object* v_a_746_, lean_object* v_x_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_739_, v_shift_740_, v___f_741_, v___f_742_, v_numDigits_743_, v_es_744_, v___x_745_, v_a_746_, v_x_747_, v___y_748_);
lean_dec(v_numDigits_743_);
lean_dec(v_shift_740_);
return v_res_749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_box(0);
v___x_751_ = lean_unsigned_to_nat(16u);
v___x_752_ = lean_mk_array(v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_found_755_; 
v___x_753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2);
v___x_754_ = lean_unsigned_to_nat(0u);
v_found_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_755_, 0, v___x_754_);
lean_ctor_set(v_found_755_, 1, v___x_753_);
return v_found_755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_found_756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3);
v___x_757_ = lean_box(0);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_found_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_759_, lean_object* v_es_760_, lean_object* v_numDigits_761_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_762_ = lean_unsigned_to_nat(4u);
v___x_763_ = lean_nat_mul(v___x_762_, v_numDigits_761_);
v___x_764_ = lean_unsigned_to_nat(64u);
v___x_765_ = lean_nat_dec_lt(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v___x_763_);
lean_dec_ref(v_es_760_);
lean_dec_ref(v_inst_759_);
return v_numDigits_761_;
}
else
{
lean_object* v_shift_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___x_772_; size_t v_sz_773_; size_t v___x_774_; lean_object* v___x_775_; lean_object* v_fst_776_; 
v_shift_766_ = lean_nat_sub(v___x_764_, v___x_763_);
lean_dec(v___x_763_);
v___f_767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0);
v___f_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1));
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13));
v___x_770_ = lean_box(0);
lean_inc_ref(v_es_760_);
lean_inc(v_numDigits_761_);
v___f_771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_771_, 0, v_inst_759_);
lean_closure_set(v___f_771_, 1, v_shift_766_);
lean_closure_set(v___f_771_, 2, v___f_767_);
lean_closure_set(v___f_771_, 3, v___f_768_);
lean_closure_set(v___f_771_, 4, v_numDigits_761_);
lean_closure_set(v___f_771_, 5, v_es_760_);
lean_closure_set(v___f_771_, 6, v___x_770_);
v___x_772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_773_ = lean_array_size(v_es_760_);
v___x_774_ = ((size_t)0ULL);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_769_, v_es_760_, v___f_771_, v_sz_773_, v___x_774_, v___x_772_);
v_fst_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_fst_776_);
lean_dec(v___x_775_);
if (lean_obj_tag(v_fst_776_) == 0)
{
return v_numDigits_761_;
}
else
{
lean_object* v_val_777_; 
lean_dec(v_numDigits_761_);
v_val_777_ = lean_ctor_get(v_fst_776_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v_fst_776_, 1);
return v_val_777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_778_, lean_object* v_shift_779_, lean_object* v___f_780_, lean_object* v___f_781_, lean_object* v_numDigits_782_, lean_object* v_es_783_, lean_object* v___x_784_, lean_object* v_a_785_, lean_object* v_x_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_snd_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_826_; 
v_snd_788_ = lean_ctor_get(v___y_787_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v___y_787_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___y_787_, 0);
lean_dec(v_unused_827_);
v___x_790_ = v___y_787_;
v_isShared_791_ = v_isSharedCheck_826_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snd_788_);
lean_dec(v___y_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_826_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc_ref(v_inst_778_);
v___x_792_ = lean_apply_1(v_inst_778_, v_a_785_);
v___x_793_ = lean_uint64_of_nat(v_shift_779_);
v___x_794_ = lean_unbox_uint64(v___x_792_);
v___x_795_ = lean_uint64_shift_right(v___x_794_, v___x_793_);
v___x_796_ = lean_box_uint64(v___x_795_);
lean_inc_ref(v___f_781_);
lean_inc_ref(v___f_780_);
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_780_, v___f_781_, v_snd_788_, v___x_796_);
if (lean_obj_tag(v___x_797_) == 1)
{
lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v___f_781_);
lean_dec_ref(v___f_780_);
v_val_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_819_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_819_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_819_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint64_t v___x_802_; uint64_t v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_unbox_uint64(v_val_798_);
lean_dec(v_val_798_);
v___x_803_ = lean_unbox_uint64(v___x_792_);
lean_dec_ref(v___x_792_);
v___x_804_ = lean_uint64_dec_eq(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec(v___x_784_);
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_add(v_numDigits_782_, v___x_805_);
v___x_807_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_778_, v_es_783_, v___x_806_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_807_);
v___x_809_ = v___x_800_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_814_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_809_);
v___x_811_ = v___x_790_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_788_);
v___x_811_ = v_reuseFailAlloc_813_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
else
{
lean_object* v___x_816_; 
lean_del_object(v___x_800_);
lean_dec_ref(v_es_783_);
lean_dec_ref(v_inst_778_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_784_);
v___x_816_ = v___x_790_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_snd_788_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec(v___x_797_);
lean_dec_ref(v_es_783_);
lean_dec_ref(v_inst_778_);
v___x_820_ = lean_box_uint64(v___x_795_);
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_780_, v___f_781_, v_snd_788_, v___x_820_, v___x_792_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_821_);
lean_ctor_set(v___x_790_, 0, v___x_784_);
v___x_823_ = v___x_790_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_821_);
v___x_823_ = v_reuseFailAlloc_825_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_828_, lean_object* v_inst_829_, lean_object* v_es_830_, lean_object* v_numDigits_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_829_, v_es_830_, v_numDigits_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter___redArg(lean_object* v_x_833_, lean_object* v_h__1_834_, lean_object* v_h__2_835_){
_start:
{
if (lean_obj_tag(v_x_833_) == 1)
{
lean_object* v_val_836_; lean_object* v___x_837_; 
lean_dec(v_h__2_835_);
v_val_836_ = lean_ctor_get(v_x_833_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v_x_833_, 1);
v___x_837_ = lean_apply_1(v_h__1_834_, v_val_836_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; 
lean_dec(v_h__1_834_);
v___x_838_ = lean_apply_2(v_h__2_835_, v_x_833_, lean_box(0));
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter(lean_object* v_motive_839_, lean_object* v_x_840_, lean_object* v_h__1_841_, lean_object* v_h__2_842_){
_start:
{
if (lean_obj_tag(v_x_840_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_844_; 
lean_dec(v_h__2_842_);
v_val_843_ = lean_ctor_get(v_x_840_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v_x_840_, 1);
v___x_844_ = lean_apply_1(v_h__1_841_, v_val_843_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; 
lean_dec(v_h__1_841_);
v___x_845_ = lean_apply_2(v_h__2_842_, v_x_840_, lean_box(0));
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_846_, lean_object* v_h__1_847_, lean_object* v_h__2_848_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_h__1_847_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_apply_1(v_h__2_848_, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v_val_851_; lean_object* v___x_852_; 
lean_dec(v_h__2_848_);
v_val_851_ = lean_ctor_get(v_x_846_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v_x_846_, 1);
v___x_852_ = lean_apply_1(v_h__1_847_, v_val_851_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_853_, lean_object* v_motive_854_, lean_object* v_x_855_, lean_object* v_h__1_856_, lean_object* v_h__2_857_){
_start:
{
if (lean_obj_tag(v_x_855_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_h__1_856_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_apply_1(v_h__2_857_, v___x_858_);
return v___x_859_;
}
else
{
lean_object* v_val_860_; lean_object* v___x_861_; 
lean_dec(v_h__2_857_);
v_val_860_ = lean_ctor_get(v_x_855_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_x_855_, 1);
v___x_861_ = lean_apply_1(v_h__1_856_, v_val_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_862_, lean_object* v_es_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(4u);
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_862_, v_es_863_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_866_, lean_object* v_inst_867_, lean_object* v_es_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_867_, v_es_868_);
return v___x_869_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_870_){
_start:
{
uint64_t v_anchor_871_; 
v_anchor_871_ = lean_ctor_get_uint64(v_e_870_, sizeof(void*)*1);
return v_anchor_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_872_){
_start:
{
uint64_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_872_);
lean_dec_ref(v_e_872_);
v_r_874_ = lean_box_uint64(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_890_, uint64_t v_anchorPrefix_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_ref_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_ref_894_ = lean_ctor_get(v_a_892_, 5);
v___x_895_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_896_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_890_, v_anchorPrefix_891_);
v___x_897_ = l_Lean_mkAtom(v___x_896_);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_mk_empty_array_with_capacity(v___x_898_);
v___x_900_ = lean_array_push(v___x_899_, v___x_897_);
v___x_901_ = lean_box(2);
v___x_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_895_);
lean_ctor_set(v___x_902_, 2, v___x_900_);
v___x_903_ = 0;
v___x_904_ = l_Lean_SourceInfo_fromRef(v_ref_894_, v___x_903_);
v___x_905_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_906_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_904_);
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_904_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_Syntax_node2(v___x_904_, v___x_905_, v___x_907_, v___x_902_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_910_, lean_object* v_anchorPrefix_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
uint64_t v_anchorPrefix_boxed_914_; lean_object* v_res_915_; 
v_anchorPrefix_boxed_914_ = lean_unbox_uint64(v_anchorPrefix_911_);
lean_dec_ref(v_anchorPrefix_911_);
v_res_915_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_910_, v_anchorPrefix_boxed_914_, v_a_912_);
lean_dec_ref(v_a_912_);
lean_dec(v_numDigits_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_916_, uint64_t v_anchorPrefix_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_916_, v_anchorPrefix_917_, v_a_918_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_922_, lean_object* v_anchorPrefix_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
uint64_t v_anchorPrefix_boxed_927_; lean_object* v_res_928_; 
v_anchorPrefix_boxed_927_ = lean_unbox_uint64(v_anchorPrefix_923_);
lean_dec_ref(v_anchorPrefix_923_);
v_res_928_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_922_, v_anchorPrefix_boxed_927_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_numDigits_922_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_929_, uint64_t v_anchor_930_, lean_object* v_a_931_){
_start:
{
uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v_anchorPrefix_938_; lean_object* v___x_939_; 
v___x_933_ = 64ULL;
v___x_934_ = lean_uint64_of_nat(v_numDigits_929_);
v___x_935_ = 2ULL;
v___x_936_ = lean_uint64_shift_left(v___x_934_, v___x_935_);
v___x_937_ = lean_uint64_sub(v___x_933_, v___x_936_);
v_anchorPrefix_938_ = lean_uint64_shift_right(v_anchor_930_, v___x_937_);
v___x_939_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_929_, v_anchorPrefix_938_, v_a_931_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_940_, lean_object* v_anchor_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint64_t v_anchor_boxed_944_; lean_object* v_res_945_; 
v_anchor_boxed_944_ = lean_unbox_uint64(v_anchor_941_);
lean_dec_ref(v_anchor_941_);
v_res_945_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_940_, v_anchor_boxed_944_, v_a_942_);
lean_dec_ref(v_a_942_);
lean_dec(v_numDigits_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_946_, uint64_t v_anchor_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_946_, v_anchor_947_, v_a_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_952_, lean_object* v_anchor_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint64_t v_anchor_boxed_957_; lean_object* v_res_958_; 
v_anchor_boxed_957_ = lean_unbox_uint64(v_anchor_953_);
lean_dec_ref(v_anchor_953_);
v_res_958_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_952_, v_anchor_boxed_957_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_numDigits_952_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_959_);
v___x_971_ = l_Lean_Meta_Grind_getAnchor(v___x_970_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_s_972_);
return v_res_983_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

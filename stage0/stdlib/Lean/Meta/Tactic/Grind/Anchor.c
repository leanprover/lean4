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
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(lean_object* v_n_1_){
_start:
{
uint8_t v___y_3_; uint8_t v___x_15_; 
v___x_15_ = l_Lean_Name_hasMacroScopes(v_n_1_);
if (v___x_15_ == 0)
{
uint8_t v___x_16_; 
lean_inc(v_n_1_);
v___x_16_ = l_Lean_Name_isInaccessibleUserName(v_n_1_);
v___y_3_ = v___x_16_;
goto v___jp_2_;
}
else
{
v___y_3_ = v___x_15_;
goto v___jp_2_;
}
v___jp_2_:
{
if (v___y_3_ == 0)
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(lean_object* v_n_17_){
_start:
{
uint64_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_17_);
v_r_19_ = lean_box_uint64(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t v_a_20_, uint64_t v_b_21_){
_start:
{
uint64_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 0ULL;
v___x_23_ = lean_uint64_dec_eq(v_a_20_, v___x_22_);
if (v___x_23_ == 0)
{
uint8_t v___x_24_; 
v___x_24_ = lean_uint64_dec_eq(v_b_21_, v___x_22_);
if (v___x_24_ == 0)
{
uint64_t v___x_25_; 
v___x_25_ = lean_uint64_mix_hash(v_a_20_, v_b_21_);
return v___x_25_;
}
else
{
return v_a_20_;
}
}
else
{
return v_b_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
uint64_t v_a_boxed_28_; uint64_t v_b_boxed_29_; uint64_t v_res_30_; lean_object* v_r_31_; 
v_a_boxed_28_ = lean_unbox_uint64(v_a_26_);
lean_dec_ref(v_a_26_);
v_b_boxed_29_ = lean_unbox_uint64(v_b_27_);
lean_dec_ref(v_b_27_);
v_res_30_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_a_boxed_28_, v_b_boxed_29_);
v_r_31_ = lean_box_uint64(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(lean_object* v_declName_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; lean_object* v_env_36_; uint8_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = lean_st_ref_get(v___y_33_);
v_env_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc_ref(v_env_36_);
lean_dec(v___x_35_);
v___x_37_ = l_Lean_Meta_isMatcherCore(v_env_36_, v_declName_32_);
v___x_38_ = lean_box(v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(lean_object* v_declName_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_40_, v___y_41_);
lean_dec(v___y_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(lean_object* v_declName_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_44_, v___y_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(lean_object* v_declName_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(v_declName_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_ks_72_; lean_object* v_vs_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_99_; 
v_ks_72_ = lean_ctor_get(v_x_68_, 0);
v_vs_73_ = lean_ctor_get(v_x_68_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_68_);
if (v_isSharedCheck_99_ == 0)
{
v___x_75_ = v_x_68_;
v_isShared_76_ = v_isSharedCheck_99_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_vs_73_);
lean_inc(v_ks_72_);
lean_dec(v_x_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_99_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_array_get_size(v_ks_72_);
v___x_78_ = lean_nat_dec_lt(v_x_69_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
lean_dec(v_x_69_);
v___x_79_ = lean_array_push(v_ks_72_, v_x_70_);
v___x_80_ = lean_array_push(v_vs_73_, v_x_71_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_80_);
lean_ctor_set(v___x_75_, 0, v___x_79_);
v___x_82_ = v___x_75_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
else
{
lean_object* v_k_x27_84_; size_t v___x_85_; size_t v___x_86_; uint8_t v___x_87_; 
v_k_x27_84_ = lean_array_fget_borrowed(v_ks_72_, v_x_69_);
v___x_85_ = lean_ptr_addr(v_x_70_);
v___x_86_ = lean_ptr_addr(v_k_x27_84_);
v___x_87_ = lean_usize_dec_eq(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; 
if (v_isShared_76_ == 0)
{
v___x_89_ = v___x_75_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_ks_72_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_vs_73_);
v___x_89_ = v_reuseFailAlloc_93_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_x_69_, v___x_90_);
lean_dec(v_x_69_);
v_x_68_ = v___x_89_;
v_x_69_ = v___x_91_;
goto _start;
}
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_94_ = lean_array_fset(v_ks_72_, v_x_69_, v_x_70_);
v___x_95_ = lean_array_fset(v_vs_73_, v_x_69_, v_x_71_);
lean_dec(v_x_69_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_95_);
lean_ctor_set(v___x_75_, 0, v___x_94_);
v___x_97_ = v___x_75_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(lean_object* v_n_100_, lean_object* v_k_101_, lean_object* v_v_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_n_100_, v___x_103_, v_k_101_, v_v_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(lean_object* v_x_106_, size_t v_x_107_, size_t v_x_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v_es_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v_j_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_es_111_ = lean_ctor_get(v_x_106_, 0);
v___x_112_ = ((size_t)31ULL);
v___x_113_ = lean_usize_land(v_x_107_, v___x_112_);
v_j_114_ = lean_usize_to_nat(v___x_113_);
v___x_115_ = lean_array_get_size(v_es_111_);
v___x_116_ = lean_nat_dec_lt(v_j_114_, v___x_115_);
if (v___x_116_ == 0)
{
lean_dec(v_j_114_);
lean_dec(v_x_110_);
lean_dec_ref(v_x_109_);
return v_x_106_;
}
else
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_157_; 
lean_inc_ref(v_es_111_);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v_x_106_, 0);
lean_dec(v_unused_158_);
v___x_118_ = v_x_106_;
v_isShared_119_ = v_isSharedCheck_157_;
goto v_resetjp_117_;
}
else
{
lean_dec(v_x_106_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_157_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_v_120_; lean_object* v___x_121_; lean_object* v_xs_x27_122_; lean_object* v___y_124_; 
v_v_120_ = lean_array_fget(v_es_111_, v_j_114_);
v___x_121_ = lean_box(0);
v_xs_x27_122_ = lean_array_fset(v_es_111_, v_j_114_, v___x_121_);
switch(lean_obj_tag(v_v_120_))
{
case 0:
{
lean_object* v_key_129_; lean_object* v_val_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_142_; 
v_key_129_ = lean_ctor_get(v_v_120_, 0);
v_val_130_ = lean_ctor_get(v_v_120_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_v_120_);
if (v_isSharedCheck_142_ == 0)
{
v___x_132_ = v_v_120_;
v_isShared_133_ = v_isSharedCheck_142_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_val_130_);
lean_inc(v_key_129_);
lean_dec(v_v_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_142_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
size_t v___x_134_; size_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = lean_ptr_addr(v_x_109_);
v___x_135_ = lean_ptr_addr(v_key_129_);
v___x_136_ = lean_usize_dec_eq(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_del_object(v___x_132_);
v___x_137_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_129_, v_val_130_, v_x_109_, v_x_110_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
v___y_124_ = v___x_138_;
goto v___jp_123_;
}
else
{
lean_object* v___x_140_; 
lean_dec(v_val_130_);
lean_dec(v_key_129_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_x_110_);
lean_ctor_set(v___x_132_, 0, v_x_109_);
v___x_140_ = v___x_132_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_x_109_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_x_110_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v___y_124_ = v___x_140_;
goto v___jp_123_;
}
}
}
}
case 1:
{
lean_object* v_node_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_155_; 
v_node_143_ = lean_ctor_get(v_v_120_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_v_120_);
if (v_isSharedCheck_155_ == 0)
{
v___x_145_ = v_v_120_;
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_node_143_);
lean_dec(v_v_120_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_147_ = ((size_t)5ULL);
v___x_148_ = lean_usize_shift_right(v_x_107_, v___x_147_);
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_add(v_x_108_, v___x_149_);
v___x_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_node_143_, v___x_148_, v___x_150_, v_x_109_, v_x_110_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_151_);
v___x_153_ = v___x_145_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v___y_124_ = v___x_153_;
goto v___jp_123_;
}
}
}
default: 
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_x_109_);
lean_ctor_set(v___x_156_, 1, v_x_110_);
v___y_124_ = v___x_156_;
goto v___jp_123_;
}
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_array_fset(v_xs_x27_122_, v_j_114_, v___y_124_);
lean_dec(v_j_114_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_125_);
v___x_127_ = v___x_118_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
else
{
lean_object* v_ks_159_; lean_object* v_vs_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_180_; 
v_ks_159_ = lean_ctor_get(v_x_106_, 0);
v_vs_160_ = lean_ctor_get(v_x_106_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_180_ == 0)
{
v___x_162_ = v_x_106_;
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_vs_160_);
lean_inc(v_ks_159_);
lean_dec(v_x_106_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_ks_159_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_vs_160_);
v___x_165_ = v_reuseFailAlloc_179_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v_newNode_166_; uint8_t v___y_168_; size_t v___x_174_; uint8_t v___x_175_; 
v_newNode_166_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v___x_165_, v_x_109_, v_x_110_);
v___x_174_ = ((size_t)7ULL);
v___x_175_ = lean_usize_dec_le(v___x_174_, v_x_108_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_166_);
v___x_177_ = lean_unsigned_to_nat(4u);
v___x_178_ = lean_nat_dec_lt(v___x_176_, v___x_177_);
lean_dec(v___x_176_);
v___y_168_ = v___x_178_;
goto v___jp_167_;
}
else
{
v___y_168_ = v___x_175_;
goto v___jp_167_;
}
v___jp_167_:
{
if (v___y_168_ == 0)
{
lean_object* v_ks_169_; lean_object* v_vs_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_ks_169_ = lean_ctor_get(v_newNode_166_, 0);
lean_inc_ref(v_ks_169_);
v_vs_170_ = lean_ctor_get(v_newNode_166_, 1);
lean_inc_ref(v_vs_170_);
lean_dec_ref(v_newNode_166_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0);
v___x_173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_x_108_, v_ks_169_, v_vs_170_, v___x_171_, v___x_172_);
lean_dec_ref(v_vs_170_);
lean_dec_ref(v_ks_169_);
return v___x_173_;
}
else
{
return v_newNode_166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(size_t v_depth_181_, lean_object* v_keys_182_, lean_object* v_vals_183_, lean_object* v_i_184_, lean_object* v_entries_185_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_array_get_size(v_keys_182_);
v___x_187_ = lean_nat_dec_lt(v_i_184_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v_i_184_);
return v_entries_185_;
}
else
{
lean_object* v_k_188_; lean_object* v_v_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; uint64_t v___x_193_; size_t v_h_194_; size_t v___x_195_; lean_object* v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v_h_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_k_188_ = lean_array_fget_borrowed(v_keys_182_, v_i_184_);
v_v_189_ = lean_array_fget_borrowed(v_vals_183_, v_i_184_);
v___x_190_ = lean_ptr_addr(v_k_188_);
v___x_191_ = ((size_t)3ULL);
v___x_192_ = lean_usize_shift_right(v___x_190_, v___x_191_);
v___x_193_ = lean_usize_to_uint64(v___x_192_);
v_h_194_ = lean_uint64_to_usize(v___x_193_);
v___x_195_ = ((size_t)5ULL);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = ((size_t)1ULL);
v___x_198_ = lean_usize_sub(v_depth_181_, v___x_197_);
v___x_199_ = lean_usize_mul(v___x_195_, v___x_198_);
v_h_200_ = lean_usize_shift_right(v_h_194_, v___x_199_);
v___x_201_ = lean_nat_add(v_i_184_, v___x_196_);
lean_dec(v_i_184_);
lean_inc(v_v_189_);
lean_inc(v_k_188_);
v___x_202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_entries_185_, v_h_200_, v_depth_181_, v_k_188_, v_v_189_);
v_i_184_ = v___x_201_;
v_entries_185_ = v___x_202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_depth_204_, lean_object* v_keys_205_, lean_object* v_vals_206_, lean_object* v_i_207_, lean_object* v_entries_208_){
_start:
{
size_t v_depth_boxed_209_; lean_object* v_res_210_; 
v_depth_boxed_209_ = lean_unbox_usize(v_depth_204_);
lean_dec(v_depth_204_);
v_res_210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_boxed_209_, v_keys_205_, v_vals_206_, v_i_207_, v_entries_208_);
lean_dec_ref(v_vals_206_);
lean_dec_ref(v_keys_205_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___boxed(lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
size_t v_x_32520__boxed_216_; size_t v_x_32521__boxed_217_; lean_object* v_res_218_; 
v_x_32520__boxed_216_ = lean_unbox_usize(v_x_212_);
lean_dec(v_x_212_);
v_x_32521__boxed_217_ = lean_unbox_usize(v_x_213_);
lean_dec(v_x_213_);
v_res_218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_211_, v_x_32520__boxed_216_, v_x_32521__boxed_217_, v_x_214_, v_x_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; uint64_t v___x_225_; size_t v___x_226_; size_t v___x_227_; lean_object* v___x_228_; 
v___x_222_ = lean_ptr_addr(v_x_220_);
v___x_223_ = ((size_t)3ULL);
v___x_224_ = lean_usize_shift_right(v___x_222_, v___x_223_);
v___x_225_ = lean_usize_to_uint64(v___x_224_);
v___x_226_ = lean_uint64_to_usize(v___x_225_);
v___x_227_ = ((size_t)1ULL);
v___x_228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_219_, v___x_226_, v___x_227_, v_x_220_, v_x_221_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object* v_keys_229_, lean_object* v_vals_230_, lean_object* v_i_231_, lean_object* v_k_232_){
_start:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_array_get_size(v_keys_229_);
v___x_234_ = lean_nat_dec_lt(v_i_231_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec(v_i_231_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v_k_x27_236_; size_t v___x_237_; size_t v___x_238_; uint8_t v___x_239_; 
v_k_x27_236_ = lean_array_fget_borrowed(v_keys_229_, v_i_231_);
v___x_237_ = lean_ptr_addr(v_k_232_);
v___x_238_ = lean_ptr_addr(v_k_x27_236_);
v___x_239_ = lean_usize_dec_eq(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_i_231_, v___x_240_);
lean_dec(v_i_231_);
v_i_231_ = v___x_241_;
goto _start;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_array_fget_borrowed(v_vals_230_, v_i_231_);
lean_dec(v_i_231_);
lean_inc(v___x_243_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_keys_245_, lean_object* v_vals_246_, lean_object* v_i_247_, lean_object* v_k_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_245_, v_vals_246_, v_i_247_, v_k_248_);
lean_dec_ref(v_k_248_);
lean_dec_ref(v_vals_246_);
lean_dec_ref(v_keys_245_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object* v_x_250_, size_t v_x_251_, lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v_es_253_; lean_object* v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v_j_257_; lean_object* v___x_258_; 
v_es_253_ = lean_ctor_get(v_x_250_, 0);
v___x_254_ = lean_box(2);
v___x_255_ = ((size_t)31ULL);
v___x_256_ = lean_usize_land(v_x_251_, v___x_255_);
v_j_257_ = lean_usize_to_nat(v___x_256_);
v___x_258_ = lean_array_get_borrowed(v___x_254_, v_es_253_, v_j_257_);
lean_dec(v_j_257_);
switch(lean_obj_tag(v___x_258_))
{
case 0:
{
lean_object* v_key_259_; lean_object* v_val_260_; size_t v___x_261_; size_t v___x_262_; uint8_t v___x_263_; 
v_key_259_ = lean_ctor_get(v___x_258_, 0);
v_val_260_ = lean_ctor_get(v___x_258_, 1);
v___x_261_ = lean_ptr_addr(v_x_252_);
v___x_262_ = lean_ptr_addr(v_key_259_);
v___x_263_ = lean_usize_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
lean_inc(v_val_260_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_val_260_);
return v___x_265_;
}
}
case 1:
{
lean_object* v_node_266_; size_t v___x_267_; size_t v___x_268_; 
v_node_266_ = lean_ctor_get(v___x_258_, 0);
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_usize_shift_right(v_x_251_, v___x_267_);
v_x_250_ = v_node_266_;
v_x_251_ = v___x_268_;
goto _start;
}
default: 
{
lean_object* v___x_270_; 
v___x_270_ = lean_box(0);
return v___x_270_;
}
}
}
else
{
lean_object* v_ks_271_; lean_object* v_vs_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_ks_271_ = lean_ctor_get(v_x_250_, 0);
v_vs_272_ = lean_ctor_get(v_x_250_, 1);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_271_, v_vs_272_, v___x_273_, v_x_252_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
size_t v_x_32725__boxed_278_; lean_object* v_res_279_; 
v_x_32725__boxed_278_ = lean_unbox_usize(v_x_276_);
lean_dec(v_x_276_);
v_res_279_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_275_, v_x_32725__boxed_278_, v_x_277_);
lean_dec_ref(v_x_277_);
lean_dec_ref(v_x_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; uint64_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v___x_282_ = lean_ptr_addr(v_x_281_);
v___x_283_ = ((size_t)3ULL);
v___x_284_ = lean_usize_shift_right(v___x_282_, v___x_283_);
v___x_285_ = lean_usize_to_uint64(v___x_284_);
v___x_286_ = lean_uint64_to_usize(v___x_285_);
v___x_287_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_280_, v___x_286_, v_x_281_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_288_, v_x_289_);
lean_dec_ref(v_x_289_);
lean_dec_ref(v_x_288_);
return v_res_290_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAnchor___closed__0(void){
_start:
{
lean_object* v___x_291_; lean_object* v_dummy_292_; 
v___x_291_ = lean_box(0);
v_dummy_292_ = l_Lean_Expr_sort___override(v___x_291_);
return v_dummy_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_pinfos_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_326_; 
if (lean_obj_tag(v_x_295_) == 5)
{
lean_object* v_fn_345_; lean_object* v_arg_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_fn_345_ = lean_ctor_get(v_x_295_, 0);
lean_inc_ref(v_fn_345_);
v_arg_346_ = lean_ctor_get(v_x_295_, 1);
lean_inc_ref(v_arg_346_);
lean_dec_ref_known(v_x_295_, 2);
v___x_347_ = lean_array_set(v_x_296_, v_x_297_, v_arg_346_);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_sub(v_x_297_, v___x_348_);
lean_dec(v_x_297_);
v_x_295_ = v_fn_345_;
v_x_296_ = v___x_347_;
v_x_297_ = v___x_349_;
goto _start;
}
else
{
uint8_t v___x_351_; 
lean_dec(v_x_297_);
v___x_351_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_295_);
if (v___x_351_ == 0)
{
v___y_326_ = v___x_351_;
goto v___jp_325_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = lean_array_get_size(v_x_296_);
v___x_353_ = lean_unsigned_to_nat(2u);
v___x_354_ = lean_nat_dec_eq(v___x_352_, v___x_353_);
v___y_326_ = v___x_354_;
goto v___jp_325_;
}
}
v___jp_308_:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Grind_getAnchor(v_x_295_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint64_t v___x_323_; lean_object* v___x_324_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v___x_321_ = lean_array_get_size(v_x_296_);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_unbox_uint64(v_a_320_);
lean_dec(v_a_320_);
v___x_324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v___x_321_, v_x_296_, v_pinfos_309_, v___x_322_, v___x_323_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec_ref(v_pinfos_309_);
lean_dec_ref(v_x_296_);
return v___x_324_;
}
else
{
lean_dec_ref(v_pinfos_309_);
lean_dec_ref(v_x_296_);
return v___x_319_;
}
}
v___jp_325_:
{
if (v___y_326_ == 0)
{
uint8_t v___x_327_; 
v___x_327_ = l_Lean_Expr_hasLooseBVars(v_x_295_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_box(0);
lean_inc_ref(v_x_295_);
v___x_329_ = l_Lean_Meta_getFunInfo(v_x_295_, v___x_328_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v_paramInfo_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v_paramInfo_331_ = lean_ctor_get(v_a_330_, 0);
lean_inc_ref(v_paramInfo_331_);
lean_dec(v_a_330_);
v_pinfos_309_ = v_paramInfo_331_;
v___y_310_ = v___y_298_;
v___y_311_ = v___y_299_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
goto v___jp_308_;
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v_x_296_);
lean_dec_ref(v_x_295_);
v_a_332_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_329_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_329_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v___x_340_; 
v___x_340_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0));
v_pinfos_309_ = v___x_340_;
v___y_310_ = v___y_298_;
v___y_311_ = v___y_299_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
goto v___jp_308_;
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec_ref(v_x_295_);
v___x_341_ = l_Lean_instInhabitedExpr;
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_array_get(v___x_341_, v_x_296_, v___x_342_);
lean_dec_ref(v_x_296_);
v___x_344_ = l_Lean_Meta_Grind_getAnchor(v___x_343_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
uint64_t v_a_367_; lean_object* v___y_368_; lean_object* v_n_393_; lean_object* v_d_394_; lean_object* v_b_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___x_414_; lean_object* v_anchors_415_; lean_object* v___x_416_; 
v___x_414_ = lean_st_ref_get(v_a_358_);
v_anchors_415_ = lean_ctor_get(v___x_414_, 8);
lean_inc_ref(v_anchors_415_);
lean_dec(v___x_414_);
v___x_416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_415_, v_e_355_);
lean_dec_ref(v_anchors_415_);
if (lean_obj_tag(v___x_416_) == 1)
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v_e_355_);
v_val_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 0);
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_val_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
lean_dec(v___x_416_);
switch(lean_obj_tag(v_e_355_))
{
case 0:
{
lean_object* v_deBruijnIndex_425_; uint64_t v___x_426_; 
v_deBruijnIndex_425_ = lean_ctor_get(v_e_355_, 0);
v___x_426_ = lean_uint64_of_nat(v_deBruijnIndex_425_);
v_a_367_ = v___x_426_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
case 1:
{
lean_object* v_fvarId_427_; lean_object* v___x_428_; 
v_fvarId_427_ = lean_ctor_get(v_e_355_, 0);
lean_inc(v_fvarId_427_);
v___x_428_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_427_, v_a_361_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; uint64_t v___x_431_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = l_Lean_LocalDecl_userName(v_a_429_);
lean_dec(v_a_429_);
v___x_431_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_430_);
v_a_367_ = v___x_431_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec_ref_known(v_e_355_, 1);
v_a_432_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_428_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
case 4:
{
lean_object* v_declName_440_; lean_object* v___x_441_; 
v_declName_440_ = lean_ctor_get(v_e_355_, 0);
lean_inc(v_declName_440_);
v___x_441_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_440_, v_a_364_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; uint8_t v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = lean_unbox(v_a_442_);
lean_dec(v_a_442_);
if (v___x_443_ == 0)
{
uint64_t v___x_444_; 
lean_inc(v_declName_440_);
v___x_444_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_440_);
v_a_367_ = v___x_444_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
else
{
uint64_t v___x_445_; 
v___x_445_ = 0ULL;
v_a_367_ = v___x_445_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref_known(v_e_355_, 2);
v_a_446_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_441_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_441_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
case 5:
{
lean_object* v_dummy_454_; lean_object* v_nargs_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_dummy_454_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_455_ = l_Lean_Expr_getAppNumArgs(v_e_355_);
lean_inc(v_nargs_455_);
v___x_456_ = lean_mk_array(v_nargs_455_, v_dummy_454_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_sub(v_nargs_455_, v___x_457_);
lean_dec(v_nargs_455_);
lean_inc_ref(v_e_355_);
v___x_459_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_355_, v___x_456_, v___x_458_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; uint64_t v___x_461_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = lean_unbox_uint64(v_a_460_);
lean_dec(v_a_460_);
v_a_367_ = v___x_461_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
else
{
lean_dec_ref_known(v_e_355_, 2);
return v___x_459_;
}
}
case 6:
{
lean_object* v_binderName_462_; lean_object* v_binderType_463_; lean_object* v_body_464_; 
v_binderName_462_ = lean_ctor_get(v_e_355_, 0);
v_binderType_463_ = lean_ctor_get(v_e_355_, 1);
v_body_464_ = lean_ctor_get(v_e_355_, 2);
lean_inc_ref(v_body_464_);
lean_inc_ref(v_binderType_463_);
lean_inc(v_binderName_462_);
v_n_393_ = v_binderName_462_;
v_d_394_ = v_binderType_463_;
v_b_395_ = v_body_464_;
v___y_396_ = v_a_356_;
v___y_397_ = v_a_357_;
v___y_398_ = v_a_358_;
v___y_399_ = v_a_359_;
v___y_400_ = v_a_360_;
v___y_401_ = v_a_361_;
v___y_402_ = v_a_362_;
v___y_403_ = v_a_363_;
v___y_404_ = v_a_364_;
goto v___jp_392_;
}
case 7:
{
lean_object* v_binderName_465_; lean_object* v_binderType_466_; lean_object* v_body_467_; 
v_binderName_465_ = lean_ctor_get(v_e_355_, 0);
v_binderType_466_ = lean_ctor_get(v_e_355_, 1);
v_body_467_ = lean_ctor_get(v_e_355_, 2);
lean_inc_ref(v_body_467_);
lean_inc_ref(v_binderType_466_);
lean_inc(v_binderName_465_);
v_n_393_ = v_binderName_465_;
v_d_394_ = v_binderType_466_;
v_b_395_ = v_body_467_;
v___y_396_ = v_a_356_;
v___y_397_ = v_a_357_;
v___y_398_ = v_a_358_;
v___y_399_ = v_a_359_;
v___y_400_ = v_a_360_;
v___y_401_ = v_a_361_;
v___y_402_ = v_a_362_;
v___y_403_ = v_a_363_;
v___y_404_ = v_a_364_;
goto v___jp_392_;
}
case 8:
{
lean_object* v_declName_468_; lean_object* v_type_469_; lean_object* v_value_470_; lean_object* v_body_471_; lean_object* v___x_472_; 
v_declName_468_ = lean_ctor_get(v_e_355_, 0);
v_type_469_ = lean_ctor_get(v_e_355_, 1);
v_value_470_ = lean_ctor_get(v_e_355_, 2);
v_body_471_ = lean_ctor_get(v_e_355_, 3);
lean_inc_ref(v_value_470_);
v___x_472_ = l_Lean_Meta_Grind_getAnchor(v_value_470_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
lean_inc_ref(v_type_469_);
v___x_474_ = l_Lean_Meta_Grind_getAnchor(v_type_469_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
lean_inc_ref(v_body_471_);
v___x_476_ = l_Lean_Meta_Grind_getAnchor(v_body_471_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
lean_inc(v_declName_468_);
v___x_478_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_468_);
v___x_479_ = lean_unbox_uint64(v_a_475_);
lean_dec(v_a_475_);
v___x_480_ = lean_unbox_uint64(v_a_477_);
lean_dec(v_a_477_);
v___x_481_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_479_, v___x_480_);
v___x_482_ = lean_unbox_uint64(v_a_473_);
lean_dec(v_a_473_);
v___x_483_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_482_, v___x_481_);
v___x_484_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_478_, v___x_483_);
v_a_367_ = v___x_484_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
else
{
lean_dec(v_a_475_);
lean_dec(v_a_473_);
lean_dec_ref_known(v_e_355_, 4);
return v___x_476_;
}
}
else
{
lean_dec(v_a_473_);
lean_dec_ref_known(v_e_355_, 4);
return v___x_474_;
}
}
else
{
lean_dec_ref_known(v_e_355_, 4);
return v___x_472_;
}
}
case 9:
{
lean_object* v_a_485_; uint64_t v___x_486_; 
v_a_485_ = lean_ctor_get(v_e_355_, 0);
v___x_486_ = l_Lean_Literal_hash(v_a_485_);
v_a_367_ = v___x_486_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
case 10:
{
lean_object* v_expr_487_; lean_object* v___x_488_; 
v_expr_487_ = lean_ctor_get(v_e_355_, 1);
lean_inc_ref(v_expr_487_);
v___x_488_ = l_Lean_Meta_Grind_getAnchor(v_expr_487_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; uint64_t v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = lean_unbox_uint64(v_a_489_);
lean_dec(v_a_489_);
v_a_367_ = v___x_490_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
else
{
lean_dec_ref_known(v_e_355_, 2);
return v___x_488_;
}
}
case 11:
{
lean_object* v_idx_491_; lean_object* v_struct_492_; lean_object* v___x_493_; 
v_idx_491_ = lean_ctor_get(v_e_355_, 1);
v_struct_492_ = lean_ctor_get(v_e_355_, 2);
lean_inc_ref(v_struct_492_);
v___x_493_ = l_Lean_Meta_Grind_getAnchor(v_struct_492_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = lean_uint64_of_nat(v_idx_491_);
v___x_496_ = lean_unbox_uint64(v_a_494_);
lean_dec(v_a_494_);
v___x_497_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_495_, v___x_496_);
v_a_367_ = v___x_497_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
else
{
lean_dec_ref_known(v_e_355_, 3);
return v___x_493_;
}
}
default: 
{
uint64_t v___x_498_; 
v___x_498_ = 0ULL;
v_a_367_ = v___x_498_;
v___y_368_ = v_a_358_;
goto v___jp_366_;
}
}
}
v___jp_366_:
{
lean_object* v___x_369_; lean_object* v_congrThms_370_; lean_object* v_simp_371_; lean_object* v_lastTag_372_; lean_object* v_counters_373_; lean_object* v_splitDiags_374_; lean_object* v_ematchDiags_375_; lean_object* v_lawfulEqCmpMap_376_; lean_object* v_reflCmpMap_377_; lean_object* v_anchors_378_; lean_object* v_instanceMap_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_391_; 
v___x_369_ = lean_st_ref_take(v___y_368_);
v_congrThms_370_ = lean_ctor_get(v___x_369_, 0);
v_simp_371_ = lean_ctor_get(v___x_369_, 1);
v_lastTag_372_ = lean_ctor_get(v___x_369_, 2);
v_counters_373_ = lean_ctor_get(v___x_369_, 3);
v_splitDiags_374_ = lean_ctor_get(v___x_369_, 4);
v_ematchDiags_375_ = lean_ctor_get(v___x_369_, 5);
v_lawfulEqCmpMap_376_ = lean_ctor_get(v___x_369_, 6);
v_reflCmpMap_377_ = lean_ctor_get(v___x_369_, 7);
v_anchors_378_ = lean_ctor_get(v___x_369_, 8);
v_instanceMap_379_ = lean_ctor_get(v___x_369_, 9);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_391_ == 0)
{
v___x_381_ = v___x_369_;
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_instanceMap_379_);
lean_inc(v_anchors_378_);
lean_inc(v_reflCmpMap_377_);
lean_inc(v_lawfulEqCmpMap_376_);
lean_inc(v_ematchDiags_375_);
lean_inc(v_splitDiags_374_);
lean_inc(v_counters_373_);
lean_inc(v_lastTag_372_);
lean_inc(v_simp_371_);
lean_inc(v_congrThms_370_);
lean_dec(v___x_369_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_383_ = lean_box_uint64(v_a_367_);
v___x_384_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_anchors_378_, v_e_355_, v___x_383_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 8, v___x_384_);
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_congrThms_370_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_simp_371_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_lastTag_372_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_counters_373_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_splitDiags_374_);
lean_ctor_set(v_reuseFailAlloc_390_, 5, v_ematchDiags_375_);
lean_ctor_set(v_reuseFailAlloc_390_, 6, v_lawfulEqCmpMap_376_);
lean_ctor_set(v_reuseFailAlloc_390_, 7, v_reflCmpMap_377_);
lean_ctor_set(v_reuseFailAlloc_390_, 8, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_390_, 9, v_instanceMap_379_);
v___x_386_ = v_reuseFailAlloc_390_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_st_ref_set(v___y_368_, v___x_386_);
v___x_388_ = lean_box_uint64(v_a_367_);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
}
v___jp_392_:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Grind_getAnchor(v_d_394_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l_Lean_Meta_Grind_getAnchor(v_b_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_393_);
v___x_410_ = lean_unbox_uint64(v_a_406_);
lean_dec(v_a_406_);
v___x_411_ = lean_unbox_uint64(v_a_408_);
lean_dec(v_a_408_);
v___x_412_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_410_, v___x_411_);
v___x_413_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_409_, v___x_412_);
v_a_367_ = v___x_413_;
v___y_368_ = v___y_398_;
goto v___jp_366_;
}
else
{
lean_dec(v_a_406_);
lean_dec(v_n_393_);
lean_dec_ref(v_e_355_);
return v___x_407_;
}
}
else
{
lean_dec_ref(v_b_395_);
lean_dec(v_n_393_);
lean_dec_ref(v_e_355_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_upperBound_499_, lean_object* v_args_500_, lean_object* v_pinfos_501_, lean_object* v_a_502_, uint64_t v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint64_t v_a_515_; uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_lt(v_a_502_, v_upperBound_499_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_a_502_);
v___x_520_ = lean_box_uint64(v_b_503_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_array_fget_borrowed(v_args_500_, v_a_502_);
v___x_523_ = lean_array_get_size(v_pinfos_501_);
v___x_524_ = lean_nat_dec_lt(v_a_502_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_inc(v___x_522_);
v___x_525_ = l_Lean_Meta_Grind_getAnchor(v___x_522_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; uint64_t v___x_527_; uint64_t v___x_528_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_unbox_uint64(v_a_526_);
lean_dec(v_a_526_);
v___x_528_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_503_, v___x_527_);
v_a_515_ = v___x_528_;
goto v___jp_514_;
}
else
{
lean_dec(v_a_502_);
return v___x_525_;
}
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_fget_borrowed(v_pinfos_501_, v_a_502_);
v___x_530_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_inc(v___x_522_);
v___x_531_ = l_Lean_Meta_Grind_getAnchor(v___x_522_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; uint64_t v___x_533_; uint64_t v___x_534_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = lean_unbox_uint64(v_a_532_);
lean_dec(v_a_532_);
v___x_534_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_503_, v___x_533_);
v_a_515_ = v___x_534_;
goto v___jp_514_;
}
else
{
lean_dec(v_a_502_);
return v___x_531_;
}
}
else
{
v_a_515_ = v_b_503_;
goto v___jp_514_;
}
}
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_a_502_, v___x_516_);
lean_dec(v_a_502_);
v_a_502_ = v___x_517_;
v_b_503_ = v_a_515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg___boxed(lean_object* v_upperBound_535_, lean_object* v_args_536_, lean_object* v_pinfos_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint64_t v_b_boxed_550_; lean_object* v_res_551_; 
v_b_boxed_550_ = lean_unbox_uint64(v_b_539_);
lean_dec_ref(v_b_539_);
v_res_551_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_535_, v_args_536_, v_pinfos_537_, v_a_538_, v_b_boxed_550_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v_pinfos_537_);
lean_dec_ref(v_args_536_);
lean_dec(v_upperBound_535_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_552_, v_x_553_, v_x_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Meta_Grind_getAnchor(v_e_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_upperBound_578_, lean_object* v_args_579_, lean_object* v_pinfos_580_, lean_object* v_inst_581_, lean_object* v_R_582_, lean_object* v_a_583_, uint64_t v_b_584_, lean_object* v_c_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_578_, v_args_579_, v_pinfos_580_, v_a_583_, v_b_584_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_597_ = _args[0];
lean_object* v_args_598_ = _args[1];
lean_object* v_pinfos_599_ = _args[2];
lean_object* v_inst_600_ = _args[3];
lean_object* v_R_601_ = _args[4];
lean_object* v_a_602_ = _args[5];
lean_object* v_b_603_ = _args[6];
lean_object* v_c_604_ = _args[7];
lean_object* v___y_605_ = _args[8];
lean_object* v___y_606_ = _args[9];
lean_object* v___y_607_ = _args[10];
lean_object* v___y_608_ = _args[11];
lean_object* v___y_609_ = _args[12];
lean_object* v___y_610_ = _args[13];
lean_object* v___y_611_ = _args[14];
lean_object* v___y_612_ = _args[15];
lean_object* v___y_613_ = _args[16];
lean_object* v___y_614_ = _args[17];
_start:
{
uint64_t v_b_boxed_615_; lean_object* v_res_616_; 
v_b_boxed_615_ = lean_unbox_uint64(v_b_603_);
lean_dec_ref(v_b_603_);
v_res_616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(v_upperBound_597_, v_args_598_, v_pinfos_599_, v_inst_600_, v_R_601_, v_a_602_, v_b_boxed_615_, v_c_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v_pinfos_599_);
lean_dec_ref(v_args_598_);
lean_dec(v_upperBound_597_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_00_u03b2_617_, lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_x_618_, v_x_619_, v_x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_626_, v_x_627_, v_x_628_);
lean_dec_ref(v_x_628_);
lean_dec_ref(v_x_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(lean_object* v_00_u03b2_630_, lean_object* v_x_631_, size_t v_x_632_, size_t v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_631_, v_x_632_, v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
size_t v_x_33315__boxed_643_; size_t v_x_33316__boxed_644_; lean_object* v_res_645_; 
v_x_33315__boxed_643_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_x_33316__boxed_644_ = lean_unbox_usize(v_x_640_);
lean_dec(v_x_640_);
v_res_645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(v_00_u03b2_637_, v_x_638_, v_x_33315__boxed_643_, v_x_33316__boxed_644_, v_x_641_, v_x_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_646_, lean_object* v_x_647_, size_t v_x_648_, lean_object* v_x_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_647_, v_x_648_, v_x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
size_t v_x_33332__boxed_655_; lean_object* v_res_656_; 
v_x_33332__boxed_655_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_res_656_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_651_, v_x_652_, v_x_33332__boxed_655_, v_x_654_);
lean_dec_ref(v_x_654_);
lean_dec_ref(v_x_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_657_, lean_object* v_n_658_, lean_object* v_k_659_, lean_object* v_v_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v_n_658_, v_k_659_, v_v_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_662_, size_t v_depth_663_, lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_heq_666_, lean_object* v_i_667_, lean_object* v_entries_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_663_, v_keys_664_, v_vals_665_, v_i_667_, v_entries_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_670_, lean_object* v_depth_671_, lean_object* v_keys_672_, lean_object* v_vals_673_, lean_object* v_heq_674_, lean_object* v_i_675_, lean_object* v_entries_676_){
_start:
{
size_t v_depth_boxed_677_; lean_object* v_res_678_; 
v_depth_boxed_677_ = lean_unbox_usize(v_depth_671_);
lean_dec(v_depth_671_);
v_res_678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(v_00_u03b2_670_, v_depth_boxed_677_, v_keys_672_, v_vals_673_, v_heq_674_, v_i_675_, v_entries_676_);
lean_dec_ref(v_vals_673_);
lean_dec_ref(v_keys_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_679_, lean_object* v_keys_680_, lean_object* v_vals_681_, lean_object* v_heq_682_, lean_object* v_i_683_, lean_object* v_k_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_680_, v_vals_681_, v_i_683_, v_k_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_686_, lean_object* v_keys_687_, lean_object* v_vals_688_, lean_object* v_heq_689_, lean_object* v_i_690_, lean_object* v_k_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_686_, v_keys_687_, v_vals_688_, v_heq_689_, v_i_690_, v_k_691_);
lean_dec_ref(v_k_691_);
lean_dec_ref(v_vals_688_);
lean_dec_ref(v_keys_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_x_694_, v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_699_, uint64_t v_anchor_700_){
_start:
{
lean_object* v_numDigits_701_; uint64_t v_anchorPrefix_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v_shift_707_; uint64_t v___x_708_; uint8_t v___x_709_; 
v_numDigits_701_ = lean_ctor_get(v_anchorRef_699_, 0);
v_anchorPrefix_702_ = lean_ctor_get_uint64(v_anchorRef_699_, sizeof(void*)*1);
v___x_703_ = 64ULL;
v___x_704_ = lean_uint64_of_nat(v_numDigits_701_);
v___x_705_ = 2ULL;
v___x_706_ = lean_uint64_shift_left(v___x_704_, v___x_705_);
v_shift_707_ = lean_uint64_sub(v___x_703_, v___x_706_);
v___x_708_ = lean_uint64_shift_right(v_anchor_700_, v_shift_707_);
v___x_709_ = lean_uint64_dec_eq(v_anchorPrefix_702_, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_710_, lean_object* v_anchor_711_){
_start:
{
uint64_t v_anchor_boxed_712_; uint8_t v_res_713_; lean_object* v_r_714_; 
v_anchor_boxed_712_ = lean_unbox_uint64(v_anchor_711_);
lean_dec_ref(v_anchor_711_);
v_res_713_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_710_, v_anchor_boxed_712_);
lean_dec_ref(v_anchorRef_710_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_715_; lean_object* v___f_716_; 
v___x_715_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_716_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_716_, 0, v___x_715_);
return v___f_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_737_, lean_object* v_shift_738_, lean_object* v___f_739_, lean_object* v___f_740_, lean_object* v_numDigits_741_, lean_object* v_es_742_, lean_object* v___x_743_, lean_object* v_a_744_, lean_object* v_x_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_737_, v_shift_738_, v___f_739_, v___f_740_, v_numDigits_741_, v_es_742_, v___x_743_, v_a_744_, v_x_745_, v___y_746_);
lean_dec(v_numDigits_741_);
lean_dec(v_shift_738_);
return v_res_747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_box(0);
v___x_749_ = lean_unsigned_to_nat(16u);
v___x_750_ = lean_mk_array(v___x_749_, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v_found_753_; 
v___x_751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2);
v___x_752_ = lean_unsigned_to_nat(0u);
v_found_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_753_, 0, v___x_752_);
lean_ctor_set(v_found_753_, 1, v___x_751_);
return v_found_753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_found_754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3);
v___x_755_ = lean_box(0);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_found_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_757_, lean_object* v_es_758_, lean_object* v_numDigits_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_760_ = lean_unsigned_to_nat(4u);
v___x_761_ = lean_nat_mul(v___x_760_, v_numDigits_759_);
v___x_762_ = lean_unsigned_to_nat(64u);
v___x_763_ = lean_nat_dec_lt(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_dec(v___x_761_);
lean_dec_ref(v_es_758_);
lean_dec_ref(v_inst_757_);
return v_numDigits_759_;
}
else
{
lean_object* v_shift_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___x_770_; size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; lean_object* v_fst_774_; 
v_shift_764_ = lean_nat_sub(v___x_762_, v___x_761_);
lean_dec(v___x_761_);
v___f_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0);
v___f_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1));
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13));
v___x_768_ = lean_box(0);
lean_inc_ref(v_es_758_);
lean_inc(v_numDigits_759_);
v___f_769_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_769_, 0, v_inst_757_);
lean_closure_set(v___f_769_, 1, v_shift_764_);
lean_closure_set(v___f_769_, 2, v___f_765_);
lean_closure_set(v___f_769_, 3, v___f_766_);
lean_closure_set(v___f_769_, 4, v_numDigits_759_);
lean_closure_set(v___f_769_, 5, v_es_758_);
lean_closure_set(v___f_769_, 6, v___x_768_);
v___x_770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_771_ = lean_array_size(v_es_758_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_767_, v_es_758_, v___f_769_, v_sz_771_, v___x_772_, v___x_770_);
v_fst_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_fst_774_);
lean_dec(v___x_773_);
if (lean_obj_tag(v_fst_774_) == 0)
{
return v_numDigits_759_;
}
else
{
lean_object* v_val_775_; 
lean_dec(v_numDigits_759_);
v_val_775_ = lean_ctor_get(v_fst_774_, 0);
lean_inc(v_val_775_);
lean_dec_ref_known(v_fst_774_, 1);
return v_val_775_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_776_, lean_object* v_shift_777_, lean_object* v___f_778_, lean_object* v___f_779_, lean_object* v_numDigits_780_, lean_object* v_es_781_, lean_object* v___x_782_, lean_object* v_a_783_, lean_object* v_x_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_824_; 
v_snd_786_ = lean_ctor_get(v___y_785_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___y_785_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___y_785_, 0);
lean_dec(v_unused_825_);
v___x_788_ = v___y_785_;
v_isShared_789_ = v_isSharedCheck_824_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_dec(v___y_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_824_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc_ref(v_inst_776_);
v___x_790_ = lean_apply_1(v_inst_776_, v_a_783_);
v___x_791_ = lean_uint64_of_nat(v_shift_777_);
v___x_792_ = lean_unbox_uint64(v___x_790_);
v___x_793_ = lean_uint64_shift_right(v___x_792_, v___x_791_);
v___x_794_ = lean_box_uint64(v___x_793_);
lean_inc_ref(v___f_779_);
lean_inc_ref(v___f_778_);
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_778_, v___f_779_, v_snd_786_, v___x_794_);
if (lean_obj_tag(v___x_795_) == 1)
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v___f_779_);
lean_dec_ref(v___f_778_);
v_val_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_817_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_817_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_817_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
uint64_t v___x_800_; uint64_t v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_unbox_uint64(v_val_796_);
lean_dec(v_val_796_);
v___x_801_ = lean_unbox_uint64(v___x_790_);
lean_dec_ref(v___x_790_);
v___x_802_ = lean_uint64_dec_eq(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v___x_782_);
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_add(v_numDigits_780_, v___x_803_);
v___x_805_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_776_, v_es_781_, v___x_804_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_805_);
v___x_807_ = v___x_798_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_812_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_807_);
v___x_809_ = v___x_788_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_snd_786_);
v___x_809_ = v_reuseFailAlloc_811_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
else
{
lean_object* v___x_814_; 
lean_del_object(v___x_798_);
lean_dec_ref(v_es_781_);
lean_dec_ref(v_inst_776_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_782_);
v___x_814_ = v___x_788_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_snd_786_);
v___x_814_ = v_reuseFailAlloc_816_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec(v___x_795_);
lean_dec_ref(v_es_781_);
lean_dec_ref(v_inst_776_);
v___x_818_ = lean_box_uint64(v___x_793_);
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_778_, v___f_779_, v_snd_786_, v___x_818_, v___x_790_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_819_);
lean_ctor_set(v___x_788_, 0, v___x_782_);
v___x_821_ = v___x_788_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_826_, lean_object* v_inst_827_, lean_object* v_es_828_, lean_object* v_numDigits_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_827_, v_es_828_, v_numDigits_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter___redArg(lean_object* v_x_831_, lean_object* v_h__1_832_, lean_object* v_h__2_833_){
_start:
{
if (lean_obj_tag(v_x_831_) == 1)
{
lean_object* v_val_834_; lean_object* v___x_835_; 
lean_dec(v_h__2_833_);
v_val_834_ = lean_ctor_get(v_x_831_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v_x_831_, 1);
v___x_835_ = lean_apply_1(v_h__1_832_, v_val_834_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; 
lean_dec(v_h__1_832_);
v___x_836_ = lean_apply_2(v_h__2_833_, v_x_831_, lean_box(0));
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter(lean_object* v_motive_837_, lean_object* v_x_838_, lean_object* v_h__1_839_, lean_object* v_h__2_840_){
_start:
{
if (lean_obj_tag(v_x_838_) == 1)
{
lean_object* v_val_841_; lean_object* v___x_842_; 
lean_dec(v_h__2_840_);
v_val_841_ = lean_ctor_get(v_x_838_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v_x_838_, 1);
v___x_842_ = lean_apply_1(v_h__1_839_, v_val_841_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; 
lean_dec(v_h__1_839_);
v___x_843_ = lean_apply_2(v_h__2_840_, v_x_838_, lean_box(0));
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_844_, lean_object* v_h__1_845_, lean_object* v_h__2_846_){
_start:
{
if (lean_obj_tag(v_x_844_) == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v_h__1_845_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_apply_1(v_h__2_846_, v___x_847_);
return v___x_848_;
}
else
{
lean_object* v_val_849_; lean_object* v___x_850_; 
lean_dec(v_h__2_846_);
v_val_849_ = lean_ctor_get(v_x_844_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v_x_844_, 1);
v___x_850_ = lean_apply_1(v_h__1_845_, v_val_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_851_, lean_object* v_motive_852_, lean_object* v_x_853_, lean_object* v_h__1_854_, lean_object* v_h__2_855_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v_h__1_854_);
v___x_856_ = lean_box(0);
v___x_857_ = lean_apply_1(v_h__2_855_, v___x_856_);
return v___x_857_;
}
else
{
lean_object* v_val_858_; lean_object* v___x_859_; 
lean_dec(v_h__2_855_);
v_val_858_ = lean_ctor_get(v_x_853_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v_x_853_, 1);
v___x_859_ = lean_apply_1(v_h__1_854_, v_val_858_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_860_, lean_object* v_es_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(4u);
v___x_863_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_860_, v_es_861_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_864_, lean_object* v_inst_865_, lean_object* v_es_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_865_, v_es_866_);
return v___x_867_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_868_){
_start:
{
uint64_t v_anchor_869_; 
v_anchor_869_ = lean_ctor_get_uint64(v_e_868_, sizeof(void*)*1);
return v_anchor_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_870_){
_start:
{
uint64_t v_res_871_; lean_object* v_r_872_; 
v_res_871_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_870_);
lean_dec_ref(v_e_870_);
v_r_872_ = lean_box_uint64(v_res_871_);
return v_r_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_888_, uint64_t v_anchorPrefix_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_ref_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_ref_892_ = lean_ctor_get(v_a_890_, 5);
v___x_893_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_894_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_888_, v_anchorPrefix_889_);
v___x_895_ = l_Lean_mkAtom(v___x_894_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_mk_empty_array_with_capacity(v___x_896_);
v___x_898_ = lean_array_push(v___x_897_, v___x_895_);
v___x_899_ = lean_box(2);
v___x_900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_893_);
lean_ctor_set(v___x_900_, 2, v___x_898_);
v___x_901_ = 0;
v___x_902_ = l_Lean_SourceInfo_fromRef(v_ref_892_, v___x_901_);
v___x_903_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_904_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_902_);
v___x_905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_902_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_Syntax_node2(v___x_902_, v___x_903_, v___x_905_, v___x_900_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_908_, lean_object* v_anchorPrefix_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
uint64_t v_anchorPrefix_boxed_912_; lean_object* v_res_913_; 
v_anchorPrefix_boxed_912_ = lean_unbox_uint64(v_anchorPrefix_909_);
lean_dec_ref(v_anchorPrefix_909_);
v_res_913_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_908_, v_anchorPrefix_boxed_912_, v_a_910_);
lean_dec_ref(v_a_910_);
lean_dec(v_numDigits_908_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_914_, uint64_t v_anchorPrefix_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_914_, v_anchorPrefix_915_, v_a_916_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_920_, lean_object* v_anchorPrefix_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
uint64_t v_anchorPrefix_boxed_925_; lean_object* v_res_926_; 
v_anchorPrefix_boxed_925_ = lean_unbox_uint64(v_anchorPrefix_921_);
lean_dec_ref(v_anchorPrefix_921_);
v_res_926_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_920_, v_anchorPrefix_boxed_925_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_numDigits_920_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_927_, uint64_t v_anchor_928_, lean_object* v_a_929_){
_start:
{
uint64_t v___x_931_; uint64_t v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v_anchorPrefix_936_; lean_object* v___x_937_; 
v___x_931_ = 64ULL;
v___x_932_ = lean_uint64_of_nat(v_numDigits_927_);
v___x_933_ = 2ULL;
v___x_934_ = lean_uint64_shift_left(v___x_932_, v___x_933_);
v___x_935_ = lean_uint64_sub(v___x_931_, v___x_934_);
v_anchorPrefix_936_ = lean_uint64_shift_right(v_anchor_928_, v___x_935_);
v___x_937_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_927_, v_anchorPrefix_936_, v_a_929_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_938_, lean_object* v_anchor_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
uint64_t v_anchor_boxed_942_; lean_object* v_res_943_; 
v_anchor_boxed_942_ = lean_unbox_uint64(v_anchor_939_);
lean_dec_ref(v_anchor_939_);
v_res_943_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_938_, v_anchor_boxed_942_, v_a_940_);
lean_dec_ref(v_a_940_);
lean_dec(v_numDigits_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_944_, uint64_t v_anchor_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_944_, v_anchor_945_, v_a_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_950_, lean_object* v_anchor_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
uint64_t v_anchor_boxed_955_; lean_object* v_res_956_; 
v_anchor_boxed_955_ = lean_unbox_uint64(v_anchor_951_);
lean_dec_ref(v_anchor_951_);
v_res_956_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_950_, v_anchor_boxed_955_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_numDigits_950_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_957_);
v___x_969_ = l_Lean_Meta_Grind_getAnchor(v___x_968_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_s_970_);
return v_res_981_;
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

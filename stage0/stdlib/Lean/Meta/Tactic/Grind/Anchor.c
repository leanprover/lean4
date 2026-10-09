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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_instDecidableEqUInt64___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_getAnchor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAnchor___closed__0;
static const lean_array_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11;
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
uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(lean_object* v_n_1_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1_ = stack[0].m_obj;
uint64_t v_res_17_;
v_res_17_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_1_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(lean_object* v_n_18_){
_start:
{
uint64_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_18_);
v_r_20_ = lean_box_uint64(v_res_19_);
return v_r_20_;
}
}
uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t v_a_21_, uint64_t v_b_22_){
_start:
{
uint64_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 0ULL;
v___x_24_ = lean_uint64_dec_eq(v_a_21_, v___x_23_);
if (v___x_24_ == 0)
{
uint8_t v___x_25_; 
v___x_25_ = lean_uint64_dec_eq(v_b_22_, v___x_23_);
if (v___x_25_ == 0)
{
uint64_t v___x_26_; 
v___x_26_ = lean_uint64_mix_hash(v_a_21_, v_b_22_);
return v___x_26_;
}
else
{
return v_a_21_;
}
}
else
{
return v_b_22_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_21_ = stack[0].m_num;
uint64_t v_b_22_ = stack[1].m_num;
uint64_t v_res_27_;
v_res_27_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_a_21_, v_b_22_);
stack->m_num = v_res_27_;
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
lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(lean_object* v_declName_34_, lean_object* v___y_35_){
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
LEAN_EXPORT void l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_34_ = stack[0].m_obj;
lean_object* v___y_35_ = stack[1].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_34_, v___y_35_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(lean_object* v_declName_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_43_, v___y_44_);
lean_dec(v___y_44_);
return v_res_46_;
}
}
lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(lean_object* v_declName_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_47_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_47_ = stack[0].m_obj;
lean_object* v___y_48_ = stack[1].m_obj;
lean_object* v___y_49_ = stack[2].m_obj;
lean_object* v___y_50_ = stack[3].m_obj;
lean_object* v___y_51_ = stack[4].m_obj;
lean_object* v___y_52_ = stack[5].m_obj;
lean_object* v___y_53_ = stack[6].m_obj;
lean_object* v___y_54_ = stack[7].m_obj;
lean_object* v___y_55_ = stack[8].m_obj;
lean_object* v___y_56_ = stack[9].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(v_declName_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(lean_object* v_declName_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(v_declName_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object* v_keys_72_, lean_object* v_vals_73_, lean_object* v_i_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = lean_array_get_size(v_keys_72_);
v___x_77_ = lean_nat_dec_lt(v_i_74_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
lean_dec(v_i_74_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
lean_object* v_k_x27_79_; size_t v___x_80_; size_t v___x_81_; uint8_t v___x_82_; 
v_k_x27_79_ = lean_array_fget_borrowed(v_keys_72_, v_i_74_);
v___x_80_ = lean_ptr_addr(v_k_75_);
v___x_81_ = lean_ptr_addr(v_k_x27_79_);
v___x_82_ = lean_usize_dec_eq(v___x_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_add(v_i_74_, v___x_83_);
lean_dec(v_i_74_);
v_i_74_ = v___x_84_;
goto _start;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_array_fget_borrowed(v_vals_73_, v_i_74_);
lean_dec(v_i_74_);
lean_inc(v___x_86_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_keys_88_, lean_object* v_vals_89_, lean_object* v_i_90_, lean_object* v_k_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_88_, v_vals_89_, v_i_90_, v_k_91_);
lean_dec_ref(v_k_91_);
lean_dec_ref(v_vals_89_);
lean_dec_ref(v_keys_88_);
return v_res_92_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object* v_x_93_, size_t v_x_94_, lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_es_96_; lean_object* v___x_97_; size_t v___x_98_; size_t v___x_99_; lean_object* v_j_100_; lean_object* v___x_101_; 
v_es_96_ = lean_ctor_get(v_x_93_, 0);
v___x_97_ = lean_box(2);
v___x_98_ = ((size_t)31ULL);
v___x_99_ = lean_usize_land(v_x_94_, v___x_98_);
v_j_100_ = lean_usize_to_nat(v___x_99_);
v___x_101_ = lean_array_get_borrowed(v___x_97_, v_es_96_, v_j_100_);
lean_dec(v_j_100_);
switch(lean_obj_tag(v___x_101_))
{
case 0:
{
lean_object* v_key_102_; lean_object* v_val_103_; size_t v___x_104_; size_t v___x_105_; uint8_t v___x_106_; 
v_key_102_ = lean_ctor_get(v___x_101_, 0);
v_val_103_ = lean_ctor_get(v___x_101_, 1);
v___x_104_ = lean_ptr_addr(v_x_95_);
v___x_105_ = lean_ptr_addr(v_key_102_);
v___x_106_ = lean_usize_dec_eq(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v___x_108_; 
lean_inc(v_val_103_);
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v_val_103_);
return v___x_108_;
}
}
case 1:
{
lean_object* v_node_109_; size_t v___x_110_; size_t v___x_111_; 
v_node_109_ = lean_ctor_get(v___x_101_, 0);
v___x_110_ = ((size_t)5ULL);
v___x_111_ = lean_usize_shift_right(v_x_94_, v___x_110_);
v_x_93_ = v_node_109_;
v_x_94_ = v___x_111_;
goto _start;
}
default: 
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(0);
return v___x_113_;
}
}
}
else
{
lean_object* v_ks_114_; lean_object* v_vs_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_ks_114_ = lean_ctor_get(v_x_93_, 0);
v_vs_115_ = lean_ctor_get(v_x_93_, 1);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_114_, v_vs_115_, v___x_116_, v_x_95_);
return v___x_117_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_93_ = stack[0].m_obj;
size_t v_x_94_ = stack[1].m_num;
lean_object* v_x_95_ = stack[2].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_93_, v_x_94_, v_x_95_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
size_t v_x_32393__boxed_122_; lean_object* v_res_123_; 
v_x_32393__boxed_122_ = lean_unbox_usize(v_x_120_);
lean_dec(v_x_120_);
v_res_123_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_119_, v_x_32393__boxed_122_, v_x_121_);
lean_dec_ref(v_x_121_);
lean_dec_ref(v_x_119_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; uint64_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_126_ = lean_ptr_addr(v_x_125_);
v___x_127_ = ((size_t)3ULL);
v___x_128_ = lean_usize_shift_right(v___x_126_, v___x_127_);
v___x_129_ = lean_usize_to_uint64(v___x_128_);
v___x_130_ = lean_uint64_to_usize(v___x_129_);
v___x_131_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_124_, v___x_130_, v_x_125_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_132_, v_x_133_);
lean_dec_ref(v_x_133_);
lean_dec_ref(v_x_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_ks_139_; lean_object* v_vs_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_166_; 
v_ks_139_ = lean_ctor_get(v_x_135_, 0);
v_vs_140_ = lean_ctor_get(v_x_135_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_166_ == 0)
{
v___x_142_ = v_x_135_;
v_isShared_143_ = v_isSharedCheck_166_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_vs_140_);
lean_inc(v_ks_139_);
lean_dec(v_x_135_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_166_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_array_get_size(v_ks_139_);
v___x_145_ = lean_nat_dec_lt(v_x_136_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_x_136_);
v___x_146_ = lean_array_push(v_ks_139_, v_x_137_);
v___x_147_ = lean_array_push(v_vs_140_, v_x_138_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_147_);
lean_ctor_set(v___x_142_, 0, v___x_146_);
v___x_149_ = v___x_142_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v_k_x27_151_; size_t v___x_152_; size_t v___x_153_; uint8_t v___x_154_; 
v_k_x27_151_ = lean_array_fget_borrowed(v_ks_139_, v_x_136_);
v___x_152_ = lean_ptr_addr(v_x_137_);
v___x_153_ = lean_ptr_addr(v_k_x27_151_);
v___x_154_ = lean_usize_dec_eq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_156_; 
if (v_isShared_143_ == 0)
{
v___x_156_ = v___x_142_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_ks_139_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_vs_140_);
v___x_156_ = v_reuseFailAlloc_160_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_x_136_, v___x_157_);
lean_dec(v_x_136_);
v_x_135_ = v___x_156_;
v_x_136_ = v___x_158_;
goto _start;
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_161_ = lean_array_fset(v_ks_139_, v_x_136_, v_x_137_);
v___x_162_ = lean_array_fset(v_vs_140_, v_x_136_, v_x_138_);
lean_dec(v_x_136_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_162_);
lean_ctor_set(v___x_142_, 0, v___x_161_);
v___x_164_ = v___x_142_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(lean_object* v_n_167_, lean_object* v_k_168_, lean_object* v_v_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(v_n_167_, v___x_170_, v_k_168_, v_v_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_172_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(lean_object* v_x_173_, size_t v_x_174_, size_t v_x_175_, lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v_es_178_; size_t v___x_179_; size_t v___x_180_; lean_object* v_j_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_es_178_ = lean_ctor_get(v_x_173_, 0);
v___x_179_ = ((size_t)31ULL);
v___x_180_ = lean_usize_land(v_x_174_, v___x_179_);
v_j_181_ = lean_usize_to_nat(v___x_180_);
v___x_182_ = lean_array_get_size(v_es_178_);
v___x_183_ = lean_nat_dec_lt(v_j_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_dec(v_j_181_);
lean_dec(v_x_177_);
lean_dec_ref(v_x_176_);
return v_x_173_;
}
else
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_224_; 
lean_inc_ref(v_es_178_);
v_isSharedCheck_224_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; 
v_unused_225_ = lean_ctor_get(v_x_173_, 0);
lean_dec(v_unused_225_);
v___x_185_ = v_x_173_;
v_isShared_186_ = v_isSharedCheck_224_;
goto v_resetjp_184_;
}
else
{
lean_dec(v_x_173_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_224_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_v_187_; lean_object* v___x_188_; lean_object* v_xs_x27_189_; lean_object* v___y_191_; 
v_v_187_ = lean_array_fget(v_es_178_, v_j_181_);
v___x_188_ = lean_box(0);
v_xs_x27_189_ = lean_array_fset(v_es_178_, v_j_181_, v___x_188_);
switch(lean_obj_tag(v_v_187_))
{
case 0:
{
lean_object* v_key_196_; lean_object* v_val_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_209_; 
v_key_196_ = lean_ctor_get(v_v_187_, 0);
v_val_197_ = lean_ctor_get(v_v_187_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_v_187_);
if (v_isSharedCheck_209_ == 0)
{
v___x_199_ = v_v_187_;
v_isShared_200_ = v_isSharedCheck_209_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_val_197_);
lean_inc(v_key_196_);
lean_dec(v_v_187_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_209_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
size_t v___x_201_; size_t v___x_202_; uint8_t v___x_203_; 
v___x_201_ = lean_ptr_addr(v_x_176_);
v___x_202_ = lean_ptr_addr(v_key_196_);
v___x_203_ = lean_usize_dec_eq(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_del_object(v___x_199_);
v___x_204_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_196_, v_val_197_, v_x_176_, v_x_177_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___y_191_ = v___x_205_;
goto v___jp_190_;
}
else
{
lean_object* v___x_207_; 
lean_dec(v_val_197_);
lean_dec(v_key_196_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v_x_177_);
lean_ctor_set(v___x_199_, 0, v_x_176_);
v___x_207_ = v___x_199_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_x_176_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_x_177_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
v___y_191_ = v___x_207_;
goto v___jp_190_;
}
}
}
}
case 1:
{
lean_object* v_node_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_222_; 
v_node_210_ = lean_ctor_get(v_v_187_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_v_187_);
if (v_isSharedCheck_222_ == 0)
{
v___x_212_ = v_v_187_;
v_isShared_213_ = v_isSharedCheck_222_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_node_210_);
lean_dec(v_v_187_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_222_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_214_ = ((size_t)5ULL);
v___x_215_ = lean_usize_shift_right(v_x_174_, v___x_214_);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_add(v_x_175_, v___x_216_);
v___x_218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_node_210_, v___x_215_, v___x_217_, v_x_176_, v_x_177_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_218_);
v___x_220_ = v___x_212_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
v___y_191_ = v___x_220_;
goto v___jp_190_;
}
}
}
default: 
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_x_176_);
lean_ctor_set(v___x_223_, 1, v_x_177_);
v___y_191_ = v___x_223_;
goto v___jp_190_;
}
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = lean_array_fset(v_xs_x27_189_, v_j_181_, v___y_191_);
lean_dec(v_j_181_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_192_);
v___x_194_ = v___x_185_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
else
{
lean_object* v_ks_226_; lean_object* v_vs_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_245_; 
v_ks_226_ = lean_ctor_get(v_x_173_, 0);
v_vs_227_ = lean_ctor_get(v_x_173_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_245_ == 0)
{
v___x_229_ = v_x_173_;
v_isShared_230_ = v_isSharedCheck_245_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_vs_227_);
lean_inc(v_ks_226_);
lean_dec(v_x_173_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_245_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_ks_226_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_vs_227_);
v___x_232_ = v_reuseFailAlloc_244_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v_newNode_233_; size_t v___x_234_; uint8_t v___x_235_; 
v_newNode_233_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(v___x_232_, v_x_176_, v_x_177_);
v___x_234_ = ((size_t)7ULL);
v___x_235_ = lean_usize_dec_le(v___x_234_, v_x_175_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_233_);
v___x_237_ = lean_unsigned_to_nat(4u);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
if (v___x_238_ == 0)
{
lean_object* v_ks_239_; lean_object* v_vs_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_ks_239_ = lean_ctor_get(v_newNode_233_, 0);
lean_inc_ref(v_ks_239_);
v_vs_240_ = lean_ctor_get(v_newNode_233_, 1);
lean_inc_ref(v_vs_240_);
lean_dec_ref(v_newNode_233_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0);
v___x_243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_x_175_, v_ks_239_, v_vs_240_, v___x_241_, v___x_242_);
lean_dec_ref(v_vs_240_);
lean_dec_ref(v_ks_239_);
return v___x_243_;
}
else
{
return v_newNode_233_;
}
}
else
{
return v_newNode_233_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_173_ = stack[0].m_obj;
size_t v_x_174_ = stack[1].m_num;
size_t v_x_175_ = stack[2].m_num;
lean_object* v_x_176_ = stack[3].m_obj;
lean_object* v_x_177_ = stack[4].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_173_, v_x_174_, v_x_175_, v_x_176_, v_x_177_);
stack->m_obj
 = v_res_246_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(size_t v_depth_247_, lean_object* v_keys_248_, lean_object* v_vals_249_, lean_object* v_i_250_, lean_object* v_entries_251_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_array_get_size(v_keys_248_);
v___x_253_ = lean_nat_dec_lt(v_i_250_, v___x_252_);
if (v___x_253_ == 0)
{
lean_dec(v_i_250_);
return v_entries_251_;
}
else
{
lean_object* v_k_254_; lean_object* v_v_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; uint64_t v___x_259_; size_t v_h_260_; size_t v___x_261_; lean_object* v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v_h_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_k_254_ = lean_array_fget_borrowed(v_keys_248_, v_i_250_);
v_v_255_ = lean_array_fget_borrowed(v_vals_249_, v_i_250_);
v___x_256_ = lean_ptr_addr(v_k_254_);
v___x_257_ = ((size_t)3ULL);
v___x_258_ = lean_usize_shift_right(v___x_256_, v___x_257_);
v___x_259_ = lean_usize_to_uint64(v___x_258_);
v_h_260_ = lean_uint64_to_usize(v___x_259_);
v___x_261_ = ((size_t)5ULL);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_sub(v_depth_247_, v___x_263_);
v___x_265_ = lean_usize_mul(v___x_261_, v___x_264_);
v_h_266_ = lean_usize_shift_right(v_h_260_, v___x_265_);
v___x_267_ = lean_nat_add(v_i_250_, v___x_262_);
lean_dec(v_i_250_);
lean_inc(v_v_255_);
lean_inc(v_k_254_);
v___x_268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_entries_251_, v_h_266_, v_depth_247_, v_k_254_, v_v_255_);
v_i_250_ = v___x_267_;
v_entries_251_ = v___x_268_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_247_ = stack[0].m_num;
lean_object* v_keys_248_ = stack[1].m_obj;
lean_object* v_vals_249_ = stack[2].m_obj;
lean_object* v_i_250_ = stack[3].m_obj;
lean_object* v_entries_251_ = stack[4].m_obj;
lean_object* v_res_270_;
v_res_270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_depth_247_, v_keys_248_, v_vals_249_, v_i_250_, v_entries_251_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_271_, lean_object* v_keys_272_, lean_object* v_vals_273_, lean_object* v_i_274_, lean_object* v_entries_275_){
_start:
{
size_t v_depth_boxed_276_; lean_object* v_res_277_; 
v_depth_boxed_276_ = lean_unbox_usize(v_depth_271_);
lean_dec(v_depth_271_);
v_res_277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_depth_boxed_276_, v_keys_272_, v_vals_273_, v_i_274_, v_entries_275_);
lean_dec_ref(v_vals_273_);
lean_dec_ref(v_keys_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___boxed(lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
size_t v_x_32615__boxed_283_; size_t v_x_32616__boxed_284_; lean_object* v_res_285_; 
v_x_32615__boxed_283_ = lean_unbox_usize(v_x_279_);
lean_dec(v_x_279_);
v_x_32616__boxed_284_ = lean_unbox_usize(v_x_280_);
lean_dec(v_x_280_);
v_res_285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_278_, v_x_32615__boxed_283_, v_x_32616__boxed_284_, v_x_281_, v_x_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; uint64_t v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v___x_289_ = lean_ptr_addr(v_x_287_);
v___x_290_ = ((size_t)3ULL);
v___x_291_ = lean_usize_shift_right(v___x_289_, v___x_290_);
v___x_292_ = lean_usize_to_uint64(v___x_291_);
v___x_293_ = lean_uint64_to_usize(v___x_292_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_286_, v___x_293_, v___x_294_, v_x_287_, v_x_288_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAnchor___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v_dummy_297_; 
v___x_296_ = lean_box(0);
v_dummy_297_ = l_Lean_Expr_sort___override(v___x_296_);
return v_dummy_297_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_pinfos_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; 
if (lean_obj_tag(v_x_300_) == 5)
{
lean_object* v_fn_330_; lean_object* v_arg_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_fn_330_ = lean_ctor_get(v_x_300_, 0);
lean_inc_ref(v_fn_330_);
v_arg_331_ = lean_ctor_get(v_x_300_, 1);
lean_inc_ref(v_arg_331_);
lean_dec_ref_known(v_x_300_, 2);
v___x_332_ = lean_array_set(v_x_301_, v_x_302_, v_arg_331_);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_sub(v_x_302_, v___x_333_);
lean_dec(v_x_302_);
v_x_300_ = v_fn_330_;
v_x_301_ = v___x_332_;
v_x_302_ = v___x_334_;
goto _start;
}
else
{
lean_object* v___x_336_; uint8_t v___y_338_; uint8_t v___x_356_; 
lean_dec(v_x_302_);
v___x_336_ = l_Lean_instInhabitedExpr;
v___x_356_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_300_);
if (v___x_356_ == 0)
{
v___y_338_ = v___x_356_;
goto v___jp_337_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_array_get_size(v_x_301_);
v___x_358_ = lean_unsigned_to_nat(2u);
v___x_359_ = lean_nat_dec_eq(v___x_357_, v___x_358_);
v___y_338_ = v___x_359_;
goto v___jp_337_;
}
v___jp_337_:
{
if (v___y_338_ == 0)
{
uint8_t v___x_339_; 
v___x_339_ = l_Lean_Expr_hasLooseBVars(v_x_300_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
lean_inc_ref(v_x_300_);
v___x_341_ = l_Lean_Meta_getFunInfo(v_x_300_, v___x_340_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v_paramInfo_343_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v_paramInfo_343_ = lean_ctor_get(v_a_342_, 0);
lean_inc_ref(v_paramInfo_343_);
lean_dec(v_a_342_);
v_pinfos_314_ = v_paramInfo_343_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
v___y_319_ = v___y_307_;
v___y_320_ = v___y_308_;
v___y_321_ = v___y_309_;
v___y_322_ = v___y_310_;
v___y_323_ = v___y_311_;
goto v___jp_313_;
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v_x_301_);
lean_dec_ref(v_x_300_);
v_a_344_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_341_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0));
v_pinfos_314_ = v___x_352_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
v___y_319_ = v___y_307_;
v___y_320_ = v___y_308_;
v___y_321_ = v___y_309_;
v___y_322_ = v___y_310_;
v___y_323_ = v___y_311_;
goto v___jp_313_;
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v_x_300_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_array_get(v___x_336_, v_x_301_, v___x_353_);
lean_dec_ref(v_x_301_);
v___x_355_ = l_Lean_Meta_Grind_getAnchor(v___x_354_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
return v___x_355_;
}
}
}
v___jp_313_:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Grind_getAnchor(v_x_300_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint64_t v___x_328_; lean_object* v___x_329_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_array_get_size(v_x_301_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_unbox_uint64(v_a_325_);
lean_dec(v_a_325_);
v___x_329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v___x_326_, v_x_301_, v_pinfos_314_, v___x_327_, v___x_328_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec_ref(v_pinfos_314_);
lean_dec_ref(v_x_301_);
return v___x_329_;
}
else
{
lean_dec_ref(v_pinfos_314_);
lean_dec_ref(v_x_301_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_300_ = stack[0].m_obj;
lean_object* v_x_301_ = stack[1].m_obj;
lean_object* v_x_302_ = stack[2].m_obj;
lean_object* v___y_303_ = stack[3].m_obj;
lean_object* v___y_304_ = stack[4].m_obj;
lean_object* v___y_305_ = stack[5].m_obj;
lean_object* v___y_306_ = stack[6].m_obj;
lean_object* v___y_307_ = stack[7].m_obj;
lean_object* v___y_308_ = stack[8].m_obj;
lean_object* v___y_309_ = stack[9].m_obj;
lean_object* v___y_310_ = stack[10].m_obj;
lean_object* v___y_311_ = stack[11].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_300_, v_x_301_, v_x_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
stack->m_obj
 = v_res_360_;
}
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
uint64_t v_a_373_; lean_object* v___y_374_; lean_object* v_n_401_; lean_object* v_d_402_; lean_object* v_b_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___x_422_; lean_object* v_anchors_423_; lean_object* v___x_424_; 
v___x_422_ = lean_st_ref_get(v_a_364_);
v_anchors_423_ = lean_ctor_get(v___x_422_, 10);
lean_inc_ref(v_anchors_423_);
lean_dec(v___x_422_);
v___x_424_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_423_, v_e_361_);
lean_dec_ref(v_anchors_423_);
if (lean_obj_tag(v___x_424_) == 1)
{
lean_object* v_val_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_e_361_);
v_val_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_val_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 0);
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_val_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
else
{
lean_dec(v___x_424_);
switch(lean_obj_tag(v_e_361_))
{
case 0:
{
lean_object* v_deBruijnIndex_433_; uint64_t v___x_434_; 
v_deBruijnIndex_433_ = lean_ctor_get(v_e_361_, 0);
v___x_434_ = lean_uint64_of_nat(v_deBruijnIndex_433_);
v_a_373_ = v___x_434_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
case 1:
{
lean_object* v_fvarId_435_; lean_object* v___x_436_; 
v_fvarId_435_ = lean_ctor_get(v_e_361_, 0);
lean_inc(v_fvarId_435_);
v___x_436_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_435_, v_a_367_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; uint64_t v___x_439_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = l_Lean_LocalDecl_userName(v_a_437_);
lean_dec(v_a_437_);
v___x_439_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_438_);
v_a_373_ = v___x_439_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref_known(v_e_361_, 1);
v_a_440_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_436_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_436_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
case 4:
{
lean_object* v_declName_448_; lean_object* v___x_449_; 
v_declName_448_ = lean_ctor_get(v_e_361_, 0);
lean_inc(v_declName_448_);
v___x_449_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_448_, v_a_370_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; uint8_t v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = lean_unbox(v_a_450_);
lean_dec(v_a_450_);
if (v___x_451_ == 0)
{
uint64_t v___x_452_; 
lean_inc(v_declName_448_);
v___x_452_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_448_);
v_a_373_ = v___x_452_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
else
{
uint64_t v___x_453_; 
v___x_453_ = 0ULL;
v_a_373_ = v___x_453_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref_known(v_e_361_, 2);
v_a_454_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_449_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_449_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
case 5:
{
lean_object* v_dummy_462_; lean_object* v_nargs_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_dummy_462_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_463_ = l_Lean_Expr_getAppNumArgs(v_e_361_);
lean_inc(v_nargs_463_);
v___x_464_ = lean_mk_array(v_nargs_463_, v_dummy_462_);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_sub(v_nargs_463_, v___x_465_);
lean_dec(v_nargs_463_);
lean_inc_ref(v_e_361_);
v___x_467_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_361_, v___x_464_, v___x_466_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; uint64_t v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_unbox_uint64(v_a_468_);
lean_dec(v_a_468_);
v_a_373_ = v___x_469_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
else
{
lean_dec_ref_known(v_e_361_, 2);
return v___x_467_;
}
}
case 6:
{
lean_object* v_binderName_470_; lean_object* v_binderType_471_; lean_object* v_body_472_; 
v_binderName_470_ = lean_ctor_get(v_e_361_, 0);
v_binderType_471_ = lean_ctor_get(v_e_361_, 1);
v_body_472_ = lean_ctor_get(v_e_361_, 2);
lean_inc_ref(v_body_472_);
lean_inc_ref(v_binderType_471_);
lean_inc(v_binderName_470_);
v_n_401_ = v_binderName_470_;
v_d_402_ = v_binderType_471_;
v_b_403_ = v_body_472_;
v___y_404_ = v_a_362_;
v___y_405_ = v_a_363_;
v___y_406_ = v_a_364_;
v___y_407_ = v_a_365_;
v___y_408_ = v_a_366_;
v___y_409_ = v_a_367_;
v___y_410_ = v_a_368_;
v___y_411_ = v_a_369_;
v___y_412_ = v_a_370_;
goto v___jp_400_;
}
case 7:
{
lean_object* v_binderName_473_; lean_object* v_binderType_474_; lean_object* v_body_475_; 
v_binderName_473_ = lean_ctor_get(v_e_361_, 0);
v_binderType_474_ = lean_ctor_get(v_e_361_, 1);
v_body_475_ = lean_ctor_get(v_e_361_, 2);
lean_inc_ref(v_body_475_);
lean_inc_ref(v_binderType_474_);
lean_inc(v_binderName_473_);
v_n_401_ = v_binderName_473_;
v_d_402_ = v_binderType_474_;
v_b_403_ = v_body_475_;
v___y_404_ = v_a_362_;
v___y_405_ = v_a_363_;
v___y_406_ = v_a_364_;
v___y_407_ = v_a_365_;
v___y_408_ = v_a_366_;
v___y_409_ = v_a_367_;
v___y_410_ = v_a_368_;
v___y_411_ = v_a_369_;
v___y_412_ = v_a_370_;
goto v___jp_400_;
}
case 8:
{
lean_object* v_declName_476_; lean_object* v_type_477_; lean_object* v_value_478_; lean_object* v_body_479_; lean_object* v___x_480_; 
v_declName_476_ = lean_ctor_get(v_e_361_, 0);
v_type_477_ = lean_ctor_get(v_e_361_, 1);
v_value_478_ = lean_ctor_get(v_e_361_, 2);
v_body_479_ = lean_ctor_get(v_e_361_, 3);
lean_inc_ref(v_value_478_);
v___x_480_ = l_Lean_Meta_Grind_getAnchor(v_value_478_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
lean_inc_ref(v_type_477_);
v___x_482_ = l_Lean_Meta_Grind_getAnchor(v_type_477_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
lean_inc_ref(v_body_479_);
v___x_484_ = l_Lean_Meta_Grind_getAnchor(v_body_479_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; uint64_t v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; uint64_t v___x_489_; uint64_t v___x_490_; uint64_t v___x_491_; uint64_t v___x_492_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
lean_inc(v_declName_476_);
v___x_486_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_476_);
v___x_487_ = lean_unbox_uint64(v_a_483_);
lean_dec(v_a_483_);
v___x_488_ = lean_unbox_uint64(v_a_485_);
lean_dec(v_a_485_);
v___x_489_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_487_, v___x_488_);
v___x_490_ = lean_unbox_uint64(v_a_481_);
lean_dec(v_a_481_);
v___x_491_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_490_, v___x_489_);
v___x_492_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_486_, v___x_491_);
v_a_373_ = v___x_492_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
else
{
lean_dec(v_a_483_);
lean_dec(v_a_481_);
lean_dec_ref_known(v_e_361_, 4);
return v___x_484_;
}
}
else
{
lean_dec(v_a_481_);
lean_dec_ref_known(v_e_361_, 4);
return v___x_482_;
}
}
else
{
lean_dec_ref_known(v_e_361_, 4);
return v___x_480_;
}
}
case 9:
{
lean_object* v_a_493_; uint64_t v___x_494_; 
v_a_493_ = lean_ctor_get(v_e_361_, 0);
v___x_494_ = l_Lean_Literal_hash(v_a_493_);
v_a_373_ = v___x_494_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
case 10:
{
lean_object* v_expr_495_; lean_object* v___x_496_; 
v_expr_495_ = lean_ctor_get(v_e_361_, 1);
lean_inc_ref(v_expr_495_);
v___x_496_ = l_Lean_Meta_Grind_getAnchor(v_expr_495_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; uint64_t v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = lean_unbox_uint64(v_a_497_);
lean_dec(v_a_497_);
v_a_373_ = v___x_498_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
else
{
lean_dec_ref_known(v_e_361_, 2);
return v___x_496_;
}
}
case 11:
{
lean_object* v_idx_499_; lean_object* v_struct_500_; lean_object* v___x_501_; 
v_idx_499_ = lean_ctor_get(v_e_361_, 1);
v_struct_500_ = lean_ctor_get(v_e_361_, 2);
lean_inc_ref(v_struct_500_);
v___x_501_ = l_Lean_Meta_Grind_getAnchor(v_struct_500_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; uint64_t v___x_503_; uint64_t v___x_504_; uint64_t v___x_505_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = lean_uint64_of_nat(v_idx_499_);
v___x_504_ = lean_unbox_uint64(v_a_502_);
lean_dec(v_a_502_);
v___x_505_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_503_, v___x_504_);
v_a_373_ = v___x_505_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
else
{
lean_dec_ref_known(v_e_361_, 3);
return v___x_501_;
}
}
default: 
{
uint64_t v___x_506_; 
v___x_506_ = 0ULL;
v_a_373_ = v___x_506_;
v___y_374_ = v_a_364_;
goto v___jp_372_;
}
}
}
v___jp_372_:
{
lean_object* v___x_375_; lean_object* v_congrThms_376_; lean_object* v_simp_377_; lean_object* v_symSimp_378_; lean_object* v_symDSimp_379_; lean_object* v_lastTag_380_; lean_object* v_counters_381_; lean_object* v_splitDiags_382_; lean_object* v_ematchDiags_383_; lean_object* v_lawfulEqCmpMap_384_; lean_object* v_reflCmpMap_385_; lean_object* v_anchors_386_; lean_object* v_instanceMap_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
v___x_375_ = lean_st_ref_take(v___y_374_);
v_congrThms_376_ = lean_ctor_get(v___x_375_, 0);
v_simp_377_ = lean_ctor_get(v___x_375_, 1);
v_symSimp_378_ = lean_ctor_get(v___x_375_, 2);
v_symDSimp_379_ = lean_ctor_get(v___x_375_, 3);
v_lastTag_380_ = lean_ctor_get(v___x_375_, 4);
v_counters_381_ = lean_ctor_get(v___x_375_, 5);
v_splitDiags_382_ = lean_ctor_get(v___x_375_, 6);
v_ematchDiags_383_ = lean_ctor_get(v___x_375_, 7);
v_lawfulEqCmpMap_384_ = lean_ctor_get(v___x_375_, 8);
v_reflCmpMap_385_ = lean_ctor_get(v___x_375_, 9);
v_anchors_386_ = lean_ctor_get(v___x_375_, 10);
v_instanceMap_387_ = lean_ctor_get(v___x_375_, 11);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_399_ == 0)
{
v___x_389_ = v___x_375_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_instanceMap_387_);
lean_inc(v_anchors_386_);
lean_inc(v_reflCmpMap_385_);
lean_inc(v_lawfulEqCmpMap_384_);
lean_inc(v_ematchDiags_383_);
lean_inc(v_splitDiags_382_);
lean_inc(v_counters_381_);
lean_inc(v_lastTag_380_);
lean_inc(v_symDSimp_379_);
lean_inc(v_symSimp_378_);
lean_inc(v_simp_377_);
lean_inc(v_congrThms_376_);
lean_dec(v___x_375_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_box_uint64(v_a_373_);
v___x_392_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_anchors_386_, v_e_361_, v___x_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 10, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_congrThms_376_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_simp_377_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_symSimp_378_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_symDSimp_379_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_lastTag_380_);
lean_ctor_set(v_reuseFailAlloc_398_, 5, v_counters_381_);
lean_ctor_set(v_reuseFailAlloc_398_, 6, v_splitDiags_382_);
lean_ctor_set(v_reuseFailAlloc_398_, 7, v_ematchDiags_383_);
lean_ctor_set(v_reuseFailAlloc_398_, 8, v_lawfulEqCmpMap_384_);
lean_ctor_set(v_reuseFailAlloc_398_, 9, v_reflCmpMap_385_);
lean_ctor_set(v_reuseFailAlloc_398_, 10, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_398_, 11, v_instanceMap_387_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_st_ref_put(v___y_374_, v___x_394_);
v___x_396_ = lean_box_uint64(v_a_373_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
}
v___jp_400_:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Grind_getAnchor(v_d_402_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = l_Lean_Meta_Grind_getAnchor(v_b_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 1);
v___x_417_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_401_);
v___x_418_ = lean_unbox_uint64(v_a_414_);
lean_dec(v_a_414_);
v___x_419_ = lean_unbox_uint64(v_a_416_);
lean_dec(v_a_416_);
v___x_420_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_418_, v___x_419_);
v___x_421_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_417_, v___x_420_);
v_a_373_ = v___x_421_;
v___y_374_ = v___y_406_;
goto v___jp_372_;
}
else
{
lean_dec(v_a_414_);
lean_dec(v_n_401_);
lean_dec_ref(v_e_361_);
return v___x_415_;
}
}
else
{
lean_dec_ref(v_b_403_);
lean_dec(v_n_401_);
lean_dec_ref(v_e_361_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getAnchor_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_361_ = stack[0].m_obj;
lean_object* v_a_362_ = stack[1].m_obj;
lean_object* v_a_363_ = stack[2].m_obj;
lean_object* v_a_364_ = stack[3].m_obj;
lean_object* v_a_365_ = stack[4].m_obj;
lean_object* v_a_366_ = stack[5].m_obj;
lean_object* v_a_367_ = stack[6].m_obj;
lean_object* v_a_368_ = stack[7].m_obj;
lean_object* v_a_369_ = stack[8].m_obj;
lean_object* v_a_370_ = stack[9].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_Lean_Meta_Grind_getAnchor(v_e_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
stack->m_obj
 = v_res_507_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object* v_upperBound_508_, lean_object* v_args_509_, lean_object* v_pinfos_510_, lean_object* v_a_511_, uint64_t v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
uint64_t v_a_524_; uint8_t v___x_528_; 
v___x_528_ = lean_nat_dec_lt(v_a_511_, v_upperBound_508_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_a_511_);
v___x_529_ = lean_box_uint64(v_b_512_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = lean_array_fget_borrowed(v_args_509_, v_a_511_);
v___x_532_ = lean_array_get_size(v_pinfos_510_);
v___x_533_ = lean_nat_dec_lt(v_a_511_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
lean_inc(v___x_531_);
v___x_534_ = l_Lean_Meta_Grind_getAnchor(v___x_531_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; uint64_t v___x_536_; uint64_t v___x_537_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = lean_unbox_uint64(v_a_535_);
lean_dec(v_a_535_);
v___x_537_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_512_, v___x_536_);
v_a_524_ = v___x_537_;
goto v___jp_523_;
}
else
{
lean_dec(v_a_511_);
return v___x_534_;
}
}
else
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_array_fget_borrowed(v_pinfos_510_, v_a_511_);
v___x_539_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_inc(v___x_531_);
v___x_540_ = l_Lean_Meta_Grind_getAnchor(v___x_531_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; uint64_t v___x_542_; uint64_t v___x_543_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = lean_unbox_uint64(v_a_541_);
lean_dec(v_a_541_);
v___x_543_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_512_, v___x_542_);
v_a_524_ = v___x_543_;
goto v___jp_523_;
}
else
{
lean_dec(v_a_511_);
return v___x_540_;
}
}
else
{
v_a_524_ = v_b_512_;
goto v___jp_523_;
}
}
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_a_511_, v___x_525_);
lean_dec(v_a_511_);
v_a_511_ = v___x_526_;
v_b_512_ = v_a_524_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_508_ = stack[0].m_obj;
lean_object* v_args_509_ = stack[1].m_obj;
lean_object* v_pinfos_510_ = stack[2].m_obj;
lean_object* v_a_511_ = stack[3].m_obj;
uint64_t v_b_512_ = stack[4].m_num;
lean_object* v___y_513_ = stack[5].m_obj;
lean_object* v___y_514_ = stack[6].m_obj;
lean_object* v___y_515_ = stack[7].m_obj;
lean_object* v___y_516_ = stack[8].m_obj;
lean_object* v___y_517_ = stack[9].m_obj;
lean_object* v___y_518_ = stack[10].m_obj;
lean_object* v___y_519_ = stack[11].m_obj;
lean_object* v___y_520_ = stack[12].m_obj;
lean_object* v___y_521_ = stack[13].m_obj;
lean_object* v_res_544_;
v_res_544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_upperBound_508_, v_args_509_, v_pinfos_510_, v_a_511_, v_b_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
stack->m_obj
 = v_res_544_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg___boxed(lean_object* v_upperBound_545_, lean_object* v_args_546_, lean_object* v_pinfos_547_, lean_object* v_a_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint64_t v_b_boxed_560_; lean_object* v_res_561_; 
v_b_boxed_560_ = lean_unbox_uint64(v_b_549_);
lean_dec_ref(v_b_549_);
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_upperBound_545_, v_args_546_, v_pinfos_547_, v_a_548_, v_b_boxed_560_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v_pinfos_547_);
lean_dec_ref(v_args_546_);
lean_dec(v_upperBound_545_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_562_, v_x_563_, v_x_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_Grind_getAnchor(v_e_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_00_u03b2_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_x_589_, v_x_590_, v_x_591_);
return v___x_592_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_upperBound_593_, lean_object* v_args_594_, lean_object* v_pinfos_595_, lean_object* v_inst_596_, lean_object* v_R_597_, lean_object* v_a_598_, uint64_t v_b_599_, lean_object* v_c_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_upperBound_593_, v_args_594_, v_pinfos_595_, v_a_598_, v_b_599_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_593_ = stack[0].m_obj;
lean_object* v_args_594_ = stack[1].m_obj;
lean_object* v_pinfos_595_ = stack[2].m_obj;
lean_object* v_a_598_ = stack[5].m_obj;
uint64_t v_b_599_ = stack[6].m_num;
lean_object* v___y_601_ = stack[8].m_obj;
lean_object* v___y_602_ = stack[9].m_obj;
lean_object* v___y_603_ = stack[10].m_obj;
lean_object* v___y_604_ = stack[11].m_obj;
lean_object* v___y_605_ = stack[12].m_obj;
lean_object* v___y_606_ = stack[13].m_obj;
lean_object* v___y_607_ = stack[14].m_obj;
lean_object* v___y_608_ = stack[15].m_obj;
lean_object* v___y_609_ = stack[16].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(v_upperBound_593_, v_args_594_, v_pinfos_595_, lean_box(0), lean_box(0), v_a_598_, v_b_599_, lean_box(0), v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_613_ = _args[0];
lean_object* v_args_614_ = _args[1];
lean_object* v_pinfos_615_ = _args[2];
lean_object* v_inst_616_ = _args[3];
lean_object* v_R_617_ = _args[4];
lean_object* v_a_618_ = _args[5];
lean_object* v_b_619_ = _args[6];
lean_object* v_c_620_ = _args[7];
lean_object* v___y_621_ = _args[8];
lean_object* v___y_622_ = _args[9];
lean_object* v___y_623_ = _args[10];
lean_object* v___y_624_ = _args[11];
lean_object* v___y_625_ = _args[12];
lean_object* v___y_626_ = _args[13];
lean_object* v___y_627_ = _args[14];
lean_object* v___y_628_ = _args[15];
lean_object* v___y_629_ = _args[16];
lean_object* v___y_630_ = _args[17];
_start:
{
uint64_t v_b_boxed_631_; lean_object* v_res_632_; 
v_b_boxed_631_ = lean_unbox_uint64(v_b_619_);
lean_dec_ref(v_b_619_);
v_res_632_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(v_upperBound_613_, v_args_614_, v_pinfos_615_, v_inst_616_, v_R_617_, v_a_618_, v_b_boxed_631_, v_c_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v_pinfos_615_);
lean_dec_ref(v_args_614_);
lean_dec(v_upperBound_613_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_633_, lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_637_, v_x_638_, v_x_639_);
lean_dec_ref(v_x_639_);
lean_dec_ref(v_x_638_);
return v_res_640_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(lean_object* v_00_u03b2_641_, lean_object* v_x_642_, size_t v_x_643_, size_t v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_642_, v_x_643_, v_x_644_, v_x_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_642_ = stack[1].m_obj;
size_t v_x_643_ = stack[2].m_num;
size_t v_x_644_ = stack[3].m_num;
lean_object* v_x_645_ = stack[4].m_obj;
lean_object* v_x_646_ = stack[5].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(lean_box(0), v_x_642_, v_x_643_, v_x_644_, v_x_645_, v_x_646_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___boxed(lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
size_t v_x_33683__boxed_655_; size_t v_x_33684__boxed_656_; lean_object* v_res_657_; 
v_x_33683__boxed_655_ = lean_unbox_usize(v_x_651_);
lean_dec(v_x_651_);
v_x_33684__boxed_656_ = lean_unbox_usize(v_x_652_);
lean_dec(v_x_652_);
v_res_657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(v_00_u03b2_649_, v_x_650_, v_x_33683__boxed_655_, v_x_33684__boxed_656_, v_x_653_, v_x_654_);
return v_res_657_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_658_, lean_object* v_x_659_, size_t v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_659_, v_x_660_, v_x_661_);
return v___x_662_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_659_ = stack[1].m_obj;
size_t v_x_660_ = stack[2].m_num;
lean_object* v_x_661_ = stack[3].m_obj;
lean_object* v_res_663_;
v_res_663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_box(0), v_x_659_, v_x_660_, v_x_661_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
size_t v_x_33711__boxed_668_; lean_object* v_res_669_; 
v_x_33711__boxed_668_ = lean_unbox_usize(v_x_666_);
lean_dec(v_x_666_);
v_res_669_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_664_, v_x_665_, v_x_33711__boxed_668_, v_x_667_);
lean_dec_ref(v_x_667_);
lean_dec_ref(v_x_665_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_670_, lean_object* v_n_671_, lean_object* v_k_672_, lean_object* v_v_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(v_n_671_, v_k_672_, v_v_673_);
return v___x_674_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_675_, size_t v_depth_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_heq_679_, lean_object* v_i_680_, lean_object* v_entries_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_depth_676_, v_keys_677_, v_vals_678_, v_i_680_, v_entries_681_);
return v___x_682_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_676_ = stack[1].m_num;
lean_object* v_keys_677_ = stack[2].m_obj;
lean_object* v_vals_678_ = stack[3].m_obj;
lean_object* v_i_680_ = stack[5].m_obj;
lean_object* v_entries_681_ = stack[6].m_obj;
lean_object* v_res_683_;
v_res_683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(lean_box(0), v_depth_676_, v_keys_677_, v_vals_678_, lean_box(0), v_i_680_, v_entries_681_);
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_684_, lean_object* v_depth_685_, lean_object* v_keys_686_, lean_object* v_vals_687_, lean_object* v_heq_688_, lean_object* v_i_689_, lean_object* v_entries_690_){
_start:
{
size_t v_depth_boxed_691_; lean_object* v_res_692_; 
v_depth_boxed_691_ = lean_unbox_usize(v_depth_685_);
lean_dec(v_depth_685_);
v_res_692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(v_00_u03b2_684_, v_depth_boxed_691_, v_keys_686_, v_vals_687_, v_heq_688_, v_i_689_, v_entries_690_);
lean_dec_ref(v_vals_687_);
lean_dec_ref(v_keys_686_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_693_, lean_object* v_keys_694_, lean_object* v_vals_695_, lean_object* v_heq_696_, lean_object* v_i_697_, lean_object* v_k_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_694_, v_vals_695_, v_i_697_, v_k_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_700_, lean_object* v_keys_701_, lean_object* v_vals_702_, lean_object* v_heq_703_, lean_object* v_i_704_, lean_object* v_k_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_700_, v_keys_701_, v_vals_702_, v_heq_703_, v_i_704_, v_k_705_);
lean_dec_ref(v_k_705_);
lean_dec_ref(v_vals_702_);
lean_dec_ref(v_keys_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(v_x_708_, v_x_709_, v_x_710_, v_x_711_);
return v___x_712_;
}
}
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_713_, uint64_t v_anchor_714_){
_start:
{
lean_object* v_numDigits_715_; uint64_t v_anchorPrefix_716_; uint64_t v___x_717_; uint64_t v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v_shift_721_; uint64_t v___x_722_; uint8_t v___x_723_; 
v_numDigits_715_ = lean_ctor_get(v_anchorRef_713_, 0);
v_anchorPrefix_716_ = lean_ctor_get_uint64(v_anchorRef_713_, sizeof(void*)*1);
v___x_717_ = 64ULL;
v___x_718_ = lean_uint64_of_nat(v_numDigits_715_);
v___x_719_ = 2ULL;
v___x_720_ = lean_uint64_shift_left(v___x_718_, v___x_719_);
v_shift_721_ = lean_uint64_sub(v___x_717_, v___x_720_);
v___x_722_ = lean_uint64_shift_right(v_anchor_714_, v_shift_721_);
v___x_723_ = lean_uint64_dec_eq(v_anchorPrefix_716_, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AnchorRef_matches_0interp(lean_interpreter_value* stack)
{
lean_object* v_anchorRef_713_ = stack[0].m_obj;
uint64_t v_anchor_714_ = stack[1].m_num;
uint8_t v_res_724_;
v_res_724_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_713_, v_anchor_714_);
stack->m_num = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_725_, lean_object* v_anchor_726_){
_start:
{
uint64_t v_anchor_boxed_727_; uint8_t v_res_728_; lean_object* v_r_729_; 
v_anchor_boxed_727_ = lean_unbox_uint64(v_anchor_726_);
lean_dec_ref(v_anchor_726_);
v_res_728_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_725_, v_anchor_boxed_727_);
lean_dec_ref(v_anchorRef_725_);
v_r_729_ = lean_box(v_res_728_);
return v_r_729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11(void){
_start:
{
lean_object* v___x_750_; lean_object* v___f_751_; 
v___x_750_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_751_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_751_, 0, v___x_750_);
return v___f_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_752_, lean_object* v_shift_753_, lean_object* v___f_754_, lean_object* v___f_755_, lean_object* v_numDigits_756_, lean_object* v_es_757_, lean_object* v___x_758_, lean_object* v_a_759_, lean_object* v_x_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_752_, v_shift_753_, v___f_754_, v___f_755_, v_numDigits_756_, v_es_757_, v___x_758_, v_a_759_, v_x_760_, v___y_761_);
lean_dec(v_numDigits_756_);
lean_dec(v_shift_753_);
return v_res_762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_box(0);
v___x_764_ = lean_unsigned_to_nat(16u);
v___x_765_ = lean_mk_array(v___x_764_, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_found_768_; 
v___x_766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12);
v___x_767_ = lean_unsigned_to_nat(0u);
v_found_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_768_, 0, v___x_767_);
lean_ctor_set(v_found_768_, 1, v___x_766_);
return v_found_768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_found_769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_found_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_772_, lean_object* v_es_773_, lean_object* v_numDigits_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9));
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = lean_nat_mul(v___x_776_, v_numDigits_774_);
v___x_778_ = lean_unsigned_to_nat(64u);
v___x_779_ = lean_nat_dec_lt(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_dec(v___x_777_);
lean_dec_ref(v_es_773_);
lean_dec_ref(v_inst_772_);
return v_numDigits_774_;
}
else
{
lean_object* v___f_780_; lean_object* v_shift_781_; lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___f_784_; lean_object* v___x_785_; size_t v_sz_786_; size_t v___x_787_; lean_object* v___x_788_; lean_object* v_fst_789_; 
v___f_780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10));
v_shift_781_ = lean_nat_sub(v___x_778_, v___x_777_);
lean_dec(v___x_777_);
v___f_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11);
v___x_783_ = lean_box(0);
lean_inc_ref(v_es_773_);
lean_inc(v_numDigits_774_);
v___f_784_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_784_, 0, v_inst_772_);
lean_closure_set(v___f_784_, 1, v_shift_781_);
lean_closure_set(v___f_784_, 2, v___f_782_);
lean_closure_set(v___f_784_, 3, v___f_780_);
lean_closure_set(v___f_784_, 4, v_numDigits_774_);
lean_closure_set(v___f_784_, 5, v_es_773_);
lean_closure_set(v___f_784_, 6, v___x_783_);
v___x_785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_786_ = lean_array_size(v_es_773_);
v___x_787_ = ((size_t)0ULL);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_775_, v_es_773_, v___f_784_, v_sz_786_, v___x_787_, v___x_785_);
v_fst_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_fst_789_);
lean_dec(v___x_788_);
if (lean_obj_tag(v_fst_789_) == 0)
{
return v_numDigits_774_;
}
else
{
lean_object* v_val_790_; 
lean_dec(v_numDigits_774_);
v_val_790_ = lean_ctor_get(v_fst_789_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v_fst_789_, 1);
return v_val_790_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_791_, lean_object* v_shift_792_, lean_object* v___f_793_, lean_object* v___f_794_, lean_object* v_numDigits_795_, lean_object* v_es_796_, lean_object* v___x_797_, lean_object* v_a_798_, lean_object* v_x_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_snd_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_839_; 
v_snd_801_ = lean_ctor_get(v___y_800_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v___y_800_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___y_800_, 0);
lean_dec(v_unused_840_);
v___x_803_ = v___y_800_;
v_isShared_804_ = v_isSharedCheck_839_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snd_801_);
lean_dec(v___y_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_839_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref(v_inst_791_);
v___x_805_ = lean_apply_1(v_inst_791_, v_a_798_);
v___x_806_ = lean_uint64_of_nat(v_shift_792_);
v___x_807_ = lean_unbox_uint64(v___x_805_);
v___x_808_ = lean_uint64_shift_right(v___x_807_, v___x_806_);
v___x_809_ = lean_box_uint64(v___x_808_);
lean_inc_ref(v___f_794_);
lean_inc_ref(v___f_793_);
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_793_, v___f_794_, v_snd_801_, v___x_809_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___f_794_);
lean_dec_ref(v___f_793_);
v_val_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_832_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_832_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_832_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint64_t v___x_815_; uint64_t v___x_816_; uint8_t v___x_817_; 
v___x_815_ = lean_unbox_uint64(v_val_811_);
lean_dec(v_val_811_);
v___x_816_ = lean_unbox_uint64(v___x_805_);
lean_dec_ref(v___x_805_);
v___x_817_ = lean_uint64_dec_eq(v___x_815_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v___x_797_);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_nat_add(v_numDigits_795_, v___x_818_);
v___x_820_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_791_, v_es_796_, v___x_819_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_820_);
v___x_822_ = v___x_813_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_827_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_822_);
v___x_824_ = v___x_803_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_snd_801_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
}
else
{
lean_object* v___x_829_; 
lean_del_object(v___x_813_);
lean_dec_ref(v_es_796_);
lean_dec_ref(v_inst_791_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_797_);
v___x_829_ = v___x_803_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_snd_801_);
v___x_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
}
}
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec(v___x_810_);
lean_dec_ref(v_es_796_);
lean_dec_ref(v_inst_791_);
v___x_833_ = lean_box_uint64(v___x_808_);
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_793_, v___f_794_, v_snd_801_, v___x_833_, v___x_805_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_834_);
lean_ctor_set(v___x_803_, 0, v___x_797_);
v___x_836_ = v___x_803_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_841_, lean_object* v_inst_842_, lean_object* v_es_843_, lean_object* v_numDigits_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_842_, v_es_843_, v_numDigits_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter___redArg(lean_object* v_x_846_, lean_object* v_h__1_847_, lean_object* v_h__2_848_){
_start:
{
if (lean_obj_tag(v_x_846_) == 1)
{
lean_object* v_val_849_; lean_object* v___x_850_; 
lean_dec(v_h__2_848_);
v_val_849_ = lean_ctor_get(v_x_846_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v_x_846_, 1);
v___x_850_ = lean_apply_1(v_h__1_847_, v_val_849_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; 
lean_dec(v_h__1_847_);
v___x_851_ = lean_apply_2(v_h__2_848_, v_x_846_, lean_box(0));
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter(lean_object* v_motive_852_, lean_object* v_x_853_, lean_object* v_h__1_854_, lean_object* v_h__2_855_){
_start:
{
if (lean_obj_tag(v_x_853_) == 1)
{
lean_object* v_val_856_; lean_object* v___x_857_; 
lean_dec(v_h__2_855_);
v_val_856_ = lean_ctor_get(v_x_853_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_x_853_, 1);
v___x_857_ = lean_apply_1(v_h__1_854_, v_val_856_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; 
lean_dec(v_h__1_854_);
v___x_858_ = lean_apply_2(v_h__2_855_, v_x_853_, lean_box(0));
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_859_, lean_object* v_h__1_860_, lean_object* v_h__2_861_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_h__1_860_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_apply_1(v_h__2_861_, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_865_; 
lean_dec(v_h__2_861_);
v_val_864_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v_x_859_, 1);
v___x_865_ = lean_apply_1(v_h__1_860_, v_val_864_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_866_, lean_object* v_motive_867_, lean_object* v_x_868_, lean_object* v_h__1_869_, lean_object* v_h__2_870_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_h__1_869_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_apply_1(v_h__2_870_, v___x_871_);
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; 
lean_dec(v_h__2_870_);
v_val_873_ = lean_ctor_get(v_x_868_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v_x_868_, 1);
v___x_874_ = lean_apply_1(v_h__1_869_, v_val_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_875_, lean_object* v_es_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(4u);
v___x_878_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_875_, v_es_876_, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_879_, lean_object* v_inst_880_, lean_object* v_es_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_880_, v_es_881_);
return v___x_882_;
}
}
uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_883_){
_start:
{
uint64_t v_anchor_884_; 
v_anchor_884_ = lean_ctor_get_uint64(v_e_883_, sizeof(void*)*1);
return v_anchor_884_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_883_ = stack[0].m_obj;
uint64_t v_res_885_;
v_res_885_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_883_);
stack->m_num = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_886_){
_start:
{
uint64_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_886_);
lean_dec_ref(v_e_886_);
v_r_888_ = lean_box_uint64(v_res_887_);
return v_r_888_;
}
}
lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_904_, uint64_t v_anchorPrefix_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_ref_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_ref_908_ = lean_ctor_get(v_a_906_, 2);
v___x_909_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_910_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_904_, v_anchorPrefix_905_);
v___x_911_ = l_Lean_mkAtom(v___x_910_);
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_mk_empty_array_with_capacity(v___x_912_);
v___x_914_ = lean_array_push(v___x_913_, v___x_911_);
v___x_915_ = lean_box(2);
v___x_916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_909_);
lean_ctor_set(v___x_916_, 2, v___x_914_);
v___x_917_ = 0;
v___x_918_ = l_Lean_SourceInfo_fromRef(v_ref_908_, v___x_917_);
v___x_919_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_920_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_918_);
v___x_921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_918_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Lean_Syntax_node2(v___x_918_, v___x_919_, v___x_921_, v___x_916_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numDigits_904_ = stack[0].m_obj;
uint64_t v_anchorPrefix_905_ = stack[1].m_num;
lean_object* v_a_906_ = stack[2].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_904_, v_anchorPrefix_905_, v_a_906_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_925_, lean_object* v_anchorPrefix_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
uint64_t v_anchorPrefix_boxed_929_; lean_object* v_res_930_; 
v_anchorPrefix_boxed_929_ = lean_unbox_uint64(v_anchorPrefix_926_);
lean_dec_ref(v_anchorPrefix_926_);
v_res_930_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_925_, v_anchorPrefix_boxed_929_, v_a_927_);
lean_dec_ref(v_a_927_);
lean_dec(v_numDigits_925_);
return v_res_930_;
}
}
lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_931_, uint64_t v_anchorPrefix_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_931_, v_anchorPrefix_932_, v_a_933_);
return v___x_936_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_numDigits_931_ = stack[0].m_obj;
uint64_t v_anchorPrefix_932_ = stack[1].m_num;
lean_object* v_a_933_ = stack[2].m_obj;
lean_object* v_a_934_ = stack[3].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_931_, v_anchorPrefix_932_, v_a_933_, v_a_934_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_938_, lean_object* v_anchorPrefix_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
uint64_t v_anchorPrefix_boxed_943_; lean_object* v_res_944_; 
v_anchorPrefix_boxed_943_ = lean_unbox_uint64(v_anchorPrefix_939_);
lean_dec_ref(v_anchorPrefix_939_);
v_res_944_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_938_, v_anchorPrefix_boxed_943_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_numDigits_938_);
return v_res_944_;
}
}
lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_945_, uint64_t v_anchor_946_, lean_object* v_a_947_){
_start:
{
uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v___x_953_; uint64_t v_anchorPrefix_954_; lean_object* v___x_955_; 
v___x_949_ = 64ULL;
v___x_950_ = lean_uint64_of_nat(v_numDigits_945_);
v___x_951_ = 2ULL;
v___x_952_ = lean_uint64_shift_left(v___x_950_, v___x_951_);
v___x_953_ = lean_uint64_sub(v___x_949_, v___x_952_);
v_anchorPrefix_954_ = lean_uint64_shift_right(v_anchor_946_, v___x_953_);
v___x_955_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_945_, v_anchorPrefix_954_, v_a_947_);
return v___x_955_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkAnchorSyntax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numDigits_945_ = stack[0].m_obj;
uint64_t v_anchor_946_ = stack[1].m_num;
lean_object* v_a_947_ = stack[2].m_obj;
lean_object* v_res_956_;
v_res_956_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_945_, v_anchor_946_, v_a_947_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_957_, lean_object* v_anchor_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
uint64_t v_anchor_boxed_961_; lean_object* v_res_962_; 
v_anchor_boxed_961_ = lean_unbox_uint64(v_anchor_958_);
lean_dec_ref(v_anchor_958_);
v_res_962_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_957_, v_anchor_boxed_961_, v_a_959_);
lean_dec_ref(v_a_959_);
lean_dec(v_numDigits_957_);
return v_res_962_;
}
}
lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_963_, uint64_t v_anchor_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_963_, v_anchor_964_, v_a_965_);
return v___x_968_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkAnchorSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_numDigits_963_ = stack[0].m_obj;
uint64_t v_anchor_964_ = stack[1].m_num;
lean_object* v_a_965_ = stack[2].m_obj;
lean_object* v_a_966_ = stack[3].m_obj;
lean_object* v_res_969_;
v_res_969_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_963_, v_anchor_964_, v_a_965_, v_a_966_);
stack->m_obj
 = v_res_969_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_970_, lean_object* v_anchor_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
uint64_t v_anchor_boxed_975_; lean_object* v_res_976_; 
v_anchor_boxed_975_ = lean_unbox_uint64(v_anchor_971_);
lean_dec_ref(v_anchor_971_);
v_res_976_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_970_, v_anchor_boxed_975_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_numDigits_970_);
return v_res_976_;
}
}
lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_977_);
v___x_989_ = l_Lean_Meta_Grind_getAnchor(v___x_988_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_989_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_SplitInfo_getAnchor_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_977_ = stack[0].m_obj;
lean_object* v_a_978_ = stack[1].m_obj;
lean_object* v_a_979_ = stack[2].m_obj;
lean_object* v_a_980_ = stack[3].m_obj;
lean_object* v_a_981_ = stack[4].m_obj;
lean_object* v_a_982_ = stack[5].m_obj;
lean_object* v_a_983_ = stack[6].m_obj;
lean_object* v_a_984_ = stack[7].m_obj;
lean_object* v_a_985_ = stack[8].m_obj;
lean_object* v_a_986_ = stack[9].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_s_991_);
return v_res_1002_;
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

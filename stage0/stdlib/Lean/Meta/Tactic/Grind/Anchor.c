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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(lean_object* v_declName_31_, lean_object* v___y_32_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(lean_object* v_declName_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_39_, v___y_40_);
lean_dec(v___y_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(lean_object* v_declName_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_43_, v___y_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(lean_object* v_declName_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(v_declName_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object* v_keys_67_, lean_object* v_vals_68_, lean_object* v_i_69_, lean_object* v_k_70_){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_array_get_size(v_keys_67_);
v___x_72_ = lean_nat_dec_lt(v_i_69_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec(v_i_69_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v_k_x27_74_; size_t v___x_75_; size_t v___x_76_; uint8_t v___x_77_; 
v_k_x27_74_ = lean_array_fget_borrowed(v_keys_67_, v_i_69_);
v___x_75_ = lean_ptr_addr(v_k_70_);
v___x_76_ = lean_ptr_addr(v_k_x27_74_);
v___x_77_ = lean_usize_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_i_69_, v___x_78_);
lean_dec(v_i_69_);
v_i_69_ = v___x_79_;
goto _start;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_array_fget_borrowed(v_vals_68_, v_i_69_);
lean_dec(v_i_69_);
lean_inc(v___x_81_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_keys_83_, lean_object* v_vals_84_, lean_object* v_i_85_, lean_object* v_k_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_83_, v_vals_84_, v_i_85_, v_k_86_);
lean_dec_ref(v_k_86_);
lean_dec_ref(v_vals_84_);
lean_dec_ref(v_keys_83_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object* v_x_88_, size_t v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_es_91_; lean_object* v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v_j_95_; lean_object* v___x_96_; 
v_es_91_ = lean_ctor_get(v_x_88_, 0);
v___x_92_ = lean_box(2);
v___x_93_ = ((size_t)31ULL);
v___x_94_ = lean_usize_land(v_x_89_, v___x_93_);
v_j_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_array_get_borrowed(v___x_92_, v_es_91_, v_j_95_);
lean_dec(v_j_95_);
switch(lean_obj_tag(v___x_96_))
{
case 0:
{
lean_object* v_key_97_; lean_object* v_val_98_; size_t v___x_99_; size_t v___x_100_; uint8_t v___x_101_; 
v_key_97_ = lean_ctor_get(v___x_96_, 0);
v_val_98_ = lean_ctor_get(v___x_96_, 1);
v___x_99_ = lean_ptr_addr(v_x_90_);
v___x_100_ = lean_ptr_addr(v_key_97_);
v___x_101_ = lean_usize_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
lean_inc(v_val_98_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_val_98_);
return v___x_103_;
}
}
case 1:
{
lean_object* v_node_104_; size_t v___x_105_; size_t v___x_106_; 
v_node_104_ = lean_ctor_get(v___x_96_, 0);
v___x_105_ = ((size_t)5ULL);
v___x_106_ = lean_usize_shift_right(v_x_89_, v___x_105_);
v_x_88_ = v_node_104_;
v_x_89_ = v___x_106_;
goto _start;
}
default: 
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(0);
return v___x_108_;
}
}
}
else
{
lean_object* v_ks_109_; lean_object* v_vs_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_ks_109_ = lean_ctor_get(v_x_88_, 0);
v_vs_110_ = lean_ctor_get(v_x_88_, 1);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_109_, v_vs_110_, v___x_111_, v_x_90_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
size_t v_x_32956__boxed_116_; lean_object* v_res_117_; 
v_x_32956__boxed_116_ = lean_unbox_usize(v_x_114_);
lean_dec(v_x_114_);
v_res_117_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_113_, v_x_32956__boxed_116_, v_x_115_);
lean_dec_ref(v_x_115_);
lean_dec_ref(v_x_113_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; uint64_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; 
v___x_120_ = lean_ptr_addr(v_x_119_);
v___x_121_ = ((size_t)3ULL);
v___x_122_ = lean_usize_shift_right(v___x_120_, v___x_121_);
v___x_123_ = lean_usize_to_uint64(v___x_122_);
v___x_124_ = lean_uint64_to_usize(v___x_123_);
v___x_125_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_118_, v___x_124_, v_x_119_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_126_, v_x_127_);
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
lean_object* v_ks_133_; lean_object* v_vs_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_160_; 
v_ks_133_ = lean_ctor_get(v_x_129_, 0);
v_vs_134_ = lean_ctor_get(v_x_129_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_129_);
if (v_isSharedCheck_160_ == 0)
{
v___x_136_ = v_x_129_;
v_isShared_137_ = v_isSharedCheck_160_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_vs_134_);
lean_inc(v_ks_133_);
lean_dec(v_x_129_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_160_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_array_get_size(v_ks_133_);
v___x_139_ = lean_nat_dec_lt(v_x_130_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
lean_dec(v_x_130_);
v___x_140_ = lean_array_push(v_ks_133_, v_x_131_);
v___x_141_ = lean_array_push(v_vs_134_, v_x_132_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_141_);
lean_ctor_set(v___x_136_, 0, v___x_140_);
v___x_143_ = v___x_136_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
else
{
lean_object* v_k_x27_145_; size_t v___x_146_; size_t v___x_147_; uint8_t v___x_148_; 
v_k_x27_145_ = lean_array_fget_borrowed(v_ks_133_, v_x_130_);
v___x_146_ = lean_ptr_addr(v_x_131_);
v___x_147_ = lean_ptr_addr(v_k_x27_145_);
v___x_148_ = lean_usize_dec_eq(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_150_; 
if (v_isShared_137_ == 0)
{
v___x_150_ = v___x_136_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_ks_133_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_vs_134_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_x_130_, v___x_151_);
lean_dec(v_x_130_);
v_x_129_ = v___x_150_;
v_x_130_ = v___x_152_;
goto _start;
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_array_fset(v_ks_133_, v_x_130_, v_x_131_);
v___x_156_ = lean_array_fset(v_vs_134_, v_x_130_, v_x_132_);
lean_dec(v_x_130_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_156_);
lean_ctor_set(v___x_136_, 0, v___x_155_);
v___x_158_ = v___x_136_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(lean_object* v_n_161_, lean_object* v_k_162_, lean_object* v_v_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(v_n_161_, v___x_164_, v_k_162_, v_v_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(lean_object* v_x_167_, size_t v_x_168_, size_t v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v_es_172_; size_t v___x_173_; size_t v___x_174_; lean_object* v_j_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_es_172_ = lean_ctor_get(v_x_167_, 0);
v___x_173_ = ((size_t)31ULL);
v___x_174_ = lean_usize_land(v_x_168_, v___x_173_);
v_j_175_ = lean_usize_to_nat(v___x_174_);
v___x_176_ = lean_array_get_size(v_es_172_);
v___x_177_ = lean_nat_dec_lt(v_j_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_dec(v_j_175_);
lean_dec(v_x_171_);
lean_dec_ref(v_x_170_);
return v_x_167_;
}
else
{
lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_218_; 
lean_inc_ref(v_es_172_);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_x_167_, 0);
lean_dec(v_unused_219_);
v___x_179_ = v_x_167_;
v_isShared_180_ = v_isSharedCheck_218_;
goto v_resetjp_178_;
}
else
{
lean_dec(v_x_167_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_218_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_v_181_; lean_object* v___x_182_; lean_object* v_xs_x27_183_; lean_object* v___y_185_; 
v_v_181_ = lean_array_fget(v_es_172_, v_j_175_);
v___x_182_ = lean_box(0);
v_xs_x27_183_ = lean_array_fset(v_es_172_, v_j_175_, v___x_182_);
switch(lean_obj_tag(v_v_181_))
{
case 0:
{
lean_object* v_key_190_; lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_203_; 
v_key_190_ = lean_ctor_get(v_v_181_, 0);
v_val_191_ = lean_ctor_get(v_v_181_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_v_181_);
if (v_isSharedCheck_203_ == 0)
{
v___x_193_ = v_v_181_;
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_inc(v_key_190_);
lean_dec(v_v_181_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
size_t v___x_195_; size_t v___x_196_; uint8_t v___x_197_; 
v___x_195_ = lean_ptr_addr(v_x_170_);
v___x_196_ = lean_ptr_addr(v_key_190_);
v___x_197_ = lean_usize_dec_eq(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_del_object(v___x_193_);
v___x_198_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_190_, v_val_191_, v_x_170_, v_x_171_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
v___y_185_ = v___x_199_;
goto v___jp_184_;
}
else
{
lean_object* v___x_201_; 
lean_dec(v_val_191_);
lean_dec(v_key_190_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v_x_171_);
lean_ctor_set(v___x_193_, 0, v_x_170_);
v___x_201_ = v___x_193_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_x_170_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_x_171_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
v___y_185_ = v___x_201_;
goto v___jp_184_;
}
}
}
}
case 1:
{
lean_object* v_node_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_216_; 
v_node_204_ = lean_ctor_get(v_v_181_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v_v_181_);
if (v_isSharedCheck_216_ == 0)
{
v___x_206_ = v_v_181_;
v_isShared_207_ = v_isSharedCheck_216_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_node_204_);
lean_dec(v_v_181_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_216_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_208_ = ((size_t)5ULL);
v___x_209_ = lean_usize_shift_right(v_x_168_, v___x_208_);
v___x_210_ = ((size_t)1ULL);
v___x_211_ = lean_usize_add(v_x_169_, v___x_210_);
v___x_212_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_node_204_, v___x_209_, v___x_211_, v_x_170_, v_x_171_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_212_);
v___x_214_ = v___x_206_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
v___y_185_ = v___x_214_;
goto v___jp_184_;
}
}
}
default: 
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_x_170_);
lean_ctor_set(v___x_217_, 1, v_x_171_);
v___y_185_ = v___x_217_;
goto v___jp_184_;
}
}
v___jp_184_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_array_fset(v_xs_x27_183_, v_j_175_, v___y_185_);
lean_dec(v_j_175_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_186_);
v___x_188_ = v___x_179_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
else
{
lean_object* v_ks_220_; lean_object* v_vs_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_239_; 
v_ks_220_ = lean_ctor_get(v_x_167_, 0);
v_vs_221_ = lean_ctor_get(v_x_167_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_239_ == 0)
{
v___x_223_ = v_x_167_;
v_isShared_224_ = v_isSharedCheck_239_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_vs_221_);
lean_inc(v_ks_220_);
lean_dec(v_x_167_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_239_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_ks_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_vs_221_);
v___x_226_ = v_reuseFailAlloc_238_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v_newNode_227_; size_t v___x_228_; uint8_t v___x_229_; 
v_newNode_227_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(v___x_226_, v_x_170_, v_x_171_);
v___x_228_ = ((size_t)7ULL);
v___x_229_ = lean_usize_dec_le(v___x_228_, v_x_169_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_227_);
v___x_231_ = lean_unsigned_to_nat(4u);
v___x_232_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
if (v___x_232_ == 0)
{
lean_object* v_ks_233_; lean_object* v_vs_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_ks_233_ = lean_ctor_get(v_newNode_227_, 0);
lean_inc_ref(v_ks_233_);
v_vs_234_ = lean_ctor_get(v_newNode_227_, 1);
lean_inc_ref(v_vs_234_);
lean_dec_ref(v_newNode_227_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0);
v___x_237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_x_169_, v_ks_233_, v_vs_234_, v___x_235_, v___x_236_);
lean_dec_ref(v_vs_234_);
lean_dec_ref(v_ks_233_);
return v___x_237_;
}
else
{
return v_newNode_227_;
}
}
else
{
return v_newNode_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(size_t v_depth_240_, lean_object* v_keys_241_, lean_object* v_vals_242_, lean_object* v_i_243_, lean_object* v_entries_244_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_array_get_size(v_keys_241_);
v___x_246_ = lean_nat_dec_lt(v_i_243_, v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v_i_243_);
return v_entries_244_;
}
else
{
lean_object* v_k_247_; lean_object* v_v_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; uint64_t v___x_252_; size_t v_h_253_; size_t v___x_254_; lean_object* v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v_h_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_k_247_ = lean_array_fget_borrowed(v_keys_241_, v_i_243_);
v_v_248_ = lean_array_fget_borrowed(v_vals_242_, v_i_243_);
v___x_249_ = lean_ptr_addr(v_k_247_);
v___x_250_ = ((size_t)3ULL);
v___x_251_ = lean_usize_shift_right(v___x_249_, v___x_250_);
v___x_252_ = lean_usize_to_uint64(v___x_251_);
v_h_253_ = lean_uint64_to_usize(v___x_252_);
v___x_254_ = ((size_t)5ULL);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_sub(v_depth_240_, v___x_256_);
v___x_258_ = lean_usize_mul(v___x_254_, v___x_257_);
v_h_259_ = lean_usize_shift_right(v_h_253_, v___x_258_);
v___x_260_ = lean_nat_add(v_i_243_, v___x_255_);
lean_dec(v_i_243_);
lean_inc(v_v_248_);
lean_inc(v_k_247_);
v___x_261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_entries_244_, v_h_259_, v_depth_240_, v_k_247_, v_v_248_);
v_i_243_ = v___x_260_;
v_entries_244_ = v___x_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_263_, lean_object* v_keys_264_, lean_object* v_vals_265_, lean_object* v_i_266_, lean_object* v_entries_267_){
_start:
{
size_t v_depth_boxed_268_; lean_object* v_res_269_; 
v_depth_boxed_268_ = lean_unbox_usize(v_depth_263_);
lean_dec(v_depth_263_);
v_res_269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_depth_boxed_268_, v_keys_264_, v_vals_265_, v_i_266_, v_entries_267_);
lean_dec_ref(v_vals_265_);
lean_dec_ref(v_keys_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___boxed(lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
size_t v_x_33108__boxed_275_; size_t v_x_33109__boxed_276_; lean_object* v_res_277_; 
v_x_33108__boxed_275_ = lean_unbox_usize(v_x_271_);
lean_dec(v_x_271_);
v_x_33109__boxed_276_ = lean_unbox_usize(v_x_272_);
lean_dec(v_x_272_);
v_res_277_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_270_, v_x_33108__boxed_275_, v_x_33109__boxed_276_, v_x_273_, v_x_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; uint64_t v___x_284_; size_t v___x_285_; size_t v___x_286_; lean_object* v___x_287_; 
v___x_281_ = lean_ptr_addr(v_x_279_);
v___x_282_ = ((size_t)3ULL);
v___x_283_ = lean_usize_shift_right(v___x_281_, v___x_282_);
v___x_284_ = lean_usize_to_uint64(v___x_283_);
v___x_285_ = lean_uint64_to_usize(v___x_284_);
v___x_286_ = ((size_t)1ULL);
v___x_287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_278_, v___x_285_, v___x_286_, v_x_279_, v_x_280_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAnchor___closed__0(void){
_start:
{
lean_object* v___x_288_; lean_object* v_dummy_289_; 
v___x_288_ = lean_box(0);
v_dummy_289_ = l_Lean_Expr_sort___override(v___x_288_);
return v_dummy_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_pinfos_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; 
if (lean_obj_tag(v_x_292_) == 5)
{
lean_object* v_fn_337_; lean_object* v_arg_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_fn_337_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_fn_337_);
v_arg_338_ = lean_ctor_get(v_x_292_, 1);
lean_inc_ref(v_arg_338_);
lean_dec_ref_known(v_x_292_, 2);
v___x_339_ = lean_array_set(v_x_293_, v_x_294_, v_arg_338_);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_sub(v_x_294_, v___x_340_);
lean_dec(v_x_294_);
v_x_292_ = v_fn_337_;
v_x_293_ = v___x_339_;
v_x_294_ = v___x_341_;
goto _start;
}
else
{
uint8_t v___x_343_; 
lean_dec(v_x_294_);
v___x_343_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_292_);
if (v___x_343_ == 0)
{
goto v___jp_322_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_array_get_size(v_x_293_);
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = lean_nat_dec_eq(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
goto v___jp_322_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v_x_292_);
v___x_347_ = l_Lean_instInhabitedExpr;
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_array_get(v___x_347_, v_x_293_, v___x_348_);
lean_dec_ref(v_x_293_);
v___x_350_ = l_Lean_Meta_Grind_getAnchor(v___x_349_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_350_;
}
}
}
v___jp_305_:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Grind_getAnchor(v_x_292_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint64_t v___x_320_; lean_object* v___x_321_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v___x_318_ = lean_array_get_size(v_x_293_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_unbox_uint64(v_a_317_);
lean_dec(v_a_317_);
v___x_321_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v___x_318_, v_x_293_, v_pinfos_306_, v___x_319_, v___x_320_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec_ref(v_pinfos_306_);
lean_dec_ref(v_x_293_);
return v___x_321_;
}
else
{
lean_dec_ref(v_pinfos_306_);
lean_dec_ref(v_x_293_);
return v___x_316_;
}
}
v___jp_322_:
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_Expr_hasLooseBVars(v_x_292_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_box(0);
lean_inc_ref(v_x_292_);
v___x_325_ = l_Lean_Meta_getFunInfo(v_x_292_, v___x_324_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v_paramInfo_327_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v_paramInfo_327_ = lean_ctor_get(v_a_326_, 0);
lean_inc_ref(v_paramInfo_327_);
lean_dec(v_a_326_);
v_pinfos_306_ = v_paramInfo_327_;
v___y_307_ = v___y_295_;
v___y_308_ = v___y_296_;
v___y_309_ = v___y_297_;
v___y_310_ = v___y_298_;
v___y_311_ = v___y_299_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
goto v___jp_305_;
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_x_293_);
lean_dec_ref(v_x_292_);
v_a_328_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_325_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v___x_336_; 
v___x_336_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0));
v_pinfos_306_ = v___x_336_;
v___y_307_ = v___y_295_;
v___y_308_ = v___y_296_;
v___y_309_ = v___y_297_;
v___y_310_ = v___y_298_;
v___y_311_ = v___y_299_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
goto v___jp_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
uint64_t v_a_363_; lean_object* v___y_364_; lean_object* v_n_391_; lean_object* v_d_392_; lean_object* v_b_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___x_412_; lean_object* v_anchors_413_; lean_object* v___x_414_; 
v___x_412_ = lean_st_ref_get(v_a_354_);
v_anchors_413_ = lean_ctor_get(v___x_412_, 10);
lean_inc_ref(v_anchors_413_);
lean_dec(v___x_412_);
v___x_414_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_413_, v_e_351_);
lean_dec_ref(v_anchors_413_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v_e_351_);
v_val_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 0);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_val_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_dec(v___x_414_);
switch(lean_obj_tag(v_e_351_))
{
case 0:
{
lean_object* v_deBruijnIndex_423_; uint64_t v___x_424_; 
v_deBruijnIndex_423_ = lean_ctor_get(v_e_351_, 0);
v___x_424_ = lean_uint64_of_nat(v_deBruijnIndex_423_);
v_a_363_ = v___x_424_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
case 1:
{
lean_object* v_fvarId_425_; lean_object* v___x_426_; 
v_fvarId_425_ = lean_ctor_get(v_e_351_, 0);
lean_inc(v_fvarId_425_);
v___x_426_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_425_, v_a_357_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; uint64_t v___x_429_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = l_Lean_LocalDecl_userName(v_a_427_);
lean_dec(v_a_427_);
v___x_429_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_428_);
v_a_363_ = v___x_429_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref_known(v_e_351_, 1);
v_a_430_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_426_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_426_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
case 4:
{
lean_object* v_declName_438_; lean_object* v___x_439_; 
v_declName_438_ = lean_ctor_get(v_e_351_, 0);
lean_inc(v_declName_438_);
v___x_439_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_438_, v_a_360_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; uint8_t v___x_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = lean_unbox(v_a_440_);
lean_dec(v_a_440_);
if (v___x_441_ == 0)
{
uint64_t v___x_442_; 
lean_inc(v_declName_438_);
v___x_442_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_438_);
v_a_363_ = v___x_442_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
else
{
uint64_t v___x_443_; 
v___x_443_ = 0ULL;
v_a_363_ = v___x_443_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec_ref_known(v_e_351_, 2);
v_a_444_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_439_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_439_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
case 5:
{
lean_object* v_dummy_452_; lean_object* v_nargs_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_dummy_452_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_453_ = l_Lean_Expr_getAppNumArgs(v_e_351_);
lean_inc(v_nargs_453_);
v___x_454_ = lean_mk_array(v_nargs_453_, v_dummy_452_);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_sub(v_nargs_453_, v___x_455_);
lean_dec(v_nargs_453_);
lean_inc_ref(v_e_351_);
v___x_457_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_351_, v___x_454_, v___x_456_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; uint64_t v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = lean_unbox_uint64(v_a_458_);
lean_dec(v_a_458_);
v_a_363_ = v___x_459_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
else
{
lean_dec_ref_known(v_e_351_, 2);
return v___x_457_;
}
}
case 6:
{
lean_object* v_binderName_460_; lean_object* v_binderType_461_; lean_object* v_body_462_; 
v_binderName_460_ = lean_ctor_get(v_e_351_, 0);
v_binderType_461_ = lean_ctor_get(v_e_351_, 1);
v_body_462_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_body_462_);
lean_inc_ref(v_binderType_461_);
lean_inc(v_binderName_460_);
v_n_391_ = v_binderName_460_;
v_d_392_ = v_binderType_461_;
v_b_393_ = v_body_462_;
v___y_394_ = v_a_352_;
v___y_395_ = v_a_353_;
v___y_396_ = v_a_354_;
v___y_397_ = v_a_355_;
v___y_398_ = v_a_356_;
v___y_399_ = v_a_357_;
v___y_400_ = v_a_358_;
v___y_401_ = v_a_359_;
v___y_402_ = v_a_360_;
goto v___jp_390_;
}
case 7:
{
lean_object* v_binderName_463_; lean_object* v_binderType_464_; lean_object* v_body_465_; 
v_binderName_463_ = lean_ctor_get(v_e_351_, 0);
v_binderType_464_ = lean_ctor_get(v_e_351_, 1);
v_body_465_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_body_465_);
lean_inc_ref(v_binderType_464_);
lean_inc(v_binderName_463_);
v_n_391_ = v_binderName_463_;
v_d_392_ = v_binderType_464_;
v_b_393_ = v_body_465_;
v___y_394_ = v_a_352_;
v___y_395_ = v_a_353_;
v___y_396_ = v_a_354_;
v___y_397_ = v_a_355_;
v___y_398_ = v_a_356_;
v___y_399_ = v_a_357_;
v___y_400_ = v_a_358_;
v___y_401_ = v_a_359_;
v___y_402_ = v_a_360_;
goto v___jp_390_;
}
case 8:
{
lean_object* v_declName_466_; lean_object* v_type_467_; lean_object* v_value_468_; lean_object* v_body_469_; lean_object* v___x_470_; 
v_declName_466_ = lean_ctor_get(v_e_351_, 0);
v_type_467_ = lean_ctor_get(v_e_351_, 1);
v_value_468_ = lean_ctor_get(v_e_351_, 2);
v_body_469_ = lean_ctor_get(v_e_351_, 3);
lean_inc_ref(v_value_468_);
v___x_470_ = l_Lean_Meta_Grind_getAnchor(v_value_468_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
lean_inc_ref(v_type_467_);
v___x_472_ = l_Lean_Meta_Grind_getAnchor(v_type_467_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
lean_inc_ref(v_body_469_);
v___x_474_ = l_Lean_Meta_Grind_getAnchor(v_body_469_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
lean_inc(v_declName_466_);
v___x_476_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_466_);
v___x_477_ = lean_unbox_uint64(v_a_473_);
lean_dec(v_a_473_);
v___x_478_ = lean_unbox_uint64(v_a_475_);
lean_dec(v_a_475_);
v___x_479_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_477_, v___x_478_);
v___x_480_ = lean_unbox_uint64(v_a_471_);
lean_dec(v_a_471_);
v___x_481_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_480_, v___x_479_);
v___x_482_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_476_, v___x_481_);
v_a_363_ = v___x_482_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
else
{
lean_dec(v_a_473_);
lean_dec(v_a_471_);
lean_dec_ref_known(v_e_351_, 4);
return v___x_474_;
}
}
else
{
lean_dec(v_a_471_);
lean_dec_ref_known(v_e_351_, 4);
return v___x_472_;
}
}
else
{
lean_dec_ref_known(v_e_351_, 4);
return v___x_470_;
}
}
case 9:
{
lean_object* v_a_483_; uint64_t v___x_484_; 
v_a_483_ = lean_ctor_get(v_e_351_, 0);
v___x_484_ = l_Lean_Literal_hash(v_a_483_);
v_a_363_ = v___x_484_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
case 10:
{
lean_object* v_expr_485_; lean_object* v___x_486_; 
v_expr_485_ = lean_ctor_get(v_e_351_, 1);
lean_inc_ref(v_expr_485_);
v___x_486_ = l_Lean_Meta_Grind_getAnchor(v_expr_485_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; uint64_t v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v___x_488_ = lean_unbox_uint64(v_a_487_);
lean_dec(v_a_487_);
v_a_363_ = v___x_488_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
else
{
lean_dec_ref_known(v_e_351_, 2);
return v___x_486_;
}
}
case 11:
{
lean_object* v_idx_489_; lean_object* v_struct_490_; lean_object* v___x_491_; 
v_idx_489_ = lean_ctor_get(v_e_351_, 1);
v_struct_490_ = lean_ctor_get(v_e_351_, 2);
lean_inc_ref(v_struct_490_);
v___x_491_ = l_Lean_Meta_Grind_getAnchor(v_struct_490_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = lean_uint64_of_nat(v_idx_489_);
v___x_494_ = lean_unbox_uint64(v_a_492_);
lean_dec(v_a_492_);
v___x_495_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_493_, v___x_494_);
v_a_363_ = v___x_495_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
else
{
lean_dec_ref_known(v_e_351_, 3);
return v___x_491_;
}
}
default: 
{
uint64_t v___x_496_; 
v___x_496_ = 0ULL;
v_a_363_ = v___x_496_;
v___y_364_ = v_a_354_;
goto v___jp_362_;
}
}
}
v___jp_362_:
{
lean_object* v___x_365_; lean_object* v_congrThms_366_; lean_object* v_simp_367_; lean_object* v_symSimp_368_; lean_object* v_symDSimp_369_; lean_object* v_lastTag_370_; lean_object* v_counters_371_; lean_object* v_splitDiags_372_; lean_object* v_ematchDiags_373_; lean_object* v_lawfulEqCmpMap_374_; lean_object* v_reflCmpMap_375_; lean_object* v_anchors_376_; lean_object* v_instanceMap_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_389_; 
v___x_365_ = lean_st_ref_take(v___y_364_);
v_congrThms_366_ = lean_ctor_get(v___x_365_, 0);
v_simp_367_ = lean_ctor_get(v___x_365_, 1);
v_symSimp_368_ = lean_ctor_get(v___x_365_, 2);
v_symDSimp_369_ = lean_ctor_get(v___x_365_, 3);
v_lastTag_370_ = lean_ctor_get(v___x_365_, 4);
v_counters_371_ = lean_ctor_get(v___x_365_, 5);
v_splitDiags_372_ = lean_ctor_get(v___x_365_, 6);
v_ematchDiags_373_ = lean_ctor_get(v___x_365_, 7);
v_lawfulEqCmpMap_374_ = lean_ctor_get(v___x_365_, 8);
v_reflCmpMap_375_ = lean_ctor_get(v___x_365_, 9);
v_anchors_376_ = lean_ctor_get(v___x_365_, 10);
v_instanceMap_377_ = lean_ctor_get(v___x_365_, 11);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_389_ == 0)
{
v___x_379_ = v___x_365_;
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_instanceMap_377_);
lean_inc(v_anchors_376_);
lean_inc(v_reflCmpMap_375_);
lean_inc(v_lawfulEqCmpMap_374_);
lean_inc(v_ematchDiags_373_);
lean_inc(v_splitDiags_372_);
lean_inc(v_counters_371_);
lean_inc(v_lastTag_370_);
lean_inc(v_symDSimp_369_);
lean_inc(v_symSimp_368_);
lean_inc(v_simp_367_);
lean_inc(v_congrThms_366_);
lean_dec(v___x_365_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_381_ = lean_box_uint64(v_a_363_);
v___x_382_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_anchors_376_, v_e_351_, v___x_381_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 10, v___x_382_);
v___x_384_ = v___x_379_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_congrThms_366_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_simp_367_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_symSimp_368_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_symDSimp_369_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_lastTag_370_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_counters_371_);
lean_ctor_set(v_reuseFailAlloc_388_, 6, v_splitDiags_372_);
lean_ctor_set(v_reuseFailAlloc_388_, 7, v_ematchDiags_373_);
lean_ctor_set(v_reuseFailAlloc_388_, 8, v_lawfulEqCmpMap_374_);
lean_ctor_set(v_reuseFailAlloc_388_, 9, v_reflCmpMap_375_);
lean_ctor_set(v_reuseFailAlloc_388_, 10, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_388_, 11, v_instanceMap_377_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_st_ref_put(v___y_364_, v___x_384_);
v___x_386_ = lean_box_uint64(v_a_363_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
v___jp_390_:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Meta_Grind_getAnchor(v_d_392_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = l_Lean_Meta_Grind_getAnchor(v_b_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_391_);
v___x_408_ = lean_unbox_uint64(v_a_404_);
lean_dec(v_a_404_);
v___x_409_ = lean_unbox_uint64(v_a_406_);
lean_dec(v_a_406_);
v___x_410_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_408_, v___x_409_);
v___x_411_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_407_, v___x_410_);
v_a_363_ = v___x_411_;
v___y_364_ = v___y_396_;
goto v___jp_362_;
}
else
{
lean_dec(v_a_404_);
lean_dec(v_n_391_);
lean_dec_ref(v_e_351_);
return v___x_405_;
}
}
else
{
lean_dec_ref(v_b_393_);
lean_dec(v_n_391_);
lean_dec_ref(v_e_351_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object* v_upperBound_497_, lean_object* v_args_498_, lean_object* v_pinfos_499_, lean_object* v_a_500_, uint64_t v_b_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint64_t v_a_513_; uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v_a_500_, v_upperBound_497_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_a_500_);
v___x_518_ = lean_box_uint64(v_b_501_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_array_fget_borrowed(v_args_498_, v_a_500_);
v___x_521_ = lean_array_get_size(v_pinfos_499_);
v___x_522_ = lean_nat_dec_lt(v_a_500_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_inc(v___x_520_);
v___x_523_ = l_Lean_Meta_Grind_getAnchor(v___x_520_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; uint64_t v___x_525_; uint64_t v___x_526_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = lean_unbox_uint64(v_a_524_);
lean_dec(v_a_524_);
v___x_526_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_501_, v___x_525_);
v_a_513_ = v___x_526_;
goto v___jp_512_;
}
else
{
lean_dec(v_a_500_);
return v___x_523_;
}
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_fget_borrowed(v_pinfos_499_, v_a_500_);
v___x_528_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_inc(v___x_520_);
v___x_529_ = l_Lean_Meta_Grind_getAnchor(v___x_520_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; uint64_t v___x_531_; uint64_t v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = lean_unbox_uint64(v_a_530_);
lean_dec(v_a_530_);
v___x_532_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_501_, v___x_531_);
v_a_513_ = v___x_532_;
goto v___jp_512_;
}
else
{
lean_dec(v_a_500_);
return v___x_529_;
}
}
else
{
v_a_513_ = v_b_501_;
goto v___jp_512_;
}
}
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_a_500_, v___x_514_);
lean_dec(v_a_500_);
v_a_500_ = v___x_515_;
v_b_501_ = v_a_513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg___boxed(lean_object* v_upperBound_533_, lean_object* v_args_534_, lean_object* v_pinfos_535_, lean_object* v_a_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint64_t v_b_boxed_548_; lean_object* v_res_549_; 
v_b_boxed_548_ = lean_unbox_uint64(v_b_537_);
lean_dec_ref(v_b_537_);
v_res_549_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_upperBound_533_, v_args_534_, v_pinfos_535_, v_a_536_, v_b_boxed_548_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v_pinfos_535_);
lean_dec_ref(v_args_534_);
lean_dec(v_upperBound_533_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_550_, v_x_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_Grind_getAnchor(v_e_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_00_u03b2_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_x_577_, v_x_578_, v_x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_upperBound_581_, lean_object* v_args_582_, lean_object* v_pinfos_583_, lean_object* v_inst_584_, lean_object* v_R_585_, lean_object* v_a_586_, uint64_t v_b_587_, lean_object* v_c_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_upperBound_581_, v_args_582_, v_pinfos_583_, v_a_586_, v_b_587_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_600_ = _args[0];
lean_object* v_args_601_ = _args[1];
lean_object* v_pinfos_602_ = _args[2];
lean_object* v_inst_603_ = _args[3];
lean_object* v_R_604_ = _args[4];
lean_object* v_a_605_ = _args[5];
lean_object* v_b_606_ = _args[6];
lean_object* v_c_607_ = _args[7];
lean_object* v___y_608_ = _args[8];
lean_object* v___y_609_ = _args[9];
lean_object* v___y_610_ = _args[10];
lean_object* v___y_611_ = _args[11];
lean_object* v___y_612_ = _args[12];
lean_object* v___y_613_ = _args[13];
lean_object* v___y_614_ = _args[14];
lean_object* v___y_615_ = _args[15];
lean_object* v___y_616_ = _args[16];
lean_object* v___y_617_ = _args[17];
_start:
{
uint64_t v_b_boxed_618_; lean_object* v_res_619_; 
v_b_boxed_618_ = lean_unbox_uint64(v_b_606_);
lean_dec_ref(v_b_606_);
v_res_619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(v_upperBound_600_, v_args_601_, v_pinfos_602_, v_inst_603_, v_R_604_, v_a_605_, v_b_boxed_618_, v_c_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v_pinfos_602_);
lean_dec_ref(v_args_601_);
lean_dec(v_upperBound_600_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_624_, v_x_625_, v_x_626_);
lean_dec_ref(v_x_626_);
lean_dec_ref(v_x_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(lean_object* v_00_u03b2_628_, lean_object* v_x_629_, size_t v_x_630_, size_t v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_629_, v_x_630_, v_x_631_, v_x_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___boxed(lean_object* v_00_u03b2_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_33806__boxed_641_; size_t v_x_33807__boxed_642_; lean_object* v_res_643_; 
v_x_33806__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_x_33807__boxed_642_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_res_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(v_00_u03b2_635_, v_x_636_, v_x_33806__boxed_641_, v_x_33807__boxed_642_, v_x_639_, v_x_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_644_, lean_object* v_x_645_, size_t v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_645_, v_x_646_, v_x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
size_t v_x_33823__boxed_653_; lean_object* v_res_654_; 
v_x_33823__boxed_653_ = lean_unbox_usize(v_x_651_);
lean_dec(v_x_651_);
v_res_654_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_649_, v_x_650_, v_x_33823__boxed_653_, v_x_652_);
lean_dec_ref(v_x_652_);
lean_dec_ref(v_x_650_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_655_, lean_object* v_n_656_, lean_object* v_k_657_, lean_object* v_v_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(v_n_656_, v_k_657_, v_v_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_660_, size_t v_depth_661_, lean_object* v_keys_662_, lean_object* v_vals_663_, lean_object* v_heq_664_, lean_object* v_i_665_, lean_object* v_entries_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_depth_661_, v_keys_662_, v_vals_663_, v_i_665_, v_entries_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_668_, lean_object* v_depth_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_heq_672_, lean_object* v_i_673_, lean_object* v_entries_674_){
_start:
{
size_t v_depth_boxed_675_; lean_object* v_res_676_; 
v_depth_boxed_675_ = lean_unbox_usize(v_depth_669_);
lean_dec(v_depth_669_);
v_res_676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(v_00_u03b2_668_, v_depth_boxed_675_, v_keys_670_, v_vals_671_, v_heq_672_, v_i_673_, v_entries_674_);
lean_dec_ref(v_vals_671_);
lean_dec_ref(v_keys_670_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_677_, lean_object* v_keys_678_, lean_object* v_vals_679_, lean_object* v_heq_680_, lean_object* v_i_681_, lean_object* v_k_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_678_, v_vals_679_, v_i_681_, v_k_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_684_, lean_object* v_keys_685_, lean_object* v_vals_686_, lean_object* v_heq_687_, lean_object* v_i_688_, lean_object* v_k_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_684_, v_keys_685_, v_vals_686_, v_heq_687_, v_i_688_, v_k_689_);
lean_dec_ref(v_k_689_);
lean_dec_ref(v_vals_686_);
lean_dec_ref(v_keys_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(v_x_692_, v_x_693_, v_x_694_, v_x_695_);
return v___x_696_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_697_, uint64_t v_anchor_698_){
_start:
{
lean_object* v_numDigits_699_; uint64_t v_anchorPrefix_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v_shift_705_; uint64_t v___x_706_; uint8_t v___x_707_; 
v_numDigits_699_ = lean_ctor_get(v_anchorRef_697_, 0);
v_anchorPrefix_700_ = lean_ctor_get_uint64(v_anchorRef_697_, sizeof(void*)*1);
v___x_701_ = 64ULL;
v___x_702_ = lean_uint64_of_nat(v_numDigits_699_);
v___x_703_ = 2ULL;
v___x_704_ = lean_uint64_shift_left(v___x_702_, v___x_703_);
v_shift_705_ = lean_uint64_sub(v___x_701_, v___x_704_);
v___x_706_ = lean_uint64_shift_right(v_anchor_698_, v_shift_705_);
v___x_707_ = lean_uint64_dec_eq(v_anchorPrefix_700_, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_708_, lean_object* v_anchor_709_){
_start:
{
uint64_t v_anchor_boxed_710_; uint8_t v_res_711_; lean_object* v_r_712_; 
v_anchor_boxed_710_ = lean_unbox_uint64(v_anchor_709_);
lean_dec_ref(v_anchor_709_);
v_res_711_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_708_, v_anchor_boxed_710_);
lean_dec_ref(v_anchorRef_708_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10(void){
_start:
{
lean_object* v___x_732_; lean_object* v___f_733_; 
v___x_732_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_733_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_733_, 0, v___x_732_);
return v___f_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_735_, lean_object* v_shift_736_, lean_object* v___f_737_, lean_object* v___f_738_, lean_object* v_numDigits_739_, lean_object* v_es_740_, lean_object* v___x_741_, lean_object* v_a_742_, lean_object* v_x_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_735_, v_shift_736_, v___f_737_, v___f_738_, v_numDigits_739_, v_es_740_, v___x_741_, v_a_742_, v_x_743_, v___y_744_);
lean_dec(v_numDigits_739_);
lean_dec(v_shift_736_);
return v_res_745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_box(0);
v___x_747_ = lean_unsigned_to_nat(16u);
v___x_748_ = lean_mk_array(v___x_747_, v___x_746_);
return v___x_748_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_found_751_; 
v___x_749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12);
v___x_750_ = lean_unsigned_to_nat(0u);
v_found_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_751_, 0, v___x_750_);
lean_ctor_set(v_found_751_, 1, v___x_749_);
return v_found_751_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_found_752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_found_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_755_, lean_object* v_es_756_, lean_object* v_numDigits_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9));
v___x_759_ = lean_unsigned_to_nat(4u);
v___x_760_ = lean_nat_mul(v___x_759_, v_numDigits_757_);
v___x_761_ = lean_unsigned_to_nat(64u);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v___x_760_);
lean_dec_ref(v_es_756_);
lean_dec_ref(v_inst_755_);
return v_numDigits_757_;
}
else
{
lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v_shift_765_; lean_object* v___x_766_; lean_object* v___f_767_; lean_object* v___x_768_; size_t v_sz_769_; size_t v___x_770_; lean_object* v___x_771_; lean_object* v_fst_772_; 
v___f_763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10);
v___f_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11));
v_shift_765_ = lean_nat_sub(v___x_761_, v___x_760_);
lean_dec(v___x_760_);
v___x_766_ = lean_box(0);
lean_inc_ref(v_es_756_);
lean_inc(v_numDigits_757_);
v___f_767_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_767_, 0, v_inst_755_);
lean_closure_set(v___f_767_, 1, v_shift_765_);
lean_closure_set(v___f_767_, 2, v___f_763_);
lean_closure_set(v___f_767_, 3, v___f_764_);
lean_closure_set(v___f_767_, 4, v_numDigits_757_);
lean_closure_set(v___f_767_, 5, v_es_756_);
lean_closure_set(v___f_767_, 6, v___x_766_);
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_769_ = lean_array_size(v_es_756_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_758_, v_es_756_, v___f_767_, v_sz_769_, v___x_770_, v___x_768_);
v_fst_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_fst_772_);
lean_dec(v___x_771_);
if (lean_obj_tag(v_fst_772_) == 0)
{
return v_numDigits_757_;
}
else
{
lean_object* v_val_773_; 
lean_dec(v_numDigits_757_);
v_val_773_ = lean_ctor_get(v_fst_772_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v_fst_772_, 1);
return v_val_773_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_774_, lean_object* v_shift_775_, lean_object* v___f_776_, lean_object* v___f_777_, lean_object* v_numDigits_778_, lean_object* v_es_779_, lean_object* v___x_780_, lean_object* v_a_781_, lean_object* v_x_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_snd_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_822_; 
v_snd_784_ = lean_ctor_get(v___y_783_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v___y_783_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___y_783_, 0);
lean_dec(v_unused_823_);
v___x_786_ = v___y_783_;
v_isShared_787_ = v_isSharedCheck_822_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snd_784_);
lean_dec(v___y_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_822_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_inc_ref(v_inst_774_);
v___x_788_ = lean_apply_1(v_inst_774_, v_a_781_);
v___x_789_ = lean_uint64_of_nat(v_shift_775_);
v___x_790_ = lean_unbox_uint64(v___x_788_);
v___x_791_ = lean_uint64_shift_right(v___x_790_, v___x_789_);
v___x_792_ = lean_box_uint64(v___x_791_);
lean_inc_ref(v___f_777_);
lean_inc_ref(v___f_776_);
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_776_, v___f_777_, v_snd_784_, v___x_792_);
if (lean_obj_tag(v___x_793_) == 1)
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___f_777_);
lean_dec_ref(v___f_776_);
v_val_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_815_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_815_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_815_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
uint64_t v___x_798_; uint64_t v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_unbox_uint64(v_val_794_);
lean_dec(v_val_794_);
v___x_799_ = lean_unbox_uint64(v___x_788_);
lean_dec_ref(v___x_788_);
v___x_800_ = lean_uint64_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
lean_dec(v___x_780_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_numDigits_778_, v___x_801_);
v___x_803_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_774_, v_es_779_, v___x_802_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_803_);
v___x_805_ = v___x_796_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_810_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_805_);
v___x_807_ = v___x_786_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_snd_784_);
v___x_807_ = v_reuseFailAlloc_809_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
else
{
lean_object* v___x_812_; 
lean_del_object(v___x_796_);
lean_dec_ref(v_es_779_);
lean_dec_ref(v_inst_774_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_780_);
v___x_812_ = v___x_786_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_snd_784_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
}
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec(v___x_793_);
lean_dec_ref(v_es_779_);
lean_dec_ref(v_inst_774_);
v___x_816_ = lean_box_uint64(v___x_791_);
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_776_, v___f_777_, v_snd_784_, v___x_816_, v___x_788_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_817_);
lean_ctor_set(v___x_786_, 0, v___x_780_);
v___x_819_ = v___x_786_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_824_, lean_object* v_inst_825_, lean_object* v_es_826_, lean_object* v_numDigits_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_825_, v_es_826_, v_numDigits_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter___redArg(lean_object* v_x_829_, lean_object* v_h__1_830_, lean_object* v_h__2_831_){
_start:
{
if (lean_obj_tag(v_x_829_) == 1)
{
lean_object* v_val_832_; lean_object* v___x_833_; 
lean_dec(v_h__2_831_);
v_val_832_ = lean_ctor_get(v_x_829_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v_x_829_, 1);
v___x_833_ = lean_apply_1(v_h__1_830_, v_val_832_);
return v___x_833_;
}
else
{
lean_object* v___x_834_; 
lean_dec(v_h__1_830_);
v___x_834_ = lean_apply_2(v_h__2_831_, v_x_829_, lean_box(0));
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter(lean_object* v_motive_835_, lean_object* v_x_836_, lean_object* v_h__1_837_, lean_object* v_h__2_838_){
_start:
{
if (lean_obj_tag(v_x_836_) == 1)
{
lean_object* v_val_839_; lean_object* v___x_840_; 
lean_dec(v_h__2_838_);
v_val_839_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v_x_836_, 1);
v___x_840_ = lean_apply_1(v_h__1_837_, v_val_839_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
lean_dec(v_h__1_837_);
v___x_841_ = lean_apply_2(v_h__2_838_, v_x_836_, lean_box(0));
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_842_, lean_object* v_h__1_843_, lean_object* v_h__2_844_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_h__1_843_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_apply_1(v_h__2_844_, v___x_845_);
return v___x_846_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_848_; 
lean_dec(v_h__2_844_);
v_val_847_ = lean_ctor_get(v_x_842_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v_x_842_, 1);
v___x_848_ = lean_apply_1(v_h__1_843_, v_val_847_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_849_, lean_object* v_motive_850_, lean_object* v_x_851_, lean_object* v_h__1_852_, lean_object* v_h__2_853_){
_start:
{
if (lean_obj_tag(v_x_851_) == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_h__1_852_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_apply_1(v_h__2_853_, v___x_854_);
return v___x_855_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_857_; 
lean_dec(v_h__2_853_);
v_val_856_ = lean_ctor_get(v_x_851_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_x_851_, 1);
v___x_857_ = lean_apply_1(v_h__1_852_, v_val_856_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_858_, lean_object* v_es_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(4u);
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_858_, v_es_859_, v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_862_, lean_object* v_inst_863_, lean_object* v_es_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_863_, v_es_864_);
return v___x_865_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_866_){
_start:
{
uint64_t v_anchor_867_; 
v_anchor_867_ = lean_ctor_get_uint64(v_e_866_, sizeof(void*)*1);
return v_anchor_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_868_){
_start:
{
uint64_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_868_);
lean_dec_ref(v_e_868_);
v_r_870_ = lean_box_uint64(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_886_, uint64_t v_anchorPrefix_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_ref_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_ref_890_ = lean_ctor_get(v_a_888_, 2);
v___x_891_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_892_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_886_, v_anchorPrefix_887_);
v___x_893_ = l_Lean_mkAtom(v___x_892_);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_mk_empty_array_with_capacity(v___x_894_);
v___x_896_ = lean_array_push(v___x_895_, v___x_893_);
v___x_897_ = lean_box(2);
v___x_898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_891_);
lean_ctor_set(v___x_898_, 2, v___x_896_);
v___x_899_ = 0;
v___x_900_ = l_Lean_SourceInfo_fromRef(v_ref_890_, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_902_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_900_);
v___x_903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_900_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_Syntax_node2(v___x_900_, v___x_901_, v___x_903_, v___x_898_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_906_, lean_object* v_anchorPrefix_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
uint64_t v_anchorPrefix_boxed_910_; lean_object* v_res_911_; 
v_anchorPrefix_boxed_910_ = lean_unbox_uint64(v_anchorPrefix_907_);
lean_dec_ref(v_anchorPrefix_907_);
v_res_911_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_906_, v_anchorPrefix_boxed_910_, v_a_908_);
lean_dec_ref(v_a_908_);
lean_dec(v_numDigits_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_912_, uint64_t v_anchorPrefix_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_912_, v_anchorPrefix_913_, v_a_914_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_918_, lean_object* v_anchorPrefix_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
uint64_t v_anchorPrefix_boxed_923_; lean_object* v_res_924_; 
v_anchorPrefix_boxed_923_ = lean_unbox_uint64(v_anchorPrefix_919_);
lean_dec_ref(v_anchorPrefix_919_);
v_res_924_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_918_, v_anchorPrefix_boxed_923_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_numDigits_918_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_925_, uint64_t v_anchor_926_, lean_object* v_a_927_){
_start:
{
uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v___x_932_; uint64_t v___x_933_; uint64_t v_anchorPrefix_934_; lean_object* v___x_935_; 
v___x_929_ = 64ULL;
v___x_930_ = lean_uint64_of_nat(v_numDigits_925_);
v___x_931_ = 2ULL;
v___x_932_ = lean_uint64_shift_left(v___x_930_, v___x_931_);
v___x_933_ = lean_uint64_sub(v___x_929_, v___x_932_);
v_anchorPrefix_934_ = lean_uint64_shift_right(v_anchor_926_, v___x_933_);
v___x_935_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_925_, v_anchorPrefix_934_, v_a_927_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_936_, lean_object* v_anchor_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
uint64_t v_anchor_boxed_940_; lean_object* v_res_941_; 
v_anchor_boxed_940_ = lean_unbox_uint64(v_anchor_937_);
lean_dec_ref(v_anchor_937_);
v_res_941_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_936_, v_anchor_boxed_940_, v_a_938_);
lean_dec_ref(v_a_938_);
lean_dec(v_numDigits_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_942_, uint64_t v_anchor_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_942_, v_anchor_943_, v_a_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_948_, lean_object* v_anchor_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
uint64_t v_anchor_boxed_953_; lean_object* v_res_954_; 
v_anchor_boxed_953_ = lean_unbox_uint64(v_anchor_949_);
lean_dec_ref(v_anchor_949_);
v_res_954_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_948_, v_anchor_boxed_953_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_numDigits_948_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_955_);
v___x_967_ = l_Lean_Meta_Grind_getAnchor(v___x_966_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_s_968_);
return v_res_979_;
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

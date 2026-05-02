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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Name_isImplementationDetail(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t lean_is_inaccessible_user_name(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2;
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
v___x_18_ = lean_is_inaccessible_user_name(v_n_3_);
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
v___x_39_ = lean_is_matcher(v_env_38_, v_declName_34_);
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
lean_object* v_ks_74_; lean_object* v_vs_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_99_; 
v_ks_74_ = lean_ctor_get(v_x_70_, 0);
v_vs_75_ = lean_ctor_get(v_x_70_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_99_ == 0)
{
v___x_77_ = v_x_70_;
v_isShared_78_ = v_isSharedCheck_99_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_vs_75_);
lean_inc(v_ks_74_);
lean_dec(v_x_70_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_99_;
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
lean_object* v_k_x27_86_; uint8_t v___x_87_; 
v_k_x27_86_ = lean_array_fget_borrowed(v_ks_74_, v_x_71_);
v___x_87_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_72_, v_k_x27_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; 
if (v_isShared_78_ == 0)
{
v___x_89_ = v___x_77_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_ks_74_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_vs_75_);
v___x_89_ = v_reuseFailAlloc_93_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_x_71_, v___x_90_);
lean_dec(v_x_71_);
v_x_70_ = v___x_89_;
v_x_71_ = v___x_91_;
goto _start;
}
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_94_ = lean_array_fset(v_ks_74_, v_x_71_, v_x_72_);
v___x_95_ = lean_array_fset(v_vs_75_, v_x_71_, v_x_73_);
lean_dec(v_x_71_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_95_);
lean_ctor_set(v___x_77_, 0, v___x_94_);
v___x_97_ = v___x_77_;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; 
v___x_105_ = ((size_t)5ULL);
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_shift_left(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; 
v___x_108_ = ((size_t)1ULL);
v___x_109_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0);
v___x_110_ = lean_usize_sub(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(lean_object* v_x_112_, size_t v_x_113_, size_t v_x_114_, lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v_es_117_; size_t v___x_118_; size_t v___x_119_; size_t v___x_120_; size_t v___x_121_; lean_object* v_j_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_es_117_ = lean_ctor_get(v_x_112_, 0);
v___x_118_ = ((size_t)5ULL);
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1);
v___x_121_ = lean_usize_land(v_x_113_, v___x_120_);
v_j_122_ = lean_usize_to_nat(v___x_121_);
v___x_123_ = lean_array_get_size(v_es_117_);
v___x_124_ = lean_nat_dec_lt(v_j_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_dec(v_j_122_);
lean_dec(v_x_116_);
lean_dec_ref(v_x_115_);
return v_x_112_;
}
else
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_161_; 
lean_inc_ref(v_es_117_);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v_x_112_, 0);
lean_dec(v_unused_162_);
v___x_126_ = v_x_112_;
v_isShared_127_ = v_isSharedCheck_161_;
goto v_resetjp_125_;
}
else
{
lean_dec(v_x_112_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_161_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_v_128_; lean_object* v___x_129_; lean_object* v_xs_x27_130_; lean_object* v___y_132_; 
v_v_128_ = lean_array_fget(v_es_117_, v_j_122_);
v___x_129_ = lean_box(0);
v_xs_x27_130_ = lean_array_fset(v_es_117_, v_j_122_, v___x_129_);
switch(lean_obj_tag(v_v_128_))
{
case 0:
{
lean_object* v_key_137_; lean_object* v_val_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_148_; 
v_key_137_ = lean_ctor_get(v_v_128_, 0);
v_val_138_ = lean_ctor_get(v_v_128_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_v_128_);
if (v_isSharedCheck_148_ == 0)
{
v___x_140_ = v_v_128_;
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_val_138_);
lean_inc(v_key_137_);
lean_dec(v_v_128_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
uint8_t v___x_142_; 
v___x_142_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_115_, v_key_137_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_del_object(v___x_140_);
v___x_143_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_137_, v_val_138_, v_x_115_, v_x_116_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___y_132_ = v___x_144_;
goto v___jp_131_;
}
else
{
lean_object* v___x_146_; 
lean_dec(v_val_138_);
lean_dec(v_key_137_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v_x_116_);
lean_ctor_set(v___x_140_, 0, v_x_115_);
v___x_146_ = v___x_140_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_x_115_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_x_116_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
v___y_132_ = v___x_146_;
goto v___jp_131_;
}
}
}
}
case 1:
{
lean_object* v_node_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_159_; 
v_node_149_ = lean_ctor_get(v_v_128_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_v_128_);
if (v_isSharedCheck_159_ == 0)
{
v___x_151_ = v_v_128_;
v_isShared_152_ = v_isSharedCheck_159_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_node_149_);
lean_dec(v_v_128_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_159_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
size_t v___x_153_; size_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_153_ = lean_usize_shift_right(v_x_113_, v___x_118_);
v___x_154_ = lean_usize_add(v_x_114_, v___x_119_);
v___x_155_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_node_149_, v___x_153_, v___x_154_, v_x_115_, v_x_116_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_155_);
v___x_157_ = v___x_151_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
v___y_132_ = v___x_157_;
goto v___jp_131_;
}
}
}
default: 
{
lean_object* v___x_160_; 
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v_x_115_);
lean_ctor_set(v___x_160_, 1, v_x_116_);
v___y_132_ = v___x_160_;
goto v___jp_131_;
}
}
v___jp_131_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_133_ = lean_array_fset(v_xs_x27_130_, v_j_122_, v___y_132_);
lean_dec(v_j_122_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_133_);
v___x_135_ = v___x_126_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
else
{
lean_object* v_ks_163_; lean_object* v_vs_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_184_; 
v_ks_163_ = lean_ctor_get(v_x_112_, 0);
v_vs_164_ = lean_ctor_get(v_x_112_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_184_ == 0)
{
v___x_166_ = v_x_112_;
v_isShared_167_ = v_isSharedCheck_184_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_vs_164_);
lean_inc(v_ks_163_);
lean_dec(v_x_112_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_184_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_ks_163_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_vs_164_);
v___x_169_ = v_reuseFailAlloc_183_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v_newNode_170_; uint8_t v___y_172_; size_t v___x_178_; uint8_t v___x_179_; 
v_newNode_170_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v___x_169_, v_x_115_, v_x_116_);
v___x_178_ = ((size_t)7ULL);
v___x_179_ = lean_usize_dec_le(v___x_178_, v_x_114_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_180_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_170_);
v___x_181_ = lean_unsigned_to_nat(4u);
v___x_182_ = lean_nat_dec_lt(v___x_180_, v___x_181_);
lean_dec(v___x_180_);
v___y_172_ = v___x_182_;
goto v___jp_171_;
}
else
{
v___y_172_ = v___x_179_;
goto v___jp_171_;
}
v___jp_171_:
{
if (v___y_172_ == 0)
{
lean_object* v_ks_173_; lean_object* v_vs_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_ks_173_ = lean_ctor_get(v_newNode_170_, 0);
lean_inc_ref(v_ks_173_);
v_vs_174_ = lean_ctor_get(v_newNode_170_, 1);
lean_inc_ref(v_vs_174_);
lean_dec_ref(v_newNode_170_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2);
v___x_177_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_x_114_, v_ks_173_, v_vs_174_, v___x_175_, v___x_176_);
lean_dec_ref(v_vs_174_);
lean_dec_ref(v_ks_173_);
return v___x_177_;
}
else
{
return v_newNode_170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(size_t v_depth_185_, lean_object* v_keys_186_, lean_object* v_vals_187_, lean_object* v_i_188_, lean_object* v_entries_189_){
_start:
{
lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_190_ = lean_array_get_size(v_keys_186_);
v___x_191_ = lean_nat_dec_lt(v_i_188_, v___x_190_);
if (v___x_191_ == 0)
{
lean_dec(v_i_188_);
return v_entries_189_;
}
else
{
lean_object* v_k_192_; lean_object* v_v_193_; uint64_t v___x_194_; size_t v_h_195_; size_t v___x_196_; lean_object* v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v_h_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_k_192_ = lean_array_fget_borrowed(v_keys_186_, v_i_188_);
v_v_193_ = lean_array_fget_borrowed(v_vals_187_, v_i_188_);
v___x_194_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_192_);
v_h_195_ = lean_uint64_to_usize(v___x_194_);
v___x_196_ = ((size_t)5ULL);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_sub(v_depth_185_, v___x_198_);
v___x_200_ = lean_usize_mul(v___x_196_, v___x_199_);
v_h_201_ = lean_usize_shift_right(v_h_195_, v___x_200_);
v___x_202_ = lean_nat_add(v_i_188_, v___x_197_);
lean_dec(v_i_188_);
lean_inc(v_v_193_);
lean_inc(v_k_192_);
v___x_203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_entries_189_, v_h_201_, v_depth_185_, v_k_192_, v_v_193_);
v_i_188_ = v___x_202_;
v_entries_189_ = v___x_203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_depth_205_, lean_object* v_keys_206_, lean_object* v_vals_207_, lean_object* v_i_208_, lean_object* v_entries_209_){
_start:
{
size_t v_depth_boxed_210_; lean_object* v_res_211_; 
v_depth_boxed_210_ = lean_unbox_usize(v_depth_205_);
lean_dec(v_depth_205_);
v_res_211_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_boxed_210_, v_keys_206_, v_vals_207_, v_i_208_, v_entries_209_);
lean_dec_ref(v_vals_207_);
lean_dec_ref(v_keys_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___boxed(lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
size_t v_x_32463__boxed_217_; size_t v_x_32464__boxed_218_; lean_object* v_res_219_; 
v_x_32463__boxed_217_ = lean_unbox_usize(v_x_213_);
lean_dec(v_x_213_);
v_x_32464__boxed_218_ = lean_unbox_usize(v_x_214_);
lean_dec(v_x_214_);
v_res_219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_212_, v_x_32463__boxed_217_, v_x_32464__boxed_218_, v_x_215_, v_x_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
uint64_t v___x_223_; size_t v___x_224_; size_t v___x_225_; lean_object* v___x_226_; 
v___x_223_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_221_);
v___x_224_ = lean_uint64_to_usize(v___x_223_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_220_, v___x_224_, v___x_225_, v_x_221_, v_x_222_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_i_229_, lean_object* v_k_230_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_keys_227_);
v___x_232_ = lean_nat_dec_lt(v_i_229_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_dec(v_i_229_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_k_x27_234_; uint8_t v___x_235_; 
v_k_x27_234_ = lean_array_fget_borrowed(v_keys_227_, v_i_229_);
v___x_235_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_230_, v_k_x27_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_i_229_, v___x_236_);
lean_dec(v_i_229_);
v_i_229_ = v___x_237_;
goto _start;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_array_fget_borrowed(v_vals_228_, v_i_229_);
lean_dec(v_i_229_);
lean_inc(v___x_239_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_keys_241_, lean_object* v_vals_242_, lean_object* v_i_243_, lean_object* v_k_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_241_, v_vals_242_, v_i_243_, v_k_244_);
lean_dec_ref(v_k_244_);
lean_dec_ref(v_vals_242_);
lean_dec_ref(v_keys_241_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object* v_x_246_, size_t v_x_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v_es_249_; lean_object* v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v_j_254_; lean_object* v___x_255_; 
v_es_249_ = lean_ctor_get(v_x_246_, 0);
v___x_250_ = lean_box(2);
v___x_251_ = ((size_t)5ULL);
v___x_252_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1);
v___x_253_ = lean_usize_land(v_x_247_, v___x_252_);
v_j_254_ = lean_usize_to_nat(v___x_253_);
v___x_255_ = lean_array_get_borrowed(v___x_250_, v_es_249_, v_j_254_);
lean_dec(v_j_254_);
switch(lean_obj_tag(v___x_255_))
{
case 0:
{
lean_object* v_key_256_; lean_object* v_val_257_; uint8_t v___x_258_; 
v_key_256_ = lean_ctor_get(v___x_255_, 0);
v_val_257_ = lean_ctor_get(v___x_255_, 1);
v___x_258_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_248_, v_key_256_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
lean_object* v___x_260_; 
lean_inc(v_val_257_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_val_257_);
return v___x_260_;
}
}
case 1:
{
lean_object* v_node_261_; size_t v___x_262_; 
v_node_261_ = lean_ctor_get(v___x_255_, 0);
v___x_262_ = lean_usize_shift_right(v_x_247_, v___x_251_);
v_x_246_ = v_node_261_;
v_x_247_ = v___x_262_;
goto _start;
}
default: 
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
}
else
{
lean_object* v_ks_265_; lean_object* v_vs_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_ks_265_ = lean_ctor_get(v_x_246_, 0);
v_vs_266_ = lean_ctor_get(v_x_246_, 1);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_265_, v_vs_266_, v___x_267_, v_x_248_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
size_t v_x_32663__boxed_272_; lean_object* v_res_273_; 
v_x_32663__boxed_272_ = lean_unbox_usize(v_x_270_);
lean_dec(v_x_270_);
v_res_273_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_269_, v_x_32663__boxed_272_, v_x_271_);
lean_dec_ref(v_x_271_);
lean_dec_ref(v_x_269_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint64_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_275_);
v___x_277_ = lean_uint64_to_usize(v___x_276_);
v___x_278_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_274_, v___x_277_, v_x_275_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_279_, v_x_280_);
lean_dec_ref(v_x_280_);
lean_dec_ref(v_x_279_);
return v_res_281_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAnchor___closed__0(void){
_start:
{
lean_object* v___x_282_; lean_object* v_dummy_283_; 
v___x_282_ = lean_box(0);
v_dummy_283_ = l_Lean_Expr_sort___override(v___x_282_);
return v_dummy_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_pinfos_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___y_317_; 
if (lean_obj_tag(v_x_286_) == 5)
{
lean_object* v_fn_336_; lean_object* v_arg_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_fn_336_ = lean_ctor_get(v_x_286_, 0);
lean_inc_ref(v_fn_336_);
v_arg_337_ = lean_ctor_get(v_x_286_, 1);
lean_inc_ref(v_arg_337_);
lean_dec_ref(v_x_286_);
v___x_338_ = lean_array_set(v_x_287_, v_x_288_, v_arg_337_);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_sub(v_x_288_, v___x_339_);
lean_dec(v_x_288_);
v_x_286_ = v_fn_336_;
v_x_287_ = v___x_338_;
v_x_288_ = v___x_340_;
goto _start;
}
else
{
uint8_t v___x_342_; 
lean_dec(v_x_288_);
v___x_342_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_286_);
if (v___x_342_ == 0)
{
v___y_317_ = v___x_342_;
goto v___jp_316_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_array_get_size(v_x_287_);
v___x_344_ = lean_unsigned_to_nat(2u);
v___x_345_ = lean_nat_dec_eq(v___x_343_, v___x_344_);
v___y_317_ = v___x_345_;
goto v___jp_316_;
}
}
v___jp_299_:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_getAnchor(v_x_286_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint64_t v___x_314_; lean_object* v___x_315_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_310_);
v___x_312_ = lean_array_get_size(v_x_287_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_unbox_uint64(v_a_311_);
lean_dec(v_a_311_);
v___x_315_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v___x_312_, v_x_287_, v_pinfos_300_, v___x_313_, v___x_314_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec_ref(v_pinfos_300_);
lean_dec_ref(v_x_287_);
return v___x_315_;
}
else
{
lean_dec_ref(v_pinfos_300_);
lean_dec_ref(v_x_287_);
return v___x_310_;
}
}
v___jp_316_:
{
if (v___y_317_ == 0)
{
uint8_t v___x_318_; 
v___x_318_ = l_Lean_Expr_hasLooseBVars(v_x_286_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_box(0);
lean_inc_ref(v_x_286_);
v___x_320_ = l_Lean_Meta_getFunInfo(v_x_286_, v___x_319_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v_paramInfo_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_320_);
v_paramInfo_322_ = lean_ctor_get(v_a_321_, 0);
lean_inc_ref(v_paramInfo_322_);
lean_dec(v_a_321_);
v_pinfos_300_ = v_paramInfo_322_;
v___y_301_ = v___y_289_;
v___y_302_ = v___y_290_;
v___y_303_ = v___y_291_;
v___y_304_ = v___y_292_;
v___y_305_ = v___y_293_;
v___y_306_ = v___y_294_;
v___y_307_ = v___y_295_;
v___y_308_ = v___y_296_;
v___y_309_ = v___y_297_;
goto v___jp_299_;
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec_ref(v_x_287_);
lean_dec_ref(v_x_286_);
v_a_323_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_320_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_320_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v___x_331_; 
v___x_331_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0));
v_pinfos_300_ = v___x_331_;
v___y_301_ = v___y_289_;
v___y_302_ = v___y_290_;
v___y_303_ = v___y_291_;
v___y_304_ = v___y_292_;
v___y_305_ = v___y_293_;
v___y_306_ = v___y_294_;
v___y_307_ = v___y_295_;
v___y_308_ = v___y_296_;
v___y_309_ = v___y_297_;
goto v___jp_299_;
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_x_286_);
v___x_332_ = l_Lean_instInhabitedExpr;
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_array_get(v___x_332_, v_x_287_, v___x_333_);
lean_dec_ref(v_x_287_);
v___x_335_ = l_Lean_Meta_Grind_getAnchor(v___x_334_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
uint64_t v_a_358_; lean_object* v___y_359_; lean_object* v_n_383_; lean_object* v_d_384_; lean_object* v_b_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___x_404_; lean_object* v_anchors_405_; lean_object* v___x_406_; 
v___x_404_ = lean_st_ref_get(v_a_349_);
v_anchors_405_ = lean_ctor_get(v___x_404_, 7);
lean_inc_ref(v_anchors_405_);
lean_dec(v___x_404_);
v___x_406_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_405_, v_e_346_);
lean_dec_ref(v_anchors_405_);
if (lean_obj_tag(v___x_406_) == 1)
{
lean_object* v_val_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v_e_346_);
v_val_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_val_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_val_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_dec(v___x_406_);
switch(lean_obj_tag(v_e_346_))
{
case 0:
{
lean_object* v_deBruijnIndex_415_; uint64_t v___x_416_; 
v_deBruijnIndex_415_ = lean_ctor_get(v_e_346_, 0);
v___x_416_ = lean_uint64_of_nat(v_deBruijnIndex_415_);
v_a_358_ = v___x_416_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
case 1:
{
lean_object* v_fvarId_417_; lean_object* v___x_418_; 
v_fvarId_417_ = lean_ctor_get(v_e_346_, 0);
lean_inc(v_fvarId_417_);
v___x_418_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_417_, v_a_352_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; uint64_t v___x_421_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
v___x_420_ = l_Lean_LocalDecl_userName(v_a_419_);
lean_dec(v_a_419_);
v___x_421_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_420_);
v_a_358_ = v___x_421_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_e_346_);
v_a_422_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_418_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
case 4:
{
lean_object* v_declName_430_; lean_object* v___x_431_; 
v_declName_430_ = lean_ctor_get(v_e_346_, 0);
lean_inc(v_declName_430_);
v___x_431_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_430_, v_a_355_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; uint8_t v___x_433_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref(v___x_431_);
v___x_433_ = lean_unbox(v_a_432_);
lean_dec(v_a_432_);
if (v___x_433_ == 0)
{
uint64_t v___x_434_; 
lean_inc(v_declName_430_);
v___x_434_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_430_);
v_a_358_ = v___x_434_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
uint64_t v___x_435_; 
v___x_435_ = 0ULL;
v_a_358_ = v___x_435_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v_e_346_);
v_a_436_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_431_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_431_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
case 5:
{
lean_object* v_dummy_444_; lean_object* v_nargs_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_dummy_444_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_445_ = l_Lean_Expr_getAppNumArgs(v_e_346_);
lean_inc(v_nargs_445_);
v___x_446_ = lean_mk_array(v_nargs_445_, v_dummy_444_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_sub(v_nargs_445_, v___x_447_);
lean_dec(v_nargs_445_);
lean_inc_ref(v_e_346_);
v___x_449_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_346_, v___x_446_, v___x_448_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; uint64_t v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_unbox_uint64(v_a_450_);
lean_dec(v_a_450_);
v_a_358_ = v___x_451_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec_ref(v_e_346_);
return v___x_449_;
}
}
case 6:
{
lean_object* v_binderName_452_; lean_object* v_binderType_453_; lean_object* v_body_454_; 
v_binderName_452_ = lean_ctor_get(v_e_346_, 0);
v_binderType_453_ = lean_ctor_get(v_e_346_, 1);
v_body_454_ = lean_ctor_get(v_e_346_, 2);
lean_inc_ref(v_body_454_);
lean_inc_ref(v_binderType_453_);
lean_inc(v_binderName_452_);
v_n_383_ = v_binderName_452_;
v_d_384_ = v_binderType_453_;
v_b_385_ = v_body_454_;
v___y_386_ = v_a_347_;
v___y_387_ = v_a_348_;
v___y_388_ = v_a_349_;
v___y_389_ = v_a_350_;
v___y_390_ = v_a_351_;
v___y_391_ = v_a_352_;
v___y_392_ = v_a_353_;
v___y_393_ = v_a_354_;
v___y_394_ = v_a_355_;
goto v___jp_382_;
}
case 7:
{
lean_object* v_binderName_455_; lean_object* v_binderType_456_; lean_object* v_body_457_; 
v_binderName_455_ = lean_ctor_get(v_e_346_, 0);
v_binderType_456_ = lean_ctor_get(v_e_346_, 1);
v_body_457_ = lean_ctor_get(v_e_346_, 2);
lean_inc_ref(v_body_457_);
lean_inc_ref(v_binderType_456_);
lean_inc(v_binderName_455_);
v_n_383_ = v_binderName_455_;
v_d_384_ = v_binderType_456_;
v_b_385_ = v_body_457_;
v___y_386_ = v_a_347_;
v___y_387_ = v_a_348_;
v___y_388_ = v_a_349_;
v___y_389_ = v_a_350_;
v___y_390_ = v_a_351_;
v___y_391_ = v_a_352_;
v___y_392_ = v_a_353_;
v___y_393_ = v_a_354_;
v___y_394_ = v_a_355_;
goto v___jp_382_;
}
case 8:
{
lean_object* v_declName_458_; lean_object* v_type_459_; lean_object* v_value_460_; lean_object* v_body_461_; lean_object* v___x_462_; 
v_declName_458_ = lean_ctor_get(v_e_346_, 0);
v_type_459_ = lean_ctor_get(v_e_346_, 1);
v_value_460_ = lean_ctor_get(v_e_346_, 2);
v_body_461_ = lean_ctor_get(v_e_346_, 3);
lean_inc_ref(v_value_460_);
v___x_462_ = l_Lean_Meta_Grind_getAnchor(v_value_460_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
lean_inc_ref(v_type_459_);
v___x_464_ = l_Lean_Meta_Grind_getAnchor(v_type_459_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref(v___x_464_);
lean_inc_ref(v_body_461_);
v___x_466_ = l_Lean_Meta_Grind_getAnchor(v_body_461_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref(v___x_466_);
lean_inc(v_declName_458_);
v___x_468_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_458_);
v___x_469_ = lean_unbox_uint64(v_a_465_);
lean_dec(v_a_465_);
v___x_470_ = lean_unbox_uint64(v_a_467_);
lean_dec(v_a_467_);
v___x_471_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_469_, v___x_470_);
v___x_472_ = lean_unbox_uint64(v_a_463_);
lean_dec(v_a_463_);
v___x_473_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_472_, v___x_471_);
v___x_474_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_468_, v___x_473_);
v_a_358_ = v___x_474_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec(v_a_465_);
lean_dec(v_a_463_);
lean_dec_ref(v_e_346_);
return v___x_466_;
}
}
else
{
lean_dec(v_a_463_);
lean_dec_ref(v_e_346_);
return v___x_464_;
}
}
else
{
lean_dec_ref(v_e_346_);
return v___x_462_;
}
}
case 9:
{
lean_object* v_a_475_; uint64_t v___x_476_; 
v_a_475_ = lean_ctor_get(v_e_346_, 0);
v___x_476_ = l_Lean_Literal_hash(v_a_475_);
v_a_358_ = v___x_476_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
case 10:
{
lean_object* v_expr_477_; lean_object* v___x_478_; 
v_expr_477_ = lean_ctor_get(v_e_346_, 1);
lean_inc_ref(v_expr_477_);
v___x_478_ = l_Lean_Meta_Grind_getAnchor(v_expr_477_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; uint64_t v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref(v___x_478_);
v___x_480_ = lean_unbox_uint64(v_a_479_);
lean_dec(v_a_479_);
v_a_358_ = v___x_480_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec_ref(v_e_346_);
return v___x_478_;
}
}
case 11:
{
lean_object* v_idx_481_; lean_object* v_struct_482_; lean_object* v___x_483_; 
v_idx_481_ = lean_ctor_get(v_e_346_, 1);
v_struct_482_ = lean_ctor_get(v_e_346_, 2);
lean_inc_ref(v_struct_482_);
v___x_483_ = l_Lean_Meta_Grind_getAnchor(v_struct_482_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_483_);
v___x_485_ = lean_uint64_of_nat(v_idx_481_);
v___x_486_ = lean_unbox_uint64(v_a_484_);
lean_dec(v_a_484_);
v___x_487_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_485_, v___x_486_);
v_a_358_ = v___x_487_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec_ref(v_e_346_);
return v___x_483_;
}
}
default: 
{
uint64_t v___x_488_; 
v___x_488_ = 0ULL;
v_a_358_ = v___x_488_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
}
}
v___jp_357_:
{
lean_object* v___x_360_; lean_object* v_congrThms_361_; lean_object* v_simp_362_; lean_object* v_lastTag_363_; lean_object* v_counters_364_; lean_object* v_splitDiags_365_; lean_object* v_lawfulEqCmpMap_366_; lean_object* v_reflCmpMap_367_; lean_object* v_anchors_368_; lean_object* v_instanceMap_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_381_; 
v___x_360_ = lean_st_ref_take(v___y_359_);
v_congrThms_361_ = lean_ctor_get(v___x_360_, 0);
v_simp_362_ = lean_ctor_get(v___x_360_, 1);
v_lastTag_363_ = lean_ctor_get(v___x_360_, 2);
v_counters_364_ = lean_ctor_get(v___x_360_, 3);
v_splitDiags_365_ = lean_ctor_get(v___x_360_, 4);
v_lawfulEqCmpMap_366_ = lean_ctor_get(v___x_360_, 5);
v_reflCmpMap_367_ = lean_ctor_get(v___x_360_, 6);
v_anchors_368_ = lean_ctor_get(v___x_360_, 7);
v_instanceMap_369_ = lean_ctor_get(v___x_360_, 8);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_381_ == 0)
{
v___x_371_ = v___x_360_;
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_instanceMap_369_);
lean_inc(v_anchors_368_);
lean_inc(v_reflCmpMap_367_);
lean_inc(v_lawfulEqCmpMap_366_);
lean_inc(v_splitDiags_365_);
lean_inc(v_counters_364_);
lean_inc(v_lastTag_363_);
lean_inc(v_simp_362_);
lean_inc(v_congrThms_361_);
lean_dec(v___x_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_box_uint64(v_a_358_);
v___x_374_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_anchors_368_, v_e_346_, v___x_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 7, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_congrThms_361_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_simp_362_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_lastTag_363_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v_counters_364_);
lean_ctor_set(v_reuseFailAlloc_380_, 4, v_splitDiags_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 5, v_lawfulEqCmpMap_366_);
lean_ctor_set(v_reuseFailAlloc_380_, 6, v_reflCmpMap_367_);
lean_ctor_set(v_reuseFailAlloc_380_, 7, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_380_, 8, v_instanceMap_369_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_st_ref_set(v___y_359_, v___x_376_);
v___x_378_ = lean_box_uint64(v_a_358_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
v___jp_382_:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Meta_Grind_getAnchor(v_d_384_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_397_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref(v___x_395_);
v___x_397_ = l_Lean_Meta_Grind_getAnchor(v_b_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
v___x_399_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_383_);
v___x_400_ = lean_unbox_uint64(v_a_396_);
lean_dec(v_a_396_);
v___x_401_ = lean_unbox_uint64(v_a_398_);
lean_dec(v_a_398_);
v___x_402_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_400_, v___x_401_);
v___x_403_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_399_, v___x_402_);
v_a_358_ = v___x_403_;
v___y_359_ = v___y_388_;
goto v___jp_357_;
}
else
{
lean_dec(v_a_396_);
lean_dec(v_n_383_);
lean_dec_ref(v_e_346_);
return v___x_397_;
}
}
else
{
lean_dec_ref(v_b_385_);
lean_dec(v_n_383_);
lean_dec_ref(v_e_346_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_upperBound_489_, lean_object* v_args_490_, lean_object* v_pinfos_491_, lean_object* v_a_492_, uint64_t v_b_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint64_t v_a_505_; uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_lt(v_a_492_, v_upperBound_489_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_a_492_);
v___x_510_ = lean_box_uint64(v_b_493_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = lean_array_fget_borrowed(v_args_490_, v_a_492_);
v___x_513_ = lean_array_get_size(v_pinfos_491_);
v___x_514_ = lean_nat_dec_lt(v_a_492_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_inc(v___x_512_);
v___x_515_ = l_Lean_Meta_Grind_getAnchor(v___x_512_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; uint64_t v___x_517_; uint64_t v___x_518_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_515_);
v___x_517_ = lean_unbox_uint64(v_a_516_);
lean_dec(v_a_516_);
v___x_518_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_493_, v___x_517_);
v_a_505_ = v___x_518_;
goto v___jp_504_;
}
else
{
lean_dec(v_a_492_);
return v___x_515_;
}
}
else
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_array_fget_borrowed(v_pinfos_491_, v_a_492_);
v___x_520_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_inc(v___x_512_);
v___x_521_ = l_Lean_Meta_Grind_getAnchor(v___x_512_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; uint64_t v___x_523_; uint64_t v___x_524_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = lean_unbox_uint64(v_a_522_);
lean_dec(v_a_522_);
v___x_524_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_493_, v___x_523_);
v_a_505_ = v___x_524_;
goto v___jp_504_;
}
else
{
lean_dec(v_a_492_);
return v___x_521_;
}
}
else
{
v_a_505_ = v_b_493_;
goto v___jp_504_;
}
}
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_a_492_, v___x_506_);
lean_dec(v_a_492_);
v_a_492_ = v___x_507_;
v_b_493_ = v_a_505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg___boxed(lean_object* v_upperBound_525_, lean_object* v_args_526_, lean_object* v_pinfos_527_, lean_object* v_a_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
uint64_t v_b_boxed_540_; lean_object* v_res_541_; 
v_b_boxed_540_ = lean_unbox_uint64(v_b_529_);
lean_dec_ref(v_b_529_);
v_res_541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_525_, v_args_526_, v_pinfos_527_, v_a_528_, v_b_boxed_540_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v_pinfos_527_);
lean_dec_ref(v_args_526_);
lean_dec(v_upperBound_525_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_542_, v_x_543_, v_x_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_Grind_getAnchor(v_e_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_upperBound_568_, lean_object* v_args_569_, lean_object* v_pinfos_570_, lean_object* v_inst_571_, lean_object* v_R_572_, lean_object* v_a_573_, uint64_t v_b_574_, lean_object* v_c_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_568_, v_args_569_, v_pinfos_570_, v_a_573_, v_b_574_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_587_ = _args[0];
lean_object* v_args_588_ = _args[1];
lean_object* v_pinfos_589_ = _args[2];
lean_object* v_inst_590_ = _args[3];
lean_object* v_R_591_ = _args[4];
lean_object* v_a_592_ = _args[5];
lean_object* v_b_593_ = _args[6];
lean_object* v_c_594_ = _args[7];
lean_object* v___y_595_ = _args[8];
lean_object* v___y_596_ = _args[9];
lean_object* v___y_597_ = _args[10];
lean_object* v___y_598_ = _args[11];
lean_object* v___y_599_ = _args[12];
lean_object* v___y_600_ = _args[13];
lean_object* v___y_601_ = _args[14];
lean_object* v___y_602_ = _args[15];
lean_object* v___y_603_ = _args[16];
lean_object* v___y_604_ = _args[17];
_start:
{
uint64_t v_b_boxed_605_; lean_object* v_res_606_; 
v_b_boxed_605_ = lean_unbox_uint64(v_b_593_);
lean_dec_ref(v_b_593_);
v_res_606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(v_upperBound_587_, v_args_588_, v_pinfos_589_, v_inst_590_, v_R_591_, v_a_592_, v_b_boxed_605_, v_c_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v_pinfos_589_);
lean_dec_ref(v_args_588_);
lean_dec(v_upperBound_587_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_x_608_, v_x_609_, v_x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_616_, v_x_617_, v_x_618_);
lean_dec_ref(v_x_618_);
lean_dec_ref(v_x_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(lean_object* v_00_u03b2_620_, lean_object* v_x_621_, size_t v_x_622_, size_t v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_621_, v_x_622_, v_x_623_, v_x_624_, v_x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
size_t v_x_33245__boxed_633_; size_t v_x_33246__boxed_634_; lean_object* v_res_635_; 
v_x_33245__boxed_633_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_x_33246__boxed_634_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_res_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(v_00_u03b2_627_, v_x_628_, v_x_33245__boxed_633_, v_x_33246__boxed_634_, v_x_631_, v_x_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_636_, lean_object* v_x_637_, size_t v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_637_, v_x_638_, v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
size_t v_x_33262__boxed_645_; lean_object* v_res_646_; 
v_x_33262__boxed_645_ = lean_unbox_usize(v_x_643_);
lean_dec(v_x_643_);
v_res_646_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_641_, v_x_642_, v_x_33262__boxed_645_, v_x_644_);
lean_dec_ref(v_x_644_);
lean_dec_ref(v_x_642_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_647_, lean_object* v_n_648_, lean_object* v_k_649_, lean_object* v_v_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v_n_648_, v_k_649_, v_v_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_652_, size_t v_depth_653_, lean_object* v_keys_654_, lean_object* v_vals_655_, lean_object* v_heq_656_, lean_object* v_i_657_, lean_object* v_entries_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_653_, v_keys_654_, v_vals_655_, v_i_657_, v_entries_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_660_, lean_object* v_depth_661_, lean_object* v_keys_662_, lean_object* v_vals_663_, lean_object* v_heq_664_, lean_object* v_i_665_, lean_object* v_entries_666_){
_start:
{
size_t v_depth_boxed_667_; lean_object* v_res_668_; 
v_depth_boxed_667_ = lean_unbox_usize(v_depth_661_);
lean_dec(v_depth_661_);
v_res_668_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(v_00_u03b2_660_, v_depth_boxed_667_, v_keys_662_, v_vals_663_, v_heq_664_, v_i_665_, v_entries_666_);
lean_dec_ref(v_vals_663_);
lean_dec_ref(v_keys_662_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_heq_672_, lean_object* v_i_673_, lean_object* v_k_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_670_, v_vals_671_, v_i_673_, v_k_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_heq_679_, lean_object* v_i_680_, lean_object* v_k_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_676_, v_keys_677_, v_vals_678_, v_heq_679_, v_i_680_, v_k_681_);
lean_dec_ref(v_k_681_);
lean_dec_ref(v_vals_678_);
lean_dec_ref(v_keys_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_x_684_, v_x_685_, v_x_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_689_, uint64_t v_anchor_690_){
_start:
{
lean_object* v_numDigits_691_; uint64_t v_anchorPrefix_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v_shift_697_; uint64_t v___x_698_; uint8_t v___x_699_; 
v_numDigits_691_ = lean_ctor_get(v_anchorRef_689_, 0);
v_anchorPrefix_692_ = lean_ctor_get_uint64(v_anchorRef_689_, sizeof(void*)*1);
v___x_693_ = 64ULL;
v___x_694_ = lean_uint64_of_nat(v_numDigits_691_);
v___x_695_ = 2ULL;
v___x_696_ = lean_uint64_shift_left(v___x_694_, v___x_695_);
v_shift_697_ = lean_uint64_sub(v___x_693_, v___x_696_);
v___x_698_ = lean_uint64_shift_right(v_anchor_690_, v_shift_697_);
v___x_699_ = lean_uint64_dec_eq(v_anchorPrefix_692_, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_700_, lean_object* v_anchor_701_){
_start:
{
uint64_t v_anchor_boxed_702_; uint8_t v_res_703_; lean_object* v_r_704_; 
v_anchor_boxed_702_ = lean_unbox_uint64(v_anchor_701_);
lean_dec_ref(v_anchor_701_);
v_res_703_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_700_, v_anchor_boxed_702_);
lean_dec_ref(v_anchorRef_700_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_705_; lean_object* v___f_706_; 
v___x_705_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_706_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_706_, 0, v___x_705_);
return v___f_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_727_, lean_object* v_shift_728_, lean_object* v___f_729_, lean_object* v___f_730_, lean_object* v___x_731_, lean_object* v_numDigits_732_, lean_object* v_es_733_, lean_object* v_a_734_, lean_object* v_x_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_727_, v_shift_728_, v___f_729_, v___f_730_, v___x_731_, v_numDigits_732_, v_es_733_, v_a_734_, v_x_735_, v___y_736_);
lean_dec(v_numDigits_732_);
lean_dec(v_shift_728_);
return v_res_737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v___x_739_ = lean_unsigned_to_nat(16u);
v___x_740_ = lean_mk_array(v___x_739_, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_found_743_; 
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2);
v___x_742_ = lean_unsigned_to_nat(0u);
v_found_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_743_, 0, v___x_742_);
lean_ctor_set(v_found_743_, 1, v___x_741_);
return v_found_743_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_found_744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3);
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_found_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_747_, lean_object* v_es_748_, lean_object* v_numDigits_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_750_ = lean_unsigned_to_nat(4u);
v___x_751_ = lean_nat_mul(v___x_750_, v_numDigits_749_);
v___x_752_ = lean_unsigned_to_nat(64u);
v___x_753_ = lean_nat_dec_lt(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec(v___x_751_);
lean_dec_ref(v_es_748_);
lean_dec_ref(v_inst_747_);
return v_numDigits_749_;
}
else
{
lean_object* v_shift_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___f_759_; lean_object* v___x_760_; size_t v_sz_761_; size_t v___x_762_; lean_object* v___x_763_; lean_object* v_fst_764_; 
v_shift_754_ = lean_nat_sub(v___x_752_, v___x_751_);
lean_dec(v___x_751_);
v___f_755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0);
v___f_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1));
v___x_757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13));
v___x_758_ = lean_box(0);
lean_inc_ref(v_es_748_);
lean_inc(v_numDigits_749_);
v___f_759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_759_, 0, v_inst_747_);
lean_closure_set(v___f_759_, 1, v_shift_754_);
lean_closure_set(v___f_759_, 2, v___f_755_);
lean_closure_set(v___f_759_, 3, v___f_756_);
lean_closure_set(v___f_759_, 4, v___x_758_);
lean_closure_set(v___f_759_, 5, v_numDigits_749_);
lean_closure_set(v___f_759_, 6, v_es_748_);
v___x_760_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_761_ = lean_array_size(v_es_748_);
v___x_762_ = ((size_t)0ULL);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_757_, v_es_748_, v___f_759_, v_sz_761_, v___x_762_, v___x_760_);
v_fst_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_fst_764_);
lean_dec(v___x_763_);
if (lean_obj_tag(v_fst_764_) == 0)
{
return v_numDigits_749_;
}
else
{
lean_object* v_val_765_; 
lean_dec(v_numDigits_749_);
v_val_765_ = lean_ctor_get(v_fst_764_, 0);
lean_inc(v_val_765_);
lean_dec_ref(v_fst_764_);
return v_val_765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_766_, lean_object* v_shift_767_, lean_object* v___f_768_, lean_object* v___f_769_, lean_object* v___x_770_, lean_object* v_numDigits_771_, lean_object* v_es_772_, lean_object* v_a_773_, lean_object* v_x_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_801_; 
v_snd_776_ = lean_ctor_get(v___y_775_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v___y_775_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v___y_775_, 0);
lean_dec(v_unused_802_);
v___x_778_ = v___y_775_;
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_dec(v___y_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
lean_inc_ref(v_inst_766_);
v___x_780_ = lean_apply_1(v_inst_766_, v_a_773_);
v___x_781_ = lean_uint64_of_nat(v_shift_767_);
v___x_782_ = lean_unbox_uint64(v___x_780_);
lean_dec_ref(v___x_780_);
v___x_783_ = lean_uint64_shift_right(v___x_782_, v___x_781_);
v___x_784_ = lean_box_uint64(v___x_783_);
lean_inc_ref(v___f_769_);
lean_inc_ref(v___f_768_);
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_768_, v___f_769_, v_snd_776_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_dec_ref(v_es_772_);
lean_dec_ref(v_inst_766_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_box_uint64(v___x_783_);
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_768_, v___f_769_, v_snd_776_, v___x_787_, v___x_786_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v___x_788_);
lean_ctor_set(v___x_778_, 0, v___x_770_);
v___x_790_ = v___x_778_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
lean_dec(v___x_770_);
lean_dec_ref(v___f_769_);
lean_dec_ref(v___f_768_);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_numDigits_771_, v___x_793_);
v___x_795_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_766_, v_es_772_, v___x_794_);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_796_);
v___x_798_ = v___x_778_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_snd_776_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_803_, lean_object* v_inst_804_, lean_object* v_es_805_, lean_object* v_numDigits_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_804_, v_es_805_, v_numDigits_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_808_, lean_object* v_h__1_809_, lean_object* v_h__2_810_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v_h__1_809_);
v___x_811_ = lean_box(0);
v___x_812_ = lean_apply_1(v_h__2_810_, v___x_811_);
return v___x_812_;
}
else
{
lean_object* v_val_813_; lean_object* v___x_814_; 
lean_dec(v_h__2_810_);
v_val_813_ = lean_ctor_get(v_x_808_, 0);
lean_inc(v_val_813_);
lean_dec_ref(v_x_808_);
v___x_814_ = lean_apply_1(v_h__1_809_, v_val_813_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_815_, lean_object* v_motive_816_, lean_object* v_x_817_, lean_object* v_h__1_818_, lean_object* v_h__2_819_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec(v_h__1_818_);
v___x_820_ = lean_box(0);
v___x_821_ = lean_apply_1(v_h__2_819_, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v_val_822_; lean_object* v___x_823_; 
lean_dec(v_h__2_819_);
v_val_822_ = lean_ctor_get(v_x_817_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v_x_817_);
v___x_823_ = lean_apply_1(v_h__1_818_, v_val_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_824_, lean_object* v_es_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(4u);
v___x_827_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_824_, v_es_825_, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_828_, lean_object* v_inst_829_, lean_object* v_es_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_829_, v_es_830_);
return v___x_831_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_832_){
_start:
{
uint64_t v_anchor_833_; 
v_anchor_833_ = lean_ctor_get_uint64(v_e_832_, sizeof(void*)*1);
return v_anchor_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_834_){
_start:
{
uint64_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_834_);
lean_dec_ref(v_e_834_);
v_r_836_ = lean_box_uint64(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_852_, uint64_t v_anchorPrefix_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_ref_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_ref_856_ = lean_ctor_get(v_a_854_, 5);
v___x_857_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_858_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_852_, v_anchorPrefix_853_);
v___x_859_ = l_Lean_mkAtom(v___x_858_);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_mk_empty_array_with_capacity(v___x_860_);
v___x_862_ = lean_array_push(v___x_861_, v___x_859_);
v___x_863_ = lean_box(2);
v___x_864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_857_);
lean_ctor_set(v___x_864_, 2, v___x_862_);
v___x_865_ = 0;
v___x_866_ = l_Lean_SourceInfo_fromRef(v_ref_856_, v___x_865_);
v___x_867_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_868_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_866_);
v___x_869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_866_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_Syntax_node2(v___x_866_, v___x_867_, v___x_869_, v___x_864_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_872_, lean_object* v_anchorPrefix_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
uint64_t v_anchorPrefix_boxed_876_; lean_object* v_res_877_; 
v_anchorPrefix_boxed_876_ = lean_unbox_uint64(v_anchorPrefix_873_);
lean_dec_ref(v_anchorPrefix_873_);
v_res_877_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_872_, v_anchorPrefix_boxed_876_, v_a_874_);
lean_dec_ref(v_a_874_);
lean_dec(v_numDigits_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_878_, uint64_t v_anchorPrefix_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_878_, v_anchorPrefix_879_, v_a_880_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_884_, lean_object* v_anchorPrefix_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
uint64_t v_anchorPrefix_boxed_889_; lean_object* v_res_890_; 
v_anchorPrefix_boxed_889_ = lean_unbox_uint64(v_anchorPrefix_885_);
lean_dec_ref(v_anchorPrefix_885_);
v_res_890_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_884_, v_anchorPrefix_boxed_889_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_numDigits_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_891_, uint64_t v_anchor_892_, lean_object* v_a_893_){
_start:
{
uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v_anchorPrefix_900_; lean_object* v___x_901_; 
v___x_895_ = 64ULL;
v___x_896_ = lean_uint64_of_nat(v_numDigits_891_);
v___x_897_ = 2ULL;
v___x_898_ = lean_uint64_shift_left(v___x_896_, v___x_897_);
v___x_899_ = lean_uint64_sub(v___x_895_, v___x_898_);
v_anchorPrefix_900_ = lean_uint64_shift_right(v_anchor_892_, v___x_899_);
v___x_901_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_891_, v_anchorPrefix_900_, v_a_893_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_902_, lean_object* v_anchor_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
uint64_t v_anchor_boxed_906_; lean_object* v_res_907_; 
v_anchor_boxed_906_ = lean_unbox_uint64(v_anchor_903_);
lean_dec_ref(v_anchor_903_);
v_res_907_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_902_, v_anchor_boxed_906_, v_a_904_);
lean_dec_ref(v_a_904_);
lean_dec(v_numDigits_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_908_, uint64_t v_anchor_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_908_, v_anchor_909_, v_a_910_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_914_, lean_object* v_anchor_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
uint64_t v_anchor_boxed_919_; lean_object* v_res_920_; 
v_anchor_boxed_919_ = lean_unbox_uint64(v_anchor_915_);
lean_dec_ref(v_anchor_915_);
v_res_920_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_914_, v_anchor_boxed_919_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_numDigits_914_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_921_);
v___x_933_ = l_Lean_Meta_Grind_getAnchor(v___x_932_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_s_934_);
return v_res_945_;
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

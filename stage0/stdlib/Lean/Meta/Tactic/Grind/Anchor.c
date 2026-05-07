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
size_t v_x_32485__boxed_217_; size_t v_x_32486__boxed_218_; lean_object* v_res_219_; 
v_x_32485__boxed_217_ = lean_unbox_usize(v_x_213_);
lean_dec(v_x_213_);
v_x_32486__boxed_218_ = lean_unbox_usize(v_x_214_);
lean_dec(v_x_214_);
v_res_219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_212_, v_x_32485__boxed_217_, v_x_32486__boxed_218_, v_x_215_, v_x_216_);
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
size_t v_x_32685__boxed_272_; lean_object* v_res_273_; 
v_x_32685__boxed_272_ = lean_unbox_usize(v_x_270_);
lean_dec(v_x_270_);
v_res_273_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_269_, v_x_32685__boxed_272_, v_x_271_);
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
uint64_t v_a_358_; lean_object* v___y_359_; lean_object* v_n_384_; lean_object* v_d_385_; lean_object* v_b_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___x_405_; lean_object* v_anchors_406_; lean_object* v___x_407_; 
v___x_405_ = lean_st_ref_get(v_a_349_);
v_anchors_406_ = lean_ctor_get(v___x_405_, 8);
lean_inc_ref(v_anchors_406_);
lean_dec(v___x_405_);
v___x_407_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_406_, v_e_346_);
lean_dec_ref(v_anchors_406_);
if (lean_obj_tag(v___x_407_) == 1)
{
lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_e_346_);
v_val_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 0);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_val_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_dec(v___x_407_);
switch(lean_obj_tag(v_e_346_))
{
case 0:
{
lean_object* v_deBruijnIndex_416_; uint64_t v___x_417_; 
v_deBruijnIndex_416_ = lean_ctor_get(v_e_346_, 0);
v___x_417_ = lean_uint64_of_nat(v_deBruijnIndex_416_);
v_a_358_ = v___x_417_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
case 1:
{
lean_object* v_fvarId_418_; lean_object* v___x_419_; 
v_fvarId_418_ = lean_ctor_get(v_e_346_, 0);
lean_inc(v_fvarId_418_);
v___x_419_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_418_, v_a_352_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; uint64_t v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref(v___x_419_);
v___x_421_ = l_Lean_LocalDecl_userName(v_a_420_);
lean_dec(v_a_420_);
v___x_422_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_421_);
v_a_358_ = v___x_422_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_e_346_);
v_a_423_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_419_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
case 4:
{
lean_object* v_declName_431_; lean_object* v___x_432_; 
v_declName_431_ = lean_ctor_get(v_e_346_, 0);
lean_inc(v_declName_431_);
v___x_432_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_431_, v_a_355_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; uint8_t v___x_434_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = lean_unbox(v_a_433_);
lean_dec(v_a_433_);
if (v___x_434_ == 0)
{
uint64_t v___x_435_; 
lean_inc(v_declName_431_);
v___x_435_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_431_);
v_a_358_ = v___x_435_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
uint64_t v___x_436_; 
v___x_436_ = 0ULL;
v_a_358_ = v___x_436_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v_e_346_);
v_a_437_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_432_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_432_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
case 5:
{
lean_object* v_dummy_445_; lean_object* v_nargs_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_dummy_445_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_446_ = l_Lean_Expr_getAppNumArgs(v_e_346_);
lean_inc(v_nargs_446_);
v___x_447_ = lean_mk_array(v_nargs_446_, v_dummy_445_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_sub(v_nargs_446_, v___x_448_);
lean_dec(v_nargs_446_);
lean_inc_ref(v_e_346_);
v___x_450_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_346_, v___x_447_, v___x_449_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; uint64_t v___x_452_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref(v___x_450_);
v___x_452_ = lean_unbox_uint64(v_a_451_);
lean_dec(v_a_451_);
v_a_358_ = v___x_452_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec_ref(v_e_346_);
return v___x_450_;
}
}
case 6:
{
lean_object* v_binderName_453_; lean_object* v_binderType_454_; lean_object* v_body_455_; 
v_binderName_453_ = lean_ctor_get(v_e_346_, 0);
v_binderType_454_ = lean_ctor_get(v_e_346_, 1);
v_body_455_ = lean_ctor_get(v_e_346_, 2);
lean_inc_ref(v_body_455_);
lean_inc_ref(v_binderType_454_);
lean_inc(v_binderName_453_);
v_n_384_ = v_binderName_453_;
v_d_385_ = v_binderType_454_;
v_b_386_ = v_body_455_;
v___y_387_ = v_a_347_;
v___y_388_ = v_a_348_;
v___y_389_ = v_a_349_;
v___y_390_ = v_a_350_;
v___y_391_ = v_a_351_;
v___y_392_ = v_a_352_;
v___y_393_ = v_a_353_;
v___y_394_ = v_a_354_;
v___y_395_ = v_a_355_;
goto v___jp_383_;
}
case 7:
{
lean_object* v_binderName_456_; lean_object* v_binderType_457_; lean_object* v_body_458_; 
v_binderName_456_ = lean_ctor_get(v_e_346_, 0);
v_binderType_457_ = lean_ctor_get(v_e_346_, 1);
v_body_458_ = lean_ctor_get(v_e_346_, 2);
lean_inc_ref(v_body_458_);
lean_inc_ref(v_binderType_457_);
lean_inc(v_binderName_456_);
v_n_384_ = v_binderName_456_;
v_d_385_ = v_binderType_457_;
v_b_386_ = v_body_458_;
v___y_387_ = v_a_347_;
v___y_388_ = v_a_348_;
v___y_389_ = v_a_349_;
v___y_390_ = v_a_350_;
v___y_391_ = v_a_351_;
v___y_392_ = v_a_352_;
v___y_393_ = v_a_353_;
v___y_394_ = v_a_354_;
v___y_395_ = v_a_355_;
goto v___jp_383_;
}
case 8:
{
lean_object* v_declName_459_; lean_object* v_type_460_; lean_object* v_value_461_; lean_object* v_body_462_; lean_object* v___x_463_; 
v_declName_459_ = lean_ctor_get(v_e_346_, 0);
v_type_460_ = lean_ctor_get(v_e_346_, 1);
v_value_461_ = lean_ctor_get(v_e_346_, 2);
v_body_462_ = lean_ctor_get(v_e_346_, 3);
lean_inc_ref(v_value_461_);
v___x_463_ = l_Lean_Meta_Grind_getAnchor(v_value_461_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref(v___x_463_);
lean_inc_ref(v_type_460_);
v___x_465_ = l_Lean_Meta_Grind_getAnchor(v_type_460_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
lean_inc_ref(v_body_462_);
v___x_467_ = l_Lean_Meta_Grind_getAnchor(v_body_462_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
lean_inc(v_declName_459_);
v___x_469_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_459_);
v___x_470_ = lean_unbox_uint64(v_a_466_);
lean_dec(v_a_466_);
v___x_471_ = lean_unbox_uint64(v_a_468_);
lean_dec(v_a_468_);
v___x_472_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_470_, v___x_471_);
v___x_473_ = lean_unbox_uint64(v_a_464_);
lean_dec(v_a_464_);
v___x_474_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_473_, v___x_472_);
v___x_475_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_469_, v___x_474_);
v_a_358_ = v___x_475_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec(v_a_466_);
lean_dec(v_a_464_);
lean_dec_ref(v_e_346_);
return v___x_467_;
}
}
else
{
lean_dec(v_a_464_);
lean_dec_ref(v_e_346_);
return v___x_465_;
}
}
else
{
lean_dec_ref(v_e_346_);
return v___x_463_;
}
}
case 9:
{
lean_object* v_a_476_; uint64_t v___x_477_; 
v_a_476_ = lean_ctor_get(v_e_346_, 0);
v___x_477_ = l_Lean_Literal_hash(v_a_476_);
v_a_358_ = v___x_477_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
case 10:
{
lean_object* v_expr_478_; lean_object* v___x_479_; 
v_expr_478_ = lean_ctor_get(v_e_346_, 1);
lean_inc_ref(v_expr_478_);
v___x_479_ = l_Lean_Meta_Grind_getAnchor(v_expr_478_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; uint64_t v___x_481_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v___x_479_);
v___x_481_ = lean_unbox_uint64(v_a_480_);
lean_dec(v_a_480_);
v_a_358_ = v___x_481_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec_ref(v_e_346_);
return v___x_479_;
}
}
case 11:
{
lean_object* v_idx_482_; lean_object* v_struct_483_; lean_object* v___x_484_; 
v_idx_482_ = lean_ctor_get(v_e_346_, 1);
v_struct_483_ = lean_ctor_get(v_e_346_, 2);
lean_inc_ref(v_struct_483_);
v___x_484_ = l_Lean_Meta_Grind_getAnchor(v_struct_483_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; uint64_t v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_uint64_of_nat(v_idx_482_);
v___x_487_ = lean_unbox_uint64(v_a_485_);
lean_dec(v_a_485_);
v___x_488_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_486_, v___x_487_);
v_a_358_ = v___x_488_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
else
{
lean_dec_ref(v_e_346_);
return v___x_484_;
}
}
default: 
{
uint64_t v___x_489_; 
v___x_489_ = 0ULL;
v_a_358_ = v___x_489_;
v___y_359_ = v_a_349_;
goto v___jp_357_;
}
}
}
v___jp_357_:
{
lean_object* v___x_360_; lean_object* v_congrThms_361_; lean_object* v_simp_362_; lean_object* v_lastTag_363_; lean_object* v_counters_364_; lean_object* v_splitDiags_365_; lean_object* v_ematchDiags_366_; lean_object* v_lawfulEqCmpMap_367_; lean_object* v_reflCmpMap_368_; lean_object* v_anchors_369_; lean_object* v_instanceMap_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_382_; 
v___x_360_ = lean_st_ref_take(v___y_359_);
v_congrThms_361_ = lean_ctor_get(v___x_360_, 0);
v_simp_362_ = lean_ctor_get(v___x_360_, 1);
v_lastTag_363_ = lean_ctor_get(v___x_360_, 2);
v_counters_364_ = lean_ctor_get(v___x_360_, 3);
v_splitDiags_365_ = lean_ctor_get(v___x_360_, 4);
v_ematchDiags_366_ = lean_ctor_get(v___x_360_, 5);
v_lawfulEqCmpMap_367_ = lean_ctor_get(v___x_360_, 6);
v_reflCmpMap_368_ = lean_ctor_get(v___x_360_, 7);
v_anchors_369_ = lean_ctor_get(v___x_360_, 8);
v_instanceMap_370_ = lean_ctor_get(v___x_360_, 9);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_382_ == 0)
{
v___x_372_ = v___x_360_;
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_instanceMap_370_);
lean_inc(v_anchors_369_);
lean_inc(v_reflCmpMap_368_);
lean_inc(v_lawfulEqCmpMap_367_);
lean_inc(v_ematchDiags_366_);
lean_inc(v_splitDiags_365_);
lean_inc(v_counters_364_);
lean_inc(v_lastTag_363_);
lean_inc(v_simp_362_);
lean_inc(v_congrThms_361_);
lean_dec(v___x_360_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_374_ = lean_box_uint64(v_a_358_);
v___x_375_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_anchors_369_, v_e_346_, v___x_374_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 8, v___x_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_congrThms_361_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_simp_362_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_lastTag_363_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_counters_364_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_splitDiags_365_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v_ematchDiags_366_);
lean_ctor_set(v_reuseFailAlloc_381_, 6, v_lawfulEqCmpMap_367_);
lean_ctor_set(v_reuseFailAlloc_381_, 7, v_reflCmpMap_368_);
lean_ctor_set(v_reuseFailAlloc_381_, 8, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_381_, 9, v_instanceMap_370_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_st_ref_set(v___y_359_, v___x_377_);
v___x_379_ = lean_box_uint64(v_a_358_);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
}
v___jp_383_:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Meta_Grind_getAnchor(v_d_385_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref(v___x_396_);
v___x_398_ = l_Lean_Meta_Grind_getAnchor(v_b_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref(v___x_398_);
v___x_400_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_384_);
v___x_401_ = lean_unbox_uint64(v_a_397_);
lean_dec(v_a_397_);
v___x_402_ = lean_unbox_uint64(v_a_399_);
lean_dec(v_a_399_);
v___x_403_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_401_, v___x_402_);
v___x_404_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_400_, v___x_403_);
v_a_358_ = v___x_404_;
v___y_359_ = v___y_389_;
goto v___jp_357_;
}
else
{
lean_dec(v_a_397_);
lean_dec(v_n_384_);
lean_dec_ref(v_e_346_);
return v___x_398_;
}
}
else
{
lean_dec_ref(v_b_386_);
lean_dec(v_n_384_);
lean_dec_ref(v_e_346_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_upperBound_490_, lean_object* v_args_491_, lean_object* v_pinfos_492_, lean_object* v_a_493_, uint64_t v_b_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint64_t v_a_506_; uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_lt(v_a_493_, v_upperBound_490_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_a_493_);
v___x_511_ = lean_box_uint64(v_b_494_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_array_fget_borrowed(v_args_491_, v_a_493_);
v___x_514_ = lean_array_get_size(v_pinfos_492_);
v___x_515_ = lean_nat_dec_lt(v_a_493_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_inc(v___x_513_);
v___x_516_ = l_Lean_Meta_Grind_getAnchor(v___x_513_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; uint64_t v___x_518_; uint64_t v___x_519_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref(v___x_516_);
v___x_518_ = lean_unbox_uint64(v_a_517_);
lean_dec(v_a_517_);
v___x_519_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_494_, v___x_518_);
v_a_506_ = v___x_519_;
goto v___jp_505_;
}
else
{
lean_dec(v_a_493_);
return v___x_516_;
}
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_array_fget_borrowed(v_pinfos_492_, v_a_493_);
v___x_521_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_inc(v___x_513_);
v___x_522_ = l_Lean_Meta_Grind_getAnchor(v___x_513_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; uint64_t v___x_524_; uint64_t v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = lean_unbox_uint64(v_a_523_);
lean_dec(v_a_523_);
v___x_525_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_494_, v___x_524_);
v_a_506_ = v___x_525_;
goto v___jp_505_;
}
else
{
lean_dec(v_a_493_);
return v___x_522_;
}
}
else
{
v_a_506_ = v_b_494_;
goto v___jp_505_;
}
}
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_a_493_, v___x_507_);
lean_dec(v_a_493_);
v_a_493_ = v___x_508_;
v_b_494_ = v_a_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg___boxed(lean_object* v_upperBound_526_, lean_object* v_args_527_, lean_object* v_pinfos_528_, lean_object* v_a_529_, lean_object* v_b_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint64_t v_b_boxed_541_; lean_object* v_res_542_; 
v_b_boxed_541_ = lean_unbox_uint64(v_b_530_);
lean_dec_ref(v_b_530_);
v_res_542_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_526_, v_args_527_, v_pinfos_528_, v_a_529_, v_b_boxed_541_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v_pinfos_528_);
lean_dec_ref(v_args_527_);
lean_dec(v_upperBound_526_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_543_, v_x_544_, v_x_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Meta_Grind_getAnchor(v_e_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_upperBound_569_, lean_object* v_args_570_, lean_object* v_pinfos_571_, lean_object* v_inst_572_, lean_object* v_R_573_, lean_object* v_a_574_, uint64_t v_b_575_, lean_object* v_c_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_569_, v_args_570_, v_pinfos_571_, v_a_574_, v_b_575_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_588_ = _args[0];
lean_object* v_args_589_ = _args[1];
lean_object* v_pinfos_590_ = _args[2];
lean_object* v_inst_591_ = _args[3];
lean_object* v_R_592_ = _args[4];
lean_object* v_a_593_ = _args[5];
lean_object* v_b_594_ = _args[6];
lean_object* v_c_595_ = _args[7];
lean_object* v___y_596_ = _args[8];
lean_object* v___y_597_ = _args[9];
lean_object* v___y_598_ = _args[10];
lean_object* v___y_599_ = _args[11];
lean_object* v___y_600_ = _args[12];
lean_object* v___y_601_ = _args[13];
lean_object* v___y_602_ = _args[14];
lean_object* v___y_603_ = _args[15];
lean_object* v___y_604_ = _args[16];
lean_object* v___y_605_ = _args[17];
_start:
{
uint64_t v_b_boxed_606_; lean_object* v_res_607_; 
v_b_boxed_606_ = lean_unbox_uint64(v_b_594_);
lean_dec_ref(v_b_594_);
v_res_607_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(v_upperBound_588_, v_args_589_, v_pinfos_590_, v_inst_591_, v_R_592_, v_a_593_, v_b_boxed_606_, v_c_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v_pinfos_590_);
lean_dec_ref(v_args_589_);
lean_dec(v_upperBound_588_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_x_609_, v_x_610_, v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_614_, v_x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_617_, v_x_618_, v_x_619_);
lean_dec_ref(v_x_619_);
lean_dec_ref(v_x_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, size_t v_x_623_, size_t v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_622_, v_x_623_, v_x_624_, v_x_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(lean_object* v_00_u03b2_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
size_t v_x_33267__boxed_634_; size_t v_x_33268__boxed_635_; lean_object* v_res_636_; 
v_x_33267__boxed_634_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_x_33268__boxed_635_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_res_636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(v_00_u03b2_628_, v_x_629_, v_x_33267__boxed_634_, v_x_33268__boxed_635_, v_x_632_, v_x_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, size_t v_x_639_, lean_object* v_x_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_638_, v_x_639_, v_x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
size_t v_x_33284__boxed_646_; lean_object* v_res_647_; 
v_x_33284__boxed_646_ = lean_unbox_usize(v_x_644_);
lean_dec(v_x_644_);
v_res_647_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_642_, v_x_643_, v_x_33284__boxed_646_, v_x_645_);
lean_dec_ref(v_x_645_);
lean_dec_ref(v_x_643_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_648_, lean_object* v_n_649_, lean_object* v_k_650_, lean_object* v_v_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v_n_649_, v_k_650_, v_v_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_653_, size_t v_depth_654_, lean_object* v_keys_655_, lean_object* v_vals_656_, lean_object* v_heq_657_, lean_object* v_i_658_, lean_object* v_entries_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_654_, v_keys_655_, v_vals_656_, v_i_658_, v_entries_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_661_, lean_object* v_depth_662_, lean_object* v_keys_663_, lean_object* v_vals_664_, lean_object* v_heq_665_, lean_object* v_i_666_, lean_object* v_entries_667_){
_start:
{
size_t v_depth_boxed_668_; lean_object* v_res_669_; 
v_depth_boxed_668_ = lean_unbox_usize(v_depth_662_);
lean_dec(v_depth_662_);
v_res_669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(v_00_u03b2_661_, v_depth_boxed_668_, v_keys_663_, v_vals_664_, v_heq_665_, v_i_666_, v_entries_667_);
lean_dec_ref(v_vals_664_);
lean_dec_ref(v_keys_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_670_, lean_object* v_keys_671_, lean_object* v_vals_672_, lean_object* v_heq_673_, lean_object* v_i_674_, lean_object* v_k_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_671_, v_vals_672_, v_i_674_, v_k_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_677_, lean_object* v_keys_678_, lean_object* v_vals_679_, lean_object* v_heq_680_, lean_object* v_i_681_, lean_object* v_k_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_677_, v_keys_678_, v_vals_679_, v_heq_680_, v_i_681_, v_k_682_);
lean_dec_ref(v_k_682_);
lean_dec_ref(v_vals_679_);
lean_dec_ref(v_keys_678_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_x_685_, v_x_686_, v_x_687_, v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_690_, uint64_t v_anchor_691_){
_start:
{
lean_object* v_numDigits_692_; uint64_t v_anchorPrefix_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v_shift_698_; uint64_t v___x_699_; uint8_t v___x_700_; 
v_numDigits_692_ = lean_ctor_get(v_anchorRef_690_, 0);
v_anchorPrefix_693_ = lean_ctor_get_uint64(v_anchorRef_690_, sizeof(void*)*1);
v___x_694_ = 64ULL;
v___x_695_ = lean_uint64_of_nat(v_numDigits_692_);
v___x_696_ = 2ULL;
v___x_697_ = lean_uint64_shift_left(v___x_695_, v___x_696_);
v_shift_698_ = lean_uint64_sub(v___x_694_, v___x_697_);
v___x_699_ = lean_uint64_shift_right(v_anchor_691_, v_shift_698_);
v___x_700_ = lean_uint64_dec_eq(v_anchorPrefix_693_, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_701_, lean_object* v_anchor_702_){
_start:
{
uint64_t v_anchor_boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v_anchor_boxed_703_ = lean_unbox_uint64(v_anchor_702_);
lean_dec_ref(v_anchor_702_);
v_res_704_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_701_, v_anchor_boxed_703_);
lean_dec_ref(v_anchorRef_701_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_706_; lean_object* v___f_707_; 
v___x_706_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_707_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_707_, 0, v___x_706_);
return v___f_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_728_, lean_object* v_shift_729_, lean_object* v___f_730_, lean_object* v___f_731_, lean_object* v___x_732_, lean_object* v_numDigits_733_, lean_object* v_es_734_, lean_object* v_a_735_, lean_object* v_x_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_728_, v_shift_729_, v___f_730_, v___f_731_, v___x_732_, v_numDigits_733_, v_es_734_, v_a_735_, v_x_736_, v___y_737_);
lean_dec(v_numDigits_733_);
lean_dec(v_shift_729_);
return v_res_738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = lean_unsigned_to_nat(16u);
v___x_741_ = lean_mk_array(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_found_744_; 
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2);
v___x_743_ = lean_unsigned_to_nat(0u);
v_found_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_744_, 0, v___x_743_);
lean_ctor_set(v_found_744_, 1, v___x_742_);
return v_found_744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_found_745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_found_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_748_, lean_object* v_es_749_, lean_object* v_numDigits_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_751_ = lean_unsigned_to_nat(4u);
v___x_752_ = lean_nat_mul(v___x_751_, v_numDigits_750_);
v___x_753_ = lean_unsigned_to_nat(64u);
v___x_754_ = lean_nat_dec_lt(v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v___x_752_);
lean_dec_ref(v_es_749_);
lean_dec_ref(v_inst_748_);
return v_numDigits_750_;
}
else
{
lean_object* v_shift_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___f_760_; lean_object* v___x_761_; size_t v_sz_762_; size_t v___x_763_; lean_object* v___x_764_; lean_object* v_fst_765_; 
v_shift_755_ = lean_nat_sub(v___x_753_, v___x_752_);
lean_dec(v___x_752_);
v___f_756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0);
v___f_757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1));
v___x_758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13));
v___x_759_ = lean_box(0);
lean_inc_ref(v_es_749_);
lean_inc(v_numDigits_750_);
v___f_760_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_760_, 0, v_inst_748_);
lean_closure_set(v___f_760_, 1, v_shift_755_);
lean_closure_set(v___f_760_, 2, v___f_756_);
lean_closure_set(v___f_760_, 3, v___f_757_);
lean_closure_set(v___f_760_, 4, v___x_759_);
lean_closure_set(v___f_760_, 5, v_numDigits_750_);
lean_closure_set(v___f_760_, 6, v_es_749_);
v___x_761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_762_ = lean_array_size(v_es_749_);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_758_, v_es_749_, v___f_760_, v_sz_762_, v___x_763_, v___x_761_);
v_fst_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_fst_765_);
lean_dec(v___x_764_);
if (lean_obj_tag(v_fst_765_) == 0)
{
return v_numDigits_750_;
}
else
{
lean_object* v_val_766_; 
lean_dec(v_numDigits_750_);
v_val_766_ = lean_ctor_get(v_fst_765_, 0);
lean_inc(v_val_766_);
lean_dec_ref(v_fst_765_);
return v_val_766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_767_, lean_object* v_shift_768_, lean_object* v___f_769_, lean_object* v___f_770_, lean_object* v___x_771_, lean_object* v_numDigits_772_, lean_object* v_es_773_, lean_object* v_a_774_, lean_object* v_x_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_snd_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_802_; 
v_snd_777_ = lean_ctor_get(v___y_776_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v___y_776_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___y_776_, 0);
lean_dec(v_unused_803_);
v___x_779_ = v___y_776_;
v_isShared_780_ = v_isSharedCheck_802_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_777_);
lean_dec(v___y_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_802_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
lean_inc_ref(v_inst_767_);
v___x_781_ = lean_apply_1(v_inst_767_, v_a_774_);
v___x_782_ = lean_uint64_of_nat(v_shift_768_);
v___x_783_ = lean_unbox_uint64(v___x_781_);
lean_dec_ref(v___x_781_);
v___x_784_ = lean_uint64_shift_right(v___x_783_, v___x_782_);
v___x_785_ = lean_box_uint64(v___x_784_);
lean_inc_ref(v___f_770_);
lean_inc_ref(v___f_769_);
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_769_, v___f_770_, v_snd_777_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
lean_dec_ref(v_es_773_);
lean_dec_ref(v_inst_767_);
v___x_787_ = lean_box(0);
v___x_788_ = lean_box_uint64(v___x_784_);
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_769_, v___f_770_, v_snd_777_, v___x_788_, v___x_787_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_789_);
lean_ctor_set(v___x_779_, 0, v___x_771_);
v___x_791_ = v___x_779_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec(v___x_771_);
lean_dec_ref(v___f_770_);
lean_dec_ref(v___f_769_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_add(v_numDigits_772_, v___x_794_);
v___x_796_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_767_, v_es_773_, v___x_795_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_797_);
v___x_799_ = v___x_779_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_snd_777_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_804_, lean_object* v_inst_805_, lean_object* v_es_806_, lean_object* v_numDigits_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_805_, v_es_806_, v_numDigits_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_809_, lean_object* v_h__1_810_, lean_object* v_h__2_811_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec(v_h__1_810_);
v___x_812_ = lean_box(0);
v___x_813_ = lean_apply_1(v_h__2_811_, v___x_812_);
return v___x_813_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_815_; 
lean_dec(v_h__2_811_);
v_val_814_ = lean_ctor_get(v_x_809_, 0);
lean_inc(v_val_814_);
lean_dec_ref(v_x_809_);
v___x_815_ = lean_apply_1(v_h__1_810_, v_val_814_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_816_, lean_object* v_motive_817_, lean_object* v_x_818_, lean_object* v_h__1_819_, lean_object* v_h__2_820_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_h__1_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_apply_1(v_h__2_820_, v___x_821_);
return v___x_822_;
}
else
{
lean_object* v_val_823_; lean_object* v___x_824_; 
lean_dec(v_h__2_820_);
v_val_823_ = lean_ctor_get(v_x_818_, 0);
lean_inc(v_val_823_);
lean_dec_ref(v_x_818_);
v___x_824_ = lean_apply_1(v_h__1_819_, v_val_823_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_825_, lean_object* v_es_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(4u);
v___x_828_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_825_, v_es_826_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_829_, lean_object* v_inst_830_, lean_object* v_es_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_830_, v_es_831_);
return v___x_832_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_833_){
_start:
{
uint64_t v_anchor_834_; 
v_anchor_834_ = lean_ctor_get_uint64(v_e_833_, sizeof(void*)*1);
return v_anchor_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_835_){
_start:
{
uint64_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_835_);
lean_dec_ref(v_e_835_);
v_r_837_ = lean_box_uint64(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_853_, uint64_t v_anchorPrefix_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_ref_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_ref_857_ = lean_ctor_get(v_a_855_, 5);
v___x_858_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_859_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_853_, v_anchorPrefix_854_);
v___x_860_ = l_Lean_mkAtom(v___x_859_);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_mk_empty_array_with_capacity(v___x_861_);
v___x_863_ = lean_array_push(v___x_862_, v___x_860_);
v___x_864_ = lean_box(2);
v___x_865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_858_);
lean_ctor_set(v___x_865_, 2, v___x_863_);
v___x_866_ = 0;
v___x_867_ = l_Lean_SourceInfo_fromRef(v_ref_857_, v___x_866_);
v___x_868_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_869_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_867_);
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_867_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_Syntax_node2(v___x_867_, v___x_868_, v___x_870_, v___x_865_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_873_, lean_object* v_anchorPrefix_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
uint64_t v_anchorPrefix_boxed_877_; lean_object* v_res_878_; 
v_anchorPrefix_boxed_877_ = lean_unbox_uint64(v_anchorPrefix_874_);
lean_dec_ref(v_anchorPrefix_874_);
v_res_878_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_873_, v_anchorPrefix_boxed_877_, v_a_875_);
lean_dec_ref(v_a_875_);
lean_dec(v_numDigits_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_879_, uint64_t v_anchorPrefix_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_879_, v_anchorPrefix_880_, v_a_881_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_885_, lean_object* v_anchorPrefix_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
uint64_t v_anchorPrefix_boxed_890_; lean_object* v_res_891_; 
v_anchorPrefix_boxed_890_ = lean_unbox_uint64(v_anchorPrefix_886_);
lean_dec_ref(v_anchorPrefix_886_);
v_res_891_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_885_, v_anchorPrefix_boxed_890_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_numDigits_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_892_, uint64_t v_anchor_893_, lean_object* v_a_894_){
_start:
{
uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v_anchorPrefix_901_; lean_object* v___x_902_; 
v___x_896_ = 64ULL;
v___x_897_ = lean_uint64_of_nat(v_numDigits_892_);
v___x_898_ = 2ULL;
v___x_899_ = lean_uint64_shift_left(v___x_897_, v___x_898_);
v___x_900_ = lean_uint64_sub(v___x_896_, v___x_899_);
v_anchorPrefix_901_ = lean_uint64_shift_right(v_anchor_893_, v___x_900_);
v___x_902_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_892_, v_anchorPrefix_901_, v_a_894_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_903_, lean_object* v_anchor_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
uint64_t v_anchor_boxed_907_; lean_object* v_res_908_; 
v_anchor_boxed_907_ = lean_unbox_uint64(v_anchor_904_);
lean_dec_ref(v_anchor_904_);
v_res_908_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_903_, v_anchor_boxed_907_, v_a_905_);
lean_dec_ref(v_a_905_);
lean_dec(v_numDigits_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_909_, uint64_t v_anchor_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_909_, v_anchor_910_, v_a_911_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_915_, lean_object* v_anchor_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint64_t v_anchor_boxed_920_; lean_object* v_res_921_; 
v_anchor_boxed_920_ = lean_unbox_uint64(v_anchor_916_);
lean_dec_ref(v_anchor_916_);
v_res_921_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_915_, v_anchor_boxed_920_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_numDigits_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_922_);
v___x_934_ = l_Lean_Meta_Grind_getAnchor(v___x_933_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_s_935_);
return v_res_946_;
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

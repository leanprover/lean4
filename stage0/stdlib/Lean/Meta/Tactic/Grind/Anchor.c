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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
size_t v_x_34856__boxed_217_; size_t v_x_34857__boxed_218_; lean_object* v_res_219_; 
v_x_34856__boxed_217_ = lean_unbox_usize(v_x_213_);
lean_dec(v_x_213_);
v_x_34857__boxed_218_ = lean_unbox_usize(v_x_214_);
lean_dec(v_x_214_);
v_res_219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_212_, v_x_34856__boxed_217_, v_x_34857__boxed_218_, v_x_215_, v_x_216_);
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
lean_object* v_es_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_270_; 
v_es_249_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_270_ == 0)
{
v___x_251_ = v_x_246_;
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_es_249_);
lean_dec(v_x_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v_j_257_; lean_object* v___x_258_; 
v___x_253_ = lean_box(2);
v___x_254_ = ((size_t)5ULL);
v___x_255_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1);
v___x_256_ = lean_usize_land(v_x_247_, v___x_255_);
v_j_257_ = lean_usize_to_nat(v___x_256_);
v___x_258_ = lean_array_get(v___x_253_, v_es_249_, v_j_257_);
lean_dec(v_j_257_);
lean_dec_ref(v_es_249_);
switch(lean_obj_tag(v___x_258_))
{
case 0:
{
lean_object* v_key_259_; lean_object* v_val_260_; uint8_t v___x_261_; 
v_key_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_key_259_);
v_val_260_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_val_260_);
lean_dec_ref(v___x_258_);
v___x_261_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_248_, v_key_259_);
lean_dec(v_key_259_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec(v_val_260_);
lean_del_object(v___x_251_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
lean_object* v___x_264_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 1);
lean_ctor_set(v___x_251_, 0, v_val_260_);
v___x_264_ = v___x_251_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_val_260_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
case 1:
{
lean_object* v_node_266_; size_t v___x_267_; 
lean_del_object(v___x_251_);
v_node_266_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_node_266_);
lean_dec_ref(v___x_258_);
v___x_267_ = lean_usize_shift_right(v_x_247_, v___x_254_);
v_x_246_ = v_node_266_;
v_x_247_ = v___x_267_;
goto _start;
}
default: 
{
lean_object* v___x_269_; 
lean_del_object(v___x_251_);
v___x_269_ = lean_box(0);
return v___x_269_;
}
}
}
}
else
{
lean_object* v_ks_271_; lean_object* v_vs_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_ks_271_ = lean_ctor_get(v_x_246_, 0);
lean_inc_ref(v_ks_271_);
v_vs_272_ = lean_ctor_get(v_x_246_, 1);
lean_inc_ref(v_vs_272_);
lean_dec_ref(v_x_246_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_271_, v_vs_272_, v___x_273_, v_x_248_);
lean_dec_ref(v_vs_272_);
lean_dec_ref(v_ks_271_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
size_t v_x_35056__boxed_278_; lean_object* v_res_279_; 
v_x_35056__boxed_278_ = lean_unbox_usize(v_x_276_);
lean_dec(v_x_276_);
v_res_279_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_275_, v_x_35056__boxed_278_, v_x_277_);
lean_dec_ref(v_x_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
uint64_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_281_);
v___x_283_ = lean_uint64_to_usize(v___x_282_);
v___x_284_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_280_, v___x_283_, v_x_281_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_285_, v_x_286_);
lean_dec_ref(v_x_286_);
return v_res_287_;
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
lean_object* v_pinfos_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; uint8_t v___y_323_; 
if (lean_obj_tag(v_x_292_) == 5)
{
lean_object* v_fn_342_; lean_object* v_arg_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_fn_342_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_fn_342_);
v_arg_343_ = lean_ctor_get(v_x_292_, 1);
lean_inc_ref(v_arg_343_);
lean_dec_ref(v_x_292_);
v___x_344_ = lean_array_set(v_x_293_, v_x_294_, v_arg_343_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_sub(v_x_294_, v___x_345_);
lean_dec(v_x_294_);
v_x_292_ = v_fn_342_;
v_x_293_ = v___x_344_;
v_x_294_ = v___x_346_;
goto _start;
}
else
{
uint8_t v___x_348_; 
lean_dec(v_x_294_);
v___x_348_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_292_);
if (v___x_348_ == 0)
{
v___y_323_ = v___x_348_;
goto v___jp_322_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_array_get_size(v_x_293_);
v___x_350_ = lean_unsigned_to_nat(2u);
v___x_351_ = lean_nat_dec_eq(v___x_349_, v___x_350_);
v___y_323_ = v___x_351_;
goto v___jp_322_;
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
lean_dec_ref(v___x_316_);
v___x_318_ = lean_array_get_size(v_x_293_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_unbox_uint64(v_a_317_);
lean_dec(v_a_317_);
v___x_321_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v___x_318_, v_x_293_, v_pinfos_306_, v___x_319_, v___x_320_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
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
if (v___y_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = l_Lean_Expr_hasLooseBVars(v_x_292_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_box(0);
lean_inc_ref(v_x_292_);
v___x_326_ = l_Lean_Meta_getFunInfo(v_x_292_, v___x_325_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v_paramInfo_328_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v___x_326_);
v_paramInfo_328_ = lean_ctor_get(v_a_327_, 0);
lean_inc_ref(v_paramInfo_328_);
lean_dec(v_a_327_);
v_pinfos_306_ = v_paramInfo_328_;
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
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec_ref(v_x_293_);
lean_dec_ref(v_x_292_);
v_a_329_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_326_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0));
v_pinfos_306_ = v___x_337_;
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
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_x_292_);
v___x_338_ = l_Lean_instInhabitedExpr;
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_array_get(v___x_338_, v_x_293_, v___x_339_);
lean_dec_ref(v_x_293_);
v___x_341_ = l_Lean_Meta_Grind_getAnchor(v___x_340_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
uint64_t v_a_364_; lean_object* v___y_365_; lean_object* v_n_390_; lean_object* v_d_391_; lean_object* v_b_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___x_411_; lean_object* v_anchors_412_; lean_object* v___x_413_; 
v___x_411_ = lean_st_ref_get(v_a_355_);
v_anchors_412_ = lean_ctor_get(v___x_411_, 8);
lean_inc_ref(v_anchors_412_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_412_, v_e_352_);
if (lean_obj_tag(v___x_413_) == 1)
{
lean_object* v_val_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v_e_352_);
v_val_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_val_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 0);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_val_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_dec(v___x_413_);
switch(lean_obj_tag(v_e_352_))
{
case 0:
{
lean_object* v_deBruijnIndex_422_; uint64_t v___x_423_; 
v_deBruijnIndex_422_ = lean_ctor_get(v_e_352_, 0);
v___x_423_ = lean_uint64_of_nat(v_deBruijnIndex_422_);
v_a_364_ = v___x_423_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
case 1:
{
lean_object* v_fvarId_424_; lean_object* v___x_425_; 
v_fvarId_424_ = lean_ctor_get(v_e_352_, 0);
lean_inc_ref(v_a_358_);
lean_inc(v_fvarId_424_);
v___x_425_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_424_, v_a_358_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; uint64_t v___x_428_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_425_);
v___x_427_ = l_Lean_LocalDecl_userName(v_a_426_);
lean_dec(v_a_426_);
v___x_428_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_427_);
v_a_364_ = v___x_428_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_e_352_);
v_a_429_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_425_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_425_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
case 4:
{
lean_object* v_declName_437_; lean_object* v___x_438_; 
v_declName_437_ = lean_ctor_get(v_e_352_, 0);
lean_inc(v_declName_437_);
v___x_438_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_437_, v_a_361_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; uint8_t v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
v___x_440_ = lean_unbox(v_a_439_);
lean_dec(v_a_439_);
if (v___x_440_ == 0)
{
uint64_t v___x_441_; 
lean_inc(v_declName_437_);
v___x_441_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_437_);
v_a_364_ = v___x_441_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
else
{
uint64_t v___x_442_; 
v___x_442_ = 0ULL;
v_a_364_ = v___x_442_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_e_352_);
v_a_443_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_438_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_438_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
case 5:
{
lean_object* v_dummy_451_; lean_object* v_nargs_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_dummy_451_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_452_ = l_Lean_Expr_getAppNumArgs(v_e_352_);
lean_inc(v_nargs_452_);
v___x_453_ = lean_mk_array(v_nargs_452_, v_dummy_451_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_sub(v_nargs_452_, v___x_454_);
lean_dec(v_nargs_452_);
lean_inc_ref(v_e_352_);
v___x_456_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_352_, v___x_453_, v___x_455_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; uint64_t v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___x_458_ = lean_unbox_uint64(v_a_457_);
lean_dec(v_a_457_);
v_a_364_ = v___x_458_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
else
{
lean_dec_ref(v_e_352_);
return v___x_456_;
}
}
case 6:
{
lean_object* v_binderName_459_; lean_object* v_binderType_460_; lean_object* v_body_461_; 
v_binderName_459_ = lean_ctor_get(v_e_352_, 0);
v_binderType_460_ = lean_ctor_get(v_e_352_, 1);
v_body_461_ = lean_ctor_get(v_e_352_, 2);
lean_inc_ref(v_body_461_);
lean_inc_ref(v_binderType_460_);
lean_inc(v_binderName_459_);
v_n_390_ = v_binderName_459_;
v_d_391_ = v_binderType_460_;
v_b_392_ = v_body_461_;
v___y_393_ = v_a_353_;
v___y_394_ = v_a_354_;
v___y_395_ = v_a_355_;
v___y_396_ = v_a_356_;
v___y_397_ = v_a_357_;
v___y_398_ = v_a_358_;
v___y_399_ = v_a_359_;
v___y_400_ = v_a_360_;
v___y_401_ = v_a_361_;
goto v___jp_389_;
}
case 7:
{
lean_object* v_binderName_462_; lean_object* v_binderType_463_; lean_object* v_body_464_; 
v_binderName_462_ = lean_ctor_get(v_e_352_, 0);
v_binderType_463_ = lean_ctor_get(v_e_352_, 1);
v_body_464_ = lean_ctor_get(v_e_352_, 2);
lean_inc_ref(v_body_464_);
lean_inc_ref(v_binderType_463_);
lean_inc(v_binderName_462_);
v_n_390_ = v_binderName_462_;
v_d_391_ = v_binderType_463_;
v_b_392_ = v_body_464_;
v___y_393_ = v_a_353_;
v___y_394_ = v_a_354_;
v___y_395_ = v_a_355_;
v___y_396_ = v_a_356_;
v___y_397_ = v_a_357_;
v___y_398_ = v_a_358_;
v___y_399_ = v_a_359_;
v___y_400_ = v_a_360_;
v___y_401_ = v_a_361_;
goto v___jp_389_;
}
case 8:
{
lean_object* v_declName_465_; lean_object* v_type_466_; lean_object* v_value_467_; lean_object* v_body_468_; lean_object* v___x_469_; 
v_declName_465_ = lean_ctor_get(v_e_352_, 0);
v_type_466_ = lean_ctor_get(v_e_352_, 1);
v_value_467_ = lean_ctor_get(v_e_352_, 2);
v_body_468_ = lean_ctor_get(v_e_352_, 3);
lean_inc_ref(v_value_467_);
v___x_469_ = l_Lean_Meta_Grind_getAnchor(v_value_467_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
lean_inc_ref(v_type_466_);
v___x_471_ = l_Lean_Meta_Grind_getAnchor(v_type_466_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
lean_inc_ref(v_body_468_);
v___x_473_ = l_Lean_Meta_Grind_getAnchor(v_body_468_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
lean_inc(v_declName_465_);
v___x_475_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_465_);
v___x_476_ = lean_unbox_uint64(v_a_472_);
lean_dec(v_a_472_);
v___x_477_ = lean_unbox_uint64(v_a_474_);
lean_dec(v_a_474_);
v___x_478_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_476_, v___x_477_);
v___x_479_ = lean_unbox_uint64(v_a_470_);
lean_dec(v_a_470_);
v___x_480_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_479_, v___x_478_);
v___x_481_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_475_, v___x_480_);
v_a_364_ = v___x_481_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
else
{
lean_dec(v_a_472_);
lean_dec(v_a_470_);
lean_dec_ref(v_e_352_);
return v___x_473_;
}
}
else
{
lean_dec(v_a_470_);
lean_dec_ref(v_e_352_);
return v___x_471_;
}
}
else
{
lean_dec_ref(v_e_352_);
return v___x_469_;
}
}
case 9:
{
lean_object* v_a_482_; uint64_t v___x_483_; 
v_a_482_ = lean_ctor_get(v_e_352_, 0);
v___x_483_ = l_Lean_Literal_hash(v_a_482_);
v_a_364_ = v___x_483_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
case 10:
{
lean_object* v_expr_484_; lean_object* v___x_485_; 
v_expr_484_ = lean_ctor_get(v_e_352_, 1);
lean_inc_ref(v_expr_484_);
v___x_485_ = l_Lean_Meta_Grind_getAnchor(v_expr_484_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; uint64_t v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref(v___x_485_);
v___x_487_ = lean_unbox_uint64(v_a_486_);
lean_dec(v_a_486_);
v_a_364_ = v___x_487_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
else
{
lean_dec_ref(v_e_352_);
return v___x_485_;
}
}
case 11:
{
lean_object* v_idx_488_; lean_object* v_struct_489_; lean_object* v___x_490_; 
v_idx_488_ = lean_ctor_get(v_e_352_, 1);
v_struct_489_ = lean_ctor_get(v_e_352_, 2);
lean_inc_ref(v_struct_489_);
v___x_490_ = l_Lean_Meta_Grind_getAnchor(v_struct_489_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_uint64_of_nat(v_idx_488_);
v___x_493_ = lean_unbox_uint64(v_a_491_);
lean_dec(v_a_491_);
v___x_494_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_492_, v___x_493_);
v_a_364_ = v___x_494_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
else
{
lean_dec_ref(v_e_352_);
return v___x_490_;
}
}
default: 
{
uint64_t v___x_495_; 
v___x_495_ = 0ULL;
v_a_364_ = v___x_495_;
v___y_365_ = v_a_355_;
goto v___jp_363_;
}
}
}
v___jp_363_:
{
lean_object* v___x_366_; lean_object* v_congrThms_367_; lean_object* v_simp_368_; lean_object* v_lastTag_369_; lean_object* v_issues_370_; lean_object* v_counters_371_; lean_object* v_splitDiags_372_; lean_object* v_lawfulEqCmpMap_373_; lean_object* v_reflCmpMap_374_; lean_object* v_anchors_375_; lean_object* v_instanceMap_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_388_; 
v___x_366_ = lean_st_ref_take(v___y_365_);
v_congrThms_367_ = lean_ctor_get(v___x_366_, 0);
v_simp_368_ = lean_ctor_get(v___x_366_, 1);
v_lastTag_369_ = lean_ctor_get(v___x_366_, 2);
v_issues_370_ = lean_ctor_get(v___x_366_, 3);
v_counters_371_ = lean_ctor_get(v___x_366_, 4);
v_splitDiags_372_ = lean_ctor_get(v___x_366_, 5);
v_lawfulEqCmpMap_373_ = lean_ctor_get(v___x_366_, 6);
v_reflCmpMap_374_ = lean_ctor_get(v___x_366_, 7);
v_anchors_375_ = lean_ctor_get(v___x_366_, 8);
v_instanceMap_376_ = lean_ctor_get(v___x_366_, 9);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_388_ == 0)
{
v___x_378_ = v___x_366_;
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_instanceMap_376_);
lean_inc(v_anchors_375_);
lean_inc(v_reflCmpMap_374_);
lean_inc(v_lawfulEqCmpMap_373_);
lean_inc(v_splitDiags_372_);
lean_inc(v_counters_371_);
lean_inc(v_issues_370_);
lean_inc(v_lastTag_369_);
lean_inc(v_simp_368_);
lean_inc(v_congrThms_367_);
lean_dec(v___x_366_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = lean_box_uint64(v_a_364_);
v___x_381_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_anchors_375_, v_e_352_, v___x_380_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 8, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_congrThms_367_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_simp_368_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_lastTag_369_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v_issues_370_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v_counters_371_);
lean_ctor_set(v_reuseFailAlloc_387_, 5, v_splitDiags_372_);
lean_ctor_set(v_reuseFailAlloc_387_, 6, v_lawfulEqCmpMap_373_);
lean_ctor_set(v_reuseFailAlloc_387_, 7, v_reflCmpMap_374_);
lean_ctor_set(v_reuseFailAlloc_387_, 8, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_387_, 9, v_instanceMap_376_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_st_ref_set(v___y_365_, v___x_383_);
v___x_385_ = lean_box_uint64(v_a_364_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
v___jp_389_:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Grind_getAnchor(v_d_391_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
v___x_404_ = l_Lean_Meta_Grind_getAnchor(v_b_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref(v___x_404_);
v___x_406_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_390_);
v___x_407_ = lean_unbox_uint64(v_a_403_);
lean_dec(v_a_403_);
v___x_408_ = lean_unbox_uint64(v_a_405_);
lean_dec(v_a_405_);
v___x_409_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_407_, v___x_408_);
v___x_410_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_406_, v___x_409_);
v_a_364_ = v___x_410_;
v___y_365_ = v___y_395_;
goto v___jp_363_;
}
else
{
lean_dec(v_a_403_);
lean_dec(v_n_390_);
lean_dec_ref(v_e_352_);
return v___x_404_;
}
}
else
{
lean_dec_ref(v_b_392_);
lean_dec(v_n_390_);
lean_dec_ref(v_e_352_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_upperBound_496_, lean_object* v_args_497_, lean_object* v_pinfos_498_, lean_object* v_a_499_, uint64_t v_b_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
uint64_t v_a_512_; uint8_t v___x_516_; 
v___x_516_ = lean_nat_dec_lt(v_a_499_, v_upperBound_496_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_a_499_);
v___x_517_ = lean_box_uint64(v_b_500_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_array_fget_borrowed(v_args_497_, v_a_499_);
v___x_520_ = lean_array_get_size(v_pinfos_498_);
v___x_521_ = lean_nat_dec_lt(v_a_499_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_inc(v___x_519_);
v___x_522_ = l_Lean_Meta_Grind_getAnchor(v___x_519_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; uint64_t v___x_524_; uint64_t v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = lean_unbox_uint64(v_a_523_);
lean_dec(v_a_523_);
v___x_525_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_500_, v___x_524_);
v_a_512_ = v___x_525_;
goto v___jp_511_;
}
else
{
lean_dec(v_a_499_);
return v___x_522_;
}
}
else
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_array_fget_borrowed(v_pinfos_498_, v_a_499_);
v___x_527_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_inc(v___x_519_);
v___x_528_ = l_Lean_Meta_Grind_getAnchor(v___x_519_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; uint64_t v___x_530_; uint64_t v___x_531_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref(v___x_528_);
v___x_530_ = lean_unbox_uint64(v_a_529_);
lean_dec(v_a_529_);
v___x_531_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_500_, v___x_530_);
v_a_512_ = v___x_531_;
goto v___jp_511_;
}
else
{
lean_dec(v_a_499_);
return v___x_528_;
}
}
else
{
v_a_512_ = v_b_500_;
goto v___jp_511_;
}
}
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v_a_499_, v___x_513_);
lean_dec(v_a_499_);
v_a_499_ = v___x_514_;
v_b_500_ = v_a_512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg___boxed(lean_object* v_upperBound_532_, lean_object* v_args_533_, lean_object* v_pinfos_534_, lean_object* v_a_535_, lean_object* v_b_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
uint64_t v_b_boxed_547_; lean_object* v_res_548_; 
v_b_boxed_547_ = lean_unbox_uint64(v_b_536_);
lean_dec_ref(v_b_536_);
v_res_548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_532_, v_args_533_, v_pinfos_534_, v_a_535_, v_b_boxed_547_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v_pinfos_534_);
lean_dec_ref(v_args_533_);
lean_dec(v_upperBound_532_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_549_, v_x_550_, v_x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_Grind_getAnchor(v_e_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_upperBound_575_, lean_object* v_args_576_, lean_object* v_pinfos_577_, lean_object* v_inst_578_, lean_object* v_R_579_, lean_object* v_a_580_, uint64_t v_b_581_, lean_object* v_c_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_upperBound_575_, v_args_576_, v_pinfos_577_, v_a_580_, v_b_581_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_594_ = _args[0];
lean_object* v_args_595_ = _args[1];
lean_object* v_pinfos_596_ = _args[2];
lean_object* v_inst_597_ = _args[3];
lean_object* v_R_598_ = _args[4];
lean_object* v_a_599_ = _args[5];
lean_object* v_b_600_ = _args[6];
lean_object* v_c_601_ = _args[7];
lean_object* v___y_602_ = _args[8];
lean_object* v___y_603_ = _args[9];
lean_object* v___y_604_ = _args[10];
lean_object* v___y_605_ = _args[11];
lean_object* v___y_606_ = _args[12];
lean_object* v___y_607_ = _args[13];
lean_object* v___y_608_ = _args[14];
lean_object* v___y_609_ = _args[15];
lean_object* v___y_610_ = _args[16];
lean_object* v___y_611_ = _args[17];
_start:
{
uint64_t v_b_boxed_612_; lean_object* v_res_613_; 
v_b_boxed_612_ = lean_unbox_uint64(v_b_600_);
lean_dec_ref(v_b_600_);
v_res_613_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(v_upperBound_594_, v_args_595_, v_pinfos_596_, v_inst_597_, v_R_598_, v_a_599_, v_b_boxed_612_, v_c_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v_pinfos_596_);
lean_dec_ref(v_args_595_);
lean_dec(v_upperBound_594_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_x_615_, v_x_616_, v_x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_620_, v_x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_623_, v_x_624_, v_x_625_);
lean_dec_ref(v_x_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, size_t v_x_629_, size_t v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_628_, v_x_629_, v_x_630_, v_x_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(lean_object* v_00_u03b2_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
size_t v_x_35650__boxed_640_; size_t v_x_35651__boxed_641_; lean_object* v_res_642_; 
v_x_35650__boxed_640_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_x_35651__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(v_00_u03b2_634_, v_x_635_, v_x_35650__boxed_640_, v_x_35651__boxed_641_, v_x_638_, v_x_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_643_, lean_object* v_x_644_, size_t v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_644_, v_x_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_648_, lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
size_t v_x_35667__boxed_652_; lean_object* v_res_653_; 
v_x_35667__boxed_652_ = lean_unbox_usize(v_x_650_);
lean_dec(v_x_650_);
v_res_653_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_648_, v_x_649_, v_x_35667__boxed_652_, v_x_651_);
lean_dec_ref(v_x_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_654_, lean_object* v_n_655_, lean_object* v_k_656_, lean_object* v_v_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v_n_655_, v_k_656_, v_v_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_659_, size_t v_depth_660_, lean_object* v_keys_661_, lean_object* v_vals_662_, lean_object* v_heq_663_, lean_object* v_i_664_, lean_object* v_entries_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_660_, v_keys_661_, v_vals_662_, v_i_664_, v_entries_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_667_, lean_object* v_depth_668_, lean_object* v_keys_669_, lean_object* v_vals_670_, lean_object* v_heq_671_, lean_object* v_i_672_, lean_object* v_entries_673_){
_start:
{
size_t v_depth_boxed_674_; lean_object* v_res_675_; 
v_depth_boxed_674_ = lean_unbox_usize(v_depth_668_);
lean_dec(v_depth_668_);
v_res_675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(v_00_u03b2_667_, v_depth_boxed_674_, v_keys_669_, v_vals_670_, v_heq_671_, v_i_672_, v_entries_673_);
lean_dec_ref(v_vals_670_);
lean_dec_ref(v_keys_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_heq_679_, lean_object* v_i_680_, lean_object* v_k_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_677_, v_vals_678_, v_i_680_, v_k_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_683_, lean_object* v_keys_684_, lean_object* v_vals_685_, lean_object* v_heq_686_, lean_object* v_i_687_, lean_object* v_k_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_683_, v_keys_684_, v_vals_685_, v_heq_686_, v_i_687_, v_k_688_);
lean_dec_ref(v_k_688_);
lean_dec_ref(v_vals_685_);
lean_dec_ref(v_keys_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_x_691_, v_x_692_, v_x_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_696_, uint64_t v_anchor_697_){
_start:
{
lean_object* v_numDigits_698_; uint64_t v_anchorPrefix_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v_shift_704_; uint64_t v___x_705_; uint8_t v___x_706_; 
v_numDigits_698_ = lean_ctor_get(v_anchorRef_696_, 0);
v_anchorPrefix_699_ = lean_ctor_get_uint64(v_anchorRef_696_, sizeof(void*)*1);
v___x_700_ = 64ULL;
v___x_701_ = lean_uint64_of_nat(v_numDigits_698_);
v___x_702_ = 2ULL;
v___x_703_ = lean_uint64_shift_left(v___x_701_, v___x_702_);
v_shift_704_ = lean_uint64_sub(v___x_700_, v___x_703_);
v___x_705_ = lean_uint64_shift_right(v_anchor_697_, v_shift_704_);
v___x_706_ = lean_uint64_dec_eq(v_anchorPrefix_699_, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_707_, lean_object* v_anchor_708_){
_start:
{
uint64_t v_anchor_boxed_709_; uint8_t v_res_710_; lean_object* v_r_711_; 
v_anchor_boxed_709_ = lean_unbox_uint64(v_anchor_708_);
lean_dec_ref(v_anchor_708_);
v_res_710_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_707_, v_anchor_boxed_709_);
lean_dec_ref(v_anchorRef_707_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_712_; lean_object* v___f_713_; 
v___x_712_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_713_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_713_, 0, v___x_712_);
return v___f_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_734_, lean_object* v_shift_735_, lean_object* v___f_736_, lean_object* v___f_737_, lean_object* v___x_738_, lean_object* v_numDigits_739_, lean_object* v_es_740_, lean_object* v_a_741_, lean_object* v_x_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_734_, v_shift_735_, v___f_736_, v___f_737_, v___x_738_, v_numDigits_739_, v_es_740_, v_a_741_, v_x_742_, v___y_743_);
lean_dec(v_numDigits_739_);
lean_dec(v_shift_735_);
return v_res_744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = lean_unsigned_to_nat(16u);
v___x_747_ = lean_mk_array(v___x_746_, v___x_745_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_found_750_; 
v___x_748_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2);
v___x_749_ = lean_unsigned_to_nat(0u);
v_found_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_750_, 0, v___x_749_);
lean_ctor_set(v_found_750_, 1, v___x_748_);
return v_found_750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_found_751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_found_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_754_, lean_object* v_es_755_, lean_object* v_numDigits_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_757_ = lean_unsigned_to_nat(4u);
v___x_758_ = lean_nat_mul(v___x_757_, v_numDigits_756_);
v___x_759_ = lean_unsigned_to_nat(64u);
v___x_760_ = lean_nat_dec_lt(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v___x_758_);
lean_dec_ref(v_es_755_);
lean_dec_ref(v_inst_754_);
return v_numDigits_756_;
}
else
{
lean_object* v_shift_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___x_767_; size_t v_sz_768_; size_t v___x_769_; lean_object* v___x_770_; lean_object* v_fst_771_; 
v_shift_761_ = lean_nat_sub(v___x_759_, v___x_758_);
lean_dec(v___x_758_);
v___f_762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0);
v___f_763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1));
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13));
v___x_765_ = lean_box(0);
lean_inc_ref(v_es_755_);
lean_inc(v_numDigits_756_);
v___f_766_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_766_, 0, v_inst_754_);
lean_closure_set(v___f_766_, 1, v_shift_761_);
lean_closure_set(v___f_766_, 2, v___f_762_);
lean_closure_set(v___f_766_, 3, v___f_763_);
lean_closure_set(v___f_766_, 4, v___x_765_);
lean_closure_set(v___f_766_, 5, v_numDigits_756_);
lean_closure_set(v___f_766_, 6, v_es_755_);
v___x_767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_768_ = lean_array_size(v_es_755_);
v___x_769_ = ((size_t)0ULL);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_764_, v_es_755_, v___f_766_, v_sz_768_, v___x_769_, v___x_767_);
v_fst_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_fst_771_);
lean_dec(v___x_770_);
if (lean_obj_tag(v_fst_771_) == 0)
{
return v_numDigits_756_;
}
else
{
lean_object* v_val_772_; 
lean_dec(v_numDigits_756_);
v_val_772_ = lean_ctor_get(v_fst_771_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v_fst_771_);
return v_val_772_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_773_, lean_object* v_shift_774_, lean_object* v___f_775_, lean_object* v___f_776_, lean_object* v___x_777_, lean_object* v_numDigits_778_, lean_object* v_es_779_, lean_object* v_a_780_, lean_object* v_x_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_snd_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_808_; 
v_snd_783_ = lean_ctor_get(v___y_782_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v___y_782_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___y_782_, 0);
lean_dec(v_unused_809_);
v___x_785_ = v___y_782_;
v_isShared_786_ = v_isSharedCheck_808_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snd_783_);
lean_dec(v___y_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_808_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; uint64_t v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
lean_inc_ref(v_inst_773_);
v___x_787_ = lean_apply_1(v_inst_773_, v_a_780_);
v___x_788_ = lean_uint64_of_nat(v_shift_774_);
v___x_789_ = lean_unbox_uint64(v___x_787_);
lean_dec_ref(v___x_787_);
v___x_790_ = lean_uint64_shift_right(v___x_789_, v___x_788_);
v___x_791_ = lean_box_uint64(v___x_790_);
lean_inc_ref(v___f_776_);
lean_inc_ref(v___f_775_);
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_775_, v___f_776_, v_snd_783_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
lean_dec_ref(v_es_779_);
lean_dec_ref(v_inst_773_);
v___x_793_ = lean_box(0);
v___x_794_ = lean_box_uint64(v___x_790_);
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_775_, v___f_776_, v_snd_783_, v___x_794_, v___x_793_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_795_);
lean_ctor_set(v___x_785_, 0, v___x_777_);
v___x_797_ = v___x_785_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_799_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
lean_dec(v___x_777_);
lean_dec_ref(v___f_776_);
lean_dec_ref(v___f_775_);
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_nat_add(v_numDigits_778_, v___x_800_);
v___x_802_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_773_, v_es_779_, v___x_801_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_803_);
v___x_805_ = v___x_785_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_783_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_810_, lean_object* v_inst_811_, lean_object* v_es_812_, lean_object* v_numDigits_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_811_, v_es_812_, v_numDigits_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_815_, lean_object* v_h__1_816_, lean_object* v_h__2_817_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec(v_h__1_816_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_apply_1(v_h__2_817_, v___x_818_);
return v___x_819_;
}
else
{
lean_object* v_val_820_; lean_object* v___x_821_; 
lean_dec(v_h__2_817_);
v_val_820_ = lean_ctor_get(v_x_815_, 0);
lean_inc(v_val_820_);
lean_dec_ref(v_x_815_);
v___x_821_ = lean_apply_1(v_h__1_816_, v_val_820_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_822_, lean_object* v_motive_823_, lean_object* v_x_824_, lean_object* v_h__1_825_, lean_object* v_h__2_826_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v_h__1_825_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_apply_1(v_h__2_826_, v___x_827_);
return v___x_828_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_830_; 
lean_dec(v_h__2_826_);
v_val_829_ = lean_ctor_get(v_x_824_, 0);
lean_inc(v_val_829_);
lean_dec_ref(v_x_824_);
v___x_830_ = lean_apply_1(v_h__1_825_, v_val_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_831_, lean_object* v_es_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(4u);
v___x_834_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_831_, v_es_832_, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_835_, lean_object* v_inst_836_, lean_object* v_es_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_836_, v_es_837_);
return v___x_838_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_839_){
_start:
{
uint64_t v_anchor_840_; 
v_anchor_840_ = lean_ctor_get_uint64(v_e_839_, sizeof(void*)*1);
return v_anchor_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_841_){
_start:
{
uint64_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_841_);
lean_dec_ref(v_e_841_);
v_r_843_ = lean_box_uint64(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_859_, uint64_t v_anchorPrefix_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_ref_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_ref_863_ = lean_ctor_get(v_a_861_, 5);
v___x_864_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_865_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_859_, v_anchorPrefix_860_);
v___x_866_ = l_Lean_mkAtom(v___x_865_);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_mk_empty_array_with_capacity(v___x_867_);
v___x_869_ = lean_array_push(v___x_868_, v___x_866_);
v___x_870_ = lean_box(2);
v___x_871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_864_);
lean_ctor_set(v___x_871_, 2, v___x_869_);
v___x_872_ = 0;
v___x_873_ = l_Lean_SourceInfo_fromRef(v_ref_863_, v___x_872_);
v___x_874_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_875_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_873_);
v___x_876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_873_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_Syntax_node2(v___x_873_, v___x_874_, v___x_876_, v___x_871_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_879_, lean_object* v_anchorPrefix_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
uint64_t v_anchorPrefix_boxed_883_; lean_object* v_res_884_; 
v_anchorPrefix_boxed_883_ = lean_unbox_uint64(v_anchorPrefix_880_);
lean_dec_ref(v_anchorPrefix_880_);
v_res_884_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_879_, v_anchorPrefix_boxed_883_, v_a_881_);
lean_dec_ref(v_a_881_);
lean_dec(v_numDigits_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_885_, uint64_t v_anchorPrefix_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_885_, v_anchorPrefix_886_, v_a_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_891_, lean_object* v_anchorPrefix_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
uint64_t v_anchorPrefix_boxed_896_; lean_object* v_res_897_; 
v_anchorPrefix_boxed_896_ = lean_unbox_uint64(v_anchorPrefix_892_);
lean_dec_ref(v_anchorPrefix_892_);
v_res_897_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_891_, v_anchorPrefix_boxed_896_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_numDigits_891_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_898_, uint64_t v_anchor_899_, lean_object* v_a_900_){
_start:
{
uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v_anchorPrefix_907_; lean_object* v___x_908_; 
v___x_902_ = 64ULL;
v___x_903_ = lean_uint64_of_nat(v_numDigits_898_);
v___x_904_ = 2ULL;
v___x_905_ = lean_uint64_shift_left(v___x_903_, v___x_904_);
v___x_906_ = lean_uint64_sub(v___x_902_, v___x_905_);
v_anchorPrefix_907_ = lean_uint64_shift_right(v_anchor_899_, v___x_906_);
v___x_908_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_898_, v_anchorPrefix_907_, v_a_900_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_909_, lean_object* v_anchor_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
uint64_t v_anchor_boxed_913_; lean_object* v_res_914_; 
v_anchor_boxed_913_ = lean_unbox_uint64(v_anchor_910_);
lean_dec_ref(v_anchor_910_);
v_res_914_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_909_, v_anchor_boxed_913_, v_a_911_);
lean_dec_ref(v_a_911_);
lean_dec(v_numDigits_909_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_915_, uint64_t v_anchor_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_915_, v_anchor_916_, v_a_917_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_921_, lean_object* v_anchor_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
uint64_t v_anchor_boxed_926_; lean_object* v_res_927_; 
v_anchor_boxed_926_ = lean_unbox_uint64(v_anchor_922_);
lean_dec_ref(v_anchor_922_);
v_res_927_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_921_, v_anchor_boxed_926_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_numDigits_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_928_);
v___x_940_ = l_Lean_Meta_Grind_getAnchor(v___x_939_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_s_941_);
return v_res_952_;
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

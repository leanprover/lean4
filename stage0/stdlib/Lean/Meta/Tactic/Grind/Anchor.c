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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInaccessibleUserName(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_isHiddenName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_isHiddenName___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_isHiddenName(lean_object* v_n_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Lean_Name_hasMacroScopes(v_n_19_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = l_Lean_Name_isInaccessibleUserName(v_n_19_);
return v___x_21_;
}
else
{
lean_dec(v_n_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_isHiddenName___boxed(lean_object* v_n_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_isHiddenName(v_n_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(uint64_t v_a_25_, uint64_t v_b_26_){
_start:
{
uint64_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 0ULL;
v___x_28_ = lean_uint64_dec_eq(v_a_25_, v___x_27_);
if (v___x_28_ == 0)
{
uint8_t v___x_29_; 
v___x_29_ = lean_uint64_dec_eq(v_b_26_, v___x_27_);
if (v___x_29_ == 0)
{
uint64_t v___x_30_; 
v___x_30_ = lean_uint64_mix_hash(v_a_25_, v_b_26_);
return v___x_30_;
}
else
{
return v_a_25_;
}
}
else
{
return v_b_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
uint64_t v_a_boxed_33_; uint64_t v_b_boxed_34_; uint64_t v_res_35_; lean_object* v_r_36_; 
v_a_boxed_33_ = lean_unbox_uint64(v_a_31_);
lean_dec_ref(v_a_31_);
v_b_boxed_34_ = lean_unbox_uint64(v_b_32_);
lean_dec_ref(v_b_32_);
v_res_35_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_a_boxed_33_, v_b_boxed_34_);
v_r_36_ = lean_box_uint64(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(lean_object* v_decl_37_, lean_object* v_baseName_38_, lean_object* v_as_39_, size_t v_i_40_, size_t v_stop_41_, lean_object* v_b_42_){
_start:
{
lean_object* v___y_44_; uint8_t v___x_48_; 
v___x_48_ = lean_usize_dec_eq(v_i_40_, v_stop_41_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
v___x_49_ = lean_array_uget_borrowed(v_as_39_, v_i_40_);
if (lean_obj_tag(v___x_49_) == 0)
{
v___y_44_ = v_b_42_;
goto v___jp_43_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_val_50_ = lean_ctor_get(v___x_49_, 0);
v___x_51_ = l_Lean_LocalDecl_index(v_val_50_);
v___x_52_ = l_Lean_LocalDecl_index(v_decl_37_);
v___x_53_ = lean_nat_dec_lt(v___x_51_, v___x_52_);
lean_dec(v___x_52_);
lean_dec(v___x_51_);
if (v___x_53_ == 0)
{
v___y_44_ = v_b_42_;
goto v___jp_43_;
}
else
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = l_Lean_LocalDecl_userName(v_val_50_);
lean_inc(v___x_54_);
v___x_55_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_isHiddenName(v___x_54_);
if (v___x_55_ == 0)
{
lean_dec(v___x_54_);
v___y_44_ = v_b_42_;
goto v___jp_43_;
}
else
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = l_Lean_Name_eraseMacroScopes(v___x_54_);
lean_dec(v___x_54_);
v___x_57_ = lean_name_eq(v___x_56_, v_baseName_38_);
lean_dec(v___x_56_);
if (v___x_57_ == 0)
{
v___y_44_ = v_b_42_;
goto v___jp_43_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_b_42_, v___x_58_);
lean_dec(v_b_42_);
v___y_44_ = v___x_59_;
goto v___jp_43_;
}
}
}
}
}
else
{
return v_b_42_;
}
v___jp_43_:
{
size_t v___x_45_; size_t v___x_46_; 
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_add(v_i_40_, v___x_45_);
v_i_40_ = v___x_46_;
v_b_42_ = v___y_44_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2___boxed(lean_object* v_decl_60_, lean_object* v_baseName_61_, lean_object* v_as_62_, lean_object* v_i_63_, lean_object* v_stop_64_, lean_object* v_b_65_){
_start:
{
size_t v_i_boxed_66_; size_t v_stop_boxed_67_; lean_object* v_res_68_; 
v_i_boxed_66_ = lean_unbox_usize(v_i_63_);
lean_dec(v_i_63_);
v_stop_boxed_67_ = lean_unbox_usize(v_stop_64_);
lean_dec(v_stop_64_);
v_res_68_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(v_decl_60_, v_baseName_61_, v_as_62_, v_i_boxed_66_, v_stop_boxed_67_, v_b_65_);
lean_dec_ref(v_as_62_);
lean_dec(v_baseName_61_);
lean_dec_ref(v_decl_60_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__3(lean_object* v_decl_69_, lean_object* v_baseName_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
lean_object* v_cs_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_cs_73_ = lean_ctor_get(v_x_71_, 0);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_array_get_size(v_cs_73_);
v___x_76_ = lean_nat_dec_lt(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
return v_x_72_;
}
else
{
size_t v___x_77_; size_t v___x_78_; lean_object* v___x_79_; 
v___x_77_ = ((size_t)0ULL);
v___x_78_ = lean_usize_of_nat(v___x_75_);
v___x_79_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1_spec__2(v_decl_69_, v_baseName_70_, v_cs_73_, v___x_77_, v___x_78_, v_x_72_);
return v___x_79_;
}
}
else
{
lean_object* v_vs_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_vs_80_ = lean_ctor_get(v_x_71_, 0);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_array_get_size(v_vs_80_);
v___x_83_ = lean_nat_dec_lt(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
return v_x_72_;
}
else
{
size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((size_t)0ULL);
v___x_85_ = lean_usize_of_nat(v___x_82_);
v___x_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(v_decl_69_, v_baseName_70_, v_vs_80_, v___x_84_, v___x_85_, v_x_72_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_decl_87_, lean_object* v_baseName_88_, lean_object* v_as_89_, size_t v_i_90_, size_t v_stop_91_, lean_object* v_b_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_usize_dec_eq(v_i_90_, v_stop_91_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; size_t v___x_96_; size_t v___x_97_; 
v___x_94_ = lean_array_uget_borrowed(v_as_89_, v_i_90_);
v___x_95_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__3(v_decl_87_, v_baseName_88_, v___x_94_, v_b_92_);
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_add(v_i_90_, v___x_96_);
v_i_90_ = v___x_97_;
v_b_92_ = v___x_95_;
goto _start;
}
else
{
return v_b_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_decl_99_, lean_object* v_baseName_100_, lean_object* v_as_101_, lean_object* v_i_102_, lean_object* v_stop_103_, lean_object* v_b_104_){
_start:
{
size_t v_i_boxed_105_; size_t v_stop_boxed_106_; lean_object* v_res_107_; 
v_i_boxed_105_ = lean_unbox_usize(v_i_102_);
lean_dec(v_i_102_);
v_stop_boxed_106_ = lean_unbox_usize(v_stop_103_);
lean_dec(v_stop_103_);
v_res_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1_spec__2(v_decl_99_, v_baseName_100_, v_as_101_, v_i_boxed_105_, v_stop_boxed_106_, v_b_104_);
lean_dec_ref(v_as_101_);
lean_dec(v_baseName_100_);
lean_dec_ref(v_decl_99_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__3___boxed(lean_object* v_decl_108_, lean_object* v_baseName_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__3(v_decl_108_, v_baseName_109_, v_x_110_, v_x_111_);
lean_dec_ref(v_x_110_);
lean_dec(v_baseName_109_);
lean_dec_ref(v_decl_108_);
return v_res_112_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1(lean_object* v_decl_114_, lean_object* v_baseName_115_, lean_object* v_x_116_, size_t v_x_117_, size_t v_x_118_, lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v_cs_120_; lean_object* v___x_121_; size_t v___x_122_; lean_object* v_j_123_; lean_object* v___x_124_; size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_cs_120_ = lean_ctor_get(v_x_116_, 0);
v___x_121_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___closed__0);
v___x_122_ = lean_usize_shift_right(v_x_117_, v_x_118_);
v_j_123_ = lean_usize_to_nat(v___x_122_);
v___x_124_ = lean_array_get_borrowed(v___x_121_, v_cs_120_, v_j_123_);
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_shift_left(v___x_125_, v_x_118_);
v___x_127_ = lean_usize_sub(v___x_126_, v___x_125_);
v___x_128_ = lean_usize_land(v_x_117_, v___x_127_);
v___x_129_ = ((size_t)5ULL);
v___x_130_ = lean_usize_sub(v_x_118_, v___x_129_);
v___x_131_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1(v_decl_114_, v_baseName_115_, v___x_124_, v___x_128_, v___x_130_, v_x_119_);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_j_123_, v___x_132_);
lean_dec(v_j_123_);
v___x_134_ = lean_array_get_size(v_cs_120_);
v___x_135_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v___x_133_);
return v___x_131_;
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_usize_of_nat(v___x_133_);
lean_dec(v___x_133_);
v___x_137_ = lean_usize_of_nat(v___x_134_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1_spec__2(v_decl_114_, v_baseName_115_, v_cs_120_, v___x_136_, v___x_137_, v___x_131_);
return v___x_138_;
}
}
else
{
lean_object* v_vs_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_vs_139_ = lean_ctor_get(v_x_116_, 0);
v___x_140_ = lean_usize_to_nat(v_x_117_);
v___x_141_ = lean_array_get_size(v_vs_139_);
v___x_142_ = lean_nat_dec_lt(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec(v___x_140_);
return v_x_119_;
}
else
{
size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_usize_of_nat(v___x_140_);
lean_dec(v___x_140_);
v___x_144_ = lean_usize_of_nat(v___x_141_);
v___x_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(v_decl_114_, v_baseName_115_, v_vs_139_, v___x_143_, v___x_144_, v_x_119_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1___boxed(lean_object* v_decl_146_, lean_object* v_baseName_147_, lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
size_t v_x_1640__boxed_152_; size_t v_x_1641__boxed_153_; lean_object* v_res_154_; 
v_x_1640__boxed_152_ = lean_unbox_usize(v_x_149_);
lean_dec(v_x_149_);
v_x_1641__boxed_153_ = lean_unbox_usize(v_x_150_);
lean_dec(v_x_150_);
v_res_154_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1(v_decl_146_, v_baseName_147_, v_x_148_, v_x_1640__boxed_152_, v_x_1641__boxed_153_, v_x_151_);
lean_dec_ref(v_x_148_);
lean_dec(v_baseName_147_);
lean_dec_ref(v_decl_146_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0(lean_object* v_decl_155_, lean_object* v_baseName_156_, lean_object* v_t_157_, lean_object* v_init_158_, lean_object* v_start_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_nat_dec_eq(v_start_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v_root_162_; lean_object* v_tail_163_; size_t v_shift_164_; lean_object* v_tailOff_165_; uint8_t v___x_166_; 
v_root_162_ = lean_ctor_get(v_t_157_, 0);
v_tail_163_ = lean_ctor_get(v_t_157_, 1);
v_shift_164_ = lean_ctor_get_usize(v_t_157_, 4);
v_tailOff_165_ = lean_ctor_get(v_t_157_, 3);
v___x_166_ = lean_nat_dec_le(v_tailOff_165_, v_start_159_);
if (v___x_166_ == 0)
{
size_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_167_ = lean_usize_of_nat(v_start_159_);
v___x_168_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__1(v_decl_155_, v_baseName_156_, v_root_162_, v___x_167_, v_shift_164_, v_init_158_);
v___x_169_ = lean_array_get_size(v_tail_163_);
v___x_170_ = lean_nat_dec_lt(v___x_160_, v___x_169_);
if (v___x_170_ == 0)
{
return v___x_168_;
}
else
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; 
v___x_171_ = ((size_t)0ULL);
v___x_172_ = lean_usize_of_nat(v___x_169_);
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(v_decl_155_, v_baseName_156_, v_tail_163_, v___x_171_, v___x_172_, v___x_168_);
return v___x_173_;
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = lean_nat_sub(v_start_159_, v_tailOff_165_);
v___x_175_ = lean_array_get_size(v_tail_163_);
v___x_176_ = lean_nat_dec_lt(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec(v___x_174_);
return v_init_158_;
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_usize_of_nat(v___x_174_);
lean_dec(v___x_174_);
v___x_178_ = lean_usize_of_nat(v___x_175_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(v_decl_155_, v_baseName_156_, v_tail_163_, v___x_177_, v___x_178_, v_init_158_);
return v___x_179_;
}
}
}
else
{
lean_object* v_root_180_; lean_object* v_tail_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_root_180_ = lean_ctor_get(v_t_157_, 0);
v_tail_181_ = lean_ctor_get(v_t_157_, 1);
v___x_182_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__3(v_decl_155_, v_baseName_156_, v_root_180_, v_init_158_);
v___x_183_ = lean_array_get_size(v_tail_181_);
v___x_184_ = lean_nat_dec_lt(v___x_160_, v___x_183_);
if (v___x_184_ == 0)
{
return v___x_182_;
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_183_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0_spec__2(v_decl_155_, v_baseName_156_, v_tail_181_, v___x_185_, v___x_186_, v___x_182_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0___boxed(lean_object* v_decl_188_, lean_object* v_baseName_189_, lean_object* v_t_190_, lean_object* v_init_191_, lean_object* v_start_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0(v_decl_188_, v_baseName_189_, v_t_190_, v_init_191_, v_start_192_);
lean_dec(v_start_192_);
lean_dec_ref(v_t_190_);
lean_dec(v_baseName_189_);
lean_dec_ref(v_decl_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0(lean_object* v_decl_194_, lean_object* v_baseName_195_, lean_object* v_lctx_196_, lean_object* v_init_197_, lean_object* v_start_198_){
_start:
{
lean_object* v_decls_199_; lean_object* v___x_200_; 
v_decls_199_ = lean_ctor_get(v_lctx_196_, 1);
v___x_200_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0_spec__0(v_decl_194_, v_baseName_195_, v_decls_199_, v_init_197_, v_start_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0___boxed(lean_object* v_decl_201_, lean_object* v_baseName_202_, lean_object* v_lctx_203_, lean_object* v_init_204_, lean_object* v_start_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0(v_decl_201_, v_baseName_202_, v_lctx_203_, v_init_204_, v_start_205_);
lean_dec(v_start_205_);
lean_dec_ref(v_lctx_203_);
lean_dec(v_baseName_202_);
lean_dec_ref(v_decl_201_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___redArg(lean_object* v_decl_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_lctx_210_; lean_object* v___x_211_; lean_object* v_baseName_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint64_t v___y_216_; 
v_lctx_210_ = lean_ctor_get(v_a_208_, 2);
v___x_211_ = l_Lean_LocalDecl_userName(v_decl_207_);
v_baseName_212_ = l_Lean_Name_eraseMacroScopes(v___x_211_);
lean_dec(v___x_211_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar_spec__0(v_decl_207_, v_baseName_212_, v_lctx_210_, v___x_213_, v___x_213_);
if (lean_obj_tag(v_baseName_212_) == 0)
{
uint64_t v___x_221_; 
v___x_221_ = 1723ULL;
v___y_216_ = v___x_221_;
goto v___jp_215_;
}
else
{
uint64_t v_hash_222_; 
v_hash_222_ = lean_ctor_get_uint64(v_baseName_212_, sizeof(void*)*2);
lean_dec(v_baseName_212_);
v___y_216_ = v_hash_222_;
goto v___jp_215_;
}
v___jp_215_:
{
uint64_t v___x_217_; uint64_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_217_ = lean_uint64_of_nat(v___x_214_);
lean_dec(v___x_214_);
v___x_218_ = lean_uint64_mix_hash(v___y_216_, v___x_217_);
v___x_219_ = lean_box_uint64(v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___redArg___boxed(lean_object* v_decl_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___redArg(v_decl_223_, v_a_224_);
lean_dec_ref(v_a_224_);
lean_dec_ref(v_decl_223_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar(lean_object* v_decl_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___redArg(v_decl_227_, v_a_228_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___boxed(lean_object* v_decl_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar(v_decl_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_decl_234_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(lean_object* v_declName_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v_env_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_244_ = lean_st_ref_get(v___y_242_);
v_env_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc_ref(v_env_245_);
lean_dec(v___x_244_);
v___x_246_ = l_Lean_Meta_isMatcherCore(v_env_245_, v_declName_241_);
v___x_247_ = lean_box(v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(lean_object* v_declName_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_249_, v___y_250_);
lean_dec(v___y_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(lean_object* v_declName_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_253_, v___y_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(lean_object* v_declName_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(v_declName_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(lean_object* v_keys_277_, lean_object* v_vals_278_, lean_object* v_i_279_, lean_object* v_k_280_){
_start:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_array_get_size(v_keys_277_);
v___x_282_ = lean_nat_dec_lt(v_i_279_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
lean_dec(v_i_279_);
v___x_283_ = lean_box(0);
return v___x_283_;
}
else
{
lean_object* v_k_x27_284_; size_t v___x_285_; size_t v___x_286_; uint8_t v___x_287_; 
v_k_x27_284_ = lean_array_fget_borrowed(v_keys_277_, v_i_279_);
v___x_285_ = lean_ptr_addr(v_k_280_);
v___x_286_ = lean_ptr_addr(v_k_x27_284_);
v___x_287_ = lean_usize_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_i_279_, v___x_288_);
lean_dec(v_i_279_);
v_i_279_ = v___x_289_;
goto _start;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_array_fget_borrowed(v_vals_278_, v_i_279_);
lean_dec(v_i_279_);
lean_inc(v___x_291_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_keys_293_, lean_object* v_vals_294_, lean_object* v_i_295_, lean_object* v_k_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_293_, v_vals_294_, v_i_295_, v_k_296_);
lean_dec_ref(v_k_296_);
lean_dec_ref(v_vals_294_);
lean_dec_ref(v_keys_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(lean_object* v_x_298_, size_t v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v_es_301_; lean_object* v___x_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v_j_305_; lean_object* v___x_306_; 
v_es_301_ = lean_ctor_get(v_x_298_, 0);
v___x_302_ = lean_box(2);
v___x_303_ = ((size_t)31ULL);
v___x_304_ = lean_usize_land(v_x_299_, v___x_303_);
v_j_305_ = lean_usize_to_nat(v___x_304_);
v___x_306_ = lean_array_get_borrowed(v___x_302_, v_es_301_, v_j_305_);
lean_dec(v_j_305_);
switch(lean_obj_tag(v___x_306_))
{
case 0:
{
lean_object* v_key_307_; lean_object* v_val_308_; size_t v___x_309_; size_t v___x_310_; uint8_t v___x_311_; 
v_key_307_ = lean_ctor_get(v___x_306_, 0);
v_val_308_ = lean_ctor_get(v___x_306_, 1);
v___x_309_ = lean_ptr_addr(v_x_300_);
v___x_310_ = lean_ptr_addr(v_key_307_);
v___x_311_ = lean_usize_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_box(0);
return v___x_312_;
}
else
{
lean_object* v___x_313_; 
lean_inc(v_val_308_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_val_308_);
return v___x_313_;
}
}
case 1:
{
lean_object* v_node_314_; size_t v___x_315_; size_t v___x_316_; 
v_node_314_ = lean_ctor_get(v___x_306_, 0);
v___x_315_ = ((size_t)5ULL);
v___x_316_ = lean_usize_shift_right(v_x_299_, v___x_315_);
v_x_298_ = v_node_314_;
v_x_299_ = v___x_316_;
goto _start;
}
default: 
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
}
else
{
lean_object* v_ks_319_; lean_object* v_vs_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_ks_319_ = lean_ctor_get(v_x_298_, 0);
v_vs_320_ = lean_ctor_get(v_x_298_, 1);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_319_, v_vs_320_, v___x_321_, v_x_300_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
size_t v_x_33808__boxed_326_; lean_object* v_res_327_; 
v_x_33808__boxed_326_ = lean_unbox_usize(v_x_324_);
lean_dec(v_x_324_);
v_res_327_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_323_, v_x_33808__boxed_326_, v_x_325_);
lean_dec_ref(v_x_325_);
lean_dec_ref(v_x_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; uint64_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v___x_330_ = lean_ptr_addr(v_x_329_);
v___x_331_ = ((size_t)3ULL);
v___x_332_ = lean_usize_shift_right(v___x_330_, v___x_331_);
v___x_333_ = lean_usize_to_uint64(v___x_332_);
v___x_334_ = lean_uint64_to_usize(v___x_333_);
v___x_335_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_328_, v___x_334_, v_x_329_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_336_, v_x_337_);
lean_dec_ref(v_x_337_);
lean_dec_ref(v_x_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_ks_343_; lean_object* v_vs_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_370_; 
v_ks_343_ = lean_ctor_get(v_x_339_, 0);
v_vs_344_ = lean_ctor_get(v_x_339_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_370_ == 0)
{
v___x_346_ = v_x_339_;
v_isShared_347_ = v_isSharedCheck_370_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_vs_344_);
lean_inc(v_ks_343_);
lean_dec(v_x_339_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_370_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_get_size(v_ks_343_);
v___x_349_ = lean_nat_dec_lt(v_x_340_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec(v_x_340_);
v___x_350_ = lean_array_push(v_ks_343_, v_x_341_);
v___x_351_ = lean_array_push(v_vs_344_, v_x_342_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_351_);
lean_ctor_set(v___x_346_, 0, v___x_350_);
v___x_353_ = v___x_346_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v_k_x27_355_; size_t v___x_356_; size_t v___x_357_; uint8_t v___x_358_; 
v_k_x27_355_ = lean_array_fget_borrowed(v_ks_343_, v_x_340_);
v___x_356_ = lean_ptr_addr(v_x_341_);
v___x_357_ = lean_ptr_addr(v_k_x27_355_);
v___x_358_ = lean_usize_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_360_; 
if (v_isShared_347_ == 0)
{
v___x_360_ = v___x_346_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_ks_343_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_vs_344_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_add(v_x_340_, v___x_361_);
lean_dec(v_x_340_);
v_x_339_ = v___x_360_;
v_x_340_ = v___x_362_;
goto _start;
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_array_fset(v_ks_343_, v_x_340_, v_x_341_);
v___x_366_ = lean_array_fset(v_vs_344_, v_x_340_, v_x_342_);
lean_dec(v_x_340_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_366_);
lean_ctor_set(v___x_346_, 0, v___x_365_);
v___x_368_ = v___x_346_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(lean_object* v_n_371_, lean_object* v_k_372_, lean_object* v_v_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(v_n_371_, v___x_374_, v_k_372_, v_v_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(lean_object* v_x_377_, size_t v_x_378_, size_t v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v_es_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v_j_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_es_382_ = lean_ctor_get(v_x_377_, 0);
v___x_383_ = ((size_t)31ULL);
v___x_384_ = lean_usize_land(v_x_378_, v___x_383_);
v_j_385_ = lean_usize_to_nat(v___x_384_);
v___x_386_ = lean_array_get_size(v_es_382_);
v___x_387_ = lean_nat_dec_lt(v_j_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_dec(v_j_385_);
lean_dec(v_x_381_);
lean_dec_ref(v_x_380_);
return v_x_377_;
}
else
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_428_; 
lean_inc_ref(v_es_382_);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v_x_377_, 0);
lean_dec(v_unused_429_);
v___x_389_ = v_x_377_;
v_isShared_390_ = v_isSharedCheck_428_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_x_377_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_428_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_v_391_; lean_object* v___x_392_; lean_object* v_xs_x27_393_; lean_object* v___y_395_; 
v_v_391_ = lean_array_fget(v_es_382_, v_j_385_);
v___x_392_ = lean_box(0);
v_xs_x27_393_ = lean_array_fset(v_es_382_, v_j_385_, v___x_392_);
switch(lean_obj_tag(v_v_391_))
{
case 0:
{
lean_object* v_key_400_; lean_object* v_val_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_413_; 
v_key_400_ = lean_ctor_get(v_v_391_, 0);
v_val_401_ = lean_ctor_get(v_v_391_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_v_391_);
if (v_isSharedCheck_413_ == 0)
{
v___x_403_ = v_v_391_;
v_isShared_404_ = v_isSharedCheck_413_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_val_401_);
lean_inc(v_key_400_);
lean_dec(v_v_391_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_413_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
size_t v___x_405_; size_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_ptr_addr(v_x_380_);
v___x_406_ = lean_ptr_addr(v_key_400_);
v___x_407_ = lean_usize_dec_eq(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_del_object(v___x_403_);
v___x_408_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_400_, v_val_401_, v_x_380_, v_x_381_);
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
v___y_395_ = v___x_409_;
goto v___jp_394_;
}
else
{
lean_object* v___x_411_; 
lean_dec(v_val_401_);
lean_dec(v_key_400_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_x_381_);
lean_ctor_set(v___x_403_, 0, v_x_380_);
v___x_411_ = v___x_403_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_x_380_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_x_381_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
v___y_395_ = v___x_411_;
goto v___jp_394_;
}
}
}
}
case 1:
{
lean_object* v_node_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_426_; 
v_node_414_ = lean_ctor_get(v_v_391_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_v_391_);
if (v_isSharedCheck_426_ == 0)
{
v___x_416_ = v_v_391_;
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_node_414_);
lean_dec(v_v_391_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_418_ = ((size_t)5ULL);
v___x_419_ = lean_usize_shift_right(v_x_378_, v___x_418_);
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_add(v_x_379_, v___x_420_);
v___x_422_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_node_414_, v___x_419_, v___x_421_, v_x_380_, v_x_381_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_422_);
v___x_424_ = v___x_416_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
v___y_395_ = v___x_424_;
goto v___jp_394_;
}
}
}
default: 
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_x_380_);
lean_ctor_set(v___x_427_, 1, v_x_381_);
v___y_395_ = v___x_427_;
goto v___jp_394_;
}
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_array_fset(v_xs_x27_393_, v_j_385_, v___y_395_);
lean_dec(v_j_385_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_396_);
v___x_398_ = v___x_389_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
else
{
lean_object* v_ks_430_; lean_object* v_vs_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_449_; 
v_ks_430_ = lean_ctor_get(v_x_377_, 0);
v_vs_431_ = lean_ctor_get(v_x_377_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_449_ == 0)
{
v___x_433_ = v_x_377_;
v_isShared_434_ = v_isSharedCheck_449_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_vs_431_);
lean_inc(v_ks_430_);
lean_dec(v_x_377_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_449_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_ks_430_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_vs_431_);
v___x_436_ = v_reuseFailAlloc_448_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v_newNode_437_; size_t v___x_438_; uint8_t v___x_439_; 
v_newNode_437_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(v___x_436_, v_x_380_, v_x_381_);
v___x_438_ = ((size_t)7ULL);
v___x_439_ = lean_usize_dec_le(v___x_438_, v_x_379_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_437_);
v___x_441_ = lean_unsigned_to_nat(4u);
v___x_442_ = lean_nat_dec_lt(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
if (v___x_442_ == 0)
{
lean_object* v_ks_443_; lean_object* v_vs_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_ks_443_ = lean_ctor_get(v_newNode_437_, 0);
lean_inc_ref(v_ks_443_);
v_vs_444_ = lean_ctor_get(v_newNode_437_, 1);
lean_inc_ref(v_vs_444_);
lean_dec_ref(v_newNode_437_);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___closed__0);
v___x_447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_x_379_, v_ks_443_, v_vs_444_, v___x_445_, v___x_446_);
lean_dec_ref(v_vs_444_);
lean_dec_ref(v_ks_443_);
return v___x_447_;
}
else
{
return v_newNode_437_;
}
}
else
{
return v_newNode_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(size_t v_depth_450_, lean_object* v_keys_451_, lean_object* v_vals_452_, lean_object* v_i_453_, lean_object* v_entries_454_){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_keys_451_);
v___x_456_ = lean_nat_dec_lt(v_i_453_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec(v_i_453_);
return v_entries_454_;
}
else
{
lean_object* v_k_457_; lean_object* v_v_458_; size_t v___x_459_; size_t v___x_460_; size_t v___x_461_; uint64_t v___x_462_; size_t v_h_463_; size_t v___x_464_; lean_object* v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v_h_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_k_457_ = lean_array_fget_borrowed(v_keys_451_, v_i_453_);
v_v_458_ = lean_array_fget_borrowed(v_vals_452_, v_i_453_);
v___x_459_ = lean_ptr_addr(v_k_457_);
v___x_460_ = ((size_t)3ULL);
v___x_461_ = lean_usize_shift_right(v___x_459_, v___x_460_);
v___x_462_ = lean_usize_to_uint64(v___x_461_);
v_h_463_ = lean_uint64_to_usize(v___x_462_);
v___x_464_ = ((size_t)5ULL);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_sub(v_depth_450_, v___x_466_);
v___x_468_ = lean_usize_mul(v___x_464_, v___x_467_);
v_h_469_ = lean_usize_shift_right(v_h_463_, v___x_468_);
v___x_470_ = lean_nat_add(v_i_453_, v___x_465_);
lean_dec(v_i_453_);
lean_inc(v_v_458_);
lean_inc(v_k_457_);
v___x_471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_entries_454_, v_h_469_, v_depth_450_, v_k_457_, v_v_458_);
v_i_453_ = v___x_470_;
v_entries_454_ = v___x_471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_i_476_, lean_object* v_entries_477_){
_start:
{
size_t v_depth_boxed_478_; lean_object* v_res_479_; 
v_depth_boxed_478_ = lean_unbox_usize(v_depth_473_);
lean_dec(v_depth_473_);
v_res_479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_depth_boxed_478_, v_keys_474_, v_vals_475_, v_i_476_, v_entries_477_);
lean_dec_ref(v_vals_475_);
lean_dec_ref(v_keys_474_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg___boxed(lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
size_t v_x_33960__boxed_485_; size_t v_x_33961__boxed_486_; lean_object* v_res_487_; 
v_x_33960__boxed_485_ = lean_unbox_usize(v_x_481_);
lean_dec(v_x_481_);
v_x_33961__boxed_486_ = lean_unbox_usize(v_x_482_);
lean_dec(v_x_482_);
v_res_487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_480_, v_x_33960__boxed_485_, v_x_33961__boxed_486_, v_x_483_, v_x_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; uint64_t v___x_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v___x_491_ = lean_ptr_addr(v_x_489_);
v___x_492_ = ((size_t)3ULL);
v___x_493_ = lean_usize_shift_right(v___x_491_, v___x_492_);
v___x_494_ = lean_usize_to_uint64(v___x_493_);
v___x_495_ = lean_uint64_to_usize(v___x_494_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_488_, v___x_495_, v___x_496_, v_x_489_, v_x_490_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAnchor___closed__0(void){
_start:
{
lean_object* v___x_498_; lean_object* v_dummy_499_; 
v___x_498_ = lean_box(0);
v_dummy_499_ = l_Lean_Expr_sort___override(v___x_498_);
return v_dummy_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_pinfos_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; 
if (lean_obj_tag(v_x_502_) == 5)
{
lean_object* v_fn_547_; lean_object* v_arg_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_fn_547_ = lean_ctor_get(v_x_502_, 0);
lean_inc_ref(v_fn_547_);
v_arg_548_ = lean_ctor_get(v_x_502_, 1);
lean_inc_ref(v_arg_548_);
lean_dec_ref_known(v_x_502_, 2);
v___x_549_ = lean_array_set(v_x_503_, v_x_504_, v_arg_548_);
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_sub(v_x_504_, v___x_550_);
lean_dec(v_x_504_);
v_x_502_ = v_fn_547_;
v_x_503_ = v___x_549_;
v_x_504_ = v___x_551_;
goto _start;
}
else
{
uint8_t v___x_553_; 
lean_dec(v_x_504_);
v___x_553_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_502_);
if (v___x_553_ == 0)
{
goto v___jp_532_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_array_get_size(v_x_503_);
v___x_555_ = lean_unsigned_to_nat(2u);
v___x_556_ = lean_nat_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
goto v___jp_532_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec_ref(v_x_502_);
v___x_557_ = l_Lean_instInhabitedExpr;
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_array_get(v___x_557_, v_x_503_, v___x_558_);
lean_dec_ref(v_x_503_);
v___x_560_ = l_Lean_Meta_Grind_getAnchor(v___x_559_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
return v___x_560_;
}
}
}
v___jp_515_:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_Grind_getAnchor(v_x_502_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint64_t v___x_530_; lean_object* v___x_531_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = lean_array_get_size(v_x_503_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_unbox_uint64(v_a_527_);
lean_dec(v_a_527_);
v___x_531_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v___x_528_, v_x_503_, v_pinfos_516_, v___x_529_, v___x_530_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec_ref(v_pinfos_516_);
lean_dec_ref(v_x_503_);
return v___x_531_;
}
else
{
lean_dec_ref(v_pinfos_516_);
lean_dec_ref(v_x_503_);
return v___x_526_;
}
}
v___jp_532_:
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Expr_hasLooseBVars(v_x_502_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_box(0);
lean_inc_ref(v_x_502_);
v___x_535_ = l_Lean_Meta_getFunInfo(v_x_502_, v___x_534_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_paramInfo_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v_paramInfo_537_ = lean_ctor_get(v_a_536_, 0);
lean_inc_ref(v_paramInfo_537_);
lean_dec(v_a_536_);
v_pinfos_516_ = v_paramInfo_537_;
v___y_517_ = v___y_505_;
v___y_518_ = v___y_506_;
v___y_519_ = v___y_507_;
v___y_520_ = v___y_508_;
v___y_521_ = v___y_509_;
v___y_522_ = v___y_510_;
v___y_523_ = v___y_511_;
v___y_524_ = v___y_512_;
v___y_525_ = v___y_513_;
goto v___jp_515_;
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_x_503_);
lean_dec_ref(v_x_502_);
v_a_538_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_535_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_535_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0));
v_pinfos_516_ = v___x_546_;
v___y_517_ = v___y_505_;
v___y_518_ = v___y_506_;
v___y_519_ = v___y_507_;
v___y_520_ = v___y_508_;
v___y_521_ = v___y_509_;
v___y_522_ = v___y_510_;
v___y_523_ = v___y_511_;
v___y_524_ = v___y_512_;
v___y_525_ = v___y_513_;
goto v___jp_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor(lean_object* v_e_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
uint64_t v_a_573_; lean_object* v___y_574_; lean_object* v_n_601_; lean_object* v_d_602_; lean_object* v_b_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___x_622_; lean_object* v_anchors_623_; lean_object* v___x_624_; 
v___x_622_ = lean_st_ref_get(v_a_564_);
v_anchors_623_ = lean_ctor_get(v___x_622_, 10);
lean_inc_ref(v_anchors_623_);
lean_dec(v___x_622_);
v___x_624_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_623_, v_e_561_);
lean_dec_ref(v_anchors_623_);
if (lean_obj_tag(v___x_624_) == 1)
{
lean_object* v_val_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_e_561_);
v_val_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_val_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 0);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_val_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_dec(v___x_624_);
switch(lean_obj_tag(v_e_561_))
{
case 0:
{
lean_object* v_deBruijnIndex_633_; uint64_t v___x_634_; 
v_deBruijnIndex_633_ = lean_ctor_get(v_e_561_, 0);
v___x_634_ = lean_uint64_of_nat(v_deBruijnIndex_633_);
v_a_573_ = v___x_634_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
case 1:
{
lean_object* v_fvarId_635_; lean_object* v___x_636_; 
v_fvarId_635_ = lean_ctor_get(v_e_561_, 0);
lean_inc(v_fvarId_635_);
v___x_636_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_635_, v_a_567_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_LocalDecl_userName(v_a_637_);
lean_inc(v___x_638_);
v___x_639_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_isHiddenName(v___x_638_);
if (v___x_639_ == 0)
{
uint64_t v___x_640_; 
lean_dec(v_a_637_);
v___x_640_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_638_);
v_a_573_ = v___x_640_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
else
{
lean_object* v___x_641_; 
lean_dec(v___x_638_);
v___x_641_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashHiddenFVar___redArg(v_a_637_, v_a_567_);
lean_dec(v_a_637_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; uint64_t v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = lean_unbox_uint64(v_a_642_);
lean_dec(v_a_642_);
v_a_573_ = v___x_643_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
else
{
lean_dec_ref_known(v_e_561_, 1);
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref_known(v_e_561_, 1);
v_a_644_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_636_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_636_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
case 4:
{
lean_object* v_declName_652_; lean_object* v___x_653_; 
v_declName_652_ = lean_ctor_get(v_e_561_, 0);
lean_inc(v_declName_652_);
v___x_653_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_652_, v_a_570_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_unbox(v_a_654_);
lean_dec(v_a_654_);
if (v___x_655_ == 0)
{
uint64_t v___x_656_; 
lean_inc(v_declName_652_);
v___x_656_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_652_);
v_a_573_ = v___x_656_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
else
{
uint64_t v___x_657_; 
v___x_657_ = 0ULL;
v_a_573_ = v___x_657_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref_known(v_e_561_, 2);
v_a_658_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_653_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
case 5:
{
lean_object* v_dummy_666_; lean_object* v_nargs_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_dummy_666_ = lean_obj_once(&l_Lean_Meta_Grind_getAnchor___closed__0, &l_Lean_Meta_Grind_getAnchor___closed__0_once, _init_l_Lean_Meta_Grind_getAnchor___closed__0);
v_nargs_667_ = l_Lean_Expr_getAppNumArgs(v_e_561_);
lean_inc(v_nargs_667_);
v___x_668_ = lean_mk_array(v_nargs_667_, v_dummy_666_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_sub(v_nargs_667_, v___x_669_);
lean_dec(v_nargs_667_);
lean_inc_ref(v_e_561_);
v___x_671_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_e_561_, v___x_668_, v___x_670_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; uint64_t v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = lean_unbox_uint64(v_a_672_);
lean_dec(v_a_672_);
v_a_573_ = v___x_673_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
else
{
lean_dec_ref_known(v_e_561_, 2);
return v___x_671_;
}
}
case 6:
{
lean_object* v_binderName_674_; lean_object* v_binderType_675_; lean_object* v_body_676_; 
v_binderName_674_ = lean_ctor_get(v_e_561_, 0);
v_binderType_675_ = lean_ctor_get(v_e_561_, 1);
v_body_676_ = lean_ctor_get(v_e_561_, 2);
lean_inc_ref(v_body_676_);
lean_inc_ref(v_binderType_675_);
lean_inc(v_binderName_674_);
v_n_601_ = v_binderName_674_;
v_d_602_ = v_binderType_675_;
v_b_603_ = v_body_676_;
v___y_604_ = v_a_562_;
v___y_605_ = v_a_563_;
v___y_606_ = v_a_564_;
v___y_607_ = v_a_565_;
v___y_608_ = v_a_566_;
v___y_609_ = v_a_567_;
v___y_610_ = v_a_568_;
v___y_611_ = v_a_569_;
v___y_612_ = v_a_570_;
goto v___jp_600_;
}
case 7:
{
lean_object* v_binderName_677_; lean_object* v_binderType_678_; lean_object* v_body_679_; 
v_binderName_677_ = lean_ctor_get(v_e_561_, 0);
v_binderType_678_ = lean_ctor_get(v_e_561_, 1);
v_body_679_ = lean_ctor_get(v_e_561_, 2);
lean_inc_ref(v_body_679_);
lean_inc_ref(v_binderType_678_);
lean_inc(v_binderName_677_);
v_n_601_ = v_binderName_677_;
v_d_602_ = v_binderType_678_;
v_b_603_ = v_body_679_;
v___y_604_ = v_a_562_;
v___y_605_ = v_a_563_;
v___y_606_ = v_a_564_;
v___y_607_ = v_a_565_;
v___y_608_ = v_a_566_;
v___y_609_ = v_a_567_;
v___y_610_ = v_a_568_;
v___y_611_ = v_a_569_;
v___y_612_ = v_a_570_;
goto v___jp_600_;
}
case 8:
{
lean_object* v_declName_680_; lean_object* v_type_681_; lean_object* v_value_682_; lean_object* v_body_683_; lean_object* v___x_684_; 
v_declName_680_ = lean_ctor_get(v_e_561_, 0);
v_type_681_ = lean_ctor_get(v_e_561_, 1);
v_value_682_ = lean_ctor_get(v_e_561_, 2);
v_body_683_ = lean_ctor_get(v_e_561_, 3);
lean_inc_ref(v_value_682_);
v___x_684_ = l_Lean_Meta_Grind_getAnchor(v_value_682_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
lean_inc_ref(v_type_681_);
v___x_686_ = l_Lean_Meta_Grind_getAnchor(v_type_681_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
lean_inc_ref(v_body_683_);
v___x_688_ = l_Lean_Meta_Grind_getAnchor(v_body_683_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; uint64_t v___x_690_; uint64_t v___x_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
lean_inc(v_declName_680_);
v___x_690_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_680_);
v___x_691_ = lean_unbox_uint64(v_a_687_);
lean_dec(v_a_687_);
v___x_692_ = lean_unbox_uint64(v_a_689_);
lean_dec(v_a_689_);
v___x_693_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_691_, v___x_692_);
v___x_694_ = lean_unbox_uint64(v_a_685_);
lean_dec(v_a_685_);
v___x_695_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_694_, v___x_693_);
v___x_696_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_690_, v___x_695_);
v_a_573_ = v___x_696_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
else
{
lean_dec(v_a_687_);
lean_dec(v_a_685_);
lean_dec_ref_known(v_e_561_, 4);
return v___x_688_;
}
}
else
{
lean_dec(v_a_685_);
lean_dec_ref_known(v_e_561_, 4);
return v___x_686_;
}
}
else
{
lean_dec_ref_known(v_e_561_, 4);
return v___x_684_;
}
}
case 9:
{
lean_object* v_a_697_; uint64_t v___x_698_; 
v_a_697_ = lean_ctor_get(v_e_561_, 0);
v___x_698_ = l_Lean_Literal_hash(v_a_697_);
v_a_573_ = v___x_698_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
case 10:
{
lean_object* v_expr_699_; lean_object* v___x_700_; 
v_expr_699_ = lean_ctor_get(v_e_561_, 1);
lean_inc_ref(v_expr_699_);
v___x_700_ = l_Lean_Meta_Grind_getAnchor(v_expr_699_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; uint64_t v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_unbox_uint64(v_a_701_);
lean_dec(v_a_701_);
v_a_573_ = v___x_702_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
else
{
lean_dec_ref_known(v_e_561_, 2);
return v___x_700_;
}
}
case 11:
{
lean_object* v_idx_703_; lean_object* v_struct_704_; lean_object* v___x_705_; 
v_idx_703_ = lean_ctor_get(v_e_561_, 1);
v_struct_704_ = lean_ctor_get(v_e_561_, 2);
lean_inc_ref(v_struct_704_);
v___x_705_ = l_Lean_Meta_Grind_getAnchor(v_struct_704_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = lean_uint64_of_nat(v_idx_703_);
v___x_708_ = lean_unbox_uint64(v_a_706_);
lean_dec(v_a_706_);
v___x_709_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_707_, v___x_708_);
v_a_573_ = v___x_709_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
else
{
lean_dec_ref_known(v_e_561_, 3);
return v___x_705_;
}
}
default: 
{
uint64_t v___x_710_; 
v___x_710_ = 0ULL;
v_a_573_ = v___x_710_;
v___y_574_ = v_a_564_;
goto v___jp_572_;
}
}
}
v___jp_572_:
{
lean_object* v___x_575_; lean_object* v_congrThms_576_; lean_object* v_simp_577_; lean_object* v_symSimp_578_; lean_object* v_symDSimp_579_; lean_object* v_lastTag_580_; lean_object* v_counters_581_; lean_object* v_splitDiags_582_; lean_object* v_ematchDiags_583_; lean_object* v_lawfulEqCmpMap_584_; lean_object* v_reflCmpMap_585_; lean_object* v_anchors_586_; lean_object* v_instanceMap_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_599_; 
v___x_575_ = lean_st_ref_take(v___y_574_);
v_congrThms_576_ = lean_ctor_get(v___x_575_, 0);
v_simp_577_ = lean_ctor_get(v___x_575_, 1);
v_symSimp_578_ = lean_ctor_get(v___x_575_, 2);
v_symDSimp_579_ = lean_ctor_get(v___x_575_, 3);
v_lastTag_580_ = lean_ctor_get(v___x_575_, 4);
v_counters_581_ = lean_ctor_get(v___x_575_, 5);
v_splitDiags_582_ = lean_ctor_get(v___x_575_, 6);
v_ematchDiags_583_ = lean_ctor_get(v___x_575_, 7);
v_lawfulEqCmpMap_584_ = lean_ctor_get(v___x_575_, 8);
v_reflCmpMap_585_ = lean_ctor_get(v___x_575_, 9);
v_anchors_586_ = lean_ctor_get(v___x_575_, 10);
v_instanceMap_587_ = lean_ctor_get(v___x_575_, 11);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_599_ == 0)
{
v___x_589_ = v___x_575_;
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_instanceMap_587_);
lean_inc(v_anchors_586_);
lean_inc(v_reflCmpMap_585_);
lean_inc(v_lawfulEqCmpMap_584_);
lean_inc(v_ematchDiags_583_);
lean_inc(v_splitDiags_582_);
lean_inc(v_counters_581_);
lean_inc(v_lastTag_580_);
lean_inc(v_symDSimp_579_);
lean_inc(v_symSimp_578_);
lean_inc(v_simp_577_);
lean_inc(v_congrThms_576_);
lean_dec(v___x_575_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_591_ = lean_box_uint64(v_a_573_);
v___x_592_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_anchors_586_, v_e_561_, v___x_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 10, v___x_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_congrThms_576_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_simp_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_symSimp_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_symDSimp_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_lastTag_580_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v_counters_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_splitDiags_582_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_ematchDiags_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_lawfulEqCmpMap_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 9, v_reflCmpMap_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 10, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_598_, 11, v_instanceMap_587_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_st_ref_put(v___y_574_, v___x_594_);
v___x_596_ = lean_box_uint64(v_a_573_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
}
v___jp_600_:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Meta_Grind_getAnchor(v_d_602_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_615_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v___x_615_ = l_Lean_Meta_Grind_getAnchor(v_b_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint64_t v___x_617_; uint64_t v___x_618_; uint64_t v___x_619_; uint64_t v___x_620_; uint64_t v___x_621_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_601_);
v___x_618_ = lean_unbox_uint64(v_a_614_);
lean_dec(v_a_614_);
v___x_619_ = lean_unbox_uint64(v_a_616_);
lean_dec(v_a_616_);
v___x_620_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_618_, v___x_619_);
v___x_621_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_617_, v___x_620_);
v_a_573_ = v___x_621_;
v___y_574_ = v___y_606_;
goto v___jp_572_;
}
else
{
lean_dec(v_a_614_);
lean_dec(v_n_601_);
lean_dec_ref(v_e_561_);
return v___x_615_;
}
}
else
{
lean_dec_ref(v_b_603_);
lean_dec(v_n_601_);
lean_dec_ref(v_e_561_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(lean_object* v_upperBound_711_, lean_object* v_args_712_, lean_object* v_pinfos_713_, lean_object* v_a_714_, uint64_t v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint64_t v_a_727_; uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_lt(v_a_714_, v_upperBound_711_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec(v_a_714_);
v___x_732_ = lean_box_uint64(v_b_715_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_array_fget_borrowed(v_args_712_, v_a_714_);
v___x_735_ = lean_array_get_size(v_pinfos_713_);
v___x_736_ = lean_nat_dec_lt(v_a_714_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_inc(v___x_734_);
v___x_737_ = l_Lean_Meta_Grind_getAnchor(v___x_734_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; uint64_t v___x_739_; uint64_t v___x_740_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = lean_unbox_uint64(v_a_738_);
lean_dec(v_a_738_);
v___x_740_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_715_, v___x_739_);
v_a_727_ = v___x_740_;
goto v___jp_726_;
}
else
{
lean_dec(v_a_714_);
return v___x_737_;
}
}
else
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_fget_borrowed(v_pinfos_713_, v_a_714_);
v___x_742_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_inc(v___x_734_);
v___x_743_ = l_Lean_Meta_Grind_getAnchor(v___x_734_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; uint64_t v___x_745_; uint64_t v___x_746_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = lean_unbox_uint64(v_a_744_);
lean_dec(v_a_744_);
v___x_746_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_715_, v___x_745_);
v_a_727_ = v___x_746_;
goto v___jp_726_;
}
else
{
lean_dec(v_a_714_);
return v___x_743_;
}
}
else
{
v_a_727_ = v_b_715_;
goto v___jp_726_;
}
}
}
v___jp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_a_714_, v___x_728_);
lean_dec(v_a_714_);
v_a_714_ = v___x_729_;
v_b_715_ = v_a_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg___boxed(lean_object* v_upperBound_747_, lean_object* v_args_748_, lean_object* v_pinfos_749_, lean_object* v_a_750_, lean_object* v_b_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
uint64_t v_b_boxed_762_; lean_object* v_res_763_; 
v_b_boxed_762_ = lean_unbox_uint64(v_b_751_);
lean_dec_ref(v_b_751_);
v_res_763_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_upperBound_747_, v_args_748_, v_pinfos_749_, v_a_750_, v_b_boxed_762_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v_pinfos_749_);
lean_dec_ref(v_args_748_);
lean_dec(v_upperBound_747_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(v_x_764_, v_x_765_, v_x_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAnchor___boxed(lean_object* v_e_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_Grind_getAnchor(v_e_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v_x_791_, v_x_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(lean_object* v_upperBound_795_, lean_object* v_args_796_, lean_object* v_pinfos_797_, lean_object* v_inst_798_, lean_object* v_R_799_, lean_object* v_a_800_, uint64_t v_b_801_, lean_object* v_c_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_upperBound_795_, v_args_796_, v_pinfos_797_, v_a_800_, v_b_801_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_814_ = _args[0];
lean_object* v_args_815_ = _args[1];
lean_object* v_pinfos_816_ = _args[2];
lean_object* v_inst_817_ = _args[3];
lean_object* v_R_818_ = _args[4];
lean_object* v_a_819_ = _args[5];
lean_object* v_b_820_ = _args[6];
lean_object* v_c_821_ = _args[7];
lean_object* v___y_822_ = _args[8];
lean_object* v___y_823_ = _args[9];
lean_object* v___y_824_ = _args[10];
lean_object* v___y_825_ = _args[11];
lean_object* v___y_826_ = _args[12];
lean_object* v___y_827_ = _args[13];
lean_object* v___y_828_ = _args[14];
lean_object* v___y_829_ = _args[15];
lean_object* v___y_830_ = _args[16];
lean_object* v___y_831_ = _args[17];
_start:
{
uint64_t v_b_boxed_832_; lean_object* v_res_833_; 
v_b_boxed_832_ = lean_unbox_uint64(v_b_820_);
lean_dec_ref(v_b_820_);
v_res_833_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__1(v_upperBound_814_, v_args_815_, v_pinfos_816_, v_inst_817_, v_R_818_, v_a_819_, v_b_boxed_832_, v_c_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v_pinfos_816_);
lean_dec_ref(v_args_815_);
lean_dec(v_upperBound_814_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_x_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(lean_object* v_00_u03b2_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(v_00_u03b2_838_, v_x_839_, v_x_840_);
lean_dec_ref(v_x_840_);
lean_dec_ref(v_x_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, size_t v_x_844_, size_t v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___redArg(v_x_843_, v_x_844_, v_x_845_, v_x_846_, v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0___boxed(lean_object* v_00_u03b2_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
size_t v_x_34667__boxed_855_; size_t v_x_34668__boxed_856_; lean_object* v_res_857_; 
v_x_34667__boxed_855_ = lean_unbox_usize(v_x_851_);
lean_dec(v_x_851_);
v_x_34668__boxed_856_ = lean_unbox_usize(v_x_852_);
lean_dec(v_x_852_);
v_res_857_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0(v_00_u03b2_849_, v_x_850_, v_x_34667__boxed_855_, v_x_34668__boxed_856_, v_x_853_, v_x_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, size_t v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_859_, v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
size_t v_x_34684__boxed_867_; lean_object* v_res_868_; 
v_x_34684__boxed_867_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_res_868_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_863_, v_x_864_, v_x_34684__boxed_867_, v_x_866_);
lean_dec_ref(v_x_866_);
lean_dec_ref(v_x_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_869_, lean_object* v_n_870_, lean_object* v_k_871_, lean_object* v_v_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2___redArg(v_n_870_, v_k_871_, v_v_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_874_, size_t v_depth_875_, lean_object* v_keys_876_, lean_object* v_vals_877_, lean_object* v_heq_878_, lean_object* v_i_879_, lean_object* v_entries_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___redArg(v_depth_875_, v_keys_876_, v_vals_877_, v_i_879_, v_entries_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_882_, lean_object* v_depth_883_, lean_object* v_keys_884_, lean_object* v_vals_885_, lean_object* v_heq_886_, lean_object* v_i_887_, lean_object* v_entries_888_){
_start:
{
size_t v_depth_boxed_889_; lean_object* v_res_890_; 
v_depth_boxed_889_ = lean_unbox_usize(v_depth_883_);
lean_dec(v_depth_883_);
v_res_890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__3(v_00_u03b2_882_, v_depth_boxed_889_, v_keys_884_, v_vals_885_, v_heq_886_, v_i_887_, v_entries_888_);
lean_dec_ref(v_vals_885_);
lean_dec_ref(v_keys_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_891_, lean_object* v_keys_892_, lean_object* v_vals_893_, lean_object* v_heq_894_, lean_object* v_i_895_, lean_object* v_k_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_892_, v_vals_893_, v_i_895_, v_k_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_898_, lean_object* v_keys_899_, lean_object* v_vals_900_, lean_object* v_heq_901_, lean_object* v_i_902_, lean_object* v_k_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_898_, v_keys_899_, v_vals_900_, v_heq_901_, v_i_902_, v_k_903_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v_vals_900_);
lean_dec_ref(v_keys_899_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__0_spec__0_spec__2_spec__6___redArg(v_x_906_, v_x_907_, v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object* v_anchorRef_911_, uint64_t v_anchor_912_){
_start:
{
lean_object* v_numDigits_913_; uint64_t v_anchorPrefix_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v_shift_919_; uint64_t v___x_920_; uint8_t v___x_921_; 
v_numDigits_913_ = lean_ctor_get(v_anchorRef_911_, 0);
v_anchorPrefix_914_ = lean_ctor_get_uint64(v_anchorRef_911_, sizeof(void*)*1);
v___x_915_ = 64ULL;
v___x_916_ = lean_uint64_of_nat(v_numDigits_913_);
v___x_917_ = 2ULL;
v___x_918_ = lean_uint64_shift_left(v___x_916_, v___x_917_);
v_shift_919_ = lean_uint64_sub(v___x_915_, v___x_918_);
v___x_920_ = lean_uint64_shift_right(v_anchor_912_, v_shift_919_);
v___x_921_ = lean_uint64_dec_eq(v_anchorPrefix_914_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AnchorRef_matches___boxed(lean_object* v_anchorRef_922_, lean_object* v_anchor_923_){
_start:
{
uint64_t v_anchor_boxed_924_; uint8_t v_res_925_; lean_object* v_r_926_; 
v_anchor_boxed_924_ = lean_unbox_uint64(v_anchor_923_);
lean_dec_ref(v_anchor_923_);
v_res_925_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_922_, v_anchor_boxed_924_);
lean_dec_ref(v_anchorRef_922_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10(void){
_start:
{
lean_object* v___x_946_; lean_object* v___f_947_; 
v___x_946_ = lean_alloc_closure((void*)(l_instDecidableEqUInt64___boxed), 2, 0);
v___f_947_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_947_, 0, v___x_946_);
return v___f_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(lean_object* v_inst_949_, lean_object* v_shift_950_, lean_object* v___f_951_, lean_object* v___f_952_, lean_object* v_numDigits_953_, lean_object* v_es_954_, lean_object* v___x_955_, lean_object* v_a_956_, lean_object* v_x_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_949_, v_shift_950_, v___f_951_, v___f_952_, v_numDigits_953_, v_es_954_, v___x_955_, v_a_956_, v_x_957_, v___y_958_);
lean_dec(v_numDigits_953_);
lean_dec(v_shift_950_);
return v_res_959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_box(0);
v___x_961_ = lean_unsigned_to_nat(16u);
v___x_962_ = lean_mk_array(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_found_965_; 
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12);
v___x_964_ = lean_unsigned_to_nat(0u);
v_found_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_found_965_, 0, v___x_964_);
lean_ctor_set(v_found_965_, 1, v___x_963_);
return v_found_965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14(void){
_start:
{
lean_object* v_found_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_found_966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13);
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_found_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(lean_object* v_inst_969_, lean_object* v_es_970_, lean_object* v_numDigits_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9));
v___x_973_ = lean_unsigned_to_nat(4u);
v___x_974_ = lean_nat_mul(v___x_973_, v_numDigits_971_);
v___x_975_ = lean_unsigned_to_nat(64u);
v___x_976_ = lean_nat_dec_lt(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_dec(v___x_974_);
lean_dec_ref(v_es_970_);
lean_dec_ref(v_inst_969_);
return v_numDigits_971_;
}
else
{
lean_object* v___f_977_; lean_object* v___f_978_; lean_object* v_shift_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_982_; size_t v_sz_983_; size_t v___x_984_; lean_object* v___x_985_; lean_object* v_fst_986_; 
v___f_977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10);
v___f_978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11));
v_shift_979_ = lean_nat_sub(v___x_975_, v___x_974_);
lean_dec(v___x_974_);
v___x_980_ = lean_box(0);
lean_inc_ref(v_es_970_);
lean_inc(v_numDigits_971_);
v___f_981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_981_, 0, v_inst_969_);
lean_closure_set(v___f_981_, 1, v_shift_979_);
lean_closure_set(v___f_981_, 2, v___f_977_);
lean_closure_set(v___f_981_, 3, v___f_978_);
lean_closure_set(v___f_981_, 4, v_numDigits_971_);
lean_closure_set(v___f_981_, 5, v_es_970_);
lean_closure_set(v___f_981_, 6, v___x_980_);
v___x_982_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
v_sz_983_ = lean_array_size(v_es_970_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_972_, v_es_970_, v___f_981_, v_sz_983_, v___x_984_, v___x_982_);
v_fst_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_fst_986_);
lean_dec(v___x_985_);
if (lean_obj_tag(v_fst_986_) == 0)
{
return v_numDigits_971_;
}
else
{
lean_object* v_val_987_; 
lean_dec(v_numDigits_971_);
v_val_987_ = lean_ctor_get(v_fst_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v_fst_986_, 1);
return v_val_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(lean_object* v_inst_988_, lean_object* v_shift_989_, lean_object* v___f_990_, lean_object* v___f_991_, lean_object* v_numDigits_992_, lean_object* v_es_993_, lean_object* v___x_994_, lean_object* v_a_995_, lean_object* v_x_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_snd_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1036_; 
v_snd_998_ = lean_ctor_get(v___y_997_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___y_997_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v___y_997_, 0);
lean_dec(v_unused_1037_);
v___x_1000_ = v___y_997_;
v_isShared_1001_ = v_isSharedCheck_1036_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snd_998_);
lean_dec(v___y_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1036_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_inc_ref(v_inst_988_);
v___x_1002_ = lean_apply_1(v_inst_988_, v_a_995_);
v___x_1003_ = lean_uint64_of_nat(v_shift_989_);
v___x_1004_ = lean_unbox_uint64(v___x_1002_);
v___x_1005_ = lean_uint64_shift_right(v___x_1004_, v___x_1003_);
v___x_1006_ = lean_box_uint64(v___x_1005_);
lean_inc_ref(v___f_991_);
lean_inc_ref(v___f_990_);
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_990_, v___f_991_, v_snd_998_, v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 1)
{
lean_object* v_val_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v___f_991_);
lean_dec_ref(v___f_990_);
v_val_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1029_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_val_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1029_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
uint64_t v___x_1012_; uint64_t v___x_1013_; uint8_t v___x_1014_; 
v___x_1012_ = lean_unbox_uint64(v_val_1008_);
lean_dec(v_val_1008_);
v___x_1013_ = lean_unbox_uint64(v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1014_ = lean_uint64_dec_eq(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_dec(v___x_994_);
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_numDigits_992_, v___x_1015_);
v___x_1017_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_988_, v_es_993_, v___x_1016_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1017_);
v___x_1019_ = v___x_1010_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1019_);
v___x_1021_ = v___x_1000_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_snd_998_);
v___x_1021_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
}
else
{
lean_object* v___x_1026_; 
lean_del_object(v___x_1010_);
lean_dec_ref(v_es_993_);
lean_dec_ref(v_inst_988_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_994_);
v___x_1026_ = v___x_1000_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_snd_998_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec(v___x_1007_);
lean_dec_ref(v_es_993_);
lean_dec_ref(v_inst_988_);
v___x_1030_ = lean_box_uint64(v___x_1005_);
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_990_, v___f_991_, v_snd_998_, v___x_1030_, v___x_1002_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v___x_1031_);
lean_ctor_set(v___x_1000_, 0, v___x_994_);
v___x_1033_ = v___x_1000_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(lean_object* v_00_u03b1_1038_, lean_object* v_inst_1039_, lean_object* v_es_1040_, lean_object* v_numDigits_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1039_, v_es_1040_, v_numDigits_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter___redArg(lean_object* v_x_1043_, lean_object* v_h__1_1044_, lean_object* v_h__2_1045_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 1)
{
lean_object* v_val_1046_; lean_object* v___x_1047_; 
lean_dec(v_h__2_1045_);
v_val_1046_ = lean_ctor_get(v_x_1043_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v_x_1043_, 1);
v___x_1047_ = lean_apply_1(v_h__1_1044_, v_val_1046_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; 
lean_dec(v_h__1_1044_);
v___x_1048_ = lean_apply_2(v_h__2_1045_, v_x_1043_, lean_box(0));
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getAnchor_match__1_splitter(lean_object* v_motive_1049_, lean_object* v_x_1050_, lean_object* v_h__1_1051_, lean_object* v_h__2_1052_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 1)
{
lean_object* v_val_1053_; lean_object* v___x_1054_; 
lean_dec(v_h__2_1052_);
v_val_1053_ = lean_ctor_get(v_x_1050_, 0);
lean_inc(v_val_1053_);
lean_dec_ref_known(v_x_1050_, 1);
v___x_1054_ = lean_apply_1(v_h__1_1051_, v_val_1053_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; 
lean_dec(v_h__1_1051_);
v___x_1055_ = lean_apply_2(v_h__2_1052_, v_x_1050_, lean_box(0));
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_1056_, lean_object* v_h__1_1057_, lean_object* v_h__2_1058_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_h__1_1057_);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_apply_1(v_h__2_1058_, v___x_1059_);
return v___x_1060_;
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1062_; 
lean_dec(v_h__2_1058_);
v_val_1061_ = lean_ctor_get(v_x_1056_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v_x_1056_, 1);
v___x_1062_ = lean_apply_1(v_h__1_1057_, v_val_1061_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_1063_, lean_object* v_motive_1064_, lean_object* v_x_1065_, lean_object* v_h__1_1066_, lean_object* v_h__2_1067_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec(v_h__1_1066_);
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_apply_1(v_h__2_1067_, v___x_1068_);
return v___x_1069_;
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__2_1067_);
v_val_1070_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v_x_1065_, 1);
v___x_1071_ = lean_apply_1(v_h__1_1066_, v_val_1070_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(lean_object* v_inst_1072_, lean_object* v_es_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(4u);
v___x_1075_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1072_, v_es_1073_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNumDigitsForAnchors(lean_object* v_00_u03b1_1076_, lean_object* v_inst_1077_, lean_object* v_es_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_1077_, v_es_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(lean_object* v_e_1080_){
_start:
{
uint64_t v_anchor_1081_; 
v_anchor_1081_ = lean_ctor_get_uint64(v_e_1080_, sizeof(void*)*1);
return v_anchor_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(lean_object* v_e_1082_){
_start:
{
uint64_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_1082_);
lean_dec_ref(v_e_1082_);
v_r_1084_ = lean_box_uint64(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(lean_object* v_numDigits_1100_, uint64_t v_anchorPrefix_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_ref_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_ref_1104_ = lean_ctor_get(v_a_1102_, 2);
v___x_1105_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1));
v___x_1106_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_1100_, v_anchorPrefix_1101_);
v___x_1107_ = l_Lean_mkAtom(v___x_1106_);
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_mk_empty_array_with_capacity(v___x_1108_);
v___x_1110_ = lean_array_push(v___x_1109_, v___x_1107_);
v___x_1111_ = lean_box(2);
v___x_1112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___x_1105_);
lean_ctor_set(v___x_1112_, 2, v___x_1110_);
v___x_1113_ = 0;
v___x_1114_ = l_Lean_SourceInfo_fromRef(v_ref_1104_, v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6));
v___x_1116_ = ((lean_object*)(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7));
lean_inc(v___x_1114_);
v___x_1117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1114_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_Syntax_node2(v___x_1114_, v___x_1115_, v___x_1117_, v___x_1112_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(lean_object* v_numDigits_1120_, lean_object* v_anchorPrefix_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
uint64_t v_anchorPrefix_boxed_1124_; lean_object* v_res_1125_; 
v_anchorPrefix_boxed_1124_ = lean_unbox_uint64(v_anchorPrefix_1121_);
lean_dec_ref(v_anchorPrefix_1121_);
v_res_1125_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1120_, v_anchorPrefix_boxed_1124_, v_a_1122_);
lean_dec_ref(v_a_1122_);
lean_dec(v_numDigits_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(lean_object* v_numDigits_1126_, uint64_t v_anchorPrefix_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1126_, v_anchorPrefix_1127_, v_a_1128_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(lean_object* v_numDigits_1132_, lean_object* v_anchorPrefix_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
uint64_t v_anchorPrefix_boxed_1137_; lean_object* v_res_1138_; 
v_anchorPrefix_boxed_1137_ = lean_unbox_uint64(v_anchorPrefix_1133_);
lean_dec_ref(v_anchorPrefix_1133_);
v_res_1138_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(v_numDigits_1132_, v_anchorPrefix_boxed_1137_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_numDigits_1132_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg(lean_object* v_numDigits_1139_, uint64_t v_anchor_1140_, lean_object* v_a_1141_){
_start:
{
uint64_t v___x_1143_; uint64_t v___x_1144_; uint64_t v___x_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v_anchorPrefix_1148_; lean_object* v___x_1149_; 
v___x_1143_ = 64ULL;
v___x_1144_ = lean_uint64_of_nat(v_numDigits_1139_);
v___x_1145_ = 2ULL;
v___x_1146_ = lean_uint64_shift_left(v___x_1144_, v___x_1145_);
v___x_1147_ = lean_uint64_sub(v___x_1143_, v___x_1146_);
v_anchorPrefix_1148_ = lean_uint64_shift_right(v_anchor_1140_, v___x_1147_);
v___x_1149_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(v_numDigits_1139_, v_anchorPrefix_1148_, v_a_1141_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(lean_object* v_numDigits_1150_, lean_object* v_anchor_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
uint64_t v_anchor_boxed_1154_; lean_object* v_res_1155_; 
v_anchor_boxed_1154_ = lean_unbox_uint64(v_anchor_1151_);
lean_dec_ref(v_anchor_1151_);
v_res_1155_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1150_, v_anchor_boxed_1154_, v_a_1152_);
lean_dec_ref(v_a_1152_);
lean_dec(v_numDigits_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax(lean_object* v_numDigits_1156_, uint64_t v_anchor_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1156_, v_anchor_1157_, v_a_1158_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAnchorSyntax___boxed(lean_object* v_numDigits_1162_, lean_object* v_anchor_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
uint64_t v_anchor_boxed_1167_; lean_object* v_res_1168_; 
v_anchor_boxed_1167_ = lean_unbox_uint64(v_anchor_1163_);
lean_dec_ref(v_anchor_1163_);
v_res_1168_ = l_Lean_Meta_Grind_mkAnchorSyntax(v_numDigits_1162_, v_anchor_boxed_1167_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_numDigits_1162_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor(lean_object* v_s_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_1169_);
v___x_1181_ = l_Lean_Meta_Grind_getAnchor(v___x_1180_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(lean_object* v_s_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(v_s_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_s_1182_);
return v_res_1193_;
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

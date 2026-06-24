// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareCommon
// Imports: public import Lean.Meta.Sym.ExprPtr
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0;
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instHashableAlphaKey = (const lean_object*)&l_Lean_Meta_Sym_instHashableAlphaKey___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instBEqAlphaKey = (const lean_object*)&l_Lean_Meta_Sym_instBEqAlphaKey___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "__dummy__"};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 141, 137, 132, 208, 124, 31, 129)}};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_shareCommonAlpha___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_shareCommonAlpha___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_shareCommonAlpha___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_shareCommonAlpha___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(lean_object* v_e_1_){
_start:
{
switch(lean_obj_tag(v_e_1_))
{
case 5:
{
uint64_t v___x_2_; 
v___x_2_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1_);
return v___x_2_;
}
case 6:
{
uint64_t v___x_3_; 
v___x_3_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1_);
return v___x_3_;
}
case 7:
{
uint64_t v___x_4_; 
v___x_4_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1_);
return v___x_4_;
}
case 8:
{
uint64_t v___x_5_; 
v___x_5_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1_);
return v___x_5_;
}
case 10:
{
uint64_t v___x_6_; 
v___x_6_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1_);
return v___x_6_;
}
case 11:
{
uint64_t v___x_7_; 
v___x_7_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_e_1_);
return v___x_7_;
}
default: 
{
uint64_t v___x_8_; 
v___x_8_ = l_Lean_Expr_hash(v_e_1_);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(lean_object* v_e_9_){
_start:
{
uint64_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_e_9_);
lean_dec_ref(v_e_9_);
v_r_11_ = lean_box_uint64(v_res_10_);
return v_r_11_;
}
}
static uint64_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0(void){
_start:
{
lean_object* v___x_12_; uint64_t v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(1723u);
v___x_13_ = lean_uint64_of_nat(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object* v_e_14_){
_start:
{
lean_object* v_d_16_; lean_object* v_b_17_; 
switch(lean_obj_tag(v_e_14_))
{
case 5:
{
lean_object* v_fn_21_; lean_object* v_arg_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; 
v_fn_21_ = lean_ctor_get(v_e_14_, 0);
v_arg_22_ = lean_ctor_get(v_e_14_, 1);
v___x_23_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_fn_21_);
v___x_24_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_arg_22_);
v___x_25_ = lean_uint64_mix_hash(v___x_23_, v___x_24_);
return v___x_25_;
}
case 6:
{
lean_object* v_binderType_26_; lean_object* v_body_27_; 
v_binderType_26_ = lean_ctor_get(v_e_14_, 1);
v_body_27_ = lean_ctor_get(v_e_14_, 2);
v_d_16_ = v_binderType_26_;
v_b_17_ = v_body_27_;
goto v___jp_15_;
}
case 7:
{
lean_object* v_binderType_28_; lean_object* v_body_29_; 
v_binderType_28_ = lean_ctor_get(v_e_14_, 1);
v_body_29_ = lean_ctor_get(v_e_14_, 2);
v_d_16_ = v_binderType_28_;
v_b_17_ = v_body_29_;
goto v___jp_15_;
}
case 8:
{
lean_object* v_value_30_; lean_object* v_body_31_; uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; 
v_value_30_ = lean_ctor_get(v_e_14_, 2);
v_body_31_ = lean_ctor_get(v_e_14_, 3);
v___x_32_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_value_30_);
v___x_33_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_body_31_);
v___x_34_ = lean_uint64_mix_hash(v___x_32_, v___x_33_);
return v___x_34_;
}
case 10:
{
lean_object* v_expr_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; 
v_expr_35_ = lean_ctor_get(v_e_14_, 1);
v___x_36_ = 13ULL;
v___x_37_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_expr_35_);
v___x_38_ = lean_uint64_mix_hash(v___x_36_, v___x_37_);
return v___x_38_;
}
case 11:
{
lean_object* v_typeName_39_; lean_object* v_idx_40_; lean_object* v_struct_41_; uint64_t v___y_43_; 
v_typeName_39_ = lean_ctor_get(v_e_14_, 0);
v_idx_40_ = lean_ctor_get(v_e_14_, 1);
v_struct_41_ = lean_ctor_get(v_e_14_, 2);
if (lean_obj_tag(v_typeName_39_) == 0)
{
uint64_t v___x_48_; 
v___x_48_ = lean_uint64_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0);
v___y_43_ = v___x_48_;
goto v___jp_42_;
}
else
{
uint64_t v_hash_49_; 
v_hash_49_ = lean_ctor_get_uint64(v_typeName_39_, sizeof(void*)*2);
v___y_43_ = v_hash_49_;
goto v___jp_42_;
}
v___jp_42_:
{
uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; 
v___x_44_ = lean_uint64_of_nat(v_idx_40_);
v___x_45_ = lean_uint64_mix_hash(v___y_43_, v___x_44_);
v___x_46_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_struct_41_);
v___x_47_ = lean_uint64_mix_hash(v___x_45_, v___x_46_);
return v___x_47_;
}
}
default: 
{
uint64_t v___x_50_; 
v___x_50_ = l_Lean_Expr_hash(v_e_14_);
return v___x_50_;
}
}
v___jp_15_:
{
uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v___x_20_; 
v___x_18_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_d_16_);
v___x_19_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_b_17_);
v___x_20_ = lean_uint64_mix_hash(v___x_18_, v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object* v_e_51_){
_start:
{
uint64_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_51_);
lean_dec_ref(v_e_51_);
v_r_53_ = lean_box_uint64(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object* v_e_u2081_54_, lean_object* v_e_u2082_55_){
_start:
{
switch(lean_obj_tag(v_e_u2081_54_))
{
case 5:
{
if (lean_obj_tag(v_e_u2082_55_) == 5)
{
lean_object* v_fn_56_; lean_object* v_arg_57_; lean_object* v_fn_58_; lean_object* v_arg_59_; uint8_t v___x_60_; 
v_fn_56_ = lean_ctor_get(v_e_u2081_54_, 0);
lean_inc_ref(v_fn_56_);
v_arg_57_ = lean_ctor_get(v_e_u2081_54_, 1);
lean_inc_ref(v_arg_57_);
lean_dec_ref_known(v_e_u2081_54_, 2);
v_fn_58_ = lean_ctor_get(v_e_u2082_55_, 0);
lean_inc_ref(v_fn_58_);
v_arg_59_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_arg_59_);
lean_dec_ref_known(v_e_u2082_55_, 2);
v___x_60_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_56_, v_fn_58_);
lean_dec_ref(v_fn_58_);
lean_dec_ref(v_fn_56_);
if (v___x_60_ == 0)
{
lean_dec_ref(v_arg_59_);
lean_dec_ref(v_arg_57_);
return v___x_60_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_57_, v_arg_59_);
lean_dec_ref(v_arg_59_);
lean_dec_ref(v_arg_57_);
return v___x_61_;
}
}
else
{
uint8_t v___x_62_; 
lean_dec_ref_known(v_e_u2081_54_, 2);
lean_dec_ref(v_e_u2082_55_);
v___x_62_ = 0;
return v___x_62_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_55_) == 6)
{
lean_object* v_binderType_63_; lean_object* v_body_64_; lean_object* v_binderType_65_; lean_object* v_body_66_; uint8_t v___x_67_; 
v_binderType_63_ = lean_ctor_get(v_e_u2081_54_, 1);
lean_inc_ref(v_binderType_63_);
v_body_64_ = lean_ctor_get(v_e_u2081_54_, 2);
lean_inc_ref(v_body_64_);
lean_dec_ref_known(v_e_u2081_54_, 3);
v_binderType_65_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_binderType_65_);
v_body_66_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_body_66_);
lean_dec_ref_known(v_e_u2082_55_, 3);
v___x_67_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_63_, v_binderType_65_);
lean_dec_ref(v_binderType_65_);
lean_dec_ref(v_binderType_63_);
if (v___x_67_ == 0)
{
lean_dec_ref(v_body_66_);
lean_dec_ref(v_body_64_);
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_64_, v_body_66_);
lean_dec_ref(v_body_66_);
lean_dec_ref(v_body_64_);
return v___x_68_;
}
}
else
{
uint8_t v___x_69_; 
lean_dec_ref_known(v_e_u2081_54_, 3);
lean_dec_ref(v_e_u2082_55_);
v___x_69_ = 0;
return v___x_69_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_55_) == 7)
{
lean_object* v_binderType_70_; lean_object* v_body_71_; lean_object* v_binderType_72_; lean_object* v_body_73_; uint8_t v___x_74_; 
v_binderType_70_ = lean_ctor_get(v_e_u2081_54_, 1);
lean_inc_ref(v_binderType_70_);
v_body_71_ = lean_ctor_get(v_e_u2081_54_, 2);
lean_inc_ref(v_body_71_);
lean_dec_ref_known(v_e_u2081_54_, 3);
v_binderType_72_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_binderType_72_);
v_body_73_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_body_73_);
lean_dec_ref_known(v_e_u2082_55_, 3);
v___x_74_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_70_, v_binderType_72_);
lean_dec_ref(v_binderType_72_);
lean_dec_ref(v_binderType_70_);
if (v___x_74_ == 0)
{
lean_dec_ref(v_body_73_);
lean_dec_ref(v_body_71_);
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_71_, v_body_73_);
lean_dec_ref(v_body_73_);
lean_dec_ref(v_body_71_);
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
lean_dec_ref_known(v_e_u2081_54_, 3);
lean_dec_ref(v_e_u2082_55_);
v___x_76_ = 0;
return v___x_76_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_55_) == 8)
{
lean_object* v_value_77_; lean_object* v_body_78_; lean_object* v_value_79_; lean_object* v_body_80_; uint8_t v___x_81_; 
v_value_77_ = lean_ctor_get(v_e_u2081_54_, 2);
lean_inc_ref(v_value_77_);
v_body_78_ = lean_ctor_get(v_e_u2081_54_, 3);
lean_inc_ref(v_body_78_);
lean_dec_ref_known(v_e_u2081_54_, 4);
v_value_79_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_value_79_);
v_body_80_ = lean_ctor_get(v_e_u2082_55_, 3);
lean_inc_ref(v_body_80_);
lean_dec_ref_known(v_e_u2082_55_, 4);
v___x_81_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_77_, v_value_79_);
lean_dec_ref(v_value_79_);
lean_dec_ref(v_value_77_);
if (v___x_81_ == 0)
{
lean_dec_ref(v_body_80_);
lean_dec_ref(v_body_78_);
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_78_, v_body_80_);
lean_dec_ref(v_body_80_);
lean_dec_ref(v_body_78_);
return v___x_82_;
}
}
else
{
uint8_t v___x_83_; 
lean_dec_ref_known(v_e_u2081_54_, 4);
lean_dec_ref(v_e_u2082_55_);
v___x_83_ = 0;
return v___x_83_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_55_) == 10)
{
lean_object* v_data_84_; lean_object* v_expr_85_; lean_object* v_data_86_; lean_object* v_expr_87_; uint8_t v___x_88_; 
v_data_84_ = lean_ctor_get(v_e_u2081_54_, 0);
lean_inc(v_data_84_);
v_expr_85_ = lean_ctor_get(v_e_u2081_54_, 1);
lean_inc_ref(v_expr_85_);
lean_dec_ref_known(v_e_u2081_54_, 2);
v_data_86_ = lean_ctor_get(v_e_u2082_55_, 0);
lean_inc(v_data_86_);
v_expr_87_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_expr_87_);
lean_dec_ref_known(v_e_u2082_55_, 2);
v___x_88_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_85_, v_expr_87_);
lean_dec_ref(v_expr_87_);
lean_dec_ref(v_expr_85_);
if (v___x_88_ == 0)
{
lean_dec(v_data_86_);
lean_dec(v_data_84_);
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = l_Lean_KVMap_eqv(v_data_84_, v_data_86_);
return v___x_89_;
}
}
else
{
uint8_t v___x_90_; 
lean_dec_ref_known(v_e_u2081_54_, 2);
lean_dec_ref(v_e_u2082_55_);
v___x_90_ = 0;
return v___x_90_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_55_) == 11)
{
lean_object* v_typeName_91_; lean_object* v_idx_92_; lean_object* v_struct_93_; lean_object* v_typeName_94_; lean_object* v_idx_95_; lean_object* v_struct_96_; uint8_t v___y_98_; uint8_t v___x_100_; 
v_typeName_91_ = lean_ctor_get(v_e_u2081_54_, 0);
lean_inc(v_typeName_91_);
v_idx_92_ = lean_ctor_get(v_e_u2081_54_, 1);
lean_inc(v_idx_92_);
v_struct_93_ = lean_ctor_get(v_e_u2081_54_, 2);
lean_inc_ref(v_struct_93_);
lean_dec_ref_known(v_e_u2081_54_, 3);
v_typeName_94_ = lean_ctor_get(v_e_u2082_55_, 0);
lean_inc(v_typeName_94_);
v_idx_95_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc(v_idx_95_);
v_struct_96_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_struct_96_);
lean_dec_ref_known(v_e_u2082_55_, 3);
v___x_100_ = lean_name_eq(v_typeName_91_, v_typeName_94_);
lean_dec(v_typeName_94_);
lean_dec(v_typeName_91_);
if (v___x_100_ == 0)
{
lean_dec(v_idx_95_);
lean_dec(v_idx_92_);
v___y_98_ = v___x_100_;
goto v___jp_97_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_eq(v_idx_92_, v_idx_95_);
lean_dec(v_idx_95_);
lean_dec(v_idx_92_);
v___y_98_ = v___x_101_;
goto v___jp_97_;
}
v___jp_97_:
{
if (v___y_98_ == 0)
{
lean_dec_ref(v_struct_96_);
lean_dec_ref(v_struct_93_);
return v___y_98_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_93_, v_struct_96_);
lean_dec_ref(v_struct_96_);
lean_dec_ref(v_struct_93_);
return v___x_99_;
}
}
}
else
{
uint8_t v___x_102_; 
lean_dec_ref_known(v_e_u2081_54_, 3);
lean_dec_ref(v_e_u2082_55_);
v___x_102_ = 0;
return v___x_102_;
}
}
default: 
{
uint8_t v___x_103_; 
v___x_103_ = lean_expr_eqv(v_e_u2081_54_, v_e_u2082_55_);
lean_dec_ref(v_e_u2082_55_);
lean_dec_ref(v_e_u2081_54_);
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object* v_e_u2081_104_, lean_object* v_e_u2082_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_e_u2081_104_, v_e_u2082_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_108_){
_start:
{
uint64_t v___x_109_; 
v___x_109_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_110_){
_start:
{
uint64_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_110_);
lean_dec_ref(v_k_110_);
v_r_112_ = lean_box_uint64(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_115_, lean_object* v_k_u2082_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_115_, v_k_u2082_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_118_, lean_object* v_k_u2082_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_118_, v_k_u2082_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_box(0);
v___x_128_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_129_ = l_Lean_mkConst(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_131_, lean_object* v_i_132_, lean_object* v_k_133_, lean_object* v_k_u2080_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_array_get_size(v_keys_131_);
v___x_136_ = lean_nat_dec_lt(v_i_132_, v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v_k_133_);
lean_dec(v_i_132_);
lean_inc_ref(v_k_u2080_134_);
return v_k_u2080_134_;
}
else
{
lean_object* v_k_x27_137_; uint8_t v___x_138_; 
v_k_x27_137_ = lean_array_fget_borrowed(v_keys_131_, v_i_132_);
lean_inc(v_k_x27_137_);
lean_inc_ref(v_k_133_);
v___x_138_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_133_, v_k_x27_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_add(v_i_132_, v___x_139_);
lean_dec(v_i_132_);
v_i_132_ = v___x_140_;
goto _start;
}
else
{
lean_dec_ref(v_k_133_);
lean_dec(v_i_132_);
lean_inc(v_k_x27_137_);
return v_k_x27_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_142_, lean_object* v_i_143_, lean_object* v_k_144_, lean_object* v_k_u2080_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_142_, v_i_143_, v_k_144_, v_k_u2080_145_);
lean_dec_ref(v_k_u2080_145_);
lean_dec_ref(v_keys_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_147_, size_t v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v_es_151_; lean_object* v___x_152_; size_t v___x_153_; size_t v___x_154_; lean_object* v_j_155_; lean_object* v___x_156_; 
v_es_151_ = lean_ctor_get(v_x_147_, 0);
lean_inc_ref(v_es_151_);
lean_dec_ref_known(v_x_147_, 1);
v___x_152_ = lean_box(2);
v___x_153_ = ((size_t)31ULL);
v___x_154_ = lean_usize_land(v_x_148_, v___x_153_);
v_j_155_ = lean_usize_to_nat(v___x_154_);
v___x_156_ = lean_array_get(v___x_152_, v_es_151_, v_j_155_);
lean_dec(v_j_155_);
lean_dec_ref(v_es_151_);
switch(lean_obj_tag(v___x_156_))
{
case 0:
{
lean_object* v_key_157_; uint8_t v___x_158_; 
v_key_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc_n(v_key_157_, 2);
lean_dec_ref_known(v___x_156_, 2);
v___x_158_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_149_, v_key_157_);
if (v___x_158_ == 0)
{
lean_dec(v_key_157_);
lean_inc_ref(v_x_150_);
return v_x_150_;
}
else
{
return v_key_157_;
}
}
case 1:
{
lean_object* v_node_159_; size_t v___x_160_; size_t v___x_161_; 
v_node_159_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_node_159_);
lean_dec_ref_known(v___x_156_, 1);
v___x_160_ = ((size_t)5ULL);
v___x_161_ = lean_usize_shift_right(v_x_148_, v___x_160_);
v_x_147_ = v_node_159_;
v_x_148_ = v___x_161_;
goto _start;
}
default: 
{
lean_dec_ref(v_x_149_);
lean_inc_ref(v_x_150_);
return v_x_150_;
}
}
}
else
{
lean_object* v_ks_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_ks_163_ = lean_ctor_get(v_x_147_, 0);
lean_inc_ref(v_ks_163_);
lean_dec_ref_known(v_x_147_, 2);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_163_, v___x_164_, v_x_149_, v_x_150_);
lean_dec_ref(v_ks_163_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
size_t v_x_1898__boxed_170_; lean_object* v_res_171_; 
v_x_1898__boxed_170_ = lean_unbox_usize(v_x_167_);
lean_dec(v_x_167_);
v_res_171_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_166_, v_x_1898__boxed_170_, v_x_168_, v_x_169_);
lean_dec_ref(v_x_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_ks_176_; lean_object* v_vs_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_201_; 
v_ks_176_ = lean_ctor_get(v_x_172_, 0);
v_vs_177_ = lean_ctor_get(v_x_172_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_172_);
if (v_isSharedCheck_201_ == 0)
{
v___x_179_ = v_x_172_;
v_isShared_180_ = v_isSharedCheck_201_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_vs_177_);
lean_inc(v_ks_176_);
lean_dec(v_x_172_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_201_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_array_get_size(v_ks_176_);
v___x_182_ = lean_nat_dec_lt(v_x_173_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v_x_173_);
v___x_183_ = lean_array_push(v_ks_176_, v_x_174_);
v___x_184_ = lean_array_push(v_vs_177_, v_x_175_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_184_);
lean_ctor_set(v___x_179_, 0, v___x_183_);
v___x_186_ = v___x_179_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
else
{
lean_object* v_k_x27_188_; uint8_t v___x_189_; 
v_k_x27_188_ = lean_array_fget_borrowed(v_ks_176_, v_x_173_);
lean_inc(v_k_x27_188_);
lean_inc_ref(v_x_174_);
v___x_189_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_174_, v_k_x27_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_191_; 
if (v_isShared_180_ == 0)
{
v___x_191_ = v___x_179_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_ks_176_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_vs_177_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_add(v_x_173_, v___x_192_);
lean_dec(v_x_173_);
v_x_172_ = v___x_191_;
v_x_173_ = v___x_193_;
goto _start;
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_array_fset(v_ks_176_, v_x_173_, v_x_174_);
v___x_197_ = lean_array_fset(v_vs_177_, v_x_173_, v_x_175_);
lean_dec(v_x_173_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_197_);
lean_ctor_set(v___x_179_, 0, v___x_196_);
v___x_199_ = v___x_179_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_202_, lean_object* v_k_203_, lean_object* v_v_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_202_, v___x_205_, v_k_203_, v_v_204_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_208_, size_t v_x_209_, size_t v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v_es_213_; size_t v___x_214_; size_t v___x_215_; lean_object* v_j_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_es_213_ = lean_ctor_get(v_x_208_, 0);
v___x_214_ = ((size_t)31ULL);
v___x_215_ = lean_usize_land(v_x_209_, v___x_214_);
v_j_216_ = lean_usize_to_nat(v___x_215_);
v___x_217_ = lean_array_get_size(v_es_213_);
v___x_218_ = lean_nat_dec_lt(v_j_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec(v_j_216_);
lean_dec(v_x_212_);
lean_dec_ref(v_x_211_);
return v_x_208_;
}
else
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_257_; 
lean_inc_ref(v_es_213_);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_x_208_, 0);
lean_dec(v_unused_258_);
v___x_220_ = v_x_208_;
v_isShared_221_ = v_isSharedCheck_257_;
goto v_resetjp_219_;
}
else
{
lean_dec(v_x_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_257_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_v_222_; lean_object* v___x_223_; lean_object* v_xs_x27_224_; lean_object* v___y_226_; 
v_v_222_ = lean_array_fget(v_es_213_, v_j_216_);
v___x_223_ = lean_box(0);
v_xs_x27_224_ = lean_array_fset(v_es_213_, v_j_216_, v___x_223_);
switch(lean_obj_tag(v_v_222_))
{
case 0:
{
lean_object* v_key_231_; lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_242_; 
v_key_231_ = lean_ctor_get(v_v_222_, 0);
v_val_232_ = lean_ctor_get(v_v_222_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_v_222_);
if (v_isSharedCheck_242_ == 0)
{
v___x_234_ = v_v_222_;
v_isShared_235_ = v_isSharedCheck_242_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_inc(v_key_231_);
lean_dec(v_v_222_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_242_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint8_t v___x_236_; 
lean_inc(v_key_231_);
lean_inc_ref(v_x_211_);
v___x_236_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_211_, v_key_231_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_del_object(v___x_234_);
v___x_237_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_231_, v_val_232_, v_x_211_, v_x_212_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
v___y_226_ = v___x_238_;
goto v___jp_225_;
}
else
{
lean_object* v___x_240_; 
lean_dec(v_val_232_);
lean_dec(v_key_231_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v_x_212_);
lean_ctor_set(v___x_234_, 0, v_x_211_);
v___x_240_ = v___x_234_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_x_211_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_x_212_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v___y_226_ = v___x_240_;
goto v___jp_225_;
}
}
}
}
case 1:
{
lean_object* v_node_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_255_; 
v_node_243_ = lean_ctor_get(v_v_222_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_v_222_);
if (v_isSharedCheck_255_ == 0)
{
v___x_245_ = v_v_222_;
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_node_243_);
lean_dec(v_v_222_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_255_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_247_ = ((size_t)5ULL);
v___x_248_ = lean_usize_shift_right(v_x_209_, v___x_247_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_add(v_x_210_, v___x_249_);
v___x_251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_243_, v___x_248_, v___x_250_, v_x_211_, v_x_212_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_251_);
v___x_253_ = v___x_245_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v___y_226_ = v___x_253_;
goto v___jp_225_;
}
}
}
default: 
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_x_211_);
lean_ctor_set(v___x_256_, 1, v_x_212_);
v___y_226_ = v___x_256_;
goto v___jp_225_;
}
}
v___jp_225_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_array_fset(v_xs_x27_224_, v_j_216_, v___y_226_);
lean_dec(v_j_216_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_227_);
v___x_229_ = v___x_220_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
else
{
lean_object* v_ks_259_; lean_object* v_vs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_280_; 
v_ks_259_ = lean_ctor_get(v_x_208_, 0);
v_vs_260_ = lean_ctor_get(v_x_208_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_280_ == 0)
{
v___x_262_ = v_x_208_;
v_isShared_263_ = v_isSharedCheck_280_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_vs_260_);
lean_inc(v_ks_259_);
lean_dec(v_x_208_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_280_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_ks_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_vs_260_);
v___x_265_ = v_reuseFailAlloc_279_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v_newNode_266_; uint8_t v___y_268_; size_t v___x_274_; uint8_t v___x_275_; 
v_newNode_266_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_265_, v_x_211_, v_x_212_);
v___x_274_ = ((size_t)7ULL);
v___x_275_ = lean_usize_dec_le(v___x_274_, v_x_210_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_266_);
v___x_277_ = lean_unsigned_to_nat(4u);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
lean_dec(v___x_276_);
v___y_268_ = v___x_278_;
goto v___jp_267_;
}
else
{
v___y_268_ = v___x_275_;
goto v___jp_267_;
}
v___jp_267_:
{
if (v___y_268_ == 0)
{
lean_object* v_ks_269_; lean_object* v_vs_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_ks_269_ = lean_ctor_get(v_newNode_266_, 0);
lean_inc_ref(v_ks_269_);
v_vs_270_ = lean_ctor_get(v_newNode_266_, 1);
lean_inc_ref(v_vs_270_);
lean_dec_ref(v_newNode_266_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_210_, v_ks_269_, v_vs_270_, v___x_271_, v___x_272_);
lean_dec_ref(v_vs_270_);
lean_dec_ref(v_ks_269_);
return v___x_273_;
}
else
{
return v_newNode_266_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_281_, lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_entries_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_keys_282_);
v___x_287_ = lean_nat_dec_lt(v_i_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_dec(v_i_284_);
return v_entries_285_;
}
else
{
lean_object* v_k_288_; lean_object* v_v_289_; uint64_t v___x_290_; size_t v_h_291_; size_t v___x_292_; lean_object* v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v_h_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_k_288_ = lean_array_fget_borrowed(v_keys_282_, v_i_284_);
v_v_289_ = lean_array_fget_borrowed(v_vals_283_, v_i_284_);
v___x_290_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_288_);
v_h_291_ = lean_uint64_to_usize(v___x_290_);
v___x_292_ = ((size_t)5ULL);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_sub(v_depth_281_, v___x_294_);
v___x_296_ = lean_usize_mul(v___x_292_, v___x_295_);
v_h_297_ = lean_usize_shift_right(v_h_291_, v___x_296_);
v___x_298_ = lean_nat_add(v_i_284_, v___x_293_);
lean_dec(v_i_284_);
lean_inc(v_v_289_);
lean_inc(v_k_288_);
v___x_299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_285_, v_h_297_, v_depth_281_, v_k_288_, v_v_289_);
v_i_284_ = v___x_298_;
v_entries_285_ = v___x_299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_301_, lean_object* v_keys_302_, lean_object* v_vals_303_, lean_object* v_i_304_, lean_object* v_entries_305_){
_start:
{
size_t v_depth_boxed_306_; lean_object* v_res_307_; 
v_depth_boxed_306_ = lean_unbox_usize(v_depth_301_);
lean_dec(v_depth_301_);
v_res_307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_306_, v_keys_302_, v_vals_303_, v_i_304_, v_entries_305_);
lean_dec_ref(v_vals_303_);
lean_dec_ref(v_keys_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
size_t v_x_2016__boxed_313_; size_t v_x_2017__boxed_314_; lean_object* v_res_315_; 
v_x_2016__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_x_2017__boxed_314_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_res_315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_308_, v_x_2016__boxed_313_, v_x_2017__boxed_314_, v_x_311_, v_x_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint64_t v___x_319_; size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_319_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_317_);
v___x_320_ = lean_uint64_to_usize(v___x_319_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_316_, v___x_320_, v___x_321_, v_x_317_, v_x_318_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_323_, lean_object* v_b_324_, lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_dec(v_b_324_);
lean_dec_ref(v_a_323_);
return v_x_325_;
}
else
{
lean_object* v_key_326_; lean_object* v_value_327_; lean_object* v_tail_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_340_; 
v_key_326_ = lean_ctor_get(v_x_325_, 0);
v_value_327_ = lean_ctor_get(v_x_325_, 1);
v_tail_328_ = lean_ctor_get(v_x_325_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_340_ == 0)
{
v___x_330_ = v_x_325_;
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_tail_328_);
lean_inc(v_value_327_);
lean_inc(v_key_326_);
lean_dec(v_x_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
uint8_t v___x_332_; 
v___x_332_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_326_, v_a_323_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_323_, v_b_324_, v_tail_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 2, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_key_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_value_327_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v___x_338_; 
lean_dec(v_value_327_);
lean_dec(v_key_326_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_b_324_);
lean_ctor_set(v___x_330_, 0, v_a_323_);
v___x_338_ = v___x_330_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_323_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_b_324_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_tail_328_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
return v_x_341_;
}
else
{
lean_object* v_key_343_; lean_object* v_value_344_; lean_object* v_tail_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_368_; 
v_key_343_ = lean_ctor_get(v_x_342_, 0);
v_value_344_ = lean_ctor_get(v_x_342_, 1);
v_tail_345_ = lean_ctor_get(v_x_342_, 2);
v_isSharedCheck_368_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_368_ == 0)
{
v___x_347_ = v_x_342_;
v_isShared_348_ = v_isSharedCheck_368_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_tail_345_);
lean_inc(v_value_344_);
lean_inc(v_key_343_);
lean_dec(v_x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_368_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v_fold_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_349_ = lean_array_get_size(v_x_341_);
v___x_350_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_343_);
v___x_351_ = 32ULL;
v___x_352_ = lean_uint64_shift_right(v___x_350_, v___x_351_);
v_fold_353_ = lean_uint64_xor(v___x_350_, v___x_352_);
v___x_354_ = 16ULL;
v___x_355_ = lean_uint64_shift_right(v_fold_353_, v___x_354_);
v___x_356_ = lean_uint64_xor(v_fold_353_, v___x_355_);
v___x_357_ = lean_uint64_to_usize(v___x_356_);
v___x_358_ = lean_usize_of_nat(v___x_349_);
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_sub(v___x_358_, v___x_359_);
v___x_361_ = lean_usize_land(v___x_357_, v___x_360_);
v___x_362_ = lean_array_uget_borrowed(v_x_341_, v___x_361_);
lean_inc(v___x_362_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 2, v___x_362_);
v___x_364_ = v___x_347_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_key_343_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_value_344_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v___x_362_);
v___x_364_ = v_reuseFailAlloc_367_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_array_uset(v_x_341_, v___x_361_, v___x_364_);
v_x_341_ = v___x_365_;
v_x_342_ = v_tail_345_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_369_, lean_object* v_source_370_, lean_object* v_target_371_){
_start:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_array_get_size(v_source_370_);
v___x_373_ = lean_nat_dec_lt(v_i_369_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v_source_370_);
lean_dec(v_i_369_);
return v_target_371_;
}
else
{
lean_object* v_es_374_; lean_object* v___x_375_; lean_object* v_source_376_; lean_object* v_target_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_es_374_ = lean_array_fget(v_source_370_, v_i_369_);
v___x_375_ = lean_box(0);
v_source_376_ = lean_array_fset(v_source_370_, v_i_369_, v___x_375_);
v_target_377_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_371_, v_es_374_);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_i_369_, v___x_378_);
lean_dec(v_i_369_);
v_i_369_ = v___x_379_;
v_source_370_ = v_source_376_;
v_target_371_ = v_target_377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_nbuckets_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_382_ = lean_array_get_size(v_data_381_);
v___x_383_ = lean_unsigned_to_nat(2u);
v_nbuckets_384_ = lean_nat_mul(v___x_382_, v___x_383_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_box(0);
v___x_387_ = lean_mk_array(v_nbuckets_384_, v___x_386_);
v___x_388_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_385_, v_data_381_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
else
{
lean_object* v_key_392_; lean_object* v_tail_393_; uint8_t v___x_394_; 
v_key_392_ = lean_ctor_get(v_x_390_, 0);
v_tail_393_ = lean_ctor_get(v_x_390_, 2);
v___x_394_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_392_, v_a_389_);
if (v___x_394_ == 0)
{
v_x_390_ = v_tail_393_;
goto _start;
}
else
{
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_396_, lean_object* v_x_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_396_, v_x_397_);
lean_dec(v_x_397_);
lean_dec_ref(v_a_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_400_, lean_object* v_a_401_, lean_object* v_b_402_){
_start:
{
lean_object* v_size_403_; lean_object* v_buckets_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_447_; 
v_size_403_ = lean_ctor_get(v_m_400_, 0);
v_buckets_404_ = lean_ctor_get(v_m_400_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_m_400_);
if (v_isSharedCheck_447_ == 0)
{
v___x_406_ = v_m_400_;
v_isShared_407_ = v_isSharedCheck_447_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_buckets_404_);
lean_inc(v_size_403_);
lean_dec(v_m_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_447_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v_fold_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v_bkt_421_; uint8_t v___x_422_; 
v___x_408_ = lean_array_get_size(v_buckets_404_);
v___x_409_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_401_);
v___x_410_ = 32ULL;
v___x_411_ = lean_uint64_shift_right(v___x_409_, v___x_410_);
v_fold_412_ = lean_uint64_xor(v___x_409_, v___x_411_);
v___x_413_ = 16ULL;
v___x_414_ = lean_uint64_shift_right(v_fold_412_, v___x_413_);
v___x_415_ = lean_uint64_xor(v_fold_412_, v___x_414_);
v___x_416_ = lean_uint64_to_usize(v___x_415_);
v___x_417_ = lean_usize_of_nat(v___x_408_);
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_sub(v___x_417_, v___x_418_);
v___x_420_ = lean_usize_land(v___x_416_, v___x_419_);
v_bkt_421_ = lean_array_uget_borrowed(v_buckets_404_, v___x_420_);
v___x_422_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_401_, v_bkt_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v_size_x27_424_; lean_object* v___x_425_; lean_object* v_buckets_x27_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_423_ = lean_unsigned_to_nat(1u);
v_size_x27_424_ = lean_nat_add(v_size_403_, v___x_423_);
lean_dec(v_size_403_);
lean_inc(v_bkt_421_);
v___x_425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_425_, 0, v_a_401_);
lean_ctor_set(v___x_425_, 1, v_b_402_);
lean_ctor_set(v___x_425_, 2, v_bkt_421_);
v_buckets_x27_426_ = lean_array_uset(v_buckets_404_, v___x_420_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(4u);
v___x_428_ = lean_nat_mul(v_size_x27_424_, v___x_427_);
v___x_429_ = lean_unsigned_to_nat(3u);
v___x_430_ = lean_nat_div(v___x_428_, v___x_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_array_get_size(v_buckets_x27_426_);
v___x_432_ = lean_nat_dec_le(v___x_430_, v___x_431_);
lean_dec(v___x_430_);
if (v___x_432_ == 0)
{
lean_object* v_val_433_; lean_object* v___x_435_; 
v_val_433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_426_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_val_433_);
lean_ctor_set(v___x_406_, 0, v_size_x27_424_);
v___x_435_ = v___x_406_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_size_x27_424_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_val_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
else
{
lean_object* v___x_438_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_buckets_x27_426_);
lean_ctor_set(v___x_406_, 0, v_size_x27_424_);
v___x_438_ = v___x_406_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_size_x27_424_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_buckets_x27_426_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v___x_440_; lean_object* v_buckets_x27_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
lean_inc(v_bkt_421_);
v___x_440_ = lean_box(0);
v_buckets_x27_441_ = lean_array_uset(v_buckets_404_, v___x_420_, v___x_440_);
v___x_442_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_401_, v_b_402_, v_bkt_421_);
v___x_443_ = lean_array_uset(v_buckets_x27_441_, v___x_420_, v___x_442_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_443_);
v___x_445_ = v___x_406_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_size_403_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_443_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_448_, lean_object* v_r_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_map_451_; lean_object* v_set_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_474_; 
v_map_451_ = lean_ctor_get(v_a_450_, 0);
v_set_452_ = lean_ctor_get(v_a_450_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_474_ == 0)
{
v___x_454_ = v_a_450_;
v_isShared_455_ = v_isSharedCheck_474_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_set_452_);
lean_inc(v_map_451_);
lean_dec(v_a_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_474_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; uint64_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_456_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_457_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_449_);
v___x_458_ = lean_uint64_to_usize(v___x_457_);
lean_inc_ref(v_r_449_);
lean_inc_ref(v_set_452_);
v___x_459_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_452_, v___x_458_, v_r_449_, v___x_456_);
v___x_460_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_459_, v___x_456_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec_ref(v_r_449_);
lean_inc_ref(v___x_459_);
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_451_, v_e_448_, v___x_459_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_461_);
v___x_463_ = v___x_454_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_set_452_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_459_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
lean_dec_ref(v___x_459_);
lean_inc_ref_n(v_r_449_, 4);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_451_, v_e_448_, v_r_449_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_466_, v_r_449_, v_r_449_);
v___x_468_ = lean_box(0);
v___x_469_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_452_, v_r_449_, v___x_468_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_469_);
lean_ctor_set(v___x_454_, 0, v___x_467_);
v___x_471_ = v___x_454_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_r_449_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_475_, lean_object* v_x_476_, size_t v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_476_, v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
size_t v_x_2436__boxed_486_; lean_object* v_res_487_; 
v_x_2436__boxed_486_ = lean_unbox_usize(v_x_483_);
lean_dec(v_x_483_);
v_res_487_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_481_, v_x_482_, v_x_2436__boxed_486_, v_x_484_, v_x_485_);
lean_dec_ref(v_x_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_488_, lean_object* v_m_489_, lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_489_, v_a_490_, v_b_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_493_, lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_494_, v_x_495_, v_x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_498_, lean_object* v_keys_499_, lean_object* v_vals_500_, lean_object* v_heq_501_, lean_object* v_i_502_, lean_object* v_k_503_, lean_object* v_k_u2080_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_499_, v_i_502_, v_k_503_, v_k_u2080_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_506_, lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_heq_509_, lean_object* v_i_510_, lean_object* v_k_511_, lean_object* v_k_u2080_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_506_, v_keys_507_, v_vals_508_, v_heq_509_, v_i_510_, v_k_511_, v_k_u2080_512_);
lean_dec_ref(v_k_u2080_512_);
lean_dec_ref(v_vals_508_);
lean_dec_ref(v_keys_507_);
return v_res_513_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_514_, lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_518_, lean_object* v_a_519_, lean_object* v_x_520_){
_start:
{
uint8_t v_res_521_; lean_object* v_r_522_; 
v_res_521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_518_, v_a_519_, v_x_520_);
lean_dec(v_x_520_);
lean_dec_ref(v_a_519_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_523_, lean_object* v_data_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_526_, lean_object* v_a_527_, lean_object* v_b_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_527_, v_b_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_531_, lean_object* v_x_532_, size_t v_x_533_, size_t v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_532_, v_x_533_, v_x_534_, v_x_535_, v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_538_, lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
size_t v_x_2473__boxed_544_; size_t v_x_2474__boxed_545_; lean_object* v_res_546_; 
v_x_2473__boxed_544_ = lean_unbox_usize(v_x_540_);
lean_dec(v_x_540_);
v_x_2474__boxed_545_ = lean_unbox_usize(v_x_541_);
lean_dec(v_x_541_);
v_res_546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_538_, v_x_539_, v_x_2473__boxed_544_, v_x_2474__boxed_545_, v_x_542_, v_x_543_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_547_, lean_object* v_i_548_, lean_object* v_source_549_, lean_object* v_target_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_548_, v_source_549_, v_target_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_552_, lean_object* v_n_553_, lean_object* v_k_554_, lean_object* v_v_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_553_, v_k_554_, v_v_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_557_, size_t v_depth_558_, lean_object* v_keys_559_, lean_object* v_vals_560_, lean_object* v_heq_561_, lean_object* v_i_562_, lean_object* v_entries_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_558_, v_keys_559_, v_vals_560_, v_i_562_, v_entries_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_565_, lean_object* v_depth_566_, lean_object* v_keys_567_, lean_object* v_vals_568_, lean_object* v_heq_569_, lean_object* v_i_570_, lean_object* v_entries_571_){
_start:
{
size_t v_depth_boxed_572_; lean_object* v_res_573_; 
v_depth_boxed_572_ = lean_unbox_usize(v_depth_566_);
lean_dec(v_depth_566_);
v_res_573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_565_, v_depth_boxed_572_, v_keys_567_, v_vals_568_, v_heq_569_, v_i_570_, v_entries_571_);
lean_dec_ref(v_vals_568_);
lean_dec_ref(v_keys_567_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_575_, v_x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_579_, v_x_580_, v_x_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_586_, lean_object* v_k_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_map_589_; lean_object* v_set_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___x_593_; 
v_map_589_ = lean_ctor_get(v_a_588_, 0);
v_set_590_ = lean_ctor_get(v_a_588_, 1);
v___f_591_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_592_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_586_);
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_591_, v___f_592_, v_map_589_, v_e_586_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_595_; 
lean_dec_ref(v_k_587_);
lean_dec_ref(v_e_586_);
v_val_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_val_594_);
lean_ctor_set(v___x_595_, 1, v_a_588_);
return v___x_595_;
}
else
{
lean_object* v___f_596_; lean_object* v___x_597_; uint64_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
lean_dec(v___x_593_);
v___f_596_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_597_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_598_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_586_);
v___x_599_ = lean_uint64_to_usize(v___x_598_);
lean_inc_ref(v_e_586_);
lean_inc_ref(v_set_590_);
v___x_600_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_596_, v_set_590_, v___x_599_, v_e_586_, v___x_597_);
v___x_601_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_600_, v___x_597_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_k_587_);
lean_dec_ref(v_e_586_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v_a_588_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; 
lean_dec(v___x_600_);
v___x_603_ = lean_apply_1(v_k_587_, v_a_588_);
v_fst_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v___x_603_, 1);
lean_inc(v_snd_605_);
lean_dec_ref(v___x_603_);
v___x_606_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_586_, v_fst_604_, v_snd_605_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_607_, lean_object* v_vals_608_, lean_object* v_i_609_, lean_object* v_k_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_array_get_size(v_keys_607_);
v___x_612_ = lean_nat_dec_lt(v_i_609_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_dec_ref(v_k_610_);
lean_dec(v_i_609_);
v___x_613_ = lean_box(0);
return v___x_613_;
}
else
{
lean_object* v_k_x27_614_; uint8_t v___x_615_; 
v_k_x27_614_ = lean_array_fget_borrowed(v_keys_607_, v_i_609_);
lean_inc(v_k_x27_614_);
lean_inc_ref(v_k_610_);
v___x_615_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_610_, v_k_x27_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_i_609_, v___x_616_);
lean_dec(v_i_609_);
v_i_609_ = v___x_617_;
goto _start;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v_k_610_);
v___x_619_ = lean_array_fget_borrowed(v_vals_608_, v_i_609_);
lean_dec(v_i_609_);
lean_inc(v___x_619_);
lean_inc(v_k_x27_614_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v_k_x27_614_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_622_, lean_object* v_vals_623_, lean_object* v_i_624_, lean_object* v_k_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_622_, v_vals_623_, v_i_624_, v_k_625_);
lean_dec_ref(v_vals_623_);
lean_dec_ref(v_keys_622_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_x_627_, size_t v_x_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v_es_630_; lean_object* v___x_631_; size_t v___x_632_; size_t v___x_633_; lean_object* v_j_634_; lean_object* v___x_635_; 
v_es_630_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_es_630_);
lean_dec_ref_known(v_x_627_, 1);
v___x_631_ = lean_box(2);
v___x_632_ = ((size_t)31ULL);
v___x_633_ = lean_usize_land(v_x_628_, v___x_632_);
v_j_634_ = lean_usize_to_nat(v___x_633_);
v___x_635_ = lean_array_get(v___x_631_, v_es_630_, v_j_634_);
lean_dec(v_j_634_);
lean_dec_ref(v_es_630_);
switch(lean_obj_tag(v___x_635_))
{
case 0:
{
lean_object* v_key_636_; lean_object* v_val_637_; uint8_t v___x_638_; 
v_key_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_n(v_key_636_, 2);
v_val_637_ = lean_ctor_get(v___x_635_, 1);
lean_inc(v_val_637_);
lean_dec_ref_known(v___x_635_, 2);
v___x_638_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_629_, v_key_636_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec(v_val_637_);
lean_dec(v_key_636_);
v___x_639_ = lean_box(0);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v_key_636_);
lean_ctor_set(v___x_640_, 1, v_val_637_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
case 1:
{
lean_object* v_node_642_; size_t v___x_643_; size_t v___x_644_; 
v_node_642_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_node_642_);
lean_dec_ref_known(v___x_635_, 1);
v___x_643_ = ((size_t)5ULL);
v___x_644_ = lean_usize_shift_right(v_x_628_, v___x_643_);
v_x_627_ = v_node_642_;
v_x_628_ = v___x_644_;
goto _start;
}
default: 
{
lean_object* v___x_646_; 
lean_dec_ref(v_x_629_);
v___x_646_ = lean_box(0);
return v___x_646_;
}
}
}
else
{
lean_object* v_ks_647_; lean_object* v_vs_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_ks_647_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_ks_647_);
v_vs_648_ = lean_ctor_get(v_x_627_, 1);
lean_inc_ref(v_vs_648_);
lean_dec_ref_known(v_x_627_, 2);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_ks_647_, v_vs_648_, v___x_649_, v_x_629_);
lean_dec_ref(v_vs_648_);
lean_dec_ref(v_ks_647_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
size_t v_x_8770__boxed_654_; lean_object* v_res_655_; 
v_x_8770__boxed_654_ = lean_unbox_usize(v_x_652_);
lean_dec(v_x_652_);
v_res_655_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_651_, v_x_8770__boxed_654_, v_x_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
uint64_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_657_);
v___x_659_ = lean_uint64_to_usize(v___x_658_);
lean_inc_ref(v_x_656_);
v___x_660_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_656_, v___x_659_, v_x_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_x_661_, v_x_662_);
lean_dec_ref(v_x_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_a_664_, lean_object* v_x_665_){
_start:
{
if (lean_obj_tag(v_x_665_) == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v_key_667_; lean_object* v_value_668_; lean_object* v_tail_669_; uint8_t v___x_670_; 
v_key_667_ = lean_ctor_get(v_x_665_, 0);
v_value_668_ = lean_ctor_get(v_x_665_, 1);
v_tail_669_ = lean_ctor_get(v_x_665_, 2);
v___x_670_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_667_, v_a_664_);
if (v___x_670_ == 0)
{
v_x_665_ = v_tail_669_;
goto _start;
}
else
{
lean_object* v___x_672_; 
lean_inc(v_value_668_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v_value_668_);
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_673_, v_x_674_);
lean_dec(v_x_674_);
lean_dec_ref(v_a_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_m_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_buckets_678_; lean_object* v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v_fold_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_buckets_678_ = lean_ctor_get(v_m_676_, 1);
v___x_679_ = lean_array_get_size(v_buckets_678_);
v___x_680_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_677_);
v___x_681_ = 32ULL;
v___x_682_ = lean_uint64_shift_right(v___x_680_, v___x_681_);
v_fold_683_ = lean_uint64_xor(v___x_680_, v___x_682_);
v___x_684_ = 16ULL;
v___x_685_ = lean_uint64_shift_right(v_fold_683_, v___x_684_);
v___x_686_ = lean_uint64_xor(v_fold_683_, v___x_685_);
v___x_687_ = lean_uint64_to_usize(v___x_686_);
v___x_688_ = lean_usize_of_nat(v___x_679_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_sub(v___x_688_, v___x_689_);
v___x_691_ = lean_usize_land(v___x_687_, v___x_690_);
v___x_692_ = lean_array_uget_borrowed(v_buckets_678_, v___x_691_);
v___x_693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_677_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_m_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_694_, v_a_695_);
lean_dec_ref(v_a_695_);
lean_dec_ref(v_m_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_697_, lean_object* v_a_698_){
_start:
{
switch(lean_obj_tag(v_e_697_))
{
case 5:
{
lean_object* v_fn_699_; lean_object* v_arg_700_; lean_object* v_map_701_; lean_object* v_set_702_; lean_object* v___x_703_; 
v_fn_699_ = lean_ctor_get(v_e_697_, 0);
v_arg_700_ = lean_ctor_get(v_e_697_, 1);
v_map_701_ = lean_ctor_get(v_a_698_, 0);
v_set_702_ = lean_ctor_get(v_a_698_, 1);
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_701_, v_e_697_);
if (lean_obj_tag(v___x_703_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_705_; 
lean_dec_ref_known(v_e_697_, 2);
v_val_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_val_704_);
lean_ctor_set(v___x_705_, 1, v_a_698_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; uint64_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
lean_dec(v___x_703_);
v___x_706_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_707_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_697_);
v___x_708_ = lean_uint64_to_usize(v___x_707_);
lean_inc_ref(v_e_697_);
lean_inc_ref(v_set_702_);
v___x_709_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_702_, v___x_708_, v_e_697_, v___x_706_);
v___x_710_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_709_, v___x_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec_ref_known(v_e_697_, 2);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v_a_698_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; uint8_t v___y_719_; size_t v___x_723_; size_t v___x_724_; uint8_t v___x_725_; 
lean_dec_ref(v___x_709_);
lean_inc_ref(v_fn_699_);
v___x_712_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_699_, v_a_698_);
v_fst_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_fst_713_);
v_snd_714_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_snd_714_);
lean_dec_ref(v___x_712_);
lean_inc_ref(v_arg_700_);
v___x_715_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_700_, v_snd_714_);
v_fst_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_fst_716_);
v_snd_717_ = lean_ctor_get(v___x_715_, 1);
lean_inc(v_snd_717_);
lean_dec_ref(v___x_715_);
v___x_723_ = lean_ptr_addr(v_fn_699_);
v___x_724_ = lean_ptr_addr(v_fst_713_);
v___x_725_ = lean_usize_dec_eq(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
v___y_719_ = v___x_725_;
goto v___jp_718_;
}
else
{
size_t v___x_726_; size_t v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_ptr_addr(v_arg_700_);
v___x_727_ = lean_ptr_addr(v_fst_716_);
v___x_728_ = lean_usize_dec_eq(v___x_726_, v___x_727_);
v___y_719_ = v___x_728_;
goto v___jp_718_;
}
v___jp_718_:
{
if (v___y_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l_Lean_Expr_app___override(v_fst_713_, v_fst_716_);
v___x_721_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_720_, v_snd_717_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
lean_dec(v_fst_716_);
lean_dec(v_fst_713_);
lean_inc_ref(v_e_697_);
v___x_722_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v_e_697_, v_snd_717_);
return v___x_722_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_729_; lean_object* v_binderType_730_; lean_object* v_body_731_; uint8_t v_binderInfo_732_; lean_object* v_map_733_; lean_object* v_set_734_; lean_object* v___x_735_; 
v_binderName_729_ = lean_ctor_get(v_e_697_, 0);
v_binderType_730_ = lean_ctor_get(v_e_697_, 1);
v_body_731_ = lean_ctor_get(v_e_697_, 2);
v_binderInfo_732_ = lean_ctor_get_uint8(v_e_697_, sizeof(void*)*3 + 8);
v_map_733_ = lean_ctor_get(v_a_698_, 0);
v_set_734_ = lean_ctor_get(v_a_698_, 1);
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_733_, v_e_697_);
if (lean_obj_tag(v___x_735_) == 1)
{
lean_object* v_val_736_; lean_object* v___x_737_; 
lean_dec_ref_known(v_e_697_, 3);
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_val_736_);
lean_ctor_set(v___x_737_, 1, v_a_698_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; uint64_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
lean_dec(v___x_735_);
v___x_738_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_739_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_697_);
v___x_740_ = lean_uint64_to_usize(v___x_739_);
lean_inc_ref(v_e_697_);
lean_inc_ref(v_set_734_);
v___x_741_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_734_, v___x_740_, v_e_697_, v___x_738_);
v___x_742_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_741_, v___x_738_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec_ref_known(v_e_697_, 3);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v_a_698_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___x_747_; lean_object* v_fst_748_; lean_object* v_snd_749_; uint8_t v___y_751_; size_t v___x_758_; size_t v___x_759_; uint8_t v___x_760_; 
lean_dec_ref(v___x_741_);
lean_inc_ref(v_binderType_730_);
v___x_744_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_730_, v_a_698_);
v_fst_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_fst_745_);
v_snd_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_snd_746_);
lean_dec_ref(v___x_744_);
lean_inc_ref(v_body_731_);
v___x_747_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_731_, v_snd_746_);
v_fst_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_fst_748_);
v_snd_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc(v_snd_749_);
lean_dec_ref(v___x_747_);
v___x_758_ = lean_ptr_addr(v_binderType_730_);
v___x_759_ = lean_ptr_addr(v_fst_745_);
v___x_760_ = lean_usize_dec_eq(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
v___y_751_ = v___x_760_;
goto v___jp_750_;
}
else
{
size_t v___x_761_; size_t v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_ptr_addr(v_body_731_);
v___x_762_ = lean_ptr_addr(v_fst_748_);
v___x_763_ = lean_usize_dec_eq(v___x_761_, v___x_762_);
v___y_751_ = v___x_763_;
goto v___jp_750_;
}
v___jp_750_:
{
if (v___y_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_inc(v_binderName_729_);
v___x_752_ = l_Lean_Expr_lam___override(v_binderName_729_, v_fst_745_, v_fst_748_, v_binderInfo_732_);
v___x_753_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_752_, v_snd_749_);
return v___x_753_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_732_, v_binderInfo_732_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_inc(v_binderName_729_);
v___x_755_ = l_Lean_Expr_lam___override(v_binderName_729_, v_fst_745_, v_fst_748_, v_binderInfo_732_);
v___x_756_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_755_, v_snd_749_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; 
lean_dec(v_fst_748_);
lean_dec(v_fst_745_);
lean_inc_ref(v_e_697_);
v___x_757_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v_e_697_, v_snd_749_);
return v___x_757_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_764_; lean_object* v_binderType_765_; lean_object* v_body_766_; uint8_t v_binderInfo_767_; lean_object* v_map_768_; lean_object* v_set_769_; lean_object* v___x_770_; 
v_binderName_764_ = lean_ctor_get(v_e_697_, 0);
v_binderType_765_ = lean_ctor_get(v_e_697_, 1);
v_body_766_ = lean_ctor_get(v_e_697_, 2);
v_binderInfo_767_ = lean_ctor_get_uint8(v_e_697_, sizeof(void*)*3 + 8);
v_map_768_ = lean_ctor_get(v_a_698_, 0);
v_set_769_ = lean_ctor_get(v_a_698_, 1);
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_768_, v_e_697_);
if (lean_obj_tag(v___x_770_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_772_; 
lean_dec_ref_known(v_e_697_, 3);
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_val_771_);
lean_ctor_set(v___x_772_, 1, v_a_698_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; uint64_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
lean_dec(v___x_770_);
v___x_773_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_774_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_697_);
v___x_775_ = lean_uint64_to_usize(v___x_774_);
lean_inc_ref(v_e_697_);
lean_inc_ref(v_set_769_);
v___x_776_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_769_, v___x_775_, v_e_697_, v___x_773_);
v___x_777_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_776_, v___x_773_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec_ref_known(v_e_697_, 3);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v_a_698_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_782_; lean_object* v_fst_783_; lean_object* v_snd_784_; uint8_t v___y_786_; size_t v___x_793_; size_t v___x_794_; uint8_t v___x_795_; 
lean_dec_ref(v___x_776_);
lean_inc_ref(v_binderType_765_);
v___x_779_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_765_, v_a_698_);
v_fst_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_fst_780_);
v_snd_781_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_snd_781_);
lean_dec_ref(v___x_779_);
lean_inc_ref(v_body_766_);
v___x_782_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_766_, v_snd_781_);
v_fst_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_fst_783_);
v_snd_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_snd_784_);
lean_dec_ref(v___x_782_);
v___x_793_ = lean_ptr_addr(v_binderType_765_);
v___x_794_ = lean_ptr_addr(v_fst_780_);
v___x_795_ = lean_usize_dec_eq(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
v___y_786_ = v___x_795_;
goto v___jp_785_;
}
else
{
size_t v___x_796_; size_t v___x_797_; uint8_t v___x_798_; 
v___x_796_ = lean_ptr_addr(v_body_766_);
v___x_797_ = lean_ptr_addr(v_fst_783_);
v___x_798_ = lean_usize_dec_eq(v___x_796_, v___x_797_);
v___y_786_ = v___x_798_;
goto v___jp_785_;
}
v___jp_785_:
{
if (v___y_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc(v_binderName_764_);
v___x_787_ = l_Lean_Expr_forallE___override(v_binderName_764_, v_fst_780_, v_fst_783_, v_binderInfo_767_);
v___x_788_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_787_, v_snd_784_);
return v___x_788_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_767_, v_binderInfo_767_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
lean_inc(v_binderName_764_);
v___x_790_ = l_Lean_Expr_forallE___override(v_binderName_764_, v_fst_780_, v_fst_783_, v_binderInfo_767_);
v___x_791_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_790_, v_snd_784_);
return v___x_791_;
}
else
{
lean_object* v___x_792_; 
lean_dec(v_fst_783_);
lean_dec(v_fst_780_);
lean_inc_ref(v_e_697_);
v___x_792_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v_e_697_, v_snd_784_);
return v___x_792_;
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_799_; lean_object* v_type_800_; lean_object* v_value_801_; lean_object* v_body_802_; uint8_t v_nondep_803_; lean_object* v_map_804_; lean_object* v_set_805_; lean_object* v___x_806_; 
v_declName_799_ = lean_ctor_get(v_e_697_, 0);
v_type_800_ = lean_ctor_get(v_e_697_, 1);
v_value_801_ = lean_ctor_get(v_e_697_, 2);
v_body_802_ = lean_ctor_get(v_e_697_, 3);
v_nondep_803_ = lean_ctor_get_uint8(v_e_697_, sizeof(void*)*4 + 8);
v_map_804_ = lean_ctor_get(v_a_698_, 0);
v_set_805_ = lean_ctor_get(v_a_698_, 1);
v___x_806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_804_, v_e_697_);
if (lean_obj_tag(v___x_806_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_808_; 
lean_dec_ref_known(v_e_697_, 4);
v_val_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v___x_806_, 1);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_val_807_);
lean_ctor_set(v___x_808_, 1, v_a_698_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; uint64_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
lean_dec(v___x_806_);
v___x_809_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_810_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_697_);
v___x_811_ = lean_uint64_to_usize(v___x_810_);
lean_inc_ref(v_e_697_);
lean_inc_ref(v_set_805_);
v___x_812_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_805_, v___x_811_, v_e_697_, v___x_809_);
v___x_813_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_812_, v___x_809_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; 
lean_dec_ref_known(v_e_697_, 4);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v_a_698_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___x_818_; lean_object* v_fst_819_; lean_object* v_snd_820_; lean_object* v___x_821_; lean_object* v_fst_822_; lean_object* v_snd_823_; uint8_t v___y_825_; size_t v___x_834_; size_t v___x_835_; uint8_t v___x_836_; 
lean_dec_ref(v___x_812_);
lean_inc_ref(v_type_800_);
v___x_815_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_800_, v_a_698_);
v_fst_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_fst_816_);
v_snd_817_ = lean_ctor_get(v___x_815_, 1);
lean_inc(v_snd_817_);
lean_dec_ref(v___x_815_);
lean_inc_ref(v_value_801_);
v___x_818_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_801_, v_snd_817_);
v_fst_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_fst_819_);
v_snd_820_ = lean_ctor_get(v___x_818_, 1);
lean_inc(v_snd_820_);
lean_dec_ref(v___x_818_);
lean_inc_ref(v_body_802_);
v___x_821_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_802_, v_snd_820_);
v_fst_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_fst_822_);
v_snd_823_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_snd_823_);
lean_dec_ref(v___x_821_);
v___x_834_ = lean_ptr_addr(v_type_800_);
v___x_835_ = lean_ptr_addr(v_fst_816_);
v___x_836_ = lean_usize_dec_eq(v___x_834_, v___x_835_);
if (v___x_836_ == 0)
{
v___y_825_ = v___x_836_;
goto v___jp_824_;
}
else
{
size_t v___x_837_; size_t v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_ptr_addr(v_value_801_);
v___x_838_ = lean_ptr_addr(v_fst_819_);
v___x_839_ = lean_usize_dec_eq(v___x_837_, v___x_838_);
v___y_825_ = v___x_839_;
goto v___jp_824_;
}
v___jp_824_:
{
if (v___y_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_inc(v_declName_799_);
v___x_826_ = l_Lean_Expr_letE___override(v_declName_799_, v_fst_816_, v_fst_819_, v_fst_822_, v_nondep_803_);
v___x_827_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_826_, v_snd_823_);
return v___x_827_;
}
else
{
size_t v___x_828_; size_t v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_ptr_addr(v_body_802_);
v___x_829_ = lean_ptr_addr(v_fst_822_);
v___x_830_ = lean_usize_dec_eq(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_inc(v_declName_799_);
v___x_831_ = l_Lean_Expr_letE___override(v_declName_799_, v_fst_816_, v_fst_819_, v_fst_822_, v_nondep_803_);
v___x_832_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_831_, v_snd_823_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; 
lean_dec(v_fst_822_);
lean_dec(v_fst_819_);
lean_dec(v_fst_816_);
lean_inc_ref(v_e_697_);
v___x_833_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v_e_697_, v_snd_823_);
return v___x_833_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_840_; lean_object* v_expr_841_; lean_object* v_map_842_; lean_object* v_set_843_; lean_object* v___x_844_; 
v_data_840_ = lean_ctor_get(v_e_697_, 0);
v_expr_841_ = lean_ctor_get(v_e_697_, 1);
v_map_842_ = lean_ctor_get(v_a_698_, 0);
v_set_843_ = lean_ctor_get(v_a_698_, 1);
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_842_, v_e_697_);
if (lean_obj_tag(v___x_844_) == 1)
{
lean_object* v_val_845_; lean_object* v___x_846_; 
lean_dec_ref_known(v_e_697_, 2);
v_val_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_val_845_);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_val_845_);
lean_ctor_set(v___x_846_, 1, v_a_698_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; uint64_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
lean_dec(v___x_844_);
v___x_847_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_848_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_697_);
v___x_849_ = lean_uint64_to_usize(v___x_848_);
lean_inc_ref(v_e_697_);
lean_inc_ref(v_set_843_);
v___x_850_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_843_, v___x_849_, v_e_697_, v___x_847_);
v___x_851_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_850_, v___x_847_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
lean_dec_ref_known(v_e_697_, 2);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v_a_698_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v_fst_854_; lean_object* v_snd_855_; size_t v___x_856_; size_t v___x_857_; uint8_t v___x_858_; 
lean_dec_ref(v___x_850_);
lean_inc_ref(v_expr_841_);
v___x_853_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_841_, v_a_698_);
v_fst_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_fst_854_);
v_snd_855_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_snd_855_);
lean_dec_ref(v___x_853_);
v___x_856_ = lean_ptr_addr(v_expr_841_);
v___x_857_ = lean_ptr_addr(v_fst_854_);
v___x_858_ = lean_usize_dec_eq(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_inc(v_data_840_);
v___x_859_ = l_Lean_Expr_mdata___override(v_data_840_, v_fst_854_);
v___x_860_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_859_, v_snd_855_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; 
lean_dec(v_fst_854_);
lean_inc_ref(v_e_697_);
v___x_861_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v_e_697_, v_snd_855_);
return v___x_861_;
}
}
}
}
case 11:
{
lean_object* v_typeName_862_; lean_object* v_idx_863_; lean_object* v_struct_864_; lean_object* v_map_865_; lean_object* v_set_866_; lean_object* v___x_867_; 
v_typeName_862_ = lean_ctor_get(v_e_697_, 0);
v_idx_863_ = lean_ctor_get(v_e_697_, 1);
v_struct_864_ = lean_ctor_get(v_e_697_, 2);
v_map_865_ = lean_ctor_get(v_a_698_, 0);
v_set_866_ = lean_ctor_get(v_a_698_, 1);
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_865_, v_e_697_);
if (lean_obj_tag(v___x_867_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_869_; 
lean_dec_ref_known(v_e_697_, 3);
v_val_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_val_868_);
lean_ctor_set(v___x_869_, 1, v_a_698_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; uint64_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
lean_dec(v___x_867_);
v___x_870_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_871_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_697_);
v___x_872_ = lean_uint64_to_usize(v___x_871_);
lean_inc_ref(v_e_697_);
lean_inc_ref(v_set_866_);
v___x_873_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_866_, v___x_872_, v_e_697_, v___x_870_);
v___x_874_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_873_, v___x_870_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
lean_dec_ref_known(v_e_697_, 3);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v_a_698_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v_fst_877_; lean_object* v_snd_878_; size_t v___x_879_; size_t v___x_880_; uint8_t v___x_881_; 
lean_dec_ref(v___x_873_);
lean_inc_ref(v_struct_864_);
v___x_876_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_864_, v_a_698_);
v_fst_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_fst_877_);
v_snd_878_ = lean_ctor_get(v___x_876_, 1);
lean_inc(v_snd_878_);
lean_dec_ref(v___x_876_);
v___x_879_ = lean_ptr_addr(v_struct_864_);
v___x_880_ = lean_ptr_addr(v_fst_877_);
v___x_881_ = lean_usize_dec_eq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_inc(v_idx_863_);
lean_inc(v_typeName_862_);
v___x_882_ = l_Lean_Expr_proj___override(v_typeName_862_, v_idx_863_, v_fst_877_);
v___x_883_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v___x_882_, v_snd_878_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; 
lean_dec(v_fst_877_);
lean_inc_ref(v_e_697_);
v___x_884_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_697_, v_e_697_, v_snd_878_);
return v___x_884_;
}
}
}
}
default: 
{
lean_object* v_map_885_; lean_object* v_set_886_; lean_object* v___x_887_; 
v_map_885_ = lean_ctor_get(v_a_698_, 0);
v_set_886_ = lean_ctor_get(v_a_698_, 1);
lean_inc_ref(v_e_697_);
v___x_887_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_set_886_, v_e_697_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_897_; 
lean_inc_ref(v_set_886_);
lean_inc_ref(v_map_885_);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_698_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; lean_object* v_unused_899_; 
v_unused_898_ = lean_ctor_get(v_a_698_, 1);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_a_698_, 0);
lean_dec(v_unused_899_);
v___x_889_ = v_a_698_;
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_a_698_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = lean_box(0);
lean_inc_ref(v_e_697_);
v___x_892_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_886_, v_e_697_, v___x_891_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_map_885_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_e_697_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
return v___x_895_;
}
}
}
else
{
lean_object* v_val_900_; lean_object* v_fst_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_e_697_);
v_val_900_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v___x_887_, 1);
v_fst_901_ = lean_ctor_get(v_val_900_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_val_900_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_val_900_, 1);
lean_dec(v_unused_909_);
v___x_903_ = v_val_900_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_fst_901_);
lean_dec(v_val_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v_a_698_);
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_fst_901_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_a_698_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_910_, lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_911_, v_a_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_914_, lean_object* v_m_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_914_, v_m_915_, v_a_916_);
lean_dec_ref(v_a_916_);
lean_dec_ref(v_m_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_x_919_, v_x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_922_, v_x_923_, v_x_924_);
lean_dec_ref(v_x_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_926_, lean_object* v_a_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_930_, lean_object* v_a_931_, lean_object* v_x_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_930_, v_a_931_, v_x_932_);
lean_dec(v_x_932_);
lean_dec_ref(v_a_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, size_t v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v___x_938_; 
lean_inc_ref(v_x_935_);
v___x_938_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_935_, v_x_936_, v_x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
size_t v_x_9291__boxed_943_; lean_object* v_res_944_; 
v_x_9291__boxed_943_ = lean_unbox_usize(v_x_941_);
lean_dec(v_x_941_);
v_res_944_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_939_, v_x_940_, v_x_9291__boxed_943_, v_x_942_);
lean_dec_ref(v_x_940_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_945_, lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_heq_948_, lean_object* v_i_949_, lean_object* v_k_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_946_, v_vals_947_, v_i_949_, v_k_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_952_, lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_heq_955_, lean_object* v_i_956_, lean_object* v_k_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(v_00_u03b2_952_, v_keys_953_, v_vals_954_, v_heq_955_, v_i_956_, v_k_957_);
lean_dec_ref(v_vals_954_);
lean_dec_ref(v_keys_953_);
return v_res_958_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_box(0);
v___x_960_ = lean_unsigned_to_nat(16u);
v___x_961_ = lean_mk_array(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonAlpha___closed__0, &l_Lean_Meta_Sym_shareCommonAlpha___closed__0_once, _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_965_, lean_object* v_s_966_){
_start:
{
lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v___x_969_; 
v___f_967_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_968_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_965_);
v___x_969_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_967_, v___f_968_, v_s_966_, v_e_965_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_snd_973_; lean_object* v_fst_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v___x_970_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonAlpha___closed__1, &l_Lean_Meta_Sym_shareCommonAlpha___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_s_966_);
v___x_972_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_965_, v___x_971_);
v_snd_973_ = lean_ctor_get(v___x_972_, 1);
v_fst_974_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_982_ == 0)
{
v___x_976_ = v___x_972_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_snd_973_);
lean_inc(v_fst_974_);
lean_dec(v___x_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_set_978_; lean_object* v___x_980_; 
v_set_978_ = lean_ctor_get(v_snd_973_, 1);
lean_inc_ref(v_set_978_);
lean_dec(v_snd_973_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_set_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_fst_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_set_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_object* v_val_983_; lean_object* v_fst_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_e_965_);
v_val_983_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_969_, 1);
v_fst_984_ = lean_ctor_get(v_val_983_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_val_983_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_val_983_, 1);
lean_dec(v_unused_992_);
v___x_986_ = v_val_983_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_fst_984_);
lean_dec(v_val_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_s_966_);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_s_966_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_995_; uint64_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_995_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_996_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_993_);
v___x_997_ = lean_uint64_to_usize(v___x_996_);
lean_inc_ref(v_e_993_);
lean_inc_ref(v_a_994_);
v___x_998_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_994_, v___x_997_, v_e_993_, v___x_995_);
v___x_999_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_998_, v___x_995_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref(v_e_993_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v_a_994_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v___x_998_);
v___x_1001_ = lean_box(0);
lean_inc_ref(v_e_993_);
v___x_1002_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_994_, v_e_993_, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_e_993_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1004_, lean_object* v_k_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___f_1007_; lean_object* v___x_1008_; uint64_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___f_1007_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1008_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1009_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1004_);
v___x_1010_ = lean_uint64_to_usize(v___x_1009_);
lean_inc_ref(v_a_1006_);
v___x_1011_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1007_, v_a_1006_, v___x_1010_, v_e_1004_, v___x_1008_);
v___x_1012_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1011_, v___x_1008_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
lean_dec_ref(v_k_1005_);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v_a_1006_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v___x_1017_; 
lean_dec(v___x_1011_);
v___x_1014_ = lean_apply_1(v_k_1005_, v_a_1006_);
v_fst_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_fst_1015_);
v_snd_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_snd_1016_);
lean_dec_ref(v___x_1014_);
v___x_1017_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_fst_1015_, v_snd_1016_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1018_, lean_object* v_a_1019_){
_start:
{
switch(lean_obj_tag(v_e_1018_))
{
case 5:
{
lean_object* v_fn_1020_; lean_object* v_arg_1021_; lean_object* v___x_1022_; uint64_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_fn_1020_ = lean_ctor_get(v_e_1018_, 0);
v_arg_1021_ = lean_ctor_get(v_e_1018_, 1);
v___x_1022_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1023_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1018_);
v___x_1024_ = lean_uint64_to_usize(v___x_1023_);
lean_inc_ref(v_e_1018_);
lean_inc_ref(v_a_1019_);
v___x_1025_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1019_, v___x_1024_, v_e_1018_, v___x_1022_);
v___x_1026_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1025_, v___x_1022_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref_known(v_e_1018_, 2);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v_a_1019_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1031_; lean_object* v_fst_1032_; lean_object* v_snd_1033_; uint8_t v___y_1035_; size_t v___x_1039_; size_t v___x_1040_; uint8_t v___x_1041_; 
lean_dec_ref(v___x_1025_);
lean_inc_ref(v_fn_1020_);
v___x_1028_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1020_, v_a_1019_);
v_fst_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_fst_1029_);
v_snd_1030_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_snd_1030_);
lean_dec_ref(v___x_1028_);
lean_inc_ref(v_arg_1021_);
v___x_1031_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1021_, v_snd_1030_);
v_fst_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_fst_1032_);
v_snd_1033_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_snd_1033_);
lean_dec_ref(v___x_1031_);
v___x_1039_ = lean_ptr_addr(v_fn_1020_);
v___x_1040_ = lean_ptr_addr(v_fst_1029_);
v___x_1041_ = lean_usize_dec_eq(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
v___y_1035_ = v___x_1041_;
goto v___jp_1034_;
}
else
{
size_t v___x_1042_; size_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = lean_ptr_addr(v_arg_1021_);
v___x_1043_ = lean_ptr_addr(v_fst_1032_);
v___x_1044_ = lean_usize_dec_eq(v___x_1042_, v___x_1043_);
v___y_1035_ = v___x_1044_;
goto v___jp_1034_;
}
v___jp_1034_:
{
if (v___y_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref_known(v_e_1018_, 2);
v___x_1036_ = l_Lean_Expr_app___override(v_fst_1029_, v_fst_1032_);
v___x_1037_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1036_, v_snd_1033_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; 
lean_dec(v_fst_1032_);
lean_dec(v_fst_1029_);
v___x_1038_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1018_, v_snd_1033_);
return v___x_1038_;
}
}
}
}
case 6:
{
lean_object* v_binderName_1045_; lean_object* v_binderType_1046_; lean_object* v_body_1047_; uint8_t v_binderInfo_1048_; lean_object* v___x_1049_; uint64_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_binderName_1045_ = lean_ctor_get(v_e_1018_, 0);
v_binderType_1046_ = lean_ctor_get(v_e_1018_, 1);
v_body_1047_ = lean_ctor_get(v_e_1018_, 2);
v_binderInfo_1048_ = lean_ctor_get_uint8(v_e_1018_, sizeof(void*)*3 + 8);
v___x_1049_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1050_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1018_);
v___x_1051_ = lean_uint64_to_usize(v___x_1050_);
lean_inc_ref(v_e_1018_);
lean_inc_ref(v_a_1019_);
v___x_1052_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1019_, v___x_1051_, v_e_1018_, v___x_1049_);
v___x_1053_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1052_, v___x_1049_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec_ref_known(v_e_1018_, 3);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v_a_1019_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1058_; lean_object* v_fst_1059_; lean_object* v_snd_1060_; uint8_t v___y_1062_; size_t v___x_1069_; size_t v___x_1070_; uint8_t v___x_1071_; 
lean_dec_ref(v___x_1052_);
lean_inc_ref(v_binderType_1046_);
v___x_1055_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1046_, v_a_1019_);
v_fst_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_fst_1056_);
v_snd_1057_ = lean_ctor_get(v___x_1055_, 1);
lean_inc(v_snd_1057_);
lean_dec_ref(v___x_1055_);
lean_inc_ref(v_body_1047_);
v___x_1058_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1047_, v_snd_1057_);
v_fst_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_fst_1059_);
v_snd_1060_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_snd_1060_);
lean_dec_ref(v___x_1058_);
v___x_1069_ = lean_ptr_addr(v_binderType_1046_);
v___x_1070_ = lean_ptr_addr(v_fst_1056_);
v___x_1071_ = lean_usize_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
v___y_1062_ = v___x_1071_;
goto v___jp_1061_;
}
else
{
size_t v___x_1072_; size_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_ptr_addr(v_body_1047_);
v___x_1073_ = lean_ptr_addr(v_fst_1059_);
v___x_1074_ = lean_usize_dec_eq(v___x_1072_, v___x_1073_);
v___y_1062_ = v___x_1074_;
goto v___jp_1061_;
}
v___jp_1061_:
{
if (v___y_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_inc(v_binderName_1045_);
lean_dec_ref_known(v_e_1018_, 3);
v___x_1063_ = l_Lean_Expr_lam___override(v_binderName_1045_, v_fst_1056_, v_fst_1059_, v_binderInfo_1048_);
v___x_1064_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1063_, v_snd_1060_);
return v___x_1064_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1048_, v_binderInfo_1048_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_inc(v_binderName_1045_);
lean_dec_ref_known(v_e_1018_, 3);
v___x_1066_ = l_Lean_Expr_lam___override(v_binderName_1045_, v_fst_1056_, v_fst_1059_, v_binderInfo_1048_);
v___x_1067_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1066_, v_snd_1060_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; 
lean_dec(v_fst_1059_);
lean_dec(v_fst_1056_);
v___x_1068_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1018_, v_snd_1060_);
return v___x_1068_;
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1075_; lean_object* v_binderType_1076_; lean_object* v_body_1077_; uint8_t v_binderInfo_1078_; lean_object* v___x_1079_; uint64_t v___x_1080_; size_t v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_binderName_1075_ = lean_ctor_get(v_e_1018_, 0);
v_binderType_1076_ = lean_ctor_get(v_e_1018_, 1);
v_body_1077_ = lean_ctor_get(v_e_1018_, 2);
v_binderInfo_1078_ = lean_ctor_get_uint8(v_e_1018_, sizeof(void*)*3 + 8);
v___x_1079_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1080_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1018_);
v___x_1081_ = lean_uint64_to_usize(v___x_1080_);
lean_inc_ref(v_e_1018_);
lean_inc_ref(v_a_1019_);
v___x_1082_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1019_, v___x_1081_, v_e_1018_, v___x_1079_);
v___x_1083_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1082_, v___x_1079_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec_ref_known(v_e_1018_, 3);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v_a_1019_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1088_; lean_object* v_fst_1089_; lean_object* v_snd_1090_; uint8_t v___y_1092_; size_t v___x_1099_; size_t v___x_1100_; uint8_t v___x_1101_; 
lean_dec_ref(v___x_1082_);
lean_inc_ref(v_binderType_1076_);
v___x_1085_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1076_, v_a_1019_);
v_fst_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_fst_1086_);
v_snd_1087_ = lean_ctor_get(v___x_1085_, 1);
lean_inc(v_snd_1087_);
lean_dec_ref(v___x_1085_);
lean_inc_ref(v_body_1077_);
v___x_1088_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1077_, v_snd_1087_);
v_fst_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_fst_1089_);
v_snd_1090_ = lean_ctor_get(v___x_1088_, 1);
lean_inc(v_snd_1090_);
lean_dec_ref(v___x_1088_);
v___x_1099_ = lean_ptr_addr(v_binderType_1076_);
v___x_1100_ = lean_ptr_addr(v_fst_1086_);
v___x_1101_ = lean_usize_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
v___y_1092_ = v___x_1101_;
goto v___jp_1091_;
}
else
{
size_t v___x_1102_; size_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = lean_ptr_addr(v_body_1077_);
v___x_1103_ = lean_ptr_addr(v_fst_1089_);
v___x_1104_ = lean_usize_dec_eq(v___x_1102_, v___x_1103_);
v___y_1092_ = v___x_1104_;
goto v___jp_1091_;
}
v___jp_1091_:
{
if (v___y_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc(v_binderName_1075_);
lean_dec_ref_known(v_e_1018_, 3);
v___x_1093_ = l_Lean_Expr_forallE___override(v_binderName_1075_, v_fst_1086_, v_fst_1089_, v_binderInfo_1078_);
v___x_1094_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1093_, v_snd_1090_);
return v___x_1094_;
}
else
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1078_, v_binderInfo_1078_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_inc(v_binderName_1075_);
lean_dec_ref_known(v_e_1018_, 3);
v___x_1096_ = l_Lean_Expr_forallE___override(v_binderName_1075_, v_fst_1086_, v_fst_1089_, v_binderInfo_1078_);
v___x_1097_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1096_, v_snd_1090_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; 
lean_dec(v_fst_1089_);
lean_dec(v_fst_1086_);
v___x_1098_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1018_, v_snd_1090_);
return v___x_1098_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_1105_; lean_object* v_type_1106_; lean_object* v_value_1107_; lean_object* v_body_1108_; uint8_t v_nondep_1109_; lean_object* v___x_1110_; uint64_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_declName_1105_ = lean_ctor_get(v_e_1018_, 0);
v_type_1106_ = lean_ctor_get(v_e_1018_, 1);
v_value_1107_ = lean_ctor_get(v_e_1018_, 2);
v_body_1108_ = lean_ctor_get(v_e_1018_, 3);
v_nondep_1109_ = lean_ctor_get_uint8(v_e_1018_, sizeof(void*)*4 + 8);
v___x_1110_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1111_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1018_);
v___x_1112_ = lean_uint64_to_usize(v___x_1111_);
lean_inc_ref(v_e_1018_);
lean_inc_ref(v_a_1019_);
v___x_1113_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1019_, v___x_1112_, v_e_1018_, v___x_1110_);
v___x_1114_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1113_, v___x_1110_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref_known(v_e_1018_, 4);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v_a_1019_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; lean_object* v_fst_1117_; lean_object* v_snd_1118_; lean_object* v___x_1119_; lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1122_; lean_object* v_fst_1123_; lean_object* v_snd_1124_; uint8_t v___y_1126_; size_t v___x_1135_; size_t v___x_1136_; uint8_t v___x_1137_; 
lean_dec_ref(v___x_1113_);
lean_inc_ref(v_type_1106_);
v___x_1116_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1106_, v_a_1019_);
v_fst_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_fst_1117_);
v_snd_1118_ = lean_ctor_get(v___x_1116_, 1);
lean_inc(v_snd_1118_);
lean_dec_ref(v___x_1116_);
lean_inc_ref(v_value_1107_);
v___x_1119_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1107_, v_snd_1118_);
v_fst_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_fst_1120_);
v_snd_1121_ = lean_ctor_get(v___x_1119_, 1);
lean_inc(v_snd_1121_);
lean_dec_ref(v___x_1119_);
lean_inc_ref(v_body_1108_);
v___x_1122_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1108_, v_snd_1121_);
v_fst_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_fst_1123_);
v_snd_1124_ = lean_ctor_get(v___x_1122_, 1);
lean_inc(v_snd_1124_);
lean_dec_ref(v___x_1122_);
v___x_1135_ = lean_ptr_addr(v_type_1106_);
v___x_1136_ = lean_ptr_addr(v_fst_1117_);
v___x_1137_ = lean_usize_dec_eq(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
v___y_1126_ = v___x_1137_;
goto v___jp_1125_;
}
else
{
size_t v___x_1138_; size_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_ptr_addr(v_value_1107_);
v___x_1139_ = lean_ptr_addr(v_fst_1120_);
v___x_1140_ = lean_usize_dec_eq(v___x_1138_, v___x_1139_);
v___y_1126_ = v___x_1140_;
goto v___jp_1125_;
}
v___jp_1125_:
{
if (v___y_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc(v_declName_1105_);
lean_dec_ref_known(v_e_1018_, 4);
v___x_1127_ = l_Lean_Expr_letE___override(v_declName_1105_, v_fst_1117_, v_fst_1120_, v_fst_1123_, v_nondep_1109_);
v___x_1128_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1127_, v_snd_1124_);
return v___x_1128_;
}
else
{
size_t v___x_1129_; size_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = lean_ptr_addr(v_body_1108_);
v___x_1130_ = lean_ptr_addr(v_fst_1123_);
v___x_1131_ = lean_usize_dec_eq(v___x_1129_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_inc(v_declName_1105_);
lean_dec_ref_known(v_e_1018_, 4);
v___x_1132_ = l_Lean_Expr_letE___override(v_declName_1105_, v_fst_1117_, v_fst_1120_, v_fst_1123_, v_nondep_1109_);
v___x_1133_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1132_, v_snd_1124_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; 
lean_dec(v_fst_1123_);
lean_dec(v_fst_1120_);
lean_dec(v_fst_1117_);
v___x_1134_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1018_, v_snd_1124_);
return v___x_1134_;
}
}
}
}
}
case 10:
{
lean_object* v_data_1141_; lean_object* v_expr_1142_; lean_object* v___x_1143_; uint64_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_data_1141_ = lean_ctor_get(v_e_1018_, 0);
v_expr_1142_ = lean_ctor_get(v_e_1018_, 1);
v___x_1143_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1144_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1018_);
v___x_1145_ = lean_uint64_to_usize(v___x_1144_);
lean_inc_ref(v_e_1018_);
lean_inc_ref(v_a_1019_);
v___x_1146_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1019_, v___x_1145_, v_e_1018_, v___x_1143_);
v___x_1147_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1146_, v___x_1143_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref_known(v_e_1018_, 2);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v_a_1019_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v_snd_1151_; size_t v___x_1152_; size_t v___x_1153_; uint8_t v___x_1154_; 
lean_dec_ref(v___x_1146_);
lean_inc_ref(v_expr_1142_);
v___x_1149_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1142_, v_a_1019_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_fst_1150_);
v_snd_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc(v_snd_1151_);
lean_dec_ref(v___x_1149_);
v___x_1152_ = lean_ptr_addr(v_expr_1142_);
v___x_1153_ = lean_ptr_addr(v_fst_1150_);
v___x_1154_ = lean_usize_dec_eq(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_inc(v_data_1141_);
lean_dec_ref_known(v_e_1018_, 2);
v___x_1155_ = l_Lean_Expr_mdata___override(v_data_1141_, v_fst_1150_);
v___x_1156_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1155_, v_snd_1151_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_fst_1150_);
v___x_1157_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1018_, v_snd_1151_);
return v___x_1157_;
}
}
}
case 11:
{
lean_object* v_typeName_1158_; lean_object* v_idx_1159_; lean_object* v_struct_1160_; lean_object* v___x_1161_; uint64_t v___x_1162_; size_t v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_typeName_1158_ = lean_ctor_get(v_e_1018_, 0);
v_idx_1159_ = lean_ctor_get(v_e_1018_, 1);
v_struct_1160_ = lean_ctor_get(v_e_1018_, 2);
v___x_1161_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1162_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1018_);
v___x_1163_ = lean_uint64_to_usize(v___x_1162_);
lean_inc_ref(v_e_1018_);
lean_inc_ref(v_a_1019_);
v___x_1164_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1019_, v___x_1163_, v_e_1018_, v___x_1161_);
v___x_1165_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1164_, v___x_1161_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref_known(v_e_1018_, 3);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v_a_1019_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v_fst_1168_; lean_object* v_snd_1169_; size_t v___x_1170_; size_t v___x_1171_; uint8_t v___x_1172_; 
lean_dec_ref(v___x_1164_);
lean_inc_ref(v_struct_1160_);
v___x_1167_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1160_, v_a_1019_);
v_fst_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_fst_1168_);
v_snd_1169_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_snd_1169_);
lean_dec_ref(v___x_1167_);
v___x_1170_ = lean_ptr_addr(v_struct_1160_);
v___x_1171_ = lean_ptr_addr(v_fst_1168_);
v___x_1172_ = lean_usize_dec_eq(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc(v_idx_1159_);
lean_inc(v_typeName_1158_);
lean_dec_ref_known(v_e_1018_, 3);
v___x_1173_ = l_Lean_Expr_proj___override(v_typeName_1158_, v_idx_1159_, v_fst_1168_);
v___x_1174_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1173_, v_snd_1169_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; 
lean_dec(v_fst_1168_);
v___x_1175_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1018_, v_snd_1169_);
return v___x_1175_;
}
}
}
default: 
{
lean_object* v___x_1176_; 
v___x_1176_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1018_, v_a_1019_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1177_, v_a_1178_);
return v___x_1179_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy = _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy();
lean_mark_persistent(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
}
#ifdef __cplusplus
}
#endif

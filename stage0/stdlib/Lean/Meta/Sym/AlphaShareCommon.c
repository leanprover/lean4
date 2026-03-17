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
size_t lean_usize_shift_left(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_e_u2081_54_);
v_fn_58_ = lean_ctor_get(v_e_u2082_55_, 0);
lean_inc_ref(v_fn_58_);
v_arg_59_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_arg_59_);
lean_dec_ref(v_e_u2082_55_);
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
lean_dec_ref(v_e_u2081_54_);
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
lean_dec_ref(v_e_u2081_54_);
v_binderType_65_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_binderType_65_);
v_body_66_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_body_66_);
lean_dec_ref(v_e_u2082_55_);
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
lean_dec_ref(v_e_u2081_54_);
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
lean_dec_ref(v_e_u2081_54_);
v_binderType_72_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_binderType_72_);
v_body_73_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_body_73_);
lean_dec_ref(v_e_u2082_55_);
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
lean_dec_ref(v_e_u2081_54_);
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
lean_dec_ref(v_e_u2081_54_);
v_value_79_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_value_79_);
v_body_80_ = lean_ctor_get(v_e_u2082_55_, 3);
lean_inc_ref(v_body_80_);
lean_dec_ref(v_e_u2082_55_);
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
lean_dec_ref(v_e_u2081_54_);
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
lean_dec_ref(v_e_u2081_54_);
v_data_86_ = lean_ctor_get(v_e_u2082_55_, 0);
lean_inc(v_data_86_);
v_expr_87_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc_ref(v_expr_87_);
lean_dec_ref(v_e_u2082_55_);
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
lean_dec_ref(v_e_u2081_54_);
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
lean_dec_ref(v_e_u2081_54_);
v_typeName_94_ = lean_ctor_get(v_e_u2082_55_, 0);
lean_inc(v_typeName_94_);
v_idx_95_ = lean_ctor_get(v_e_u2082_55_, 1);
lean_inc(v_idx_95_);
v_struct_96_ = lean_ctor_get(v_e_u2082_55_, 2);
lean_inc_ref(v_struct_96_);
lean_dec_ref(v_e_u2082_55_);
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
lean_dec_ref(v_e_u2081_54_);
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
static size_t _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; 
v___x_147_ = ((size_t)5ULL);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_shift_left(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; 
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_once(&l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__0);
v___x_152_ = lean_usize_sub(v___x_151_, v___x_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_153_, size_t v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v_es_157_; lean_object* v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; lean_object* v_j_162_; lean_object* v___x_163_; 
v_es_157_ = lean_ctor_get(v_x_153_, 0);
lean_inc_ref(v_es_157_);
lean_dec_ref(v_x_153_);
v___x_158_ = lean_box(2);
v___x_159_ = ((size_t)5ULL);
v___x_160_ = lean_usize_once(&l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
v___x_161_ = lean_usize_land(v_x_154_, v___x_160_);
v_j_162_ = lean_usize_to_nat(v___x_161_);
v___x_163_ = lean_array_get(v___x_158_, v_es_157_, v_j_162_);
lean_dec(v_j_162_);
lean_dec_ref(v_es_157_);
switch(lean_obj_tag(v___x_163_))
{
case 0:
{
lean_object* v_key_164_; uint8_t v___x_165_; 
v_key_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_key_164_);
lean_dec_ref(v___x_163_);
lean_inc(v_key_164_);
v___x_165_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_155_, v_key_164_);
if (v___x_165_ == 0)
{
lean_dec(v_key_164_);
lean_inc_ref(v_x_156_);
return v_x_156_;
}
else
{
return v_key_164_;
}
}
case 1:
{
lean_object* v_node_166_; size_t v___x_167_; 
v_node_166_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_node_166_);
lean_dec_ref(v___x_163_);
v___x_167_ = lean_usize_shift_right(v_x_154_, v___x_159_);
v_x_153_ = v_node_166_;
v_x_154_ = v___x_167_;
goto _start;
}
default: 
{
lean_dec_ref(v_x_155_);
lean_inc_ref(v_x_156_);
return v_x_156_;
}
}
}
else
{
lean_object* v_ks_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_ks_169_ = lean_ctor_get(v_x_153_, 0);
lean_inc_ref(v_ks_169_);
lean_dec_ref(v_x_153_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_169_, v___x_170_, v_x_155_, v_x_156_);
lean_dec_ref(v_ks_169_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
size_t v_x_1900__boxed_176_; lean_object* v_res_177_; 
v_x_1900__boxed_176_ = lean_unbox_usize(v_x_173_);
lean_dec(v_x_173_);
v_res_177_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_172_, v_x_1900__boxed_176_, v_x_174_, v_x_175_);
lean_dec_ref(v_x_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_ks_182_; lean_object* v_vs_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_207_; 
v_ks_182_ = lean_ctor_get(v_x_178_, 0);
v_vs_183_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_207_ == 0)
{
v___x_185_ = v_x_178_;
v_isShared_186_ = v_isSharedCheck_207_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_vs_183_);
lean_inc(v_ks_182_);
lean_dec(v_x_178_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_207_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_array_get_size(v_ks_182_);
v___x_188_ = lean_nat_dec_lt(v_x_179_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec(v_x_179_);
v___x_189_ = lean_array_push(v_ks_182_, v_x_180_);
v___x_190_ = lean_array_push(v_vs_183_, v_x_181_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_190_);
lean_ctor_set(v___x_185_, 0, v___x_189_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_object* v_k_x27_194_; uint8_t v___x_195_; 
v_k_x27_194_ = lean_array_fget_borrowed(v_ks_182_, v_x_179_);
lean_inc(v_k_x27_194_);
lean_inc_ref(v_x_180_);
v___x_195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_180_, v_k_x27_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_197_; 
if (v_isShared_186_ == 0)
{
v___x_197_ = v___x_185_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_ks_182_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_vs_183_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v_x_179_, v___x_198_);
lean_dec(v_x_179_);
v_x_178_ = v___x_197_;
v_x_179_ = v___x_199_;
goto _start;
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_202_ = lean_array_fset(v_ks_182_, v_x_179_, v_x_180_);
v___x_203_ = lean_array_fset(v_vs_183_, v_x_179_, v_x_181_);
lean_dec(v_x_179_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_203_);
lean_ctor_set(v___x_185_, 0, v___x_202_);
v___x_205_ = v___x_185_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_208_, lean_object* v_k_209_, lean_object* v_v_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_208_, v___x_211_, v_k_209_, v_v_210_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_214_, size_t v_x_215_, size_t v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_es_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v_j_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_es_219_ = lean_ctor_get(v_x_214_, 0);
v___x_220_ = ((size_t)5ULL);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_once(&l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
v___x_223_ = lean_usize_land(v_x_215_, v___x_222_);
v_j_224_ = lean_usize_to_nat(v___x_223_);
v___x_225_ = lean_array_get_size(v_es_219_);
v___x_226_ = lean_nat_dec_lt(v_j_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec(v_j_224_);
lean_dec(v_x_218_);
lean_dec_ref(v_x_217_);
return v_x_214_;
}
else
{
lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_263_; 
lean_inc_ref(v_es_219_);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v_x_214_, 0);
lean_dec(v_unused_264_);
v___x_228_ = v_x_214_;
v_isShared_229_ = v_isSharedCheck_263_;
goto v_resetjp_227_;
}
else
{
lean_dec(v_x_214_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_263_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_v_230_; lean_object* v___x_231_; lean_object* v_xs_x27_232_; lean_object* v___y_234_; 
v_v_230_ = lean_array_fget(v_es_219_, v_j_224_);
v___x_231_ = lean_box(0);
v_xs_x27_232_ = lean_array_fset(v_es_219_, v_j_224_, v___x_231_);
switch(lean_obj_tag(v_v_230_))
{
case 0:
{
lean_object* v_key_239_; lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_250_; 
v_key_239_ = lean_ctor_get(v_v_230_, 0);
v_val_240_ = lean_ctor_get(v_v_230_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_v_230_);
if (v_isSharedCheck_250_ == 0)
{
v___x_242_ = v_v_230_;
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_inc(v_key_239_);
lean_dec(v_v_230_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; 
lean_inc(v_key_239_);
lean_inc_ref(v_x_217_);
v___x_244_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_217_, v_key_239_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_del_object(v___x_242_);
v___x_245_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_239_, v_val_240_, v_x_217_, v_x_218_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
v___y_234_ = v___x_246_;
goto v___jp_233_;
}
else
{
lean_object* v___x_248_; 
lean_dec(v_val_240_);
lean_dec(v_key_239_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_x_218_);
lean_ctor_set(v___x_242_, 0, v_x_217_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_x_217_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_x_218_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v___y_234_ = v___x_248_;
goto v___jp_233_;
}
}
}
}
case 1:
{
lean_object* v_node_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_261_; 
v_node_251_ = lean_ctor_get(v_v_230_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_v_230_);
if (v_isSharedCheck_261_ == 0)
{
v___x_253_ = v_v_230_;
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_node_251_);
lean_dec(v_v_230_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
size_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_255_ = lean_usize_shift_right(v_x_215_, v___x_220_);
v___x_256_ = lean_usize_add(v_x_216_, v___x_221_);
v___x_257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_251_, v___x_255_, v___x_256_, v_x_217_, v_x_218_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_257_);
v___x_259_ = v___x_253_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
v___y_234_ = v___x_259_;
goto v___jp_233_;
}
}
}
default: 
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_x_217_);
lean_ctor_set(v___x_262_, 1, v_x_218_);
v___y_234_ = v___x_262_;
goto v___jp_233_;
}
}
v___jp_233_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_array_fset(v_xs_x27_232_, v_j_224_, v___y_234_);
lean_dec(v_j_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_235_);
v___x_237_ = v___x_228_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
else
{
lean_object* v_ks_265_; lean_object* v_vs_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_286_; 
v_ks_265_ = lean_ctor_get(v_x_214_, 0);
v_vs_266_ = lean_ctor_get(v_x_214_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_286_ == 0)
{
v___x_268_ = v_x_214_;
v_isShared_269_ = v_isSharedCheck_286_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_vs_266_);
lean_inc(v_ks_265_);
lean_dec(v_x_214_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_286_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_ks_265_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_vs_266_);
v___x_271_ = v_reuseFailAlloc_285_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v_newNode_272_; uint8_t v___y_274_; size_t v___x_280_; uint8_t v___x_281_; 
v_newNode_272_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_271_, v_x_217_, v_x_218_);
v___x_280_ = ((size_t)7ULL);
v___x_281_ = lean_usize_dec_le(v___x_280_, v_x_216_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_282_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_272_);
v___x_283_ = lean_unsigned_to_nat(4u);
v___x_284_ = lean_nat_dec_lt(v___x_282_, v___x_283_);
lean_dec(v___x_282_);
v___y_274_ = v___x_284_;
goto v___jp_273_;
}
else
{
v___y_274_ = v___x_281_;
goto v___jp_273_;
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
lean_object* v_ks_275_; lean_object* v_vs_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_ks_275_ = lean_ctor_get(v_newNode_272_, 0);
lean_inc_ref(v_ks_275_);
v_vs_276_ = lean_ctor_get(v_newNode_272_, 1);
lean_inc_ref(v_vs_276_);
lean_dec_ref(v_newNode_272_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_216_, v_ks_275_, v_vs_276_, v___x_277_, v___x_278_);
lean_dec_ref(v_vs_276_);
lean_dec_ref(v_ks_275_);
return v___x_279_;
}
else
{
return v_newNode_272_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_287_, lean_object* v_keys_288_, lean_object* v_vals_289_, lean_object* v_i_290_, lean_object* v_entries_291_){
_start:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_array_get_size(v_keys_288_);
v___x_293_ = lean_nat_dec_lt(v_i_290_, v___x_292_);
if (v___x_293_ == 0)
{
lean_dec(v_i_290_);
return v_entries_291_;
}
else
{
lean_object* v_k_294_; lean_object* v_v_295_; uint64_t v___x_296_; size_t v_h_297_; size_t v___x_298_; lean_object* v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v_h_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_k_294_ = lean_array_fget_borrowed(v_keys_288_, v_i_290_);
v_v_295_ = lean_array_fget_borrowed(v_vals_289_, v_i_290_);
v___x_296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_294_);
v_h_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = ((size_t)5ULL);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_sub(v_depth_287_, v___x_300_);
v___x_302_ = lean_usize_mul(v___x_298_, v___x_301_);
v_h_303_ = lean_usize_shift_right(v_h_297_, v___x_302_);
v___x_304_ = lean_nat_add(v_i_290_, v___x_299_);
lean_dec(v_i_290_);
lean_inc(v_v_295_);
lean_inc(v_k_294_);
v___x_305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_291_, v_h_303_, v_depth_287_, v_k_294_, v_v_295_);
v_i_290_ = v___x_304_;
v_entries_291_ = v___x_305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_307_, lean_object* v_keys_308_, lean_object* v_vals_309_, lean_object* v_i_310_, lean_object* v_entries_311_){
_start:
{
size_t v_depth_boxed_312_; lean_object* v_res_313_; 
v_depth_boxed_312_ = lean_unbox_usize(v_depth_307_);
lean_dec(v_depth_307_);
v_res_313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_312_, v_keys_308_, v_vals_309_, v_i_310_, v_entries_311_);
lean_dec_ref(v_vals_309_);
lean_dec_ref(v_keys_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
size_t v_x_2030__boxed_319_; size_t v_x_2031__boxed_320_; lean_object* v_res_321_; 
v_x_2030__boxed_319_ = lean_unbox_usize(v_x_315_);
lean_dec(v_x_315_);
v_x_2031__boxed_320_ = lean_unbox_usize(v_x_316_);
lean_dec(v_x_316_);
v_res_321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_314_, v_x_2030__boxed_319_, v_x_2031__boxed_320_, v_x_317_, v_x_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
uint64_t v___x_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_325_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_323_);
v___x_326_ = lean_uint64_to_usize(v___x_325_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_322_, v___x_326_, v___x_327_, v_x_323_, v_x_324_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_329_, lean_object* v_b_330_, lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
lean_dec(v_b_330_);
lean_dec_ref(v_a_329_);
return v_x_331_;
}
else
{
lean_object* v_key_332_; lean_object* v_value_333_; lean_object* v_tail_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_346_; 
v_key_332_ = lean_ctor_get(v_x_331_, 0);
v_value_333_ = lean_ctor_get(v_x_331_, 1);
v_tail_334_ = lean_ctor_get(v_x_331_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_331_);
if (v_isSharedCheck_346_ == 0)
{
v___x_336_ = v_x_331_;
v_isShared_337_ = v_isSharedCheck_346_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_tail_334_);
lean_inc(v_value_333_);
lean_inc(v_key_332_);
lean_dec(v_x_331_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_346_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint8_t v___x_338_; 
v___x_338_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_332_, v_a_329_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_329_, v_b_330_, v_tail_334_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 2, v___x_339_);
v___x_341_ = v___x_336_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_key_332_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_value_333_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; 
lean_dec(v_value_333_);
lean_dec(v_key_332_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_b_330_);
lean_ctor_set(v___x_336_, 0, v_a_329_);
v___x_344_ = v___x_336_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_329_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_b_330_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_tail_334_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
return v_x_347_;
}
else
{
lean_object* v_key_349_; lean_object* v_value_350_; lean_object* v_tail_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_374_; 
v_key_349_ = lean_ctor_get(v_x_348_, 0);
v_value_350_ = lean_ctor_get(v_x_348_, 1);
v_tail_351_ = lean_ctor_get(v_x_348_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_374_ == 0)
{
v___x_353_ = v_x_348_;
v_isShared_354_ = v_isSharedCheck_374_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_tail_351_);
lean_inc(v_value_350_);
lean_inc(v_key_349_);
lean_dec(v_x_348_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_374_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; uint64_t v___x_356_; uint64_t v___x_357_; uint64_t v___x_358_; uint64_t v_fold_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_355_ = lean_array_get_size(v_x_347_);
v___x_356_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_349_);
v___x_357_ = 32ULL;
v___x_358_ = lean_uint64_shift_right(v___x_356_, v___x_357_);
v_fold_359_ = lean_uint64_xor(v___x_356_, v___x_358_);
v___x_360_ = 16ULL;
v___x_361_ = lean_uint64_shift_right(v_fold_359_, v___x_360_);
v___x_362_ = lean_uint64_xor(v_fold_359_, v___x_361_);
v___x_363_ = lean_uint64_to_usize(v___x_362_);
v___x_364_ = lean_usize_of_nat(v___x_355_);
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_sub(v___x_364_, v___x_365_);
v___x_367_ = lean_usize_land(v___x_363_, v___x_366_);
v___x_368_ = lean_array_uget_borrowed(v_x_347_, v___x_367_);
lean_inc(v___x_368_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 2, v___x_368_);
v___x_370_ = v___x_353_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_key_349_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_value_350_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_368_);
v___x_370_ = v_reuseFailAlloc_373_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; 
v___x_371_ = lean_array_uset(v_x_347_, v___x_367_, v___x_370_);
v_x_347_ = v___x_371_;
v_x_348_ = v_tail_351_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_375_, lean_object* v_source_376_, lean_object* v_target_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_array_get_size(v_source_376_);
v___x_379_ = lean_nat_dec_lt(v_i_375_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec_ref(v_source_376_);
lean_dec(v_i_375_);
return v_target_377_;
}
else
{
lean_object* v_es_380_; lean_object* v___x_381_; lean_object* v_source_382_; lean_object* v_target_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_es_380_ = lean_array_fget(v_source_376_, v_i_375_);
v___x_381_ = lean_box(0);
v_source_382_ = lean_array_fset(v_source_376_, v_i_375_, v___x_381_);
v_target_383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_377_, v_es_380_);
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_i_375_, v___x_384_);
lean_dec(v_i_375_);
v_i_375_ = v___x_385_;
v_source_376_ = v_source_382_;
v_target_377_ = v_target_383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_nbuckets_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_388_ = lean_array_get_size(v_data_387_);
v___x_389_ = lean_unsigned_to_nat(2u);
v_nbuckets_390_ = lean_nat_mul(v___x_388_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_box(0);
v___x_393_ = lean_mk_array(v_nbuckets_390_, v___x_392_);
v___x_394_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_391_, v_data_387_, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_395_, lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
else
{
lean_object* v_key_398_; lean_object* v_tail_399_; uint8_t v___x_400_; 
v_key_398_ = lean_ctor_get(v_x_396_, 0);
v_tail_399_ = lean_ctor_get(v_x_396_, 2);
v___x_400_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_398_, v_a_395_);
if (v___x_400_ == 0)
{
v_x_396_ = v_tail_399_;
goto _start;
}
else
{
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_402_, lean_object* v_x_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_402_, v_x_403_);
lean_dec(v_x_403_);
lean_dec_ref(v_a_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_406_, lean_object* v_a_407_, lean_object* v_b_408_){
_start:
{
lean_object* v_size_409_; lean_object* v_buckets_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_453_; 
v_size_409_ = lean_ctor_get(v_m_406_, 0);
v_buckets_410_ = lean_ctor_get(v_m_406_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_m_406_);
if (v_isSharedCheck_453_ == 0)
{
v___x_412_ = v_m_406_;
v_isShared_413_ = v_isSharedCheck_453_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_buckets_410_);
lean_inc(v_size_409_);
lean_dec(v_m_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_453_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v_fold_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v_bkt_427_; uint8_t v___x_428_; 
v___x_414_ = lean_array_get_size(v_buckets_410_);
v___x_415_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_407_);
v___x_416_ = 32ULL;
v___x_417_ = lean_uint64_shift_right(v___x_415_, v___x_416_);
v_fold_418_ = lean_uint64_xor(v___x_415_, v___x_417_);
v___x_419_ = 16ULL;
v___x_420_ = lean_uint64_shift_right(v_fold_418_, v___x_419_);
v___x_421_ = lean_uint64_xor(v_fold_418_, v___x_420_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
v___x_423_ = lean_usize_of_nat(v___x_414_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_sub(v___x_423_, v___x_424_);
v___x_426_ = lean_usize_land(v___x_422_, v___x_425_);
v_bkt_427_ = lean_array_uget_borrowed(v_buckets_410_, v___x_426_);
v___x_428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_407_, v_bkt_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v_size_x27_430_; lean_object* v___x_431_; lean_object* v_buckets_x27_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v_size_x27_430_ = lean_nat_add(v_size_409_, v___x_429_);
lean_dec(v_size_409_);
lean_inc(v_bkt_427_);
v___x_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_431_, 0, v_a_407_);
lean_ctor_set(v___x_431_, 1, v_b_408_);
lean_ctor_set(v___x_431_, 2, v_bkt_427_);
v_buckets_x27_432_ = lean_array_uset(v_buckets_410_, v___x_426_, v___x_431_);
v___x_433_ = lean_unsigned_to_nat(4u);
v___x_434_ = lean_nat_mul(v_size_x27_430_, v___x_433_);
v___x_435_ = lean_unsigned_to_nat(3u);
v___x_436_ = lean_nat_div(v___x_434_, v___x_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_array_get_size(v_buckets_x27_432_);
v___x_438_ = lean_nat_dec_le(v___x_436_, v___x_437_);
lean_dec(v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v_val_439_; lean_object* v___x_441_; 
v_val_439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_432_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_val_439_);
lean_ctor_set(v___x_412_, 0, v_size_x27_430_);
v___x_441_ = v___x_412_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_size_x27_430_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_val_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_444_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_buckets_x27_432_);
lean_ctor_set(v___x_412_, 0, v_size_x27_430_);
v___x_444_ = v___x_412_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_size_x27_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_buckets_x27_432_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v___x_446_; lean_object* v_buckets_x27_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_bkt_427_);
v___x_446_ = lean_box(0);
v_buckets_x27_447_ = lean_array_uset(v_buckets_410_, v___x_426_, v___x_446_);
v___x_448_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_407_, v_b_408_, v_bkt_427_);
v___x_449_ = lean_array_uset(v_buckets_x27_447_, v___x_426_, v___x_448_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_449_);
v___x_451_ = v___x_412_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_size_409_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_454_, lean_object* v_r_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_map_457_; lean_object* v_set_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_480_; 
v_map_457_ = lean_ctor_get(v_a_456_, 0);
v_set_458_ = lean_ctor_get(v_a_456_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_480_ == 0)
{
v___x_460_ = v_a_456_;
v_isShared_461_ = v_isSharedCheck_480_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_set_458_);
lean_inc(v_map_457_);
lean_dec(v_a_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_480_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; uint64_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_462_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_463_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_455_);
v___x_464_ = lean_uint64_to_usize(v___x_463_);
lean_inc_ref(v_r_455_);
lean_inc_ref(v_set_458_);
v___x_465_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_458_, v___x_464_, v_r_455_, v___x_462_);
v___x_466_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_465_, v___x_462_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec_ref(v_r_455_);
lean_inc_ref(v___x_465_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_457_, v_e_454_, v___x_465_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_467_);
v___x_469_ = v___x_460_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_set_458_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_465_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
return v___x_470_;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec_ref(v___x_465_);
lean_inc_ref(v_r_455_);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_457_, v_e_454_, v_r_455_);
lean_inc_ref_n(v_r_455_, 2);
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_472_, v_r_455_, v_r_455_);
v___x_474_ = lean_box(0);
lean_inc_ref(v_r_455_);
v___x_475_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_458_, v_r_455_, v___x_474_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v___x_475_);
lean_ctor_set(v___x_460_, 0, v___x_473_);
v___x_477_ = v___x_460_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_r_455_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, size_t v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_482_, v_x_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
size_t v_x_2450__boxed_492_; lean_object* v_res_493_; 
v_x_2450__boxed_492_ = lean_unbox_usize(v_x_489_);
lean_dec(v_x_489_);
v_res_493_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_487_, v_x_488_, v_x_2450__boxed_492_, v_x_490_, v_x_491_);
lean_dec_ref(v_x_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_494_, lean_object* v_m_495_, lean_object* v_a_496_, lean_object* v_b_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_495_, v_a_496_, v_b_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_500_, v_x_501_, v_x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_504_, lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_heq_507_, lean_object* v_i_508_, lean_object* v_k_509_, lean_object* v_k_u2080_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_505_, v_i_508_, v_k_509_, v_k_u2080_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_512_, lean_object* v_keys_513_, lean_object* v_vals_514_, lean_object* v_heq_515_, lean_object* v_i_516_, lean_object* v_k_517_, lean_object* v_k_u2080_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_512_, v_keys_513_, v_vals_514_, v_heq_515_, v_i_516_, v_k_517_, v_k_u2080_518_);
lean_dec_ref(v_k_u2080_518_);
lean_dec_ref(v_vals_514_);
lean_dec_ref(v_keys_513_);
return v_res_519_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_524_, lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_524_, v_a_525_, v_x_526_);
lean_dec(v_x_526_);
lean_dec_ref(v_a_525_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_529_, lean_object* v_data_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_532_, lean_object* v_a_533_, lean_object* v_b_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_533_, v_b_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_537_, lean_object* v_x_538_, size_t v_x_539_, size_t v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_538_, v_x_539_, v_x_540_, v_x_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
size_t v_x_2487__boxed_550_; size_t v_x_2488__boxed_551_; lean_object* v_res_552_; 
v_x_2487__boxed_550_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_x_2488__boxed_551_ = lean_unbox_usize(v_x_547_);
lean_dec(v_x_547_);
v_res_552_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_544_, v_x_545_, v_x_2487__boxed_550_, v_x_2488__boxed_551_, v_x_548_, v_x_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_553_, lean_object* v_i_554_, lean_object* v_source_555_, lean_object* v_target_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_554_, v_source_555_, v_target_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_558_, lean_object* v_n_559_, lean_object* v_k_560_, lean_object* v_v_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_559_, v_k_560_, v_v_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_563_, size_t v_depth_564_, lean_object* v_keys_565_, lean_object* v_vals_566_, lean_object* v_heq_567_, lean_object* v_i_568_, lean_object* v_entries_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_564_, v_keys_565_, v_vals_566_, v_i_568_, v_entries_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_571_, lean_object* v_depth_572_, lean_object* v_keys_573_, lean_object* v_vals_574_, lean_object* v_heq_575_, lean_object* v_i_576_, lean_object* v_entries_577_){
_start:
{
size_t v_depth_boxed_578_; lean_object* v_res_579_; 
v_depth_boxed_578_ = lean_unbox_usize(v_depth_572_);
lean_dec(v_depth_572_);
v_res_579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_571_, v_depth_boxed_578_, v_keys_573_, v_vals_574_, v_heq_575_, v_i_576_, v_entries_577_);
lean_dec_ref(v_vals_574_);
lean_dec_ref(v_keys_573_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_580_, lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_585_, v_x_586_, v_x_587_, v_x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_592_, lean_object* v_k_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_map_595_; lean_object* v_set_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___x_599_; 
v_map_595_ = lean_ctor_get(v_a_594_, 0);
v_set_596_ = lean_ctor_get(v_a_594_, 1);
v___f_597_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_598_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_592_);
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_597_, v___f_598_, v_map_595_, v_e_592_);
if (lean_obj_tag(v___x_599_) == 1)
{
lean_object* v_val_600_; lean_object* v___x_601_; 
lean_dec_ref(v_k_593_);
lean_dec_ref(v_e_592_);
v_val_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_val_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_val_600_);
lean_ctor_set(v___x_601_, 1, v_a_594_);
return v___x_601_;
}
else
{
lean_object* v___f_602_; lean_object* v___x_603_; uint64_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
lean_dec(v___x_599_);
v___f_602_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_603_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_604_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_592_);
v___x_605_ = lean_uint64_to_usize(v___x_604_);
lean_inc_ref(v_e_592_);
lean_inc_ref(v_set_596_);
v___x_606_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_602_, v_set_596_, v___x_605_, v_e_592_, v___x_603_);
v___x_607_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_606_, v___x_603_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v_k_593_);
lean_dec_ref(v_e_592_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v_a_594_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_612_; 
lean_dec(v___x_606_);
v___x_609_ = lean_apply_1(v_k_593_, v_a_594_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_fst_610_);
v_snd_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_snd_611_);
lean_dec_ref(v___x_609_);
v___x_612_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_592_, v_fst_610_, v_snd_611_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_613_, lean_object* v_vals_614_, lean_object* v_i_615_, lean_object* v_k_616_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_array_get_size(v_keys_613_);
v___x_618_ = lean_nat_dec_lt(v_i_615_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec_ref(v_k_616_);
lean_dec(v_i_615_);
v___x_619_ = lean_box(0);
return v___x_619_;
}
else
{
lean_object* v_k_x27_620_; uint8_t v___x_621_; 
v_k_x27_620_ = lean_array_fget_borrowed(v_keys_613_, v_i_615_);
lean_inc(v_k_x27_620_);
lean_inc_ref(v_k_616_);
v___x_621_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_616_, v_k_x27_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v_i_615_, v___x_622_);
lean_dec(v_i_615_);
v_i_615_ = v___x_623_;
goto _start;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v_k_616_);
v___x_625_ = lean_array_fget_borrowed(v_vals_614_, v_i_615_);
lean_dec(v_i_615_);
lean_inc(v___x_625_);
lean_inc(v_k_x27_620_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_k_x27_620_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_628_, lean_object* v_vals_629_, lean_object* v_i_630_, lean_object* v_k_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_628_, v_vals_629_, v_i_630_, v_k_631_);
lean_dec_ref(v_vals_629_);
lean_dec_ref(v_keys_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_x_633_, size_t v_x_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v_es_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_664_; 
v_es_636_ = lean_ctor_get(v_x_633_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_664_ == 0)
{
v___x_638_ = v_x_633_;
v_isShared_639_ = v_isSharedCheck_664_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_es_636_);
lean_dec(v_x_633_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_664_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; lean_object* v_j_644_; lean_object* v___x_645_; 
v___x_640_ = lean_box(2);
v___x_641_ = ((size_t)5ULL);
v___x_642_ = lean_usize_once(&l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___closed__1);
v___x_643_ = lean_usize_land(v_x_634_, v___x_642_);
v_j_644_ = lean_usize_to_nat(v___x_643_);
v___x_645_ = lean_array_get(v___x_640_, v_es_636_, v_j_644_);
lean_dec(v_j_644_);
lean_dec_ref(v_es_636_);
switch(lean_obj_tag(v___x_645_))
{
case 0:
{
lean_object* v_key_646_; lean_object* v_val_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_659_; 
v_key_646_ = lean_ctor_get(v___x_645_, 0);
v_val_647_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_659_ == 0)
{
v___x_649_ = v___x_645_;
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_val_647_);
lean_inc(v_key_646_);
lean_dec(v___x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___x_651_; 
lean_inc(v_key_646_);
v___x_651_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_635_, v_key_646_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_del_object(v___x_649_);
lean_dec(v_val_647_);
lean_dec(v_key_646_);
lean_del_object(v___x_638_);
v___x_652_ = lean_box(0);
return v___x_652_;
}
else
{
lean_object* v___x_654_; 
if (v_isShared_650_ == 0)
{
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_key_646_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_val_647_);
v___x_654_ = v_reuseFailAlloc_658_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 1);
lean_ctor_set(v___x_638_, 0, v___x_654_);
v___x_656_ = v___x_638_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
case 1:
{
lean_object* v_node_660_; size_t v___x_661_; 
lean_del_object(v___x_638_);
v_node_660_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_node_660_);
lean_dec_ref(v___x_645_);
v___x_661_ = lean_usize_shift_right(v_x_634_, v___x_641_);
v_x_633_ = v_node_660_;
v_x_634_ = v___x_661_;
goto _start;
}
default: 
{
lean_object* v___x_663_; 
lean_del_object(v___x_638_);
lean_dec_ref(v_x_635_);
v___x_663_ = lean_box(0);
return v___x_663_;
}
}
}
}
else
{
lean_object* v_ks_665_; lean_object* v_vs_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_ks_665_ = lean_ctor_get(v_x_633_, 0);
lean_inc_ref(v_ks_665_);
v_vs_666_ = lean_ctor_get(v_x_633_, 1);
lean_inc_ref(v_vs_666_);
lean_dec_ref(v_x_633_);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_ks_665_, v_vs_666_, v___x_667_, v_x_635_);
lean_dec_ref(v_vs_666_);
lean_dec_ref(v_ks_665_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
size_t v_x_8779__boxed_672_; lean_object* v_res_673_; 
v_x_8779__boxed_672_ = lean_unbox_usize(v_x_670_);
lean_dec(v_x_670_);
v_res_673_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_669_, v_x_8779__boxed_672_, v_x_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
uint64_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_676_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_675_);
v___x_677_ = lean_uint64_to_usize(v___x_676_);
v___x_678_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_674_, v___x_677_, v_x_675_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_680_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_box(0);
return v___x_681_;
}
else
{
lean_object* v_key_682_; lean_object* v_value_683_; lean_object* v_tail_684_; uint8_t v___x_685_; 
v_key_682_ = lean_ctor_get(v_x_680_, 0);
v_value_683_ = lean_ctor_get(v_x_680_, 1);
v_tail_684_ = lean_ctor_get(v_x_680_, 2);
v___x_685_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_682_, v_a_679_);
if (v___x_685_ == 0)
{
v_x_680_ = v_tail_684_;
goto _start;
}
else
{
lean_object* v___x_687_; 
lean_inc(v_value_683_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v_value_683_);
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_688_, lean_object* v_x_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_688_, v_x_689_);
lean_dec(v_x_689_);
lean_dec_ref(v_a_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_m_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_buckets_693_; lean_object* v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v_fold_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_buckets_693_ = lean_ctor_get(v_m_691_, 1);
v___x_694_ = lean_array_get_size(v_buckets_693_);
v___x_695_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_692_);
v___x_696_ = 32ULL;
v___x_697_ = lean_uint64_shift_right(v___x_695_, v___x_696_);
v_fold_698_ = lean_uint64_xor(v___x_695_, v___x_697_);
v___x_699_ = 16ULL;
v___x_700_ = lean_uint64_shift_right(v_fold_698_, v___x_699_);
v___x_701_ = lean_uint64_xor(v_fold_698_, v___x_700_);
v___x_702_ = lean_uint64_to_usize(v___x_701_);
v___x_703_ = lean_usize_of_nat(v___x_694_);
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_sub(v___x_703_, v___x_704_);
v___x_706_ = lean_usize_land(v___x_702_, v___x_705_);
v___x_707_ = lean_array_uget_borrowed(v_buckets_693_, v___x_706_);
v___x_708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_692_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_m_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_709_, v_a_710_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_m_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_712_, lean_object* v_a_713_){
_start:
{
switch(lean_obj_tag(v_e_712_))
{
case 5:
{
lean_object* v_fn_714_; lean_object* v_arg_715_; lean_object* v_map_716_; lean_object* v_set_717_; lean_object* v___x_718_; 
v_fn_714_ = lean_ctor_get(v_e_712_, 0);
v_arg_715_ = lean_ctor_get(v_e_712_, 1);
v_map_716_ = lean_ctor_get(v_a_713_, 0);
v_set_717_ = lean_ctor_get(v_a_713_, 1);
v___x_718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_716_, v_e_712_);
if (lean_obj_tag(v___x_718_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_720_; 
lean_dec_ref(v_e_712_);
v_val_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_val_719_);
lean_ctor_set(v___x_720_, 1, v_a_713_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; uint64_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
lean_dec(v___x_718_);
v___x_721_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_722_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_712_);
v___x_723_ = lean_uint64_to_usize(v___x_722_);
lean_inc_ref(v_e_712_);
lean_inc_ref(v_set_717_);
v___x_724_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_717_, v___x_723_, v_e_712_, v___x_721_);
v___x_725_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_724_, v___x_721_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v_e_712_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v_a_713_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; uint8_t v___y_734_; size_t v___x_738_; size_t v___x_739_; uint8_t v___x_740_; 
lean_dec_ref(v___x_724_);
lean_inc_ref(v_fn_714_);
v___x_727_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_714_, v_a_713_);
v_fst_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_fst_728_);
v_snd_729_ = lean_ctor_get(v___x_727_, 1);
lean_inc(v_snd_729_);
lean_dec_ref(v___x_727_);
lean_inc_ref(v_arg_715_);
v___x_730_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_715_, v_snd_729_);
v_fst_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_fst_731_);
v_snd_732_ = lean_ctor_get(v___x_730_, 1);
lean_inc(v_snd_732_);
lean_dec_ref(v___x_730_);
v___x_738_ = lean_ptr_addr(v_fn_714_);
v___x_739_ = lean_ptr_addr(v_fst_728_);
v___x_740_ = lean_usize_dec_eq(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
v___y_734_ = v___x_740_;
goto v___jp_733_;
}
else
{
size_t v___x_741_; size_t v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_ptr_addr(v_arg_715_);
v___x_742_ = lean_ptr_addr(v_fst_731_);
v___x_743_ = lean_usize_dec_eq(v___x_741_, v___x_742_);
v___y_734_ = v___x_743_;
goto v___jp_733_;
}
v___jp_733_:
{
if (v___y_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = l_Lean_Expr_app___override(v_fst_728_, v_fst_731_);
v___x_736_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_735_, v_snd_732_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
lean_dec(v_fst_731_);
lean_dec(v_fst_728_);
lean_inc_ref(v_e_712_);
v___x_737_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v_e_712_, v_snd_732_);
return v___x_737_;
}
}
}
}
}
case 6:
{
lean_object* v_binderName_744_; lean_object* v_binderType_745_; lean_object* v_body_746_; uint8_t v_binderInfo_747_; lean_object* v_map_748_; lean_object* v_set_749_; lean_object* v___x_750_; 
v_binderName_744_ = lean_ctor_get(v_e_712_, 0);
v_binderType_745_ = lean_ctor_get(v_e_712_, 1);
v_body_746_ = lean_ctor_get(v_e_712_, 2);
v_binderInfo_747_ = lean_ctor_get_uint8(v_e_712_, sizeof(void*)*3 + 8);
v_map_748_ = lean_ctor_get(v_a_713_, 0);
v_set_749_ = lean_ctor_get(v_a_713_, 1);
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_748_, v_e_712_);
if (lean_obj_tag(v___x_750_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_752_; 
lean_dec_ref(v_e_712_);
v_val_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_val_751_);
lean_dec_ref(v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_val_751_);
lean_ctor_set(v___x_752_, 1, v_a_713_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; uint64_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
lean_dec(v___x_750_);
v___x_753_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_754_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_712_);
v___x_755_ = lean_uint64_to_usize(v___x_754_);
lean_inc_ref(v_e_712_);
lean_inc_ref(v_set_749_);
v___x_756_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_749_, v___x_755_, v_e_712_, v___x_753_);
v___x_757_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_756_, v___x_753_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec_ref(v_e_712_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v_a_713_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v___x_762_; lean_object* v_fst_763_; lean_object* v_snd_764_; uint8_t v___y_766_; size_t v___x_773_; size_t v___x_774_; uint8_t v___x_775_; 
lean_dec_ref(v___x_756_);
lean_inc_ref(v_binderType_745_);
v___x_759_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_745_, v_a_713_);
v_fst_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_fst_760_);
v_snd_761_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_snd_761_);
lean_dec_ref(v___x_759_);
lean_inc_ref(v_body_746_);
v___x_762_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_746_, v_snd_761_);
v_fst_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_fst_763_);
v_snd_764_ = lean_ctor_get(v___x_762_, 1);
lean_inc(v_snd_764_);
lean_dec_ref(v___x_762_);
v___x_773_ = lean_ptr_addr(v_binderType_745_);
v___x_774_ = lean_ptr_addr(v_fst_760_);
v___x_775_ = lean_usize_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
v___y_766_ = v___x_775_;
goto v___jp_765_;
}
else
{
size_t v___x_776_; size_t v___x_777_; uint8_t v___x_778_; 
v___x_776_ = lean_ptr_addr(v_body_746_);
v___x_777_ = lean_ptr_addr(v_fst_763_);
v___x_778_ = lean_usize_dec_eq(v___x_776_, v___x_777_);
v___y_766_ = v___x_778_;
goto v___jp_765_;
}
v___jp_765_:
{
if (v___y_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_inc(v_binderName_744_);
v___x_767_ = l_Lean_Expr_lam___override(v_binderName_744_, v_fst_760_, v_fst_763_, v_binderInfo_747_);
v___x_768_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_767_, v_snd_764_);
return v___x_768_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_747_, v_binderInfo_747_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc(v_binderName_744_);
v___x_770_ = l_Lean_Expr_lam___override(v_binderName_744_, v_fst_760_, v_fst_763_, v_binderInfo_747_);
v___x_771_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_770_, v_snd_764_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; 
lean_dec(v_fst_763_);
lean_dec(v_fst_760_);
lean_inc_ref(v_e_712_);
v___x_772_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v_e_712_, v_snd_764_);
return v___x_772_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_779_; lean_object* v_binderType_780_; lean_object* v_body_781_; uint8_t v_binderInfo_782_; lean_object* v_map_783_; lean_object* v_set_784_; lean_object* v___x_785_; 
v_binderName_779_ = lean_ctor_get(v_e_712_, 0);
v_binderType_780_ = lean_ctor_get(v_e_712_, 1);
v_body_781_ = lean_ctor_get(v_e_712_, 2);
v_binderInfo_782_ = lean_ctor_get_uint8(v_e_712_, sizeof(void*)*3 + 8);
v_map_783_ = lean_ctor_get(v_a_713_, 0);
v_set_784_ = lean_ctor_get(v_a_713_, 1);
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_783_, v_e_712_);
if (lean_obj_tag(v___x_785_) == 1)
{
lean_object* v_val_786_; lean_object* v___x_787_; 
lean_dec_ref(v_e_712_);
v_val_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_val_786_);
lean_dec_ref(v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_val_786_);
lean_ctor_set(v___x_787_, 1, v_a_713_);
return v___x_787_;
}
else
{
lean_object* v___x_788_; uint64_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
lean_dec(v___x_785_);
v___x_788_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_789_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_712_);
v___x_790_ = lean_uint64_to_usize(v___x_789_);
lean_inc_ref(v_e_712_);
lean_inc_ref(v_set_784_);
v___x_791_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_784_, v___x_790_, v_e_712_, v___x_788_);
v___x_792_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_791_, v___x_788_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec_ref(v_e_712_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v_a_713_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v_fst_795_; lean_object* v_snd_796_; lean_object* v___x_797_; lean_object* v_fst_798_; lean_object* v_snd_799_; uint8_t v___y_801_; size_t v___x_808_; size_t v___x_809_; uint8_t v___x_810_; 
lean_dec_ref(v___x_791_);
lean_inc_ref(v_binderType_780_);
v___x_794_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_780_, v_a_713_);
v_fst_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_fst_795_);
v_snd_796_ = lean_ctor_get(v___x_794_, 1);
lean_inc(v_snd_796_);
lean_dec_ref(v___x_794_);
lean_inc_ref(v_body_781_);
v___x_797_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_781_, v_snd_796_);
v_fst_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_fst_798_);
v_snd_799_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_snd_799_);
lean_dec_ref(v___x_797_);
v___x_808_ = lean_ptr_addr(v_binderType_780_);
v___x_809_ = lean_ptr_addr(v_fst_795_);
v___x_810_ = lean_usize_dec_eq(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
v___y_801_ = v___x_810_;
goto v___jp_800_;
}
else
{
size_t v___x_811_; size_t v___x_812_; uint8_t v___x_813_; 
v___x_811_ = lean_ptr_addr(v_body_781_);
v___x_812_ = lean_ptr_addr(v_fst_798_);
v___x_813_ = lean_usize_dec_eq(v___x_811_, v___x_812_);
v___y_801_ = v___x_813_;
goto v___jp_800_;
}
v___jp_800_:
{
if (v___y_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc(v_binderName_779_);
v___x_802_ = l_Lean_Expr_forallE___override(v_binderName_779_, v_fst_795_, v_fst_798_, v_binderInfo_782_);
v___x_803_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_802_, v_snd_799_);
return v___x_803_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_782_, v_binderInfo_782_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_inc(v_binderName_779_);
v___x_805_ = l_Lean_Expr_forallE___override(v_binderName_779_, v_fst_795_, v_fst_798_, v_binderInfo_782_);
v___x_806_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_805_, v_snd_799_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; 
lean_dec(v_fst_798_);
lean_dec(v_fst_795_);
lean_inc_ref(v_e_712_);
v___x_807_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v_e_712_, v_snd_799_);
return v___x_807_;
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_814_; lean_object* v_type_815_; lean_object* v_value_816_; lean_object* v_body_817_; uint8_t v_nondep_818_; lean_object* v_map_819_; lean_object* v_set_820_; lean_object* v___x_821_; 
v_declName_814_ = lean_ctor_get(v_e_712_, 0);
v_type_815_ = lean_ctor_get(v_e_712_, 1);
v_value_816_ = lean_ctor_get(v_e_712_, 2);
v_body_817_ = lean_ctor_get(v_e_712_, 3);
v_nondep_818_ = lean_ctor_get_uint8(v_e_712_, sizeof(void*)*4 + 8);
v_map_819_ = lean_ctor_get(v_a_713_, 0);
v_set_820_ = lean_ctor_get(v_a_713_, 1);
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_819_, v_e_712_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v_val_822_; lean_object* v___x_823_; 
lean_dec_ref(v_e_712_);
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_val_822_);
lean_ctor_set(v___x_823_, 1, v_a_713_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; uint64_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
lean_dec(v___x_821_);
v___x_824_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_825_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_712_);
v___x_826_ = lean_uint64_to_usize(v___x_825_);
lean_inc_ref(v_e_712_);
lean_inc_ref(v_set_820_);
v___x_827_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_820_, v___x_826_, v_e_712_, v___x_824_);
v___x_828_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_827_, v___x_824_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec_ref(v_e_712_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v_a_713_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v_fst_831_; lean_object* v_snd_832_; lean_object* v___x_833_; lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v___x_836_; lean_object* v_fst_837_; lean_object* v_snd_838_; uint8_t v___y_840_; size_t v___x_849_; size_t v___x_850_; uint8_t v___x_851_; 
lean_dec_ref(v___x_827_);
lean_inc_ref(v_type_815_);
v___x_830_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_815_, v_a_713_);
v_fst_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_fst_831_);
v_snd_832_ = lean_ctor_get(v___x_830_, 1);
lean_inc(v_snd_832_);
lean_dec_ref(v___x_830_);
lean_inc_ref(v_value_816_);
v___x_833_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_816_, v_snd_832_);
v_fst_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_fst_834_);
v_snd_835_ = lean_ctor_get(v___x_833_, 1);
lean_inc(v_snd_835_);
lean_dec_ref(v___x_833_);
lean_inc_ref(v_body_817_);
v___x_836_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_817_, v_snd_835_);
v_fst_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_fst_837_);
v_snd_838_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_snd_838_);
lean_dec_ref(v___x_836_);
v___x_849_ = lean_ptr_addr(v_type_815_);
v___x_850_ = lean_ptr_addr(v_fst_831_);
v___x_851_ = lean_usize_dec_eq(v___x_849_, v___x_850_);
if (v___x_851_ == 0)
{
v___y_840_ = v___x_851_;
goto v___jp_839_;
}
else
{
size_t v___x_852_; size_t v___x_853_; uint8_t v___x_854_; 
v___x_852_ = lean_ptr_addr(v_value_816_);
v___x_853_ = lean_ptr_addr(v_fst_834_);
v___x_854_ = lean_usize_dec_eq(v___x_852_, v___x_853_);
v___y_840_ = v___x_854_;
goto v___jp_839_;
}
v___jp_839_:
{
if (v___y_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc(v_declName_814_);
v___x_841_ = l_Lean_Expr_letE___override(v_declName_814_, v_fst_831_, v_fst_834_, v_fst_837_, v_nondep_818_);
v___x_842_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_841_, v_snd_838_);
return v___x_842_;
}
else
{
size_t v___x_843_; size_t v___x_844_; uint8_t v___x_845_; 
v___x_843_ = lean_ptr_addr(v_body_817_);
v___x_844_ = lean_ptr_addr(v_fst_837_);
v___x_845_ = lean_usize_dec_eq(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_inc(v_declName_814_);
v___x_846_ = l_Lean_Expr_letE___override(v_declName_814_, v_fst_831_, v_fst_834_, v_fst_837_, v_nondep_818_);
v___x_847_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_846_, v_snd_838_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; 
lean_dec(v_fst_837_);
lean_dec(v_fst_834_);
lean_dec(v_fst_831_);
lean_inc_ref(v_e_712_);
v___x_848_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v_e_712_, v_snd_838_);
return v___x_848_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_855_; lean_object* v_expr_856_; lean_object* v_map_857_; lean_object* v_set_858_; lean_object* v___x_859_; 
v_data_855_ = lean_ctor_get(v_e_712_, 0);
v_expr_856_ = lean_ctor_get(v_e_712_, 1);
v_map_857_ = lean_ctor_get(v_a_713_, 0);
v_set_858_ = lean_ctor_get(v_a_713_, 1);
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_857_, v_e_712_);
if (lean_obj_tag(v___x_859_) == 1)
{
lean_object* v_val_860_; lean_object* v___x_861_; 
lean_dec_ref(v_e_712_);
v_val_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_val_860_);
lean_dec_ref(v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_val_860_);
lean_ctor_set(v___x_861_, 1, v_a_713_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; uint64_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
lean_dec(v___x_859_);
v___x_862_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_863_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_712_);
v___x_864_ = lean_uint64_to_usize(v___x_863_);
lean_inc_ref(v_e_712_);
lean_inc_ref(v_set_858_);
v___x_865_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_858_, v___x_864_, v_e_712_, v___x_862_);
v___x_866_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_865_, v___x_862_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_dec_ref(v_e_712_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v_a_713_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; size_t v___x_871_; size_t v___x_872_; uint8_t v___x_873_; 
lean_dec_ref(v___x_865_);
lean_inc_ref(v_expr_856_);
v___x_868_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_856_, v_a_713_);
v_fst_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_snd_870_);
lean_dec_ref(v___x_868_);
v___x_871_ = lean_ptr_addr(v_expr_856_);
v___x_872_ = lean_ptr_addr(v_fst_869_);
v___x_873_ = lean_usize_dec_eq(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc(v_data_855_);
v___x_874_ = l_Lean_Expr_mdata___override(v_data_855_, v_fst_869_);
v___x_875_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_874_, v_snd_870_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; 
lean_dec(v_fst_869_);
lean_inc_ref(v_e_712_);
v___x_876_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v_e_712_, v_snd_870_);
return v___x_876_;
}
}
}
}
case 11:
{
lean_object* v_typeName_877_; lean_object* v_idx_878_; lean_object* v_struct_879_; lean_object* v_map_880_; lean_object* v_set_881_; lean_object* v___x_882_; 
v_typeName_877_ = lean_ctor_get(v_e_712_, 0);
v_idx_878_ = lean_ctor_get(v_e_712_, 1);
v_struct_879_ = lean_ctor_get(v_e_712_, 2);
v_map_880_ = lean_ctor_get(v_a_713_, 0);
v_set_881_ = lean_ctor_get(v_a_713_, 1);
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_map_880_, v_e_712_);
if (lean_obj_tag(v___x_882_) == 1)
{
lean_object* v_val_883_; lean_object* v___x_884_; 
lean_dec_ref(v_e_712_);
v_val_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref(v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_val_883_);
lean_ctor_set(v___x_884_, 1, v_a_713_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; uint64_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
lean_dec(v___x_882_);
v___x_885_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_886_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_712_);
v___x_887_ = lean_uint64_to_usize(v___x_886_);
lean_inc_ref(v_e_712_);
lean_inc_ref(v_set_881_);
v___x_888_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_881_, v___x_887_, v_e_712_, v___x_885_);
v___x_889_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_888_, v___x_885_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec_ref(v_e_712_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v_a_713_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; lean_object* v_fst_892_; lean_object* v_snd_893_; size_t v___x_894_; size_t v___x_895_; uint8_t v___x_896_; 
lean_dec_ref(v___x_888_);
lean_inc_ref(v_struct_879_);
v___x_891_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_879_, v_a_713_);
v_fst_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_fst_892_);
v_snd_893_ = lean_ctor_get(v___x_891_, 1);
lean_inc(v_snd_893_);
lean_dec_ref(v___x_891_);
v___x_894_ = lean_ptr_addr(v_struct_879_);
v___x_895_ = lean_ptr_addr(v_fst_892_);
v___x_896_ = lean_usize_dec_eq(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_inc(v_idx_878_);
lean_inc(v_typeName_877_);
v___x_897_ = l_Lean_Expr_proj___override(v_typeName_877_, v_idx_878_, v_fst_892_);
v___x_898_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v___x_897_, v_snd_893_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; 
lean_dec(v_fst_892_);
lean_inc_ref(v_e_712_);
v___x_899_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_712_, v_e_712_, v_snd_893_);
return v___x_899_;
}
}
}
}
default: 
{
lean_object* v_map_900_; lean_object* v_set_901_; lean_object* v___x_902_; 
v_map_900_ = lean_ctor_get(v_a_713_, 0);
v_set_901_ = lean_ctor_get(v_a_713_, 1);
lean_inc_ref(v_e_712_);
lean_inc_ref(v_set_901_);
v___x_902_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_set_901_, v_e_712_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
lean_inc_ref(v_set_901_);
lean_inc_ref(v_map_900_);
v_isSharedCheck_912_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; lean_object* v_unused_914_; 
v_unused_913_ = lean_ctor_get(v_a_713_, 1);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_a_713_, 0);
lean_dec(v_unused_914_);
v___x_904_ = v_a_713_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_dec(v_a_713_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_906_ = lean_box(0);
lean_inc_ref(v_e_712_);
v___x_907_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_901_, v_e_712_, v___x_906_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_map_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_911_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_e_712_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
return v___x_910_;
}
}
}
else
{
lean_object* v_val_915_; lean_object* v_fst_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_e_712_);
v_val_915_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_val_915_);
lean_dec_ref(v___x_902_);
v_fst_916_ = lean_ctor_get(v_val_915_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_val_915_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_val_915_, 1);
lean_dec(v_unused_924_);
v___x_918_ = v_val_915_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_fst_916_);
lean_dec(v_val_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_a_713_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_fst_916_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_a_713_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_925_, lean_object* v_m_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_m_926_, v_a_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_929_, lean_object* v_m_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_929_, v_m_930_, v_a_931_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v_m_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_x_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_937_, lean_object* v_a_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_a_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_941_, lean_object* v_a_942_, lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_941_, v_a_942_, v_x_943_);
lean_dec(v_x_943_);
lean_dec_ref(v_a_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, size_t v_x_947_, lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_x_946_, v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
size_t v_x_9322__boxed_954_; lean_object* v_res_955_; 
v_x_9322__boxed_954_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_955_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_950_, v_x_951_, v_x_9322__boxed_954_, v_x_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_956_, lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_heq_959_, lean_object* v_i_960_, lean_object* v_k_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___redArg(v_keys_957_, v_vals_958_, v_i_960_, v_k_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_963_, lean_object* v_keys_964_, lean_object* v_vals_965_, lean_object* v_heq_966_, lean_object* v_i_967_, lean_object* v_k_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2_spec__3(v_00_u03b2_963_, v_keys_964_, v_vals_965_, v_heq_966_, v_i_967_, v_k_968_);
lean_dec_ref(v_vals_965_);
lean_dec_ref(v_keys_964_);
return v_res_969_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_box(0);
v___x_971_ = lean_unsigned_to_nat(16u);
v___x_972_ = lean_mk_array(v___x_971_, v___x_970_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonAlpha___closed__0, &l_Lean_Meta_Sym_shareCommonAlpha___closed__0_once, _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__0);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_976_, lean_object* v_s_977_){
_start:
{
lean_object* v___f_978_; lean_object* v___f_979_; lean_object* v___x_980_; 
v___f_978_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_979_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_976_);
lean_inc_ref(v_s_977_);
v___x_980_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_978_, v___f_979_, v_s_977_, v_e_976_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_snd_984_; lean_object* v_fst_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v___x_981_ = lean_obj_once(&l_Lean_Meta_Sym_shareCommonAlpha___closed__1, &l_Lean_Meta_Sym_shareCommonAlpha___closed__1_once, _init_l_Lean_Meta_Sym_shareCommonAlpha___closed__1);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_s_977_);
v___x_983_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_976_, v___x_982_);
v_snd_984_ = lean_ctor_get(v___x_983_, 1);
v_fst_985_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_993_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snd_984_);
lean_inc(v_fst_985_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_set_989_; lean_object* v___x_991_; 
v_set_989_ = lean_ctor_get(v_snd_984_, 1);
lean_inc_ref(v_set_989_);
lean_dec(v_snd_984_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_set_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fst_985_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_set_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_val_994_; lean_object* v_fst_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v_e_976_);
v_val_994_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_val_994_);
lean_dec_ref(v___x_980_);
v_fst_995_ = lean_ctor_get(v_val_994_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_val_994_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_val_994_, 1);
lean_dec(v_unused_1003_);
v___x_997_ = v_val_994_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_fst_995_);
lean_dec(v_val_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_s_977_);
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_fst_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_s_977_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1006_; uint64_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1006_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1007_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1004_);
v___x_1008_ = lean_uint64_to_usize(v___x_1007_);
lean_inc_ref(v_e_1004_);
lean_inc_ref(v_a_1005_);
v___x_1009_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1005_, v___x_1008_, v_e_1004_, v___x_1006_);
v___x_1010_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1009_, v___x_1006_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_dec_ref(v_e_1004_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v_a_1005_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec_ref(v___x_1009_);
v___x_1012_ = lean_box(0);
lean_inc_ref(v_e_1004_);
v___x_1013_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1005_, v_e_1004_, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_e_1004_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1015_, lean_object* v_k_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; uint64_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___f_1018_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1019_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1020_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1015_);
v___x_1021_ = lean_uint64_to_usize(v___x_1020_);
lean_inc_ref(v_a_1017_);
v___x_1022_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1018_, v_a_1017_, v___x_1021_, v_e_1015_, v___x_1019_);
v___x_1023_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1022_, v___x_1019_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_dec_ref(v_k_1016_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v_a_1017_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v___x_1028_; 
lean_dec(v___x_1022_);
v___x_1025_ = lean_apply_1(v_k_1016_, v_a_1017_);
v_fst_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_fst_1026_);
v_snd_1027_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_snd_1027_);
lean_dec_ref(v___x_1025_);
v___x_1028_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_fst_1026_, v_snd_1027_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1029_, lean_object* v_a_1030_){
_start:
{
switch(lean_obj_tag(v_e_1029_))
{
case 5:
{
lean_object* v_fn_1031_; lean_object* v_arg_1032_; lean_object* v___x_1033_; uint64_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_fn_1031_ = lean_ctor_get(v_e_1029_, 0);
v_arg_1032_ = lean_ctor_get(v_e_1029_, 1);
v___x_1033_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1034_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1029_);
v___x_1035_ = lean_uint64_to_usize(v___x_1034_);
lean_inc_ref(v_e_1029_);
lean_inc_ref(v_a_1030_);
v___x_1036_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1030_, v___x_1035_, v_e_1029_, v___x_1033_);
v___x_1037_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1036_, v___x_1033_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_e_1029_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v_a_1030_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v_fst_1040_; lean_object* v_snd_1041_; lean_object* v___x_1042_; lean_object* v_fst_1043_; lean_object* v_snd_1044_; uint8_t v___y_1046_; size_t v___x_1050_; size_t v___x_1051_; uint8_t v___x_1052_; 
lean_dec_ref(v___x_1036_);
lean_inc_ref(v_fn_1031_);
v___x_1039_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1031_, v_a_1030_);
v_fst_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_fst_1040_);
v_snd_1041_ = lean_ctor_get(v___x_1039_, 1);
lean_inc(v_snd_1041_);
lean_dec_ref(v___x_1039_);
lean_inc_ref(v_arg_1032_);
v___x_1042_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1032_, v_snd_1041_);
v_fst_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_fst_1043_);
v_snd_1044_ = lean_ctor_get(v___x_1042_, 1);
lean_inc(v_snd_1044_);
lean_dec_ref(v___x_1042_);
v___x_1050_ = lean_ptr_addr(v_fn_1031_);
v___x_1051_ = lean_ptr_addr(v_fst_1040_);
v___x_1052_ = lean_usize_dec_eq(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
v___y_1046_ = v___x_1052_;
goto v___jp_1045_;
}
else
{
size_t v___x_1053_; size_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1053_ = lean_ptr_addr(v_arg_1032_);
v___x_1054_ = lean_ptr_addr(v_fst_1043_);
v___x_1055_ = lean_usize_dec_eq(v___x_1053_, v___x_1054_);
v___y_1046_ = v___x_1055_;
goto v___jp_1045_;
}
v___jp_1045_:
{
if (v___y_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec_ref(v_e_1029_);
v___x_1047_ = l_Lean_Expr_app___override(v_fst_1040_, v_fst_1043_);
v___x_1048_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1047_, v_snd_1044_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; 
lean_dec(v_fst_1043_);
lean_dec(v_fst_1040_);
v___x_1049_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1029_, v_snd_1044_);
return v___x_1049_;
}
}
}
}
case 6:
{
lean_object* v_binderName_1056_; lean_object* v_binderType_1057_; lean_object* v_body_1058_; uint8_t v_binderInfo_1059_; lean_object* v___x_1060_; uint64_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_binderName_1056_ = lean_ctor_get(v_e_1029_, 0);
v_binderType_1057_ = lean_ctor_get(v_e_1029_, 1);
v_body_1058_ = lean_ctor_get(v_e_1029_, 2);
v_binderInfo_1059_ = lean_ctor_get_uint8(v_e_1029_, sizeof(void*)*3 + 8);
v___x_1060_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1061_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1029_);
v___x_1062_ = lean_uint64_to_usize(v___x_1061_);
lean_inc_ref(v_e_1029_);
lean_inc_ref(v_a_1030_);
v___x_1063_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1030_, v___x_1062_, v_e_1029_, v___x_1060_);
v___x_1064_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1063_, v___x_1060_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_dec_ref(v_e_1029_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v_a_1030_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1069_; lean_object* v_fst_1070_; lean_object* v_snd_1071_; uint8_t v___y_1073_; size_t v___x_1080_; size_t v___x_1081_; uint8_t v___x_1082_; 
lean_dec_ref(v___x_1063_);
lean_inc_ref(v_binderType_1057_);
v___x_1066_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1057_, v_a_1030_);
v_fst_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_fst_1067_);
v_snd_1068_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_snd_1068_);
lean_dec_ref(v___x_1066_);
lean_inc_ref(v_body_1058_);
v___x_1069_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1058_, v_snd_1068_);
v_fst_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_fst_1070_);
v_snd_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_snd_1071_);
lean_dec_ref(v___x_1069_);
v___x_1080_ = lean_ptr_addr(v_binderType_1057_);
v___x_1081_ = lean_ptr_addr(v_fst_1067_);
v___x_1082_ = lean_usize_dec_eq(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
v___y_1073_ = v___x_1082_;
goto v___jp_1072_;
}
else
{
size_t v___x_1083_; size_t v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = lean_ptr_addr(v_body_1058_);
v___x_1084_ = lean_ptr_addr(v_fst_1070_);
v___x_1085_ = lean_usize_dec_eq(v___x_1083_, v___x_1084_);
v___y_1073_ = v___x_1085_;
goto v___jp_1072_;
}
v___jp_1072_:
{
if (v___y_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_inc(v_binderName_1056_);
lean_dec_ref(v_e_1029_);
v___x_1074_ = l_Lean_Expr_lam___override(v_binderName_1056_, v_fst_1067_, v_fst_1070_, v_binderInfo_1059_);
v___x_1075_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1074_, v_snd_1071_);
return v___x_1075_;
}
else
{
uint8_t v___x_1076_; 
v___x_1076_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1059_, v_binderInfo_1059_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc(v_binderName_1056_);
lean_dec_ref(v_e_1029_);
v___x_1077_ = l_Lean_Expr_lam___override(v_binderName_1056_, v_fst_1067_, v_fst_1070_, v_binderInfo_1059_);
v___x_1078_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1077_, v_snd_1071_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; 
lean_dec(v_fst_1070_);
lean_dec(v_fst_1067_);
v___x_1079_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1029_, v_snd_1071_);
return v___x_1079_;
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1086_; lean_object* v_binderType_1087_; lean_object* v_body_1088_; uint8_t v_binderInfo_1089_; lean_object* v___x_1090_; uint64_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_binderName_1086_ = lean_ctor_get(v_e_1029_, 0);
v_binderType_1087_ = lean_ctor_get(v_e_1029_, 1);
v_body_1088_ = lean_ctor_get(v_e_1029_, 2);
v_binderInfo_1089_ = lean_ctor_get_uint8(v_e_1029_, sizeof(void*)*3 + 8);
v___x_1090_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1091_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1029_);
v___x_1092_ = lean_uint64_to_usize(v___x_1091_);
lean_inc_ref(v_e_1029_);
lean_inc_ref(v_a_1030_);
v___x_1093_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1030_, v___x_1092_, v_e_1029_, v___x_1090_);
v___x_1094_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1093_, v___x_1090_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec_ref(v_e_1029_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v_a_1030_);
return v___x_1095_;
}
else
{
lean_object* v___x_1096_; lean_object* v_fst_1097_; lean_object* v_snd_1098_; lean_object* v___x_1099_; lean_object* v_fst_1100_; lean_object* v_snd_1101_; uint8_t v___y_1103_; size_t v___x_1110_; size_t v___x_1111_; uint8_t v___x_1112_; 
lean_dec_ref(v___x_1093_);
lean_inc_ref(v_binderType_1087_);
v___x_1096_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1087_, v_a_1030_);
v_fst_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_fst_1097_);
v_snd_1098_ = lean_ctor_get(v___x_1096_, 1);
lean_inc(v_snd_1098_);
lean_dec_ref(v___x_1096_);
lean_inc_ref(v_body_1088_);
v___x_1099_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1088_, v_snd_1098_);
v_fst_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_fst_1100_);
v_snd_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_snd_1101_);
lean_dec_ref(v___x_1099_);
v___x_1110_ = lean_ptr_addr(v_binderType_1087_);
v___x_1111_ = lean_ptr_addr(v_fst_1097_);
v___x_1112_ = lean_usize_dec_eq(v___x_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
v___y_1103_ = v___x_1112_;
goto v___jp_1102_;
}
else
{
size_t v___x_1113_; size_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = lean_ptr_addr(v_body_1088_);
v___x_1114_ = lean_ptr_addr(v_fst_1100_);
v___x_1115_ = lean_usize_dec_eq(v___x_1113_, v___x_1114_);
v___y_1103_ = v___x_1115_;
goto v___jp_1102_;
}
v___jp_1102_:
{
if (v___y_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_inc(v_binderName_1086_);
lean_dec_ref(v_e_1029_);
v___x_1104_ = l_Lean_Expr_forallE___override(v_binderName_1086_, v_fst_1097_, v_fst_1100_, v_binderInfo_1089_);
v___x_1105_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1104_, v_snd_1101_);
return v___x_1105_;
}
else
{
uint8_t v___x_1106_; 
v___x_1106_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1089_, v_binderInfo_1089_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_inc(v_binderName_1086_);
lean_dec_ref(v_e_1029_);
v___x_1107_ = l_Lean_Expr_forallE___override(v_binderName_1086_, v_fst_1097_, v_fst_1100_, v_binderInfo_1089_);
v___x_1108_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1107_, v_snd_1101_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_fst_1100_);
lean_dec(v_fst_1097_);
v___x_1109_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1029_, v_snd_1101_);
return v___x_1109_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_1116_; lean_object* v_type_1117_; lean_object* v_value_1118_; lean_object* v_body_1119_; uint8_t v_nondep_1120_; lean_object* v___x_1121_; uint64_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_declName_1116_ = lean_ctor_get(v_e_1029_, 0);
v_type_1117_ = lean_ctor_get(v_e_1029_, 1);
v_value_1118_ = lean_ctor_get(v_e_1029_, 2);
v_body_1119_ = lean_ctor_get(v_e_1029_, 3);
v_nondep_1120_ = lean_ctor_get_uint8(v_e_1029_, sizeof(void*)*4 + 8);
v___x_1121_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1122_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1029_);
v___x_1123_ = lean_uint64_to_usize(v___x_1122_);
lean_inc_ref(v_e_1029_);
lean_inc_ref(v_a_1030_);
v___x_1124_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1030_, v___x_1123_, v_e_1029_, v___x_1121_);
v___x_1125_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1124_, v___x_1121_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v_e_1029_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v_a_1030_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; lean_object* v_fst_1128_; lean_object* v_snd_1129_; lean_object* v___x_1130_; lean_object* v_fst_1131_; lean_object* v_snd_1132_; lean_object* v___x_1133_; lean_object* v_fst_1134_; lean_object* v_snd_1135_; uint8_t v___y_1137_; size_t v___x_1146_; size_t v___x_1147_; uint8_t v___x_1148_; 
lean_dec_ref(v___x_1124_);
lean_inc_ref(v_type_1117_);
v___x_1127_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1117_, v_a_1030_);
v_fst_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_fst_1128_);
v_snd_1129_ = lean_ctor_get(v___x_1127_, 1);
lean_inc(v_snd_1129_);
lean_dec_ref(v___x_1127_);
lean_inc_ref(v_value_1118_);
v___x_1130_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1118_, v_snd_1129_);
v_fst_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_fst_1131_);
v_snd_1132_ = lean_ctor_get(v___x_1130_, 1);
lean_inc(v_snd_1132_);
lean_dec_ref(v___x_1130_);
lean_inc_ref(v_body_1119_);
v___x_1133_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1119_, v_snd_1132_);
v_fst_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_fst_1134_);
v_snd_1135_ = lean_ctor_get(v___x_1133_, 1);
lean_inc(v_snd_1135_);
lean_dec_ref(v___x_1133_);
v___x_1146_ = lean_ptr_addr(v_type_1117_);
v___x_1147_ = lean_ptr_addr(v_fst_1128_);
v___x_1148_ = lean_usize_dec_eq(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
v___y_1137_ = v___x_1148_;
goto v___jp_1136_;
}
else
{
size_t v___x_1149_; size_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1149_ = lean_ptr_addr(v_value_1118_);
v___x_1150_ = lean_ptr_addr(v_fst_1131_);
v___x_1151_ = lean_usize_dec_eq(v___x_1149_, v___x_1150_);
v___y_1137_ = v___x_1151_;
goto v___jp_1136_;
}
v___jp_1136_:
{
if (v___y_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_declName_1116_);
lean_dec_ref(v_e_1029_);
v___x_1138_ = l_Lean_Expr_letE___override(v_declName_1116_, v_fst_1128_, v_fst_1131_, v_fst_1134_, v_nondep_1120_);
v___x_1139_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1138_, v_snd_1135_);
return v___x_1139_;
}
else
{
size_t v___x_1140_; size_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = lean_ptr_addr(v_body_1119_);
v___x_1141_ = lean_ptr_addr(v_fst_1134_);
v___x_1142_ = lean_usize_dec_eq(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_inc(v_declName_1116_);
lean_dec_ref(v_e_1029_);
v___x_1143_ = l_Lean_Expr_letE___override(v_declName_1116_, v_fst_1128_, v_fst_1131_, v_fst_1134_, v_nondep_1120_);
v___x_1144_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1143_, v_snd_1135_);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; 
lean_dec(v_fst_1134_);
lean_dec(v_fst_1131_);
lean_dec(v_fst_1128_);
v___x_1145_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1029_, v_snd_1135_);
return v___x_1145_;
}
}
}
}
}
case 10:
{
lean_object* v_data_1152_; lean_object* v_expr_1153_; lean_object* v___x_1154_; uint64_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v_data_1152_ = lean_ctor_get(v_e_1029_, 0);
v_expr_1153_ = lean_ctor_get(v_e_1029_, 1);
v___x_1154_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1155_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1029_);
v___x_1156_ = lean_uint64_to_usize(v___x_1155_);
lean_inc_ref(v_e_1029_);
lean_inc_ref(v_a_1030_);
v___x_1157_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1030_, v___x_1156_, v_e_1029_, v___x_1154_);
v___x_1158_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1157_, v___x_1154_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v_e_1029_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v_a_1030_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v_fst_1161_; lean_object* v_snd_1162_; size_t v___x_1163_; size_t v___x_1164_; uint8_t v___x_1165_; 
lean_dec_ref(v___x_1157_);
lean_inc_ref(v_expr_1153_);
v___x_1160_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1153_, v_a_1030_);
v_fst_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_fst_1161_);
v_snd_1162_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_snd_1162_);
lean_dec_ref(v___x_1160_);
v___x_1163_ = lean_ptr_addr(v_expr_1153_);
v___x_1164_ = lean_ptr_addr(v_fst_1161_);
v___x_1165_ = lean_usize_dec_eq(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_inc(v_data_1152_);
lean_dec_ref(v_e_1029_);
v___x_1166_ = l_Lean_Expr_mdata___override(v_data_1152_, v_fst_1161_);
v___x_1167_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1166_, v_snd_1162_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v_fst_1161_);
v___x_1168_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1029_, v_snd_1162_);
return v___x_1168_;
}
}
}
case 11:
{
lean_object* v_typeName_1169_; lean_object* v_idx_1170_; lean_object* v_struct_1171_; lean_object* v___x_1172_; uint64_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v_typeName_1169_ = lean_ctor_get(v_e_1029_, 0);
v_idx_1170_ = lean_ctor_get(v_e_1029_, 1);
v_struct_1171_ = lean_ctor_get(v_e_1029_, 2);
v___x_1172_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1173_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1029_);
v___x_1174_ = lean_uint64_to_usize(v___x_1173_);
lean_inc_ref(v_e_1029_);
lean_inc_ref(v_a_1030_);
v___x_1175_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1030_, v___x_1174_, v_e_1029_, v___x_1172_);
v___x_1176_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1175_, v___x_1172_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref(v_e_1029_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v_a_1030_);
return v___x_1177_;
}
else
{
lean_object* v___x_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; size_t v___x_1181_; size_t v___x_1182_; uint8_t v___x_1183_; 
lean_dec_ref(v___x_1175_);
lean_inc_ref(v_struct_1171_);
v___x_1178_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1171_, v_a_1030_);
v_fst_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_fst_1179_);
v_snd_1180_ = lean_ctor_get(v___x_1178_, 1);
lean_inc(v_snd_1180_);
lean_dec_ref(v___x_1178_);
v___x_1181_ = lean_ptr_addr(v_struct_1171_);
v___x_1182_ = lean_ptr_addr(v_fst_1179_);
v___x_1183_ = lean_usize_dec_eq(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_inc(v_idx_1170_);
lean_inc(v_typeName_1169_);
lean_dec_ref(v_e_1029_);
v___x_1184_ = l_Lean_Expr_proj___override(v_typeName_1169_, v_idx_1170_, v_fst_1179_);
v___x_1185_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v___x_1184_, v_snd_1180_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; 
lean_dec(v_fst_1179_);
v___x_1186_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1029_, v_snd_1180_);
return v___x_1186_;
}
}
}
default: 
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1029_, v_a_1030_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1188_, v_a_1189_);
return v___x_1190_;
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

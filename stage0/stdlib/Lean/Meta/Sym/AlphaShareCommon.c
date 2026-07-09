// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareCommon
// Imports: public import Lean.Meta.Sym.ExprPtr public import Lean.Environment import Init.Grind.Util import Lean.ReducibilityAttrs import Lean.ProjFns
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0;
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "EqMatch"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 191, 100, 49, 216, 68, 143, 22)}};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchCond"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 187, 249, 156, 65, 204, 232)}};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_122_ = lean_name_eq(v_declName_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__5));
v___x_124_ = lean_name_eq(v_declName_120_, v___x_123_);
return v___x_124_;
}
else
{
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_125_);
lean_dec(v_declName_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object* v_env_128_, lean_object* v_declName_129_){
_start:
{
uint8_t v___x_130_; 
lean_inc(v_declName_129_);
lean_inc_ref(v_env_128_);
v___x_130_ = l_Lean_getReducibilityStatusCore(v_env_128_, v_declName_129_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_129_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = l_Lean_Environment_isProjectionFn(v_env_128_, v_declName_129_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
v___x_133_ = 1;
return v___x_133_;
}
else
{
return v___x_131_;
}
}
else
{
uint8_t v___x_134_; 
lean_dec(v_declName_129_);
lean_dec_ref(v_env_128_);
v___x_134_ = 0;
return v___x_134_;
}
}
else
{
uint8_t v___x_135_; 
lean_dec(v_declName_129_);
lean_dec_ref(v_env_128_);
v___x_135_ = 0;
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object* v_env_136_, lean_object* v_declName_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_136_, v_declName_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_140_){
_start:
{
uint64_t v___x_141_; 
v___x_141_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_142_){
_start:
{
uint64_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_142_);
lean_dec_ref(v_k_142_);
v_r_144_ = lean_box_uint64(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_147_, lean_object* v_k_u2082_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_147_, v_k_u2082_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_150_, lean_object* v_k_u2082_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_150_, v_k_u2082_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object* v_ctx_156_, lean_object* v_declName_157_){
_start:
{
uint8_t v_checkReducible_158_; 
v_checkReducible_158_ = lean_ctor_get_uint8(v_ctx_156_, sizeof(void*)*1);
if (v_checkReducible_158_ == 0)
{
lean_dec(v_declName_157_);
lean_dec_ref(v_ctx_156_);
return v_checkReducible_158_;
}
else
{
lean_object* v_env_159_; uint8_t v___x_160_; 
v_env_159_ = lean_ctor_get(v_ctx_156_, 0);
lean_inc_ref(v_env_159_);
lean_dec_ref(v_ctx_156_);
v___x_160_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_159_, v_declName_157_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object* v_ctx_161_, lean_object* v_declName_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_161_, v_declName_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_170_ = l_Lean_mkConst(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_172_, lean_object* v_i_173_, lean_object* v_k_174_, lean_object* v_k_u2080_175_){
_start:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_array_get_size(v_keys_172_);
v___x_177_ = lean_nat_dec_lt(v_i_173_, v___x_176_);
if (v___x_177_ == 0)
{
lean_dec_ref(v_k_174_);
lean_dec(v_i_173_);
lean_inc_ref(v_k_u2080_175_);
return v_k_u2080_175_;
}
else
{
lean_object* v_k_x27_178_; uint8_t v___x_179_; 
v_k_x27_178_ = lean_array_fget_borrowed(v_keys_172_, v_i_173_);
lean_inc(v_k_x27_178_);
lean_inc_ref(v_k_174_);
v___x_179_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_174_, v_k_x27_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_i_173_, v___x_180_);
lean_dec(v_i_173_);
v_i_173_ = v___x_181_;
goto _start;
}
else
{
lean_dec_ref(v_k_174_);
lean_dec(v_i_173_);
lean_inc(v_k_x27_178_);
return v_k_x27_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_183_, lean_object* v_i_184_, lean_object* v_k_185_, lean_object* v_k_u2080_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_183_, v_i_184_, v_k_185_, v_k_u2080_186_);
lean_dec_ref(v_k_u2080_186_);
lean_dec_ref(v_keys_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_188_, size_t v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v_es_192_; lean_object* v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v_j_196_; lean_object* v___x_197_; 
v_es_192_ = lean_ctor_get(v_x_188_, 0);
lean_inc_ref(v_es_192_);
lean_dec_ref_known(v_x_188_, 1);
v___x_193_ = lean_box(2);
v___x_194_ = ((size_t)31ULL);
v___x_195_ = lean_usize_land(v_x_189_, v___x_194_);
v_j_196_ = lean_usize_to_nat(v___x_195_);
v___x_197_ = lean_array_get(v___x_193_, v_es_192_, v_j_196_);
lean_dec(v_j_196_);
lean_dec_ref(v_es_192_);
switch(lean_obj_tag(v___x_197_))
{
case 0:
{
lean_object* v_key_198_; uint8_t v___x_199_; 
v_key_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc_n(v_key_198_, 2);
lean_dec_ref_known(v___x_197_, 2);
v___x_199_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_190_, v_key_198_);
if (v___x_199_ == 0)
{
lean_dec(v_key_198_);
lean_inc_ref(v_x_191_);
return v_x_191_;
}
else
{
return v_key_198_;
}
}
case 1:
{
lean_object* v_node_200_; size_t v___x_201_; size_t v___x_202_; 
v_node_200_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_node_200_);
lean_dec_ref_known(v___x_197_, 1);
v___x_201_ = ((size_t)5ULL);
v___x_202_ = lean_usize_shift_right(v_x_189_, v___x_201_);
v_x_188_ = v_node_200_;
v_x_189_ = v___x_202_;
goto _start;
}
default: 
{
lean_dec_ref(v_x_190_);
lean_inc_ref(v_x_191_);
return v_x_191_;
}
}
}
else
{
lean_object* v_ks_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_ks_204_ = lean_ctor_get(v_x_188_, 0);
lean_inc_ref(v_ks_204_);
lean_dec_ref_known(v_x_188_, 2);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_204_, v___x_205_, v_x_190_, v_x_191_);
lean_dec_ref(v_ks_204_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
size_t v_x_2046__boxed_211_; lean_object* v_res_212_; 
v_x_2046__boxed_211_ = lean_unbox_usize(v_x_208_);
lean_dec(v_x_208_);
v_res_212_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_207_, v_x_2046__boxed_211_, v_x_209_, v_x_210_);
lean_dec_ref(v_x_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_ks_217_; lean_object* v_vs_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_242_; 
v_ks_217_ = lean_ctor_get(v_x_213_, 0);
v_vs_218_ = lean_ctor_get(v_x_213_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_242_ == 0)
{
v___x_220_ = v_x_213_;
v_isShared_221_ = v_isSharedCheck_242_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_vs_218_);
lean_inc(v_ks_217_);
lean_dec(v_x_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_242_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_array_get_size(v_ks_217_);
v___x_223_ = lean_nat_dec_lt(v_x_214_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
lean_dec(v_x_214_);
v___x_224_ = lean_array_push(v_ks_217_, v_x_215_);
v___x_225_ = lean_array_push(v_vs_218_, v_x_216_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_225_);
lean_ctor_set(v___x_220_, 0, v___x_224_);
v___x_227_ = v___x_220_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
else
{
lean_object* v_k_x27_229_; uint8_t v___x_230_; 
v_k_x27_229_ = lean_array_fget_borrowed(v_ks_217_, v_x_214_);
lean_inc(v_k_x27_229_);
lean_inc_ref(v_x_215_);
v___x_230_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_215_, v_k_x27_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_232_; 
if (v_isShared_221_ == 0)
{
v___x_232_ = v___x_220_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_ks_217_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_vs_218_);
v___x_232_ = v_reuseFailAlloc_236_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_x_214_, v___x_233_);
lean_dec(v_x_214_);
v_x_213_ = v___x_232_;
v_x_214_ = v___x_234_;
goto _start;
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_237_ = lean_array_fset(v_ks_217_, v_x_214_, v_x_215_);
v___x_238_ = lean_array_fset(v_vs_218_, v_x_214_, v_x_216_);
lean_dec(v_x_214_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_238_);
lean_ctor_set(v___x_220_, 0, v___x_237_);
v___x_240_ = v___x_220_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_243_, lean_object* v_k_244_, lean_object* v_v_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_243_, v___x_246_, v_k_244_, v_v_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_249_, size_t v_x_250_, size_t v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v_es_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v_j_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_es_254_ = lean_ctor_get(v_x_249_, 0);
v___x_255_ = ((size_t)31ULL);
v___x_256_ = lean_usize_land(v_x_250_, v___x_255_);
v_j_257_ = lean_usize_to_nat(v___x_256_);
v___x_258_ = lean_array_get_size(v_es_254_);
v___x_259_ = lean_nat_dec_lt(v_j_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_dec(v_j_257_);
lean_dec(v_x_253_);
lean_dec_ref(v_x_252_);
return v_x_249_;
}
else
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_298_; 
lean_inc_ref(v_es_254_);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v_x_249_, 0);
lean_dec(v_unused_299_);
v___x_261_ = v_x_249_;
v_isShared_262_ = v_isSharedCheck_298_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_x_249_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_298_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v_v_263_; lean_object* v___x_264_; lean_object* v_xs_x27_265_; lean_object* v___y_267_; 
v_v_263_ = lean_array_fget(v_es_254_, v_j_257_);
v___x_264_ = lean_box(0);
v_xs_x27_265_ = lean_array_fset(v_es_254_, v_j_257_, v___x_264_);
switch(lean_obj_tag(v_v_263_))
{
case 0:
{
lean_object* v_key_272_; lean_object* v_val_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_283_; 
v_key_272_ = lean_ctor_get(v_v_263_, 0);
v_val_273_ = lean_ctor_get(v_v_263_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_v_263_);
if (v_isSharedCheck_283_ == 0)
{
v___x_275_ = v_v_263_;
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_val_273_);
lean_inc(v_key_272_);
lean_dec(v_v_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_283_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___x_277_; 
lean_inc(v_key_272_);
lean_inc_ref(v_x_252_);
v___x_277_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_252_, v_key_272_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_del_object(v___x_275_);
v___x_278_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_272_, v_val_273_, v_x_252_, v_x_253_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
v___y_267_ = v___x_279_;
goto v___jp_266_;
}
else
{
lean_object* v___x_281_; 
lean_dec(v_val_273_);
lean_dec(v_key_272_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_x_253_);
lean_ctor_set(v___x_275_, 0, v_x_252_);
v___x_281_ = v___x_275_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_x_252_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_x_253_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
v___y_267_ = v___x_281_;
goto v___jp_266_;
}
}
}
}
case 1:
{
lean_object* v_node_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_296_; 
v_node_284_ = lean_ctor_get(v_v_263_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_v_263_);
if (v_isSharedCheck_296_ == 0)
{
v___x_286_ = v_v_263_;
v_isShared_287_ = v_isSharedCheck_296_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_node_284_);
lean_dec(v_v_263_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_296_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_288_ = ((size_t)5ULL);
v___x_289_ = lean_usize_shift_right(v_x_250_, v___x_288_);
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_add(v_x_251_, v___x_290_);
v___x_292_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_284_, v___x_289_, v___x_291_, v_x_252_, v_x_253_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_292_);
v___x_294_ = v___x_286_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
v___y_267_ = v___x_294_;
goto v___jp_266_;
}
}
}
default: 
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_x_252_);
lean_ctor_set(v___x_297_, 1, v_x_253_);
v___y_267_ = v___x_297_;
goto v___jp_266_;
}
}
v___jp_266_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_array_fset(v_xs_x27_265_, v_j_257_, v___y_267_);
lean_dec(v_j_257_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_268_);
v___x_270_ = v___x_261_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
else
{
lean_object* v_ks_300_; lean_object* v_vs_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_321_; 
v_ks_300_ = lean_ctor_get(v_x_249_, 0);
v_vs_301_ = lean_ctor_get(v_x_249_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_321_ == 0)
{
v___x_303_ = v_x_249_;
v_isShared_304_ = v_isSharedCheck_321_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_vs_301_);
lean_inc(v_ks_300_);
lean_dec(v_x_249_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_321_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_ks_300_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_vs_301_);
v___x_306_ = v_reuseFailAlloc_320_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v_newNode_307_; uint8_t v___y_309_; size_t v___x_315_; uint8_t v___x_316_; 
v_newNode_307_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_306_, v_x_252_, v_x_253_);
v___x_315_ = ((size_t)7ULL);
v___x_316_ = lean_usize_dec_le(v___x_315_, v_x_251_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_307_);
v___x_318_ = lean_unsigned_to_nat(4u);
v___x_319_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
lean_dec(v___x_317_);
v___y_309_ = v___x_319_;
goto v___jp_308_;
}
else
{
v___y_309_ = v___x_316_;
goto v___jp_308_;
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
lean_object* v_ks_310_; lean_object* v_vs_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_ks_310_ = lean_ctor_get(v_newNode_307_, 0);
lean_inc_ref(v_ks_310_);
v_vs_311_ = lean_ctor_get(v_newNode_307_, 1);
lean_inc_ref(v_vs_311_);
lean_dec_ref(v_newNode_307_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_314_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_251_, v_ks_310_, v_vs_311_, v___x_312_, v___x_313_);
lean_dec_ref(v_vs_311_);
lean_dec_ref(v_ks_310_);
return v___x_314_;
}
else
{
return v_newNode_307_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_322_, lean_object* v_keys_323_, lean_object* v_vals_324_, lean_object* v_i_325_, lean_object* v_entries_326_){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_array_get_size(v_keys_323_);
v___x_328_ = lean_nat_dec_lt(v_i_325_, v___x_327_);
if (v___x_328_ == 0)
{
lean_dec(v_i_325_);
return v_entries_326_;
}
else
{
lean_object* v_k_329_; lean_object* v_v_330_; uint64_t v___x_331_; size_t v_h_332_; size_t v___x_333_; lean_object* v___x_334_; size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; size_t v_h_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_k_329_ = lean_array_fget_borrowed(v_keys_323_, v_i_325_);
v_v_330_ = lean_array_fget_borrowed(v_vals_324_, v_i_325_);
v___x_331_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_329_);
v_h_332_ = lean_uint64_to_usize(v___x_331_);
v___x_333_ = ((size_t)5ULL);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_sub(v_depth_322_, v___x_335_);
v___x_337_ = lean_usize_mul(v___x_333_, v___x_336_);
v_h_338_ = lean_usize_shift_right(v_h_332_, v___x_337_);
v___x_339_ = lean_nat_add(v_i_325_, v___x_334_);
lean_dec(v_i_325_);
lean_inc(v_v_330_);
lean_inc(v_k_329_);
v___x_340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_326_, v_h_338_, v_depth_322_, v_k_329_, v_v_330_);
v_i_325_ = v___x_339_;
v_entries_326_ = v___x_340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_342_, lean_object* v_keys_343_, lean_object* v_vals_344_, lean_object* v_i_345_, lean_object* v_entries_346_){
_start:
{
size_t v_depth_boxed_347_; lean_object* v_res_348_; 
v_depth_boxed_347_ = lean_unbox_usize(v_depth_342_);
lean_dec(v_depth_342_);
v_res_348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_347_, v_keys_343_, v_vals_344_, v_i_345_, v_entries_346_);
lean_dec_ref(v_vals_344_);
lean_dec_ref(v_keys_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
size_t v_x_2164__boxed_354_; size_t v_x_2165__boxed_355_; lean_object* v_res_356_; 
v_x_2164__boxed_354_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_x_2165__boxed_355_ = lean_unbox_usize(v_x_351_);
lean_dec(v_x_351_);
v_res_356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_349_, v_x_2164__boxed_354_, v_x_2165__boxed_355_, v_x_352_, v_x_353_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
uint64_t v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v___x_360_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_358_);
v___x_361_ = lean_uint64_to_usize(v___x_360_);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_357_, v___x_361_, v___x_362_, v_x_358_, v_x_359_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_364_, lean_object* v_b_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_dec(v_b_365_);
lean_dec_ref(v_a_364_);
return v_x_366_;
}
else
{
lean_object* v_key_367_; lean_object* v_value_368_; lean_object* v_tail_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_381_; 
v_key_367_ = lean_ctor_get(v_x_366_, 0);
v_value_368_ = lean_ctor_get(v_x_366_, 1);
v_tail_369_ = lean_ctor_get(v_x_366_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_381_ == 0)
{
v___x_371_ = v_x_366_;
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_tail_369_);
lean_inc(v_value_368_);
lean_inc(v_key_367_);
lean_dec(v_x_366_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___x_373_; 
v___x_373_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_367_, v_a_364_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_364_, v_b_365_, v_tail_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 2, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_key_367_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_value_368_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v_value_368_);
lean_dec(v_key_367_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v_b_365_);
lean_ctor_set(v___x_371_, 0, v_a_364_);
v___x_379_ = v___x_371_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_364_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_b_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_tail_369_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
return v_x_382_;
}
else
{
lean_object* v_key_384_; lean_object* v_value_385_; lean_object* v_tail_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_409_; 
v_key_384_ = lean_ctor_get(v_x_383_, 0);
v_value_385_ = lean_ctor_get(v_x_383_, 1);
v_tail_386_ = lean_ctor_get(v_x_383_, 2);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_409_ == 0)
{
v___x_388_ = v_x_383_;
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_tail_386_);
lean_inc(v_value_385_);
lean_inc(v_key_384_);
lean_dec(v_x_383_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_409_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v_fold_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_390_ = lean_array_get_size(v_x_382_);
v___x_391_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_384_);
v___x_392_ = 32ULL;
v___x_393_ = lean_uint64_shift_right(v___x_391_, v___x_392_);
v_fold_394_ = lean_uint64_xor(v___x_391_, v___x_393_);
v___x_395_ = 16ULL;
v___x_396_ = lean_uint64_shift_right(v_fold_394_, v___x_395_);
v___x_397_ = lean_uint64_xor(v_fold_394_, v___x_396_);
v___x_398_ = lean_uint64_to_usize(v___x_397_);
v___x_399_ = lean_usize_of_nat(v___x_390_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_sub(v___x_399_, v___x_400_);
v___x_402_ = lean_usize_land(v___x_398_, v___x_401_);
v___x_403_ = lean_array_uget_borrowed(v_x_382_, v___x_402_);
lean_inc(v___x_403_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 2, v___x_403_);
v___x_405_ = v___x_388_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_key_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_value_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v___x_403_);
v___x_405_ = v_reuseFailAlloc_408_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; 
v___x_406_ = lean_array_uset(v_x_382_, v___x_402_, v___x_405_);
v_x_382_ = v___x_406_;
v_x_383_ = v_tail_386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_410_, lean_object* v_source_411_, lean_object* v_target_412_){
_start:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_array_get_size(v_source_411_);
v___x_414_ = lean_nat_dec_lt(v_i_410_, v___x_413_);
if (v___x_414_ == 0)
{
lean_dec_ref(v_source_411_);
lean_dec(v_i_410_);
return v_target_412_;
}
else
{
lean_object* v_es_415_; lean_object* v___x_416_; lean_object* v_source_417_; lean_object* v_target_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_es_415_ = lean_array_fget(v_source_411_, v_i_410_);
v___x_416_ = lean_box(0);
v_source_417_ = lean_array_fset(v_source_411_, v_i_410_, v___x_416_);
v_target_418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_412_, v_es_415_);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_add(v_i_410_, v___x_419_);
lean_dec(v_i_410_);
v_i_410_ = v___x_420_;
v_source_411_ = v_source_417_;
v_target_412_ = v_target_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_nbuckets_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_423_ = lean_array_get_size(v_data_422_);
v___x_424_ = lean_unsigned_to_nat(2u);
v_nbuckets_425_ = lean_nat_mul(v___x_423_, v___x_424_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_box(0);
v___x_428_ = lean_mk_array(v_nbuckets_425_, v___x_427_);
v___x_429_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_426_, v_data_422_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
uint8_t v___x_432_; 
v___x_432_ = 0;
return v___x_432_;
}
else
{
lean_object* v_key_433_; lean_object* v_tail_434_; uint8_t v___x_435_; 
v_key_433_ = lean_ctor_get(v_x_431_, 0);
v_tail_434_ = lean_ctor_get(v_x_431_, 2);
v___x_435_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_433_, v_a_430_);
if (v___x_435_ == 0)
{
v_x_431_ = v_tail_434_;
goto _start;
}
else
{
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_437_, lean_object* v_x_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec_ref(v_a_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_size_444_; lean_object* v_buckets_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_488_; 
v_size_444_ = lean_ctor_get(v_m_441_, 0);
v_buckets_445_ = lean_ctor_get(v_m_441_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_m_441_);
if (v_isSharedCheck_488_ == 0)
{
v___x_447_ = v_m_441_;
v_isShared_448_ = v_isSharedCheck_488_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_buckets_445_);
lean_inc(v_size_444_);
lean_dec(v_m_441_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_488_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v_fold_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v_bkt_462_; uint8_t v___x_463_; 
v___x_449_ = lean_array_get_size(v_buckets_445_);
v___x_450_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_442_);
v___x_451_ = 32ULL;
v___x_452_ = lean_uint64_shift_right(v___x_450_, v___x_451_);
v_fold_453_ = lean_uint64_xor(v___x_450_, v___x_452_);
v___x_454_ = 16ULL;
v___x_455_ = lean_uint64_shift_right(v_fold_453_, v___x_454_);
v___x_456_ = lean_uint64_xor(v_fold_453_, v___x_455_);
v___x_457_ = lean_uint64_to_usize(v___x_456_);
v___x_458_ = lean_usize_of_nat(v___x_449_);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_sub(v___x_458_, v___x_459_);
v___x_461_ = lean_usize_land(v___x_457_, v___x_460_);
v_bkt_462_ = lean_array_uget_borrowed(v_buckets_445_, v___x_461_);
v___x_463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_442_, v_bkt_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v_size_x27_465_; lean_object* v___x_466_; lean_object* v_buckets_x27_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v_size_x27_465_ = lean_nat_add(v_size_444_, v___x_464_);
lean_dec(v_size_444_);
lean_inc(v_bkt_462_);
v___x_466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_466_, 0, v_a_442_);
lean_ctor_set(v___x_466_, 1, v_b_443_);
lean_ctor_set(v___x_466_, 2, v_bkt_462_);
v_buckets_x27_467_ = lean_array_uset(v_buckets_445_, v___x_461_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(4u);
v___x_469_ = lean_nat_mul(v_size_x27_465_, v___x_468_);
v___x_470_ = lean_unsigned_to_nat(3u);
v___x_471_ = lean_nat_div(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_array_get_size(v_buckets_x27_467_);
v___x_473_ = lean_nat_dec_le(v___x_471_, v___x_472_);
lean_dec(v___x_471_);
if (v___x_473_ == 0)
{
lean_object* v_val_474_; lean_object* v___x_476_; 
v_val_474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_467_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_val_474_);
lean_ctor_set(v___x_447_, 0, v_size_x27_465_);
v___x_476_ = v___x_447_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_size_x27_465_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_val_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_479_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_buckets_x27_467_);
lean_ctor_set(v___x_447_, 0, v_size_x27_465_);
v___x_479_ = v___x_447_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_size_x27_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_buckets_x27_467_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v___x_481_; lean_object* v_buckets_x27_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
lean_inc(v_bkt_462_);
v___x_481_ = lean_box(0);
v_buckets_x27_482_ = lean_array_uset(v_buckets_445_, v___x_461_, v___x_481_);
v___x_483_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_442_, v_b_443_, v_bkt_462_);
v___x_484_ = lean_array_uset(v_buckets_x27_482_, v___x_461_, v___x_483_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_484_);
v___x_486_ = v___x_447_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_size_444_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_489_, lean_object* v_r_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_map_492_; lean_object* v_set_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_515_; 
v_map_492_ = lean_ctor_get(v_a_491_, 0);
v_set_493_ = lean_ctor_get(v_a_491_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_491_);
if (v_isSharedCheck_515_ == 0)
{
v___x_495_ = v_a_491_;
v_isShared_496_ = v_isSharedCheck_515_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_set_493_);
lean_inc(v_map_492_);
lean_dec(v_a_491_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_515_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; uint64_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_497_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_498_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_490_);
v___x_499_ = lean_uint64_to_usize(v___x_498_);
lean_inc_ref(v_r_490_);
lean_inc_ref(v_set_493_);
v___x_500_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_493_, v___x_499_, v_r_490_, v___x_497_);
v___x_501_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_500_, v___x_497_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec_ref(v_r_490_);
lean_inc_ref(v___x_500_);
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_492_, v_e_489_, v___x_500_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_502_);
v___x_504_ = v___x_495_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_set_493_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_500_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
return v___x_505_;
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
lean_dec_ref(v___x_500_);
lean_inc_ref_n(v_r_490_, 4);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_492_, v_e_489_, v_r_490_);
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_507_, v_r_490_, v_r_490_);
v___x_509_ = lean_box(0);
v___x_510_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_493_, v_r_490_, v___x_509_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_510_);
lean_ctor_set(v___x_495_, 0, v___x_508_);
v___x_512_ = v___x_495_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_510_);
v___x_512_ = v_reuseFailAlloc_514_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; 
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_r_490_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_516_, lean_object* v_r_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_516_, v_r_517_, v_a_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_521_, lean_object* v_r_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_521_, v_r_522_, v_a_523_, v_a_524_);
lean_dec_ref(v_a_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_526_, lean_object* v_x_527_, size_t v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_527_, v_x_528_, v_x_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
size_t v_x_2589__boxed_537_; lean_object* v_res_538_; 
v_x_2589__boxed_537_ = lean_unbox_usize(v_x_534_);
lean_dec(v_x_534_);
v_res_538_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_532_, v_x_533_, v_x_2589__boxed_537_, v_x_535_, v_x_536_);
lean_dec_ref(v_x_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_539_, lean_object* v_m_540_, lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_540_, v_a_541_, v_b_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_545_, v_x_546_, v_x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_549_, lean_object* v_keys_550_, lean_object* v_vals_551_, lean_object* v_heq_552_, lean_object* v_i_553_, lean_object* v_k_554_, lean_object* v_k_u2080_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_550_, v_i_553_, v_k_554_, v_k_u2080_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_557_, lean_object* v_keys_558_, lean_object* v_vals_559_, lean_object* v_heq_560_, lean_object* v_i_561_, lean_object* v_k_562_, lean_object* v_k_u2080_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_557_, v_keys_558_, v_vals_559_, v_heq_560_, v_i_561_, v_k_562_, v_k_u2080_563_);
lean_dec_ref(v_k_u2080_563_);
lean_dec_ref(v_vals_559_);
lean_dec_ref(v_keys_558_);
return v_res_564_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_565_, lean_object* v_a_566_, lean_object* v_x_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_566_, v_x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_569_, lean_object* v_a_570_, lean_object* v_x_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_569_, v_a_570_, v_x_571_);
lean_dec(v_x_571_);
lean_dec_ref(v_a_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_574_, lean_object* v_data_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_577_, lean_object* v_a_578_, lean_object* v_b_579_, lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_578_, v_b_579_, v_x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_582_, lean_object* v_x_583_, size_t v_x_584_, size_t v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_583_, v_x_584_, v_x_585_, v_x_586_, v_x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
size_t v_x_2626__boxed_595_; size_t v_x_2627__boxed_596_; lean_object* v_res_597_; 
v_x_2626__boxed_595_ = lean_unbox_usize(v_x_591_);
lean_dec(v_x_591_);
v_x_2627__boxed_596_ = lean_unbox_usize(v_x_592_);
lean_dec(v_x_592_);
v_res_597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_589_, v_x_590_, v_x_2626__boxed_595_, v_x_2627__boxed_596_, v_x_593_, v_x_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_598_, lean_object* v_i_599_, lean_object* v_source_600_, lean_object* v_target_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_599_, v_source_600_, v_target_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_603_, lean_object* v_n_604_, lean_object* v_k_605_, lean_object* v_v_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_604_, v_k_605_, v_v_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_608_, size_t v_depth_609_, lean_object* v_keys_610_, lean_object* v_vals_611_, lean_object* v_heq_612_, lean_object* v_i_613_, lean_object* v_entries_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_609_, v_keys_610_, v_vals_611_, v_i_613_, v_entries_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_616_, lean_object* v_depth_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_heq_620_, lean_object* v_i_621_, lean_object* v_entries_622_){
_start:
{
size_t v_depth_boxed_623_; lean_object* v_res_624_; 
v_depth_boxed_623_ = lean_unbox_usize(v_depth_617_);
lean_dec(v_depth_617_);
v_res_624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_616_, v_depth_boxed_623_, v_keys_618_, v_vals_619_, v_heq_620_, v_i_621_, v_entries_622_);
lean_dec_ref(v_vals_619_);
lean_dec_ref(v_keys_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_630_, v_x_631_, v_x_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_637_, lean_object* v_k_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_map_641_; lean_object* v_set_642_; lean_object* v___f_643_; lean_object* v___f_644_; lean_object* v___x_645_; 
v_map_641_ = lean_ctor_get(v_a_640_, 0);
v_set_642_ = lean_ctor_get(v_a_640_, 1);
v___f_643_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_644_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_637_);
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_643_, v___f_644_, v_map_641_, v_e_637_);
if (lean_obj_tag(v___x_645_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_647_; 
lean_dec_ref(v_k_638_);
lean_dec_ref(v_e_637_);
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v_val_646_);
lean_ctor_set(v___x_647_, 1, v_a_640_);
return v___x_647_;
}
else
{
lean_object* v___f_648_; lean_object* v___x_649_; uint64_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
lean_dec(v___x_645_);
v___f_648_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_649_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_650_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_637_);
v___x_651_ = lean_uint64_to_usize(v___x_650_);
lean_inc_ref(v_e_637_);
lean_inc_ref(v_set_642_);
v___x_652_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_648_, v_set_642_, v___x_651_, v_e_637_, v___x_649_);
v___x_653_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_652_, v___x_649_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v_k_638_);
lean_dec_ref(v_e_637_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v_a_640_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; 
lean_dec(v___x_652_);
lean_inc_ref(v_a_639_);
v___x_655_ = lean_apply_2(v_k_638_, v_a_639_, v_a_640_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
v_a_657_ = lean_ctor_get(v___x_655_, 1);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_655_, 2);
v___x_658_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_637_, v_a_656_, v_a_657_);
return v___x_658_;
}
else
{
lean_dec_ref(v_e_637_);
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_659_, lean_object* v_k_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_659_, v_k_660_, v_a_661_, v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_664_, lean_object* v_x_665_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_673_, v_x_674_);
lean_dec(v_x_674_);
lean_dec_ref(v_a_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_676_, lean_object* v_a_677_){
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
v___x_693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_677_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_694_, v_a_695_);
lean_dec_ref(v_a_695_);
lean_dec_ref(v_m_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_697_, lean_object* v_vals_698_, lean_object* v_i_699_, lean_object* v_k_700_){
_start:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_array_get_size(v_keys_697_);
v___x_702_ = lean_nat_dec_lt(v_i_699_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_dec_ref(v_k_700_);
lean_dec(v_i_699_);
v___x_703_ = lean_box(0);
return v___x_703_;
}
else
{
lean_object* v_k_x27_704_; uint8_t v___x_705_; 
v_k_x27_704_ = lean_array_fget_borrowed(v_keys_697_, v_i_699_);
lean_inc(v_k_x27_704_);
lean_inc_ref(v_k_700_);
v___x_705_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_700_, v_k_x27_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v_i_699_, v___x_706_);
lean_dec(v_i_699_);
v_i_699_ = v___x_707_;
goto _start;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec_ref(v_k_700_);
v___x_709_ = lean_array_fget_borrowed(v_vals_698_, v_i_699_);
lean_dec(v_i_699_);
lean_inc(v___x_709_);
lean_inc(v_k_x27_704_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_k_x27_704_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_i_714_, lean_object* v_k_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_712_, v_vals_713_, v_i_714_, v_k_715_);
lean_dec_ref(v_vals_713_);
lean_dec_ref(v_keys_712_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_717_, size_t v_x_718_, lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_717_) == 0)
{
lean_object* v_es_720_; lean_object* v___x_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v_j_724_; lean_object* v___x_725_; 
v_es_720_ = lean_ctor_get(v_x_717_, 0);
lean_inc_ref(v_es_720_);
lean_dec_ref_known(v_x_717_, 1);
v___x_721_ = lean_box(2);
v___x_722_ = ((size_t)31ULL);
v___x_723_ = lean_usize_land(v_x_718_, v___x_722_);
v_j_724_ = lean_usize_to_nat(v___x_723_);
v___x_725_ = lean_array_get(v___x_721_, v_es_720_, v_j_724_);
lean_dec(v_j_724_);
lean_dec_ref(v_es_720_);
switch(lean_obj_tag(v___x_725_))
{
case 0:
{
lean_object* v_key_726_; lean_object* v_val_727_; uint8_t v___x_728_; 
v_key_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_n(v_key_726_, 2);
v_val_727_ = lean_ctor_get(v___x_725_, 1);
lean_inc(v_val_727_);
lean_dec_ref_known(v___x_725_, 2);
v___x_728_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_719_, v_key_726_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v_val_727_);
lean_dec(v_key_726_);
v___x_729_ = lean_box(0);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_key_726_);
lean_ctor_set(v___x_730_, 1, v_val_727_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
case 1:
{
lean_object* v_node_732_; size_t v___x_733_; size_t v___x_734_; 
v_node_732_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_node_732_);
lean_dec_ref_known(v___x_725_, 1);
v___x_733_ = ((size_t)5ULL);
v___x_734_ = lean_usize_shift_right(v_x_718_, v___x_733_);
v_x_717_ = v_node_732_;
v_x_718_ = v___x_734_;
goto _start;
}
default: 
{
lean_object* v___x_736_; 
lean_dec_ref(v_x_719_);
v___x_736_ = lean_box(0);
return v___x_736_;
}
}
}
else
{
lean_object* v_ks_737_; lean_object* v_vs_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_ks_737_ = lean_ctor_get(v_x_717_, 0);
lean_inc_ref(v_ks_737_);
v_vs_738_ = lean_ctor_get(v_x_717_, 1);
lean_inc_ref(v_vs_738_);
lean_dec_ref_known(v_x_717_, 2);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_737_, v_vs_738_, v___x_739_, v_x_719_);
lean_dec_ref(v_vs_738_);
lean_dec_ref(v_ks_737_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
size_t v_x_11024__boxed_744_; lean_object* v_res_745_; 
v_x_11024__boxed_744_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_res_745_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_741_, v_x_11024__boxed_744_, v_x_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
uint64_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_747_);
v___x_749_ = lean_uint64_to_usize(v___x_748_);
lean_inc_ref(v_x_746_);
v___x_750_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_746_, v___x_749_, v_x_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_751_, v_x_752_);
lean_dec_ref(v_x_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___y_758_; lean_object* v___y_763_; lean_object* v___y_768_; lean_object* v___y_773_; 
switch(lean_obj_tag(v_e_754_))
{
case 4:
{
lean_object* v_declName_777_; lean_object* v_map_778_; lean_object* v_set_779_; lean_object* v___x_780_; 
v_declName_777_ = lean_ctor_get(v_e_754_, 0);
v_map_778_ = lean_ctor_get(v_a_756_, 0);
v_set_779_ = lean_ctor_get(v_a_756_, 1);
lean_inc_ref(v_e_754_);
v___x_780_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_779_, v_e_754_);
if (lean_obj_tag(v___x_780_) == 0)
{
uint8_t v___x_781_; 
lean_inc(v_declName_777_);
lean_inc_ref(v_a_755_);
v___x_781_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_755_, v_declName_777_);
if (v___x_781_ == 0)
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
lean_inc_ref(v_set_779_);
lean_inc_ref(v_map_778_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_756_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_792_ = lean_ctor_get(v_a_756_, 1);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_a_756_, 0);
lean_dec(v_unused_793_);
v___x_783_ = v_a_756_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_a_756_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_box(0);
lean_inc_ref(v_e_754_);
v___x_786_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_779_, v_e_754_, v___x_785_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_map_778_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_790_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_e_754_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec_ref_known(v_e_754_, 2);
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_a_756_);
return v___x_795_;
}
}
else
{
lean_object* v_val_796_; lean_object* v_fst_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref_known(v_e_754_, 2);
v_val_796_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_val_796_);
lean_dec_ref_known(v___x_780_, 1);
v_fst_797_ = lean_ctor_get(v_val_796_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_val_796_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v_val_796_, 1);
lean_dec(v_unused_805_);
v___x_799_ = v_val_796_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_fst_797_);
lean_dec(v_val_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_a_756_);
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_fst_797_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_a_756_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
case 5:
{
lean_object* v_fn_806_; lean_object* v_arg_807_; lean_object* v_map_808_; lean_object* v_set_809_; lean_object* v___x_810_; 
v_fn_806_ = lean_ctor_get(v_e_754_, 0);
v_arg_807_ = lean_ctor_get(v_e_754_, 1);
v_map_808_ = lean_ctor_get(v_a_756_, 0);
v_set_809_ = lean_ctor_get(v_a_756_, 1);
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_808_, v_e_754_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_812_; 
lean_dec_ref_known(v_e_754_, 2);
v_val_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_val_811_);
lean_ctor_set(v___x_812_, 1, v_a_756_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; uint64_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
lean_dec(v___x_810_);
v___x_813_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_814_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_754_);
v___x_815_ = lean_uint64_to_usize(v___x_814_);
lean_inc_ref(v_e_754_);
lean_inc_ref(v_set_809_);
v___x_816_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_809_, v___x_815_, v_e_754_, v___x_813_);
v___x_817_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_816_, v___x_813_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
lean_dec_ref_known(v_e_754_, 2);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v_a_756_);
return v___x_818_;
}
else
{
lean_object* v___x_819_; 
lean_dec_ref(v___x_816_);
lean_inc_ref(v_fn_806_);
v___x_819_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_806_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
v_a_821_ = lean_ctor_get(v___x_819_, 1);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_819_, 2);
lean_inc_ref(v_arg_807_);
v___x_822_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_807_, v_a_755_, v_a_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v_a_824_; uint8_t v___y_826_; size_t v___x_830_; size_t v___x_831_; uint8_t v___x_832_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
v_a_824_ = lean_ctor_get(v___x_822_, 1);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_822_, 2);
v___x_830_ = lean_ptr_addr(v_fn_806_);
v___x_831_ = lean_ptr_addr(v_a_820_);
v___x_832_ = lean_usize_dec_eq(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
v___y_826_ = v___x_832_;
goto v___jp_825_;
}
else
{
size_t v___x_833_; size_t v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_ptr_addr(v_arg_807_);
v___x_834_ = lean_ptr_addr(v_a_823_);
v___x_835_ = lean_usize_dec_eq(v___x_833_, v___x_834_);
v___y_826_ = v___x_835_;
goto v___jp_825_;
}
v___jp_825_:
{
if (v___y_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l_Lean_Expr_app___override(v_a_820_, v_a_823_);
v___x_828_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_827_, v_a_824_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; 
lean_dec(v_a_823_);
lean_dec(v_a_820_);
lean_inc_ref(v_e_754_);
v___x_829_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_e_754_, v_a_824_);
return v___x_829_;
}
}
}
else
{
lean_dec(v_a_820_);
v___y_768_ = v___x_822_;
goto v___jp_767_;
}
}
else
{
v___y_768_ = v___x_819_;
goto v___jp_767_;
}
}
}
}
case 6:
{
lean_object* v_binderName_836_; lean_object* v_binderType_837_; lean_object* v_body_838_; uint8_t v_binderInfo_839_; lean_object* v_map_840_; lean_object* v_set_841_; lean_object* v___x_842_; 
v_binderName_836_ = lean_ctor_get(v_e_754_, 0);
v_binderType_837_ = lean_ctor_get(v_e_754_, 1);
v_body_838_ = lean_ctor_get(v_e_754_, 2);
v_binderInfo_839_ = lean_ctor_get_uint8(v_e_754_, sizeof(void*)*3 + 8);
v_map_840_ = lean_ctor_get(v_a_756_, 0);
v_set_841_ = lean_ctor_get(v_a_756_, 1);
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_840_, v_e_754_);
if (lean_obj_tag(v___x_842_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_844_; 
lean_dec_ref_known(v_e_754_, 3);
v_val_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_842_, 1);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_val_843_);
lean_ctor_set(v___x_844_, 1, v_a_756_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; uint64_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
lean_dec(v___x_842_);
v___x_845_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_846_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_754_);
v___x_847_ = lean_uint64_to_usize(v___x_846_);
lean_inc_ref(v_e_754_);
lean_inc_ref(v_set_841_);
v___x_848_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_841_, v___x_847_, v_e_754_, v___x_845_);
v___x_849_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_848_, v___x_845_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec_ref_known(v_e_754_, 3);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v_a_756_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; 
lean_dec_ref(v___x_848_);
lean_inc_ref(v_binderType_837_);
v___x_851_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_837_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
v_a_853_ = lean_ctor_get(v___x_851_, 1);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_851_, 2);
lean_inc_ref(v_body_838_);
v___x_854_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_838_, v_a_755_, v_a_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v_a_856_; uint8_t v___y_858_; size_t v___x_865_; size_t v___x_866_; uint8_t v___x_867_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
v_a_856_ = lean_ctor_get(v___x_854_, 1);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_854_, 2);
v___x_865_ = lean_ptr_addr(v_binderType_837_);
v___x_866_ = lean_ptr_addr(v_a_852_);
v___x_867_ = lean_usize_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
v___y_858_ = v___x_867_;
goto v___jp_857_;
}
else
{
size_t v___x_868_; size_t v___x_869_; uint8_t v___x_870_; 
v___x_868_ = lean_ptr_addr(v_body_838_);
v___x_869_ = lean_ptr_addr(v_a_855_);
v___x_870_ = lean_usize_dec_eq(v___x_868_, v___x_869_);
v___y_858_ = v___x_870_;
goto v___jp_857_;
}
v___jp_857_:
{
if (v___y_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_inc(v_binderName_836_);
v___x_859_ = l_Lean_Expr_lam___override(v_binderName_836_, v_a_852_, v_a_855_, v_binderInfo_839_);
v___x_860_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_859_, v_a_856_);
return v___x_860_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_839_, v_binderInfo_839_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc(v_binderName_836_);
v___x_862_ = l_Lean_Expr_lam___override(v_binderName_836_, v_a_852_, v_a_855_, v_binderInfo_839_);
v___x_863_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_862_, v_a_856_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; 
lean_dec(v_a_855_);
lean_dec(v_a_852_);
lean_inc_ref(v_e_754_);
v___x_864_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_e_754_, v_a_856_);
return v___x_864_;
}
}
}
}
else
{
lean_dec(v_a_852_);
v___y_763_ = v___x_854_;
goto v___jp_762_;
}
}
else
{
v___y_763_ = v___x_851_;
goto v___jp_762_;
}
}
}
}
case 7:
{
lean_object* v_binderName_871_; lean_object* v_binderType_872_; lean_object* v_body_873_; uint8_t v_binderInfo_874_; lean_object* v_map_875_; lean_object* v_set_876_; lean_object* v___x_877_; 
v_binderName_871_ = lean_ctor_get(v_e_754_, 0);
v_binderType_872_ = lean_ctor_get(v_e_754_, 1);
v_body_873_ = lean_ctor_get(v_e_754_, 2);
v_binderInfo_874_ = lean_ctor_get_uint8(v_e_754_, sizeof(void*)*3 + 8);
v_map_875_ = lean_ctor_get(v_a_756_, 0);
v_set_876_ = lean_ctor_get(v_a_756_, 1);
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_875_, v_e_754_);
if (lean_obj_tag(v___x_877_) == 1)
{
lean_object* v_val_878_; lean_object* v___x_879_; 
lean_dec_ref_known(v_e_754_, 3);
v_val_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_val_878_);
lean_ctor_set(v___x_879_, 1, v_a_756_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; uint64_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
lean_dec(v___x_877_);
v___x_880_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_881_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_754_);
v___x_882_ = lean_uint64_to_usize(v___x_881_);
lean_inc_ref(v_e_754_);
lean_inc_ref(v_set_876_);
v___x_883_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_876_, v___x_882_, v_e_754_, v___x_880_);
v___x_884_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_883_, v___x_880_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
lean_dec_ref_known(v_e_754_, 3);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v_a_756_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
lean_dec_ref(v___x_883_);
lean_inc_ref(v_binderType_872_);
v___x_886_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_872_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
v_a_888_ = lean_ctor_get(v___x_886_, 1);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_886_, 2);
lean_inc_ref(v_body_873_);
v___x_889_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_873_, v_a_755_, v_a_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v_a_891_; uint8_t v___y_893_; size_t v___x_900_; size_t v___x_901_; uint8_t v___x_902_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
v_a_891_ = lean_ctor_get(v___x_889_, 1);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_889_, 2);
v___x_900_ = lean_ptr_addr(v_binderType_872_);
v___x_901_ = lean_ptr_addr(v_a_887_);
v___x_902_ = lean_usize_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
v___y_893_ = v___x_902_;
goto v___jp_892_;
}
else
{
size_t v___x_903_; size_t v___x_904_; uint8_t v___x_905_; 
v___x_903_ = lean_ptr_addr(v_body_873_);
v___x_904_ = lean_ptr_addr(v_a_890_);
v___x_905_ = lean_usize_dec_eq(v___x_903_, v___x_904_);
v___y_893_ = v___x_905_;
goto v___jp_892_;
}
v___jp_892_:
{
if (v___y_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc(v_binderName_871_);
v___x_894_ = l_Lean_Expr_forallE___override(v_binderName_871_, v_a_887_, v_a_890_, v_binderInfo_874_);
v___x_895_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_894_, v_a_891_);
return v___x_895_;
}
else
{
uint8_t v___x_896_; 
v___x_896_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_874_, v_binderInfo_874_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_inc(v_binderName_871_);
v___x_897_ = l_Lean_Expr_forallE___override(v_binderName_871_, v_a_887_, v_a_890_, v_binderInfo_874_);
v___x_898_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_897_, v_a_891_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; 
lean_dec(v_a_890_);
lean_dec(v_a_887_);
lean_inc_ref(v_e_754_);
v___x_899_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_e_754_, v_a_891_);
return v___x_899_;
}
}
}
}
else
{
lean_dec(v_a_887_);
v___y_773_ = v___x_889_;
goto v___jp_772_;
}
}
else
{
v___y_773_ = v___x_886_;
goto v___jp_772_;
}
}
}
}
case 8:
{
lean_object* v_declName_906_; lean_object* v_type_907_; lean_object* v_value_908_; lean_object* v_body_909_; uint8_t v_nondep_910_; lean_object* v_map_911_; lean_object* v_set_912_; lean_object* v___x_913_; 
v_declName_906_ = lean_ctor_get(v_e_754_, 0);
v_type_907_ = lean_ctor_get(v_e_754_, 1);
v_value_908_ = lean_ctor_get(v_e_754_, 2);
v_body_909_ = lean_ctor_get(v_e_754_, 3);
v_nondep_910_ = lean_ctor_get_uint8(v_e_754_, sizeof(void*)*4 + 8);
v_map_911_ = lean_ctor_get(v_a_756_, 0);
v_set_912_ = lean_ctor_get(v_a_756_, 1);
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_911_, v_e_754_);
if (lean_obj_tag(v___x_913_) == 1)
{
lean_object* v_val_914_; lean_object* v___x_915_; 
lean_dec_ref_known(v_e_754_, 4);
v_val_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_val_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_val_914_);
lean_ctor_set(v___x_915_, 1, v_a_756_);
return v___x_915_;
}
else
{
lean_object* v___x_916_; uint64_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
lean_dec(v___x_913_);
v___x_916_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_917_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_754_);
v___x_918_ = lean_uint64_to_usize(v___x_917_);
lean_inc_ref(v_e_754_);
lean_inc_ref(v_set_912_);
v___x_919_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_912_, v___x_918_, v_e_754_, v___x_916_);
v___x_920_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_919_, v___x_916_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_dec_ref_known(v_e_754_, 4);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v_a_756_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; 
lean_dec_ref(v___x_919_);
lean_inc_ref(v_type_907_);
v___x_922_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_907_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v_a_924_; lean_object* v___x_925_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
v_a_924_ = lean_ctor_get(v___x_922_, 1);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_922_, 2);
lean_inc_ref(v_value_908_);
v___x_925_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_908_, v_a_755_, v_a_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
v_a_927_ = lean_ctor_get(v___x_925_, 1);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_925_, 2);
lean_inc_ref(v_body_909_);
v___x_928_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_909_, v_a_755_, v_a_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_a_930_; uint8_t v___y_932_; size_t v___x_941_; size_t v___x_942_; uint8_t v___x_943_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
v_a_930_ = lean_ctor_get(v___x_928_, 1);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_928_, 2);
v___x_941_ = lean_ptr_addr(v_type_907_);
v___x_942_ = lean_ptr_addr(v_a_923_);
v___x_943_ = lean_usize_dec_eq(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
v___y_932_ = v___x_943_;
goto v___jp_931_;
}
else
{
size_t v___x_944_; size_t v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_ptr_addr(v_value_908_);
v___x_945_ = lean_ptr_addr(v_a_926_);
v___x_946_ = lean_usize_dec_eq(v___x_944_, v___x_945_);
v___y_932_ = v___x_946_;
goto v___jp_931_;
}
v___jp_931_:
{
if (v___y_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc(v_declName_906_);
v___x_933_ = l_Lean_Expr_letE___override(v_declName_906_, v_a_923_, v_a_926_, v_a_929_, v_nondep_910_);
v___x_934_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_933_, v_a_930_);
return v___x_934_;
}
else
{
size_t v___x_935_; size_t v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_ptr_addr(v_body_909_);
v___x_936_ = lean_ptr_addr(v_a_929_);
v___x_937_ = lean_usize_dec_eq(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_inc(v_declName_906_);
v___x_938_ = l_Lean_Expr_letE___override(v_declName_906_, v_a_923_, v_a_926_, v_a_929_, v_nondep_910_);
v___x_939_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_938_, v_a_930_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; 
lean_dec(v_a_929_);
lean_dec(v_a_926_);
lean_dec(v_a_923_);
lean_inc_ref(v_e_754_);
v___x_940_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_e_754_, v_a_930_);
return v___x_940_;
}
}
}
}
else
{
lean_dec(v_a_926_);
lean_dec(v_a_923_);
v___y_758_ = v___x_928_;
goto v___jp_757_;
}
}
else
{
lean_dec(v_a_923_);
v___y_758_ = v___x_925_;
goto v___jp_757_;
}
}
else
{
v___y_758_ = v___x_922_;
goto v___jp_757_;
}
}
}
}
case 10:
{
lean_object* v_data_947_; lean_object* v_expr_948_; lean_object* v_map_949_; lean_object* v_set_950_; lean_object* v___x_951_; 
v_data_947_ = lean_ctor_get(v_e_754_, 0);
v_expr_948_ = lean_ctor_get(v_e_754_, 1);
v_map_949_ = lean_ctor_get(v_a_756_, 0);
v_set_950_ = lean_ctor_get(v_a_756_, 1);
v___x_951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_949_, v_e_754_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_val_952_; lean_object* v___x_953_; 
lean_dec_ref_known(v_e_754_, 2);
v_val_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_val_952_);
lean_ctor_set(v___x_953_, 1, v_a_756_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; uint64_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
lean_dec(v___x_951_);
v___x_954_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_955_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_754_);
v___x_956_ = lean_uint64_to_usize(v___x_955_);
lean_inc_ref(v_e_754_);
lean_inc_ref(v_set_950_);
v___x_957_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_950_, v___x_956_, v_e_754_, v___x_954_);
v___x_958_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_957_, v___x_954_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec_ref_known(v_e_754_, 2);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v_a_756_);
return v___x_959_;
}
else
{
lean_object* v___x_960_; 
lean_dec_ref(v___x_957_);
lean_inc_ref(v_expr_948_);
v___x_960_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_948_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_a_962_; size_t v___x_963_; size_t v___x_964_; uint8_t v___x_965_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
v_a_962_ = lean_ctor_get(v___x_960_, 1);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_960_, 2);
v___x_963_ = lean_ptr_addr(v_expr_948_);
v___x_964_ = lean_ptr_addr(v_a_961_);
v___x_965_ = lean_usize_dec_eq(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_inc(v_data_947_);
v___x_966_ = l_Lean_Expr_mdata___override(v_data_947_, v_a_961_);
v___x_967_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_966_, v_a_962_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; 
lean_dec(v_a_961_);
lean_inc_ref(v_e_754_);
v___x_968_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_e_754_, v_a_962_);
return v___x_968_;
}
}
else
{
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_969_; lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_969_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_969_);
v_a_970_ = lean_ctor_get(v___x_960_, 1);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_960_, 2);
v___x_971_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_a_969_, v_a_970_);
return v___x_971_;
}
else
{
lean_dec_ref_known(v_e_754_, 2);
return v___x_960_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_972_; lean_object* v_idx_973_; lean_object* v_struct_974_; lean_object* v_map_975_; lean_object* v_set_976_; lean_object* v___x_977_; 
v_typeName_972_ = lean_ctor_get(v_e_754_, 0);
v_idx_973_ = lean_ctor_get(v_e_754_, 1);
v_struct_974_ = lean_ctor_get(v_e_754_, 2);
v_map_975_ = lean_ctor_get(v_a_756_, 0);
v_set_976_ = lean_ctor_get(v_a_756_, 1);
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_975_, v_e_754_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_979_; 
lean_dec_ref_known(v_e_754_, 3);
v_val_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_val_978_);
lean_ctor_set(v___x_979_, 1, v_a_756_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; uint64_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
lean_dec(v___x_977_);
v___x_980_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_981_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_754_);
v___x_982_ = lean_uint64_to_usize(v___x_981_);
lean_inc_ref(v_e_754_);
lean_inc_ref(v_set_976_);
v___x_983_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_976_, v___x_982_, v_e_754_, v___x_980_);
v___x_984_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_983_, v___x_980_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec_ref_known(v_e_754_, 3);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v_a_756_);
return v___x_985_;
}
else
{
uint8_t v_checkProj_986_; 
lean_dec_ref(v___x_983_);
v_checkProj_986_ = lean_ctor_get_uint8(v_a_755_, sizeof(void*)*1 + 1);
if (v_checkProj_986_ == 0)
{
lean_object* v___x_987_; 
lean_inc_ref(v_struct_974_);
v___x_987_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_974_, v_a_755_, v_a_756_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_a_989_; size_t v___x_990_; size_t v___x_991_; uint8_t v___x_992_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
v_a_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_987_, 2);
v___x_990_ = lean_ptr_addr(v_struct_974_);
v___x_991_ = lean_ptr_addr(v_a_988_);
v___x_992_ = lean_usize_dec_eq(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; 
lean_inc(v_idx_973_);
lean_inc(v_typeName_972_);
v___x_993_ = l_Lean_Expr_proj___override(v_typeName_972_, v_idx_973_, v_a_988_);
v___x_994_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v___x_993_, v_a_989_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; 
lean_dec(v_a_988_);
lean_inc_ref(v_e_754_);
v___x_995_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_e_754_, v_a_989_);
return v___x_995_;
}
}
else
{
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_996_; lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_996_);
v_a_997_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_987_, 2);
v___x_998_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_a_996_, v_a_997_);
return v___x_998_;
}
else
{
lean_dec_ref_known(v_e_754_, 3);
return v___x_987_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec_ref_known(v_e_754_, 3);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v_a_756_);
return v___x_1000_;
}
}
}
}
default: 
{
lean_object* v_map_1001_; lean_object* v_set_1002_; lean_object* v___x_1003_; 
v_map_1001_ = lean_ctor_get(v_a_756_, 0);
v_set_1002_ = lean_ctor_get(v_a_756_, 1);
lean_inc_ref(v_e_754_);
v___x_1003_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1002_, v_e_754_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1013_; 
lean_inc_ref(v_set_1002_);
lean_inc_ref(v_map_1001_);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_756_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; 
v_unused_1014_ = lean_ctor_get(v_a_756_, 1);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_a_756_, 0);
lean_dec(v_unused_1015_);
v___x_1005_ = v_a_756_;
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_a_756_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = lean_box(0);
lean_inc_ref(v_e_754_);
v___x_1008_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1002_, v_e_754_, v___x_1007_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v___x_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_map_1001_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_e_754_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
return v___x_1011_;
}
}
}
else
{
lean_object* v_val_1016_; lean_object* v_fst_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_e_754_);
v_val_1016_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1003_, 1);
v_fst_1017_ = lean_ctor_get(v_val_1016_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_val_1016_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_val_1016_, 1);
lean_dec(v_unused_1025_);
v___x_1019_ = v_val_1016_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_fst_1017_);
lean_dec(v_val_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_756_);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_fst_1017_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_a_756_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
v___jp_757_:
{
if (lean_obj_tag(v___y_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_759_ = lean_ctor_get(v___y_758_, 0);
lean_inc(v_a_759_);
v_a_760_ = lean_ctor_get(v___y_758_, 1);
lean_inc(v_a_760_);
lean_dec_ref_known(v___y_758_, 2);
v___x_761_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_a_759_, v_a_760_);
return v___x_761_;
}
else
{
lean_dec_ref(v_e_754_);
return v___y_758_;
}
}
v___jp_762_:
{
if (lean_obj_tag(v___y_763_) == 0)
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_764_ = lean_ctor_get(v___y_763_, 0);
lean_inc(v_a_764_);
v_a_765_ = lean_ctor_get(v___y_763_, 1);
lean_inc(v_a_765_);
lean_dec_ref_known(v___y_763_, 2);
v___x_766_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_a_764_, v_a_765_);
return v___x_766_;
}
else
{
lean_dec_ref(v_e_754_);
return v___y_763_;
}
}
v___jp_767_:
{
if (lean_obj_tag(v___y_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_769_ = lean_ctor_get(v___y_768_, 0);
lean_inc(v_a_769_);
v_a_770_ = lean_ctor_get(v___y_768_, 1);
lean_inc(v_a_770_);
lean_dec_ref_known(v___y_768_, 2);
v___x_771_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_a_769_, v_a_770_);
return v___x_771_;
}
else
{
lean_dec_ref(v_e_754_);
return v___y_768_;
}
}
v___jp_772_:
{
if (lean_obj_tag(v___y_773_) == 0)
{
lean_object* v_a_774_; lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_774_ = lean_ctor_get(v___y_773_, 0);
lean_inc(v_a_774_);
v_a_775_ = lean_ctor_get(v___y_773_, 1);
lean_inc(v_a_775_);
lean_dec_ref_known(v___y_773_, 2);
v___x_776_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_754_, v_a_774_, v_a_775_);
return v___x_776_;
}
else
{
lean_dec_ref(v_e_754_);
return v___y_773_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1026_, v_a_1027_, v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1031_, v_x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1034_, v_x_1035_, v_x_1036_);
lean_dec_ref(v_x_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1039_, v_a_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1042_, lean_object* v_m_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1042_, v_m_1043_, v_a_1044_);
lean_dec_ref(v_a_1044_);
lean_dec_ref(v_m_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, size_t v_x_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
lean_inc_ref(v_x_1047_);
v___x_1050_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1047_, v_x_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
size_t v_x_11634__boxed_1055_; lean_object* v_res_1056_; 
v_x_11634__boxed_1055_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_res_1056_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1051_, v_x_1052_, v_x_11634__boxed_1055_, v_x_1054_);
lean_dec_ref(v_x_1052_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1057_, lean_object* v_a_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1058_, v_x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1061_, lean_object* v_a_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1061_, v_a_1062_, v_x_1063_);
lean_dec(v_x_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1065_, lean_object* v_keys_1066_, lean_object* v_vals_1067_, lean_object* v_heq_1068_, lean_object* v_i_1069_, lean_object* v_k_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1066_, v_vals_1067_, v_i_1069_, v_k_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_keys_1073_, lean_object* v_vals_1074_, lean_object* v_heq_1075_, lean_object* v_i_1076_, lean_object* v_k_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1072_, v_keys_1073_, v_vals_1074_, v_heq_1075_, v_i_1076_, v_k_1077_);
lean_dec_ref(v_vals_1074_);
lean_dec_ref(v_keys_1073_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1079_, lean_object* v_cache_1080_, lean_object* v_ctx_1081_, lean_object* v_s_1082_){
_start:
{
lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v___f_1083_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1084_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1079_);
v___x_1085_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1083_, v___f_1084_, v_s_1082_, v_e_1079_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_cache_1080_);
lean_ctor_set(v___x_1086_, 1, v_s_1082_);
v___x_1087_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1079_, v_ctx_1081_, v___x_1086_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 1);
v_a_1089_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v___x_1087_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1088_);
lean_inc(v_a_1089_);
lean_dec(v___x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_set_1093_; lean_object* v___x_1095_; 
v_set_1093_ = lean_ctor_get(v_a_1088_, 1);
lean_inc_ref(v_set_1093_);
lean_dec(v_a_1088_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_set_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1089_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_set_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
v_a_1098_ = lean_ctor_get(v___x_1087_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1108_);
v___x_1100_ = v___x_1087_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1087_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_map_1102_; lean_object* v_set_1103_; lean_object* v___x_1105_; 
v_map_1102_ = lean_ctor_get(v_a_1098_, 0);
lean_inc_ref(v_map_1102_);
v_set_1103_ = lean_ctor_get(v_a_1098_, 1);
lean_inc_ref(v_set_1103_);
lean_dec(v_a_1098_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v_set_1103_);
lean_ctor_set(v___x_1100_, 0, v_map_1102_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_map_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_set_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_val_1109_; lean_object* v_fst_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_cache_1080_);
lean_dec_ref(v_e_1079_);
v_val_1109_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v___x_1085_, 1);
v_fst_1110_ = lean_ctor_get(v_val_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_val_1109_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_val_1109_, 1);
lean_dec(v_unused_1118_);
v___x_1112_ = v_val_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_fst_1110_);
lean_dec(v_val_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_s_1082_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_fst_1110_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_s_1082_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1119_, lean_object* v_cache_1120_, lean_object* v_ctx_1121_, lean_object* v_s_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1119_, v_cache_1120_, v_ctx_1121_, v_s_1122_);
lean_dec_ref(v_ctx_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1126_; uint64_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1126_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1127_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1124_);
v___x_1128_ = lean_uint64_to_usize(v___x_1127_);
lean_inc_ref(v_e_1124_);
lean_inc_ref(v_a_1125_);
v___x_1129_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1125_, v___x_1128_, v_e_1124_, v___x_1126_);
v___x_1130_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1129_, v___x_1126_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_e_1124_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v_a_1125_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v___x_1129_);
v___x_1132_ = lean_box(0);
lean_inc_ref(v_e_1124_);
v___x_1133_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1125_, v_e_1124_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_e_1124_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1135_, v_a_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1139_, v_a_1140_, v_a_1141_);
lean_dec_ref(v_a_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1143_, lean_object* v_k_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___f_1147_; lean_object* v___x_1148_; uint64_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___f_1147_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1148_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1149_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1143_);
v___x_1150_ = lean_uint64_to_usize(v___x_1149_);
lean_inc_ref(v_a_1146_);
v___x_1151_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1147_, v_a_1146_, v___x_1150_, v_e_1143_, v___x_1148_);
v___x_1152_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1151_, v___x_1148_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_dec_ref(v_k_1144_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v_a_1146_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; 
lean_dec(v___x_1151_);
lean_inc_ref(v_a_1145_);
v___x_1154_ = lean_apply_2(v_k_1144_, v_a_1145_, v_a_1146_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
v_a_1156_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1154_, 2);
v___x_1157_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1155_, v_a_1156_);
return v___x_1157_;
}
else
{
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1158_, lean_object* v_k_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1158_, v_k_1159_, v_a_1160_, v_a_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_unsigned_to_nat(16u);
v___x_1165_ = lean_mk_array(v___x_1164_, v___x_1163_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___y_1173_; lean_object* v___y_1178_; lean_object* v___y_1183_; lean_object* v___y_1188_; 
switch(lean_obj_tag(v_e_1169_))
{
case 4:
{
lean_object* v_declName_1192_; lean_object* v___x_1193_; uint64_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_declName_1192_ = lean_ctor_get(v_e_1169_, 0);
v___x_1193_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1194_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1169_);
v___x_1195_ = lean_uint64_to_usize(v___x_1194_);
lean_inc_ref(v_e_1169_);
lean_inc_ref(v_a_1171_);
v___x_1196_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1171_, v___x_1195_, v_e_1169_, v___x_1193_);
v___x_1197_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1196_, v___x_1193_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref_known(v_e_1169_, 2);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v_a_1171_);
return v___x_1198_;
}
else
{
uint8_t v___x_1199_; 
lean_dec_ref(v___x_1196_);
lean_inc(v_declName_1192_);
lean_inc_ref(v_a_1170_);
v___x_1199_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1170_, v_declName_1192_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_box(0);
lean_inc_ref(v_e_1169_);
v___x_1201_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1171_, v_e_1169_, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_e_1169_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref_known(v_e_1169_, 2);
v___x_1203_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v_a_1171_);
return v___x_1204_;
}
}
}
case 5:
{
lean_object* v_fn_1205_; lean_object* v_arg_1206_; lean_object* v___x_1207_; uint64_t v___x_1208_; size_t v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_fn_1205_ = lean_ctor_get(v_e_1169_, 0);
v_arg_1206_ = lean_ctor_get(v_e_1169_, 1);
v___x_1207_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1169_);
v___x_1209_ = lean_uint64_to_usize(v___x_1208_);
lean_inc_ref(v_e_1169_);
lean_inc_ref(v_a_1171_);
v___x_1210_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1171_, v___x_1209_, v_e_1169_, v___x_1207_);
v___x_1211_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1210_, v___x_1207_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; 
lean_dec_ref_known(v_e_1169_, 2);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v_a_1171_);
return v___x_1212_;
}
else
{
lean_object* v___x_1213_; 
lean_dec_ref(v___x_1210_);
lean_inc_ref(v_fn_1205_);
v___x_1213_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1205_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
v_a_1215_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1213_, 2);
lean_inc_ref(v_arg_1206_);
v___x_1216_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1206_, v_a_1170_, v_a_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v_a_1218_; uint8_t v___y_1220_; size_t v___x_1224_; size_t v___x_1225_; uint8_t v___x_1226_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
v_a_1218_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1216_, 2);
v___x_1224_ = lean_ptr_addr(v_fn_1205_);
v___x_1225_ = lean_ptr_addr(v_a_1214_);
v___x_1226_ = lean_usize_dec_eq(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
v___y_1220_ = v___x_1226_;
goto v___jp_1219_;
}
else
{
size_t v___x_1227_; size_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1227_ = lean_ptr_addr(v_arg_1206_);
v___x_1228_ = lean_ptr_addr(v_a_1217_);
v___x_1229_ = lean_usize_dec_eq(v___x_1227_, v___x_1228_);
v___y_1220_ = v___x_1229_;
goto v___jp_1219_;
}
v___jp_1219_:
{
if (v___y_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref_known(v_e_1169_, 2);
v___x_1221_ = l_Lean_Expr_app___override(v_a_1214_, v_a_1217_);
v___x_1222_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1221_, v_a_1218_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_a_1217_);
lean_dec(v_a_1214_);
v___x_1223_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1169_, v_a_1218_);
return v___x_1223_;
}
}
}
else
{
lean_dec(v_a_1214_);
lean_dec_ref_known(v_e_1169_, 2);
v___y_1183_ = v___x_1216_;
goto v___jp_1182_;
}
}
else
{
lean_dec_ref_known(v_e_1169_, 2);
v___y_1183_ = v___x_1213_;
goto v___jp_1182_;
}
}
}
case 6:
{
lean_object* v_binderName_1230_; lean_object* v_binderType_1231_; lean_object* v_body_1232_; uint8_t v_binderInfo_1233_; lean_object* v___x_1234_; uint64_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_binderName_1230_ = lean_ctor_get(v_e_1169_, 0);
v_binderType_1231_ = lean_ctor_get(v_e_1169_, 1);
v_body_1232_ = lean_ctor_get(v_e_1169_, 2);
v_binderInfo_1233_ = lean_ctor_get_uint8(v_e_1169_, sizeof(void*)*3 + 8);
v___x_1234_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1235_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1169_);
v___x_1236_ = lean_uint64_to_usize(v___x_1235_);
lean_inc_ref(v_e_1169_);
lean_inc_ref(v_a_1171_);
v___x_1237_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1171_, v___x_1236_, v_e_1169_, v___x_1234_);
v___x_1238_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1237_, v___x_1234_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref_known(v_e_1169_, 3);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v_a_1171_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v___x_1237_);
lean_inc_ref(v_binderType_1231_);
v___x_1240_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1231_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1243_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
v_a_1242_ = lean_ctor_get(v___x_1240_, 1);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1240_, 2);
lean_inc_ref(v_body_1232_);
v___x_1243_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1232_, v_a_1170_, v_a_1242_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v_a_1245_; uint8_t v___y_1247_; size_t v___x_1254_; size_t v___x_1255_; uint8_t v___x_1256_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
v_a_1245_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1243_, 2);
v___x_1254_ = lean_ptr_addr(v_binderType_1231_);
v___x_1255_ = lean_ptr_addr(v_a_1241_);
v___x_1256_ = lean_usize_dec_eq(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
v___y_1247_ = v___x_1256_;
goto v___jp_1246_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = lean_ptr_addr(v_body_1232_);
v___x_1258_ = lean_ptr_addr(v_a_1244_);
v___x_1259_ = lean_usize_dec_eq(v___x_1257_, v___x_1258_);
v___y_1247_ = v___x_1259_;
goto v___jp_1246_;
}
v___jp_1246_:
{
if (v___y_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_inc(v_binderName_1230_);
lean_dec_ref_known(v_e_1169_, 3);
v___x_1248_ = l_Lean_Expr_lam___override(v_binderName_1230_, v_a_1241_, v_a_1244_, v_binderInfo_1233_);
v___x_1249_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1248_, v_a_1245_);
return v___x_1249_;
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1233_, v_binderInfo_1233_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_inc(v_binderName_1230_);
lean_dec_ref_known(v_e_1169_, 3);
v___x_1251_ = l_Lean_Expr_lam___override(v_binderName_1230_, v_a_1241_, v_a_1244_, v_binderInfo_1233_);
v___x_1252_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1251_, v_a_1245_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; 
lean_dec(v_a_1244_);
lean_dec(v_a_1241_);
v___x_1253_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1169_, v_a_1245_);
return v___x_1253_;
}
}
}
}
else
{
lean_dec(v_a_1241_);
lean_dec_ref_known(v_e_1169_, 3);
v___y_1178_ = v___x_1243_;
goto v___jp_1177_;
}
}
else
{
lean_dec_ref_known(v_e_1169_, 3);
v___y_1178_ = v___x_1240_;
goto v___jp_1177_;
}
}
}
case 7:
{
lean_object* v_binderName_1260_; lean_object* v_binderType_1261_; lean_object* v_body_1262_; uint8_t v_binderInfo_1263_; lean_object* v___x_1264_; uint64_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_binderName_1260_ = lean_ctor_get(v_e_1169_, 0);
v_binderType_1261_ = lean_ctor_get(v_e_1169_, 1);
v_body_1262_ = lean_ctor_get(v_e_1169_, 2);
v_binderInfo_1263_ = lean_ctor_get_uint8(v_e_1169_, sizeof(void*)*3 + 8);
v___x_1264_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1265_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1169_);
v___x_1266_ = lean_uint64_to_usize(v___x_1265_);
lean_inc_ref(v_e_1169_);
lean_inc_ref(v_a_1171_);
v___x_1267_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1171_, v___x_1266_, v_e_1169_, v___x_1264_);
v___x_1268_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1267_, v___x_1264_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_dec_ref_known(v_e_1169_, 3);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v_a_1171_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; 
lean_dec_ref(v___x_1267_);
lean_inc_ref(v_binderType_1261_);
v___x_1270_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1261_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
v_a_1272_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1270_, 2);
lean_inc_ref(v_body_1262_);
v___x_1273_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1262_, v_a_1170_, v_a_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v_a_1275_; uint8_t v___y_1277_; size_t v___x_1284_; size_t v___x_1285_; uint8_t v___x_1286_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
v_a_1275_ = lean_ctor_get(v___x_1273_, 1);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1273_, 2);
v___x_1284_ = lean_ptr_addr(v_binderType_1261_);
v___x_1285_ = lean_ptr_addr(v_a_1271_);
v___x_1286_ = lean_usize_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
v___y_1277_ = v___x_1286_;
goto v___jp_1276_;
}
else
{
size_t v___x_1287_; size_t v___x_1288_; uint8_t v___x_1289_; 
v___x_1287_ = lean_ptr_addr(v_body_1262_);
v___x_1288_ = lean_ptr_addr(v_a_1274_);
v___x_1289_ = lean_usize_dec_eq(v___x_1287_, v___x_1288_);
v___y_1277_ = v___x_1289_;
goto v___jp_1276_;
}
v___jp_1276_:
{
if (v___y_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_inc(v_binderName_1260_);
lean_dec_ref_known(v_e_1169_, 3);
v___x_1278_ = l_Lean_Expr_forallE___override(v_binderName_1260_, v_a_1271_, v_a_1274_, v_binderInfo_1263_);
v___x_1279_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1278_, v_a_1275_);
return v___x_1279_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1263_, v_binderInfo_1263_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_inc(v_binderName_1260_);
lean_dec_ref_known(v_e_1169_, 3);
v___x_1281_ = l_Lean_Expr_forallE___override(v_binderName_1260_, v_a_1271_, v_a_1274_, v_binderInfo_1263_);
v___x_1282_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1281_, v_a_1275_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; 
lean_dec(v_a_1274_);
lean_dec(v_a_1271_);
v___x_1283_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1169_, v_a_1275_);
return v___x_1283_;
}
}
}
}
else
{
lean_dec(v_a_1271_);
lean_dec_ref_known(v_e_1169_, 3);
v___y_1188_ = v___x_1273_;
goto v___jp_1187_;
}
}
else
{
lean_dec_ref_known(v_e_1169_, 3);
v___y_1188_ = v___x_1270_;
goto v___jp_1187_;
}
}
}
case 8:
{
lean_object* v_declName_1290_; lean_object* v_type_1291_; lean_object* v_value_1292_; lean_object* v_body_1293_; uint8_t v_nondep_1294_; lean_object* v___x_1295_; uint64_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_declName_1290_ = lean_ctor_get(v_e_1169_, 0);
v_type_1291_ = lean_ctor_get(v_e_1169_, 1);
v_value_1292_ = lean_ctor_get(v_e_1169_, 2);
v_body_1293_ = lean_ctor_get(v_e_1169_, 3);
v_nondep_1294_ = lean_ctor_get_uint8(v_e_1169_, sizeof(void*)*4 + 8);
v___x_1295_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1169_);
v___x_1297_ = lean_uint64_to_usize(v___x_1296_);
lean_inc_ref(v_e_1169_);
lean_inc_ref(v_a_1171_);
v___x_1298_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1171_, v___x_1297_, v_e_1169_, v___x_1295_);
v___x_1299_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1298_, v___x_1295_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
lean_dec_ref_known(v_e_1169_, 4);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v_a_1171_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; 
lean_dec_ref(v___x_1298_);
lean_inc_ref(v_type_1291_);
v___x_1301_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1291_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
v_a_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1301_, 2);
lean_inc_ref(v_value_1292_);
v___x_1304_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1292_, v_a_1170_, v_a_1303_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v_a_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
v_a_1306_ = lean_ctor_get(v___x_1304_, 1);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1304_, 2);
lean_inc_ref(v_body_1293_);
v___x_1307_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1293_, v_a_1170_, v_a_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v_a_1309_; uint8_t v___y_1311_; size_t v___x_1320_; size_t v___x_1321_; uint8_t v___x_1322_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
v_a_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1307_, 2);
v___x_1320_ = lean_ptr_addr(v_type_1291_);
v___x_1321_ = lean_ptr_addr(v_a_1302_);
v___x_1322_ = lean_usize_dec_eq(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
v___y_1311_ = v___x_1322_;
goto v___jp_1310_;
}
else
{
size_t v___x_1323_; size_t v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_ptr_addr(v_value_1292_);
v___x_1324_ = lean_ptr_addr(v_a_1305_);
v___x_1325_ = lean_usize_dec_eq(v___x_1323_, v___x_1324_);
v___y_1311_ = v___x_1325_;
goto v___jp_1310_;
}
v___jp_1310_:
{
if (v___y_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_inc(v_declName_1290_);
lean_dec_ref_known(v_e_1169_, 4);
v___x_1312_ = l_Lean_Expr_letE___override(v_declName_1290_, v_a_1302_, v_a_1305_, v_a_1308_, v_nondep_1294_);
v___x_1313_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1312_, v_a_1309_);
return v___x_1313_;
}
else
{
size_t v___x_1314_; size_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_ptr_addr(v_body_1293_);
v___x_1315_ = lean_ptr_addr(v_a_1308_);
v___x_1316_ = lean_usize_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_inc(v_declName_1290_);
lean_dec_ref_known(v_e_1169_, 4);
v___x_1317_ = l_Lean_Expr_letE___override(v_declName_1290_, v_a_1302_, v_a_1305_, v_a_1308_, v_nondep_1294_);
v___x_1318_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1317_, v_a_1309_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; 
lean_dec(v_a_1308_);
lean_dec(v_a_1305_);
lean_dec(v_a_1302_);
v___x_1319_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1169_, v_a_1309_);
return v___x_1319_;
}
}
}
}
else
{
lean_dec(v_a_1305_);
lean_dec(v_a_1302_);
lean_dec_ref_known(v_e_1169_, 4);
v___y_1173_ = v___x_1307_;
goto v___jp_1172_;
}
}
else
{
lean_dec(v_a_1302_);
lean_dec_ref_known(v_e_1169_, 4);
v___y_1173_ = v___x_1304_;
goto v___jp_1172_;
}
}
else
{
lean_dec_ref_known(v_e_1169_, 4);
v___y_1173_ = v___x_1301_;
goto v___jp_1172_;
}
}
}
case 10:
{
lean_object* v_data_1326_; lean_object* v_expr_1327_; lean_object* v___x_1328_; uint64_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_data_1326_ = lean_ctor_get(v_e_1169_, 0);
v_expr_1327_ = lean_ctor_get(v_e_1169_, 1);
v___x_1328_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1329_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1169_);
v___x_1330_ = lean_uint64_to_usize(v___x_1329_);
lean_inc_ref(v_e_1169_);
lean_inc_ref(v_a_1171_);
v___x_1331_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1171_, v___x_1330_, v_e_1169_, v___x_1328_);
v___x_1332_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1331_, v___x_1328_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref_known(v_e_1169_, 2);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v_a_1171_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; 
lean_dec_ref(v___x_1331_);
lean_inc_ref(v_expr_1327_);
v___x_1334_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1327_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v_a_1336_; size_t v___x_1337_; size_t v___x_1338_; uint8_t v___x_1339_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
v_a_1336_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1334_, 2);
v___x_1337_ = lean_ptr_addr(v_expr_1327_);
v___x_1338_ = lean_ptr_addr(v_a_1335_);
v___x_1339_ = lean_usize_dec_eq(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_inc(v_data_1326_);
lean_dec_ref_known(v_e_1169_, 2);
v___x_1340_ = l_Lean_Expr_mdata___override(v_data_1326_, v_a_1335_);
v___x_1341_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1340_, v_a_1336_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; 
lean_dec(v_a_1335_);
v___x_1342_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1169_, v_a_1336_);
return v___x_1342_;
}
}
else
{
lean_dec_ref_known(v_e_1169_, 2);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1343_; lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1343_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1343_);
v_a_1344_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1334_, 2);
v___x_1345_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1343_, v_a_1344_);
return v___x_1345_;
}
else
{
return v___x_1334_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1346_; lean_object* v_idx_1347_; lean_object* v_struct_1348_; lean_object* v___x_1349_; uint64_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_typeName_1346_ = lean_ctor_get(v_e_1169_, 0);
v_idx_1347_ = lean_ctor_get(v_e_1169_, 1);
v_struct_1348_ = lean_ctor_get(v_e_1169_, 2);
v___x_1349_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1350_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1169_);
v___x_1351_ = lean_uint64_to_usize(v___x_1350_);
lean_inc_ref(v_e_1169_);
lean_inc_ref(v_a_1171_);
v___x_1352_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1171_, v___x_1351_, v_e_1169_, v___x_1349_);
v___x_1353_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1352_, v___x_1349_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref_known(v_e_1169_, 3);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v_a_1171_);
return v___x_1354_;
}
else
{
uint8_t v_checkProj_1355_; 
lean_dec_ref(v___x_1352_);
v_checkProj_1355_ = lean_ctor_get_uint8(v_a_1170_, sizeof(void*)*1 + 1);
if (v_checkProj_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_inc_ref(v_struct_1348_);
v___x_1356_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1348_, v_a_1170_, v_a_1171_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v_a_1358_; size_t v___x_1359_; size_t v___x_1360_; uint8_t v___x_1361_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
v_a_1358_ = lean_ctor_get(v___x_1356_, 1);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1356_, 2);
v___x_1359_ = lean_ptr_addr(v_struct_1348_);
v___x_1360_ = lean_ptr_addr(v_a_1357_);
v___x_1361_ = lean_usize_dec_eq(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_inc(v_idx_1347_);
lean_inc(v_typeName_1346_);
lean_dec_ref_known(v_e_1169_, 3);
v___x_1362_ = l_Lean_Expr_proj___override(v_typeName_1346_, v_idx_1347_, v_a_1357_);
v___x_1363_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1362_, v_a_1358_);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_a_1357_);
v___x_1364_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1169_, v_a_1358_);
return v___x_1364_;
}
}
else
{
lean_dec_ref_known(v_e_1169_, 3);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1365_; lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1365_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1365_);
v_a_1366_ = lean_ctor_get(v___x_1356_, 1);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1356_, 2);
v___x_1367_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1365_, v_a_1366_);
return v___x_1367_;
}
else
{
return v___x_1356_;
}
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref_known(v_e_1169_, 3);
v___x_1368_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v_a_1171_);
return v___x_1369_;
}
}
}
default: 
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1169_, v_a_1171_);
return v___x_1370_;
}
}
v___jp_1172_:
{
if (lean_obj_tag(v___y_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v_a_1175_; lean_object* v___x_1176_; 
v_a_1174_ = lean_ctor_get(v___y_1173_, 0);
lean_inc(v_a_1174_);
v_a_1175_ = lean_ctor_get(v___y_1173_, 1);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___y_1173_, 2);
v___x_1176_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1174_, v_a_1175_);
return v___x_1176_;
}
else
{
return v___y_1173_;
}
}
v___jp_1177_:
{
if (lean_obj_tag(v___y_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v_a_1180_; lean_object* v___x_1181_; 
v_a_1179_ = lean_ctor_get(v___y_1178_, 0);
lean_inc(v_a_1179_);
v_a_1180_ = lean_ctor_get(v___y_1178_, 1);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___y_1178_, 2);
v___x_1181_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1179_, v_a_1180_);
return v___x_1181_;
}
else
{
return v___y_1178_;
}
}
v___jp_1182_:
{
if (lean_obj_tag(v___y_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v_a_1185_; lean_object* v___x_1186_; 
v_a_1184_ = lean_ctor_get(v___y_1183_, 0);
lean_inc(v_a_1184_);
v_a_1185_ = lean_ctor_get(v___y_1183_, 1);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___y_1183_, 2);
v___x_1186_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1184_, v_a_1185_);
return v___x_1186_;
}
else
{
return v___y_1183_;
}
}
v___jp_1187_:
{
if (lean_obj_tag(v___y_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v_a_1190_; lean_object* v___x_1191_; 
v_a_1189_ = lean_ctor_get(v___y_1188_, 0);
lean_inc(v_a_1189_);
v_a_1190_ = lean_ctor_get(v___y_1188_, 1);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___y_1188_, 2);
v___x_1191_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1189_, v_a_1190_);
return v___x_1191_;
}
else
{
return v___y_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1371_, v_a_1372_, v_a_1373_);
lean_dec_ref(v_a_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1375_, v_a_1376_, v_a_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1379_, v_a_1380_, v_a_1381_);
lean_dec_ref(v_a_1380_);
return v_res_1382_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReducibilityAttrs(uint8_t builtin);
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReducibilityAttrs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ProjFns(builtin);
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
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_ReducibilityAttrs(uint8_t builtin);
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReducibilityAttrs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin);
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

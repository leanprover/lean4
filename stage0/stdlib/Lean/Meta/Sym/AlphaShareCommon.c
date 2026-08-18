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
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "EqMatch"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 191, 100, 49, 216, 68, 143, 22)}};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchCond"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__6_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 187, 249, 156, 65, 204, 232)}};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__7_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2;
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
size_t v___x_7_; size_t v___x_8_; size_t v___x_9_; uint64_t v___x_10_; 
v___x_7_ = lean_ptr_addr(v_e_1_);
v___x_8_ = ((size_t)3ULL);
v___x_9_ = lean_usize_shift_right(v___x_7_, v___x_8_);
v___x_10_ = lean_usize_to_uint64(v___x_9_);
return v___x_10_;
}
case 6:
{
goto v___jp_2_;
}
case 7:
{
goto v___jp_2_;
}
case 8:
{
size_t v___x_11_; size_t v___x_12_; size_t v___x_13_; uint64_t v___x_14_; 
v___x_11_ = lean_ptr_addr(v_e_1_);
v___x_12_ = ((size_t)3ULL);
v___x_13_ = lean_usize_shift_right(v___x_11_, v___x_12_);
v___x_14_ = lean_usize_to_uint64(v___x_13_);
return v___x_14_;
}
case 10:
{
size_t v___x_15_; size_t v___x_16_; size_t v___x_17_; uint64_t v___x_18_; 
v___x_15_ = lean_ptr_addr(v_e_1_);
v___x_16_ = ((size_t)3ULL);
v___x_17_ = lean_usize_shift_right(v___x_15_, v___x_16_);
v___x_18_ = lean_usize_to_uint64(v___x_17_);
return v___x_18_;
}
case 11:
{
size_t v___x_19_; size_t v___x_20_; size_t v___x_21_; uint64_t v___x_22_; 
v___x_19_ = lean_ptr_addr(v_e_1_);
v___x_20_ = ((size_t)3ULL);
v___x_21_ = lean_usize_shift_right(v___x_19_, v___x_20_);
v___x_22_ = lean_usize_to_uint64(v___x_21_);
return v___x_22_;
}
default: 
{
uint64_t v___x_23_; 
v___x_23_ = l_Lean_Expr_hash(v_e_1_);
return v___x_23_;
}
}
v___jp_2_:
{
size_t v___x_3_; size_t v___x_4_; size_t v___x_5_; uint64_t v___x_6_; 
v___x_3_ = lean_ptr_addr(v_e_1_);
v___x_4_ = ((size_t)3ULL);
v___x_5_ = lean_usize_shift_right(v___x_3_, v___x_4_);
v___x_6_ = lean_usize_to_uint64(v___x_5_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(lean_object* v_e_24_){
_start:
{
uint64_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_e_24_);
lean_dec_ref(v_e_24_);
v_r_26_ = lean_box_uint64(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object* v_e_27_){
_start:
{
lean_object* v_d_29_; lean_object* v_b_30_; 
switch(lean_obj_tag(v_e_27_))
{
case 5:
{
lean_object* v_fn_34_; lean_object* v_arg_35_; uint64_t v___x_36_; uint64_t v___x_37_; uint64_t v___x_38_; 
v_fn_34_ = lean_ctor_get(v_e_27_, 0);
v_arg_35_ = lean_ctor_get(v_e_27_, 1);
v___x_36_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_fn_34_);
v___x_37_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_arg_35_);
v___x_38_ = lean_uint64_mix_hash(v___x_36_, v___x_37_);
return v___x_38_;
}
case 6:
{
lean_object* v_binderType_39_; lean_object* v_body_40_; 
v_binderType_39_ = lean_ctor_get(v_e_27_, 1);
v_body_40_ = lean_ctor_get(v_e_27_, 2);
v_d_29_ = v_binderType_39_;
v_b_30_ = v_body_40_;
goto v___jp_28_;
}
case 7:
{
lean_object* v_binderType_41_; lean_object* v_body_42_; 
v_binderType_41_ = lean_ctor_get(v_e_27_, 1);
v_body_42_ = lean_ctor_get(v_e_27_, 2);
v_d_29_ = v_binderType_41_;
v_b_30_ = v_body_42_;
goto v___jp_28_;
}
case 8:
{
lean_object* v_value_43_; lean_object* v_body_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; 
v_value_43_ = lean_ctor_get(v_e_27_, 2);
v_body_44_ = lean_ctor_get(v_e_27_, 3);
v___x_45_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_value_43_);
v___x_46_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_body_44_);
v___x_47_ = lean_uint64_mix_hash(v___x_45_, v___x_46_);
return v___x_47_;
}
case 10:
{
lean_object* v_expr_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; 
v_expr_48_ = lean_ctor_get(v_e_27_, 1);
v___x_49_ = 13ULL;
v___x_50_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_expr_48_);
v___x_51_ = lean_uint64_mix_hash(v___x_49_, v___x_50_);
return v___x_51_;
}
case 11:
{
lean_object* v_typeName_52_; lean_object* v_idx_53_; lean_object* v_struct_54_; uint64_t v___y_56_; 
v_typeName_52_ = lean_ctor_get(v_e_27_, 0);
v_idx_53_ = lean_ctor_get(v_e_27_, 1);
v_struct_54_ = lean_ctor_get(v_e_27_, 2);
if (lean_obj_tag(v_typeName_52_) == 0)
{
uint64_t v___x_61_; 
v___x_61_ = 1723ULL;
v___y_56_ = v___x_61_;
goto v___jp_55_;
}
else
{
uint64_t v_hash_62_; 
v_hash_62_ = lean_ctor_get_uint64(v_typeName_52_, sizeof(void*)*2);
v___y_56_ = v_hash_62_;
goto v___jp_55_;
}
v___jp_55_:
{
uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; 
v___x_57_ = lean_uint64_of_nat(v_idx_53_);
v___x_58_ = lean_uint64_mix_hash(v___y_56_, v___x_57_);
v___x_59_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_struct_54_);
v___x_60_ = lean_uint64_mix_hash(v___x_58_, v___x_59_);
return v___x_60_;
}
}
default: 
{
uint64_t v___x_63_; 
v___x_63_ = l_Lean_Expr_hash(v_e_27_);
return v___x_63_;
}
}
v___jp_28_:
{
uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v___x_33_; 
v___x_31_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_d_29_);
v___x_32_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_b_30_);
v___x_33_ = lean_uint64_mix_hash(v___x_31_, v___x_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object* v_e_64_){
_start:
{
uint64_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_64_);
lean_dec_ref(v_e_64_);
v_r_66_ = lean_box_uint64(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object* v_e_u2081_67_, lean_object* v_e_u2082_68_){
_start:
{
switch(lean_obj_tag(v_e_u2081_67_))
{
case 5:
{
if (lean_obj_tag(v_e_u2082_68_) == 5)
{
lean_object* v_fn_69_; lean_object* v_arg_70_; lean_object* v_fn_71_; lean_object* v_arg_72_; size_t v___x_73_; size_t v___x_74_; uint8_t v___x_75_; 
v_fn_69_ = lean_ctor_get(v_e_u2081_67_, 0);
v_arg_70_ = lean_ctor_get(v_e_u2081_67_, 1);
v_fn_71_ = lean_ctor_get(v_e_u2082_68_, 0);
v_arg_72_ = lean_ctor_get(v_e_u2082_68_, 1);
v___x_73_ = lean_ptr_addr(v_fn_69_);
v___x_74_ = lean_ptr_addr(v_fn_71_);
v___x_75_ = lean_usize_dec_eq(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
return v___x_75_;
}
else
{
size_t v___x_76_; size_t v___x_77_; uint8_t v___x_78_; 
v___x_76_ = lean_ptr_addr(v_arg_70_);
v___x_77_ = lean_ptr_addr(v_arg_72_);
v___x_78_ = lean_usize_dec_eq(v___x_76_, v___x_77_);
return v___x_78_;
}
}
else
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_68_) == 6)
{
lean_object* v_binderType_80_; lean_object* v_body_81_; lean_object* v_binderType_82_; lean_object* v_body_83_; size_t v___x_84_; size_t v___x_85_; uint8_t v___x_86_; 
v_binderType_80_ = lean_ctor_get(v_e_u2081_67_, 1);
v_body_81_ = lean_ctor_get(v_e_u2081_67_, 2);
v_binderType_82_ = lean_ctor_get(v_e_u2082_68_, 1);
v_body_83_ = lean_ctor_get(v_e_u2082_68_, 2);
v___x_84_ = lean_ptr_addr(v_binderType_80_);
v___x_85_ = lean_ptr_addr(v_binderType_82_);
v___x_86_ = lean_usize_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
return v___x_86_;
}
else
{
size_t v___x_87_; size_t v___x_88_; uint8_t v___x_89_; 
v___x_87_ = lean_ptr_addr(v_body_81_);
v___x_88_ = lean_ptr_addr(v_body_83_);
v___x_89_ = lean_usize_dec_eq(v___x_87_, v___x_88_);
return v___x_89_;
}
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_68_) == 7)
{
lean_object* v_binderType_91_; lean_object* v_body_92_; lean_object* v_binderType_93_; lean_object* v_body_94_; size_t v___x_95_; size_t v___x_96_; uint8_t v___x_97_; 
v_binderType_91_ = lean_ctor_get(v_e_u2081_67_, 1);
v_body_92_ = lean_ctor_get(v_e_u2081_67_, 2);
v_binderType_93_ = lean_ctor_get(v_e_u2082_68_, 1);
v_body_94_ = lean_ctor_get(v_e_u2082_68_, 2);
v___x_95_ = lean_ptr_addr(v_binderType_91_);
v___x_96_ = lean_ptr_addr(v_binderType_93_);
v___x_97_ = lean_usize_dec_eq(v___x_95_, v___x_96_);
if (v___x_97_ == 0)
{
return v___x_97_;
}
else
{
size_t v___x_98_; size_t v___x_99_; uint8_t v___x_100_; 
v___x_98_ = lean_ptr_addr(v_body_92_);
v___x_99_ = lean_ptr_addr(v_body_94_);
v___x_100_ = lean_usize_dec_eq(v___x_98_, v___x_99_);
return v___x_100_;
}
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_68_) == 8)
{
lean_object* v_value_102_; lean_object* v_body_103_; lean_object* v_value_104_; lean_object* v_body_105_; size_t v___x_106_; size_t v___x_107_; uint8_t v___x_108_; 
v_value_102_ = lean_ctor_get(v_e_u2081_67_, 2);
v_body_103_ = lean_ctor_get(v_e_u2081_67_, 3);
v_value_104_ = lean_ctor_get(v_e_u2082_68_, 2);
v_body_105_ = lean_ctor_get(v_e_u2082_68_, 3);
v___x_106_ = lean_ptr_addr(v_value_102_);
v___x_107_ = lean_ptr_addr(v_value_104_);
v___x_108_ = lean_usize_dec_eq(v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
return v___x_108_;
}
else
{
size_t v___x_109_; size_t v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_ptr_addr(v_body_103_);
v___x_110_ = lean_ptr_addr(v_body_105_);
v___x_111_ = lean_usize_dec_eq(v___x_109_, v___x_110_);
return v___x_111_;
}
}
else
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_68_) == 10)
{
lean_object* v_data_113_; lean_object* v_expr_114_; lean_object* v_data_115_; lean_object* v_expr_116_; size_t v___x_117_; size_t v___x_118_; uint8_t v___x_119_; 
v_data_113_ = lean_ctor_get(v_e_u2081_67_, 0);
v_expr_114_ = lean_ctor_get(v_e_u2081_67_, 1);
v_data_115_ = lean_ctor_get(v_e_u2082_68_, 0);
v_expr_116_ = lean_ctor_get(v_e_u2082_68_, 1);
v___x_117_ = lean_ptr_addr(v_expr_114_);
v___x_118_ = lean_ptr_addr(v_expr_116_);
v___x_119_ = lean_usize_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = l_Lean_KVMap_eqv(v_data_113_, v_data_115_);
return v___x_120_;
}
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_68_) == 11)
{
lean_object* v_typeName_122_; lean_object* v_idx_123_; lean_object* v_struct_124_; lean_object* v_typeName_125_; lean_object* v_idx_126_; lean_object* v_struct_127_; uint8_t v___y_129_; uint8_t v___x_133_; 
v_typeName_122_ = lean_ctor_get(v_e_u2081_67_, 0);
v_idx_123_ = lean_ctor_get(v_e_u2081_67_, 1);
v_struct_124_ = lean_ctor_get(v_e_u2081_67_, 2);
v_typeName_125_ = lean_ctor_get(v_e_u2082_68_, 0);
v_idx_126_ = lean_ctor_get(v_e_u2082_68_, 1);
v_struct_127_ = lean_ctor_get(v_e_u2082_68_, 2);
v___x_133_ = lean_name_eq(v_typeName_122_, v_typeName_125_);
if (v___x_133_ == 0)
{
v___y_129_ = v___x_133_;
goto v___jp_128_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_eq(v_idx_123_, v_idx_126_);
v___y_129_ = v___x_134_;
goto v___jp_128_;
}
v___jp_128_:
{
if (v___y_129_ == 0)
{
return v___y_129_;
}
else
{
size_t v___x_130_; size_t v___x_131_; uint8_t v___x_132_; 
v___x_130_ = lean_ptr_addr(v_struct_124_);
v___x_131_ = lean_ptr_addr(v_struct_127_);
v___x_132_ = lean_usize_dec_eq(v___x_130_, v___x_131_);
return v___x_132_;
}
}
}
else
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
}
default: 
{
uint8_t v___x_136_; 
v___x_136_ = lean_expr_eqv(v_e_u2081_67_, v_e_u2082_68_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object* v_e_u2081_137_, lean_object* v_e_u2082_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_e_u2081_137_, v_e_u2082_138_);
lean_dec_ref(v_e_u2082_138_);
lean_dec_ref(v_e_u2081_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_158_){
_start:
{
uint8_t v___y_160_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__5));
v___x_164_ = lean_name_eq(v_declName_158_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__7));
v___x_166_ = lean_name_eq(v_declName_158_, v___x_165_);
v___y_160_ = v___x_166_;
goto v___jp_159_;
}
else
{
v___y_160_ = v___x_164_;
goto v___jp_159_;
}
v___jp_159_:
{
if (v___y_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_162_ = lean_name_eq(v_declName_158_, v___x_161_);
return v___x_162_;
}
else
{
return v___y_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_167_);
lean_dec(v_declName_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object* v_env_170_, lean_object* v_declName_171_){
_start:
{
uint8_t v___x_172_; 
lean_inc(v_declName_171_);
lean_inc_ref(v_env_170_);
v___x_172_ = l_Lean_getReducibilityStatusCore(v_env_170_, v_declName_171_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
v___x_173_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_171_);
if (v___x_173_ == 0)
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_Environment_isProjectionFn(v_env_170_, v_declName_171_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; 
v___x_175_ = 1;
return v___x_175_;
}
else
{
return v___x_173_;
}
}
else
{
uint8_t v___x_176_; 
lean_dec(v_declName_171_);
lean_dec_ref(v_env_170_);
v___x_176_ = 0;
return v___x_176_;
}
}
else
{
uint8_t v___x_177_; 
lean_dec(v_declName_171_);
lean_dec_ref(v_env_170_);
v___x_177_ = 0;
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object* v_env_178_, lean_object* v_declName_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_178_, v_declName_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_182_){
_start:
{
uint64_t v___x_183_; 
v___x_183_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_184_){
_start:
{
uint64_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_184_);
lean_dec_ref(v_k_184_);
v_r_186_ = lean_box_uint64(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_189_, lean_object* v_k_u2082_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_189_, v_k_u2082_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_192_, lean_object* v_k_u2082_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_192_, v_k_u2082_193_);
lean_dec_ref(v_k_u2082_193_);
lean_dec_ref(v_k_u2081_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object* v_ctx_198_, lean_object* v_declName_199_){
_start:
{
uint8_t v_checkReducible_200_; 
v_checkReducible_200_ = lean_ctor_get_uint8(v_ctx_198_, sizeof(void*)*1);
if (v_checkReducible_200_ == 0)
{
lean_dec(v_declName_199_);
lean_dec_ref(v_ctx_198_);
return v_checkReducible_200_;
}
else
{
lean_object* v_env_201_; uint8_t v___x_202_; 
v_env_201_ = lean_ctor_get(v_ctx_198_, 0);
lean_inc_ref(v_env_201_);
lean_dec_ref(v_ctx_198_);
v___x_202_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_201_, v_declName_199_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object* v_ctx_203_, lean_object* v_declName_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_203_, v_declName_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_box(0);
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_212_ = l_Lean_mkConst(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_214_, lean_object* v_i_215_, lean_object* v_k_216_, lean_object* v_k_u2080_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_array_get_size(v_keys_214_);
v___x_219_ = lean_nat_dec_lt(v_i_215_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec(v_i_215_);
lean_inc_ref(v_k_u2080_217_);
return v_k_u2080_217_;
}
else
{
lean_object* v_k_x27_220_; uint8_t v___x_221_; 
v_k_x27_220_ = lean_array_fget_borrowed(v_keys_214_, v_i_215_);
v___x_221_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_216_, v_k_x27_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_i_215_, v___x_222_);
lean_dec(v_i_215_);
v_i_215_ = v___x_223_;
goto _start;
}
else
{
lean_dec(v_i_215_);
lean_inc(v_k_x27_220_);
return v_k_x27_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_225_, lean_object* v_i_226_, lean_object* v_k_227_, lean_object* v_k_u2080_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_225_, v_i_226_, v_k_227_, v_k_u2080_228_);
lean_dec_ref(v_k_u2080_228_);
lean_dec_ref(v_k_227_);
lean_dec_ref(v_keys_225_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_230_, size_t v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v_es_234_; lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; lean_object* v_j_238_; lean_object* v___x_239_; 
v_es_234_ = lean_ctor_get(v_x_230_, 0);
v___x_235_ = lean_box(2);
v___x_236_ = ((size_t)31ULL);
v___x_237_ = lean_usize_land(v_x_231_, v___x_236_);
v_j_238_ = lean_usize_to_nat(v___x_237_);
v___x_239_ = lean_array_get_borrowed(v___x_235_, v_es_234_, v_j_238_);
lean_dec(v_j_238_);
switch(lean_obj_tag(v___x_239_))
{
case 0:
{
lean_object* v_key_240_; uint8_t v___x_241_; 
v_key_240_ = lean_ctor_get(v___x_239_, 0);
v___x_241_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_232_, v_key_240_);
if (v___x_241_ == 0)
{
lean_inc_ref(v_x_233_);
return v_x_233_;
}
else
{
lean_inc(v_key_240_);
return v_key_240_;
}
}
case 1:
{
lean_object* v_node_242_; size_t v___x_243_; size_t v___x_244_; 
v_node_242_ = lean_ctor_get(v___x_239_, 0);
v___x_243_ = ((size_t)5ULL);
v___x_244_ = lean_usize_shift_right(v_x_231_, v___x_243_);
v_x_230_ = v_node_242_;
v_x_231_ = v___x_244_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_233_);
return v_x_233_;
}
}
}
else
{
lean_object* v_ks_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_ks_246_ = lean_ctor_get(v_x_230_, 0);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_246_, v___x_247_, v_x_232_, v_x_233_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
size_t v_x_5449__boxed_253_; lean_object* v_res_254_; 
v_x_5449__boxed_253_ = lean_unbox_usize(v_x_250_);
lean_dec(v_x_250_);
v_res_254_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_249_, v_x_5449__boxed_253_, v_x_251_, v_x_252_);
lean_dec_ref(v_x_252_);
lean_dec_ref(v_x_251_);
lean_dec_ref(v_x_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_m_255_, lean_object* v_query_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_zero_260_; uint8_t v_isZero_261_; 
v_zero_260_ = lean_unsigned_to_nat(0u);
v_isZero_261_ = lean_nat_dec_eq(v_x_258_, v_zero_260_);
if (v_isZero_261_ == 1)
{
lean_dec(v_x_259_);
lean_dec(v_x_258_);
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_box(2);
return v___x_262_;
}
else
{
lean_object* v_val_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_val_263_ = lean_ctor_get(v_x_257_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v_x_257_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_val_263_);
lean_dec(v_x_257_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_val_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_keyArray_271_; lean_object* v_valueArray_272_; lean_object* v___x_273_; uint8_t v_isSome_274_; 
v_keyArray_271_ = lean_ctor_get(v_m_255_, 1);
v_valueArray_272_ = lean_ctor_get(v_m_255_, 2);
v___x_273_ = lean_array_fget_borrowed(v_keyArray_271_, v_x_259_);
v_isSome_274_ = lean_noption_is_some(v___x_273_);
if (v_isSome_274_ == 0)
{
lean_dec(v_x_258_);
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_x_259_);
return v___x_275_;
}
else
{
lean_object* v_val_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_x_259_);
v_val_276_ = lean_ctor_get(v_x_257_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v_x_257_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_val_276_);
lean_dec(v_x_257_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_val_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v_one_284_; lean_object* v_n_285_; lean_object* v___y_287_; 
v_one_284_ = lean_unsigned_to_nat(1u);
v_n_285_ = lean_nat_sub(v_x_258_, v_one_284_);
lean_dec(v_x_258_);
if (v_isSome_274_ == 0)
{
goto v___jp_293_;
}
else
{
lean_object* v___x_295_; uint8_t v_isSome_296_; 
v___x_295_ = lean_array_fget_borrowed(v_valueArray_272_, v_x_259_);
v_isSome_296_ = lean_noption_is_some(v___x_295_);
if (v_isSome_296_ == 0)
{
goto v___jp_293_;
}
else
{
lean_object* v_val_297_; size_t v___x_298_; size_t v___x_299_; uint8_t v___x_300_; 
lean_inc(v___x_273_);
v_val_297_ = lean_noption_get(v___x_273_);
v___x_298_ = lean_ptr_addr(v_val_297_);
v___x_299_ = lean_ptr_addr(v_query_256_);
v___x_300_ = lean_usize_dec_eq(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
lean_dec(v_val_297_);
v___x_301_ = lean_array_get_size(v_keyArray_271_);
v___x_302_ = lean_nat_add(v_x_259_, v_one_284_);
lean_dec(v_x_259_);
v___x_303_ = lean_nat_dec_lt(v___x_302_, v___x_301_);
if (v___x_303_ == 0)
{
lean_dec(v___x_302_);
v_x_258_ = v_n_285_;
v_x_259_ = v_zero_260_;
goto _start;
}
else
{
v_x_258_ = v_n_285_;
v_x_259_ = v___x_302_;
goto _start;
}
}
else
{
lean_object* v_val_306_; lean_object* v___x_307_; 
lean_dec(v_n_285_);
lean_dec(v_x_257_);
lean_inc(v___x_295_);
v_val_306_ = lean_noption_get(v___x_295_);
v___x_307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_307_, 0, v_x_259_);
lean_ctor_set(v___x_307_, 1, v_val_297_);
lean_ctor_set(v___x_307_, 2, v_val_306_);
return v___x_307_;
}
}
}
v___jp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_array_get_size(v_keyArray_271_);
v___x_289_ = lean_nat_add(v_x_259_, v_one_284_);
lean_dec(v_x_259_);
v___x_290_ = lean_nat_dec_lt(v___x_289_, v___x_288_);
if (v___x_290_ == 0)
{
lean_dec(v___x_289_);
v_x_257_ = v___y_287_;
v_x_258_ = v_n_285_;
v_x_259_ = v_zero_260_;
goto _start;
}
else
{
v_x_257_ = v___y_287_;
v_x_258_ = v_n_285_;
v_x_259_ = v___x_289_;
goto _start;
}
}
v___jp_293_:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v___x_294_; 
lean_inc(v_x_259_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_x_259_);
v___y_287_ = v___x_294_;
goto v___jp_286_;
}
else
{
v___y_287_ = v_x_257_;
goto v___jp_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_m_308_, lean_object* v_query_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_m_308_, v_query_309_, v_x_310_, v_x_311_, v_x_312_);
lean_dec_ref(v_query_309_);
lean_dec_ref(v_m_308_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_314_, lean_object* v_query_315_){
_start:
{
lean_object* v_keyArray_316_; lean_object* v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v_fold_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_keyArray_316_ = lean_ctor_get(v_m_314_, 1);
v___x_317_ = lean_array_get_size(v_keyArray_316_);
v___x_318_ = lean_ptr_addr(v_query_315_);
v___x_319_ = ((size_t)3ULL);
v___x_320_ = lean_usize_shift_right(v___x_318_, v___x_319_);
v___x_321_ = lean_usize_to_uint64(v___x_320_);
v___x_322_ = 32ULL;
v___x_323_ = lean_uint64_shift_right(v___x_321_, v___x_322_);
v_fold_324_ = lean_uint64_xor(v___x_321_, v___x_323_);
v___x_325_ = 16ULL;
v___x_326_ = lean_uint64_shift_right(v_fold_324_, v___x_325_);
v___x_327_ = lean_uint64_xor(v_fold_324_, v___x_326_);
v___x_328_ = lean_uint64_to_usize(v___x_327_);
v___x_329_ = lean_usize_of_nat(v___x_317_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_sub(v___x_329_, v___x_330_);
v___x_332_ = lean_usize_land(v___x_328_, v___x_331_);
v___x_333_ = lean_usize_to_nat(v___x_332_);
v___x_334_ = lean_box(0);
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_m_314_, v_query_315_, v___x_334_, v___x_317_, v___x_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg___boxed(lean_object* v_m_336_, lean_object* v_query_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_336_, v_query_337_);
lean_dec_ref(v_query_337_);
lean_dec_ref(v_m_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8_spec__9___redArg(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_ks_343_; lean_object* v_vs_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_368_; 
v_ks_343_ = lean_ctor_get(v_x_339_, 0);
v_vs_344_ = lean_ctor_get(v_x_339_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_x_339_);
if (v_isSharedCheck_368_ == 0)
{
v___x_346_ = v_x_339_;
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_vs_344_);
lean_inc(v_ks_343_);
lean_dec(v_x_339_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_368_;
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
lean_object* v_k_x27_355_; uint8_t v___x_356_; 
v_k_x27_355_ = lean_array_fget_borrowed(v_ks_343_, v_x_340_);
v___x_356_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_341_, v_k_x27_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_358_; 
if (v_isShared_347_ == 0)
{
v___x_358_ = v___x_346_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_ks_343_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_vs_344_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_x_340_, v___x_359_);
lean_dec(v_x_340_);
v_x_339_ = v___x_358_;
v_x_340_ = v___x_360_;
goto _start;
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_array_fset(v_ks_343_, v_x_340_, v_x_341_);
v___x_364_ = lean_array_fset(v_vs_344_, v_x_340_, v_x_342_);
lean_dec(v_x_340_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_364_);
lean_ctor_set(v___x_346_, 0, v___x_363_);
v___x_366_ = v___x_346_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8___redArg(lean_object* v_n_369_, lean_object* v_k_370_, lean_object* v_v_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8_spec__9___redArg(v_n_369_, v___x_372_, v_k_370_, v_v_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg(lean_object* v_x_375_, size_t v_x_376_, size_t v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v_es_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_j_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_es_380_ = lean_ctor_get(v_x_375_, 0);
v___x_381_ = ((size_t)31ULL);
v___x_382_ = lean_usize_land(v_x_376_, v___x_381_);
v_j_383_ = lean_usize_to_nat(v___x_382_);
v___x_384_ = lean_array_get_size(v_es_380_);
v___x_385_ = lean_nat_dec_lt(v_j_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec(v_j_383_);
lean_dec(v_x_379_);
lean_dec_ref(v_x_378_);
return v_x_375_;
}
else
{
lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_424_; 
lean_inc_ref(v_es_380_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_x_375_, 0);
lean_dec(v_unused_425_);
v___x_387_ = v_x_375_;
v_isShared_388_ = v_isSharedCheck_424_;
goto v_resetjp_386_;
}
else
{
lean_dec(v_x_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_424_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_v_389_; lean_object* v___x_390_; lean_object* v_xs_x27_391_; lean_object* v___y_393_; 
v_v_389_ = lean_array_fget(v_es_380_, v_j_383_);
v___x_390_ = lean_box(0);
v_xs_x27_391_ = lean_array_fset(v_es_380_, v_j_383_, v___x_390_);
switch(lean_obj_tag(v_v_389_))
{
case 0:
{
lean_object* v_key_398_; lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v_key_398_ = lean_ctor_get(v_v_389_, 0);
v_val_399_ = lean_ctor_get(v_v_389_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_v_389_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v_v_389_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_inc(v_key_398_);
lean_dec(v_v_389_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
uint8_t v___x_403_; 
v___x_403_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_378_, v_key_398_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_del_object(v___x_401_);
v___x_404_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_398_, v_val_399_, v_x_378_, v_x_379_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
v___y_393_ = v___x_405_;
goto v___jp_392_;
}
else
{
lean_object* v___x_407_; 
lean_dec(v_val_399_);
lean_dec(v_key_398_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 1, v_x_379_);
lean_ctor_set(v___x_401_, 0, v_x_378_);
v___x_407_ = v___x_401_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_x_378_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_x_379_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
v___y_393_ = v___x_407_;
goto v___jp_392_;
}
}
}
}
case 1:
{
lean_object* v_node_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_422_; 
v_node_410_ = lean_ctor_get(v_v_389_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_v_389_);
if (v_isSharedCheck_422_ == 0)
{
v___x_412_ = v_v_389_;
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_node_410_);
lean_dec(v_v_389_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_414_ = ((size_t)5ULL);
v___x_415_ = lean_usize_shift_right(v_x_376_, v___x_414_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_x_377_, v___x_416_);
v___x_418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg(v_node_410_, v___x_415_, v___x_417_, v_x_378_, v_x_379_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_418_);
v___x_420_ = v___x_412_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v___y_393_ = v___x_420_;
goto v___jp_392_;
}
}
}
default: 
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_x_378_);
lean_ctor_set(v___x_423_, 1, v_x_379_);
v___y_393_ = v___x_423_;
goto v___jp_392_;
}
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_array_fset(v_xs_x27_391_, v_j_383_, v___y_393_);
lean_dec(v_j_383_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_394_);
v___x_396_ = v___x_387_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
else
{
lean_object* v_ks_426_; lean_object* v_vs_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_447_; 
v_ks_426_ = lean_ctor_get(v_x_375_, 0);
v_vs_427_ = lean_ctor_get(v_x_375_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_375_);
if (v_isSharedCheck_447_ == 0)
{
v___x_429_ = v_x_375_;
v_isShared_430_ = v_isSharedCheck_447_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_vs_427_);
lean_inc(v_ks_426_);
lean_dec(v_x_375_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_447_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_ks_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_vs_427_);
v___x_432_ = v_reuseFailAlloc_446_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v_newNode_433_; uint8_t v___y_435_; size_t v___x_441_; uint8_t v___x_442_; 
v_newNode_433_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8___redArg(v___x_432_, v_x_378_, v_x_379_);
v___x_441_ = ((size_t)7ULL);
v___x_442_ = lean_usize_dec_le(v___x_441_, v_x_377_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_433_);
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_nat_dec_lt(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
v___y_435_ = v___x_445_;
goto v___jp_434_;
}
else
{
v___y_435_ = v___x_442_;
goto v___jp_434_;
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
lean_object* v_ks_436_; lean_object* v_vs_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_ks_436_ = lean_ctor_get(v_newNode_433_, 0);
lean_inc_ref(v_ks_436_);
v_vs_437_ = lean_ctor_get(v_newNode_433_, 1);
lean_inc_ref(v_vs_437_);
lean_dec_ref(v_newNode_433_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___closed__0);
v___x_440_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___redArg(v_x_377_, v_ks_436_, v_vs_437_, v___x_438_, v___x_439_);
lean_dec_ref(v_vs_437_);
lean_dec_ref(v_ks_436_);
return v___x_440_;
}
else
{
return v_newNode_433_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___redArg(size_t v_depth_448_, lean_object* v_keys_449_, lean_object* v_vals_450_, lean_object* v_i_451_, lean_object* v_entries_452_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_get_size(v_keys_449_);
v___x_454_ = lean_nat_dec_lt(v_i_451_, v___x_453_);
if (v___x_454_ == 0)
{
lean_dec(v_i_451_);
return v_entries_452_;
}
else
{
lean_object* v_k_455_; lean_object* v_v_456_; uint64_t v___x_457_; size_t v_h_458_; size_t v___x_459_; lean_object* v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v_h_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_k_455_ = lean_array_fget_borrowed(v_keys_449_, v_i_451_);
v_v_456_ = lean_array_fget_borrowed(v_vals_450_, v_i_451_);
v___x_457_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_455_);
v_h_458_ = lean_uint64_to_usize(v___x_457_);
v___x_459_ = ((size_t)5ULL);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_sub(v_depth_448_, v___x_461_);
v___x_463_ = lean_usize_mul(v___x_459_, v___x_462_);
v_h_464_ = lean_usize_shift_right(v_h_458_, v___x_463_);
v___x_465_ = lean_nat_add(v_i_451_, v___x_460_);
lean_dec(v_i_451_);
lean_inc(v_v_456_);
lean_inc(v_k_455_);
v___x_466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg(v_entries_452_, v_h_464_, v_depth_448_, v_k_455_, v_v_456_);
v_i_451_ = v___x_465_;
v_entries_452_ = v___x_466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_depth_468_, lean_object* v_keys_469_, lean_object* v_vals_470_, lean_object* v_i_471_, lean_object* v_entries_472_){
_start:
{
size_t v_depth_boxed_473_; lean_object* v_res_474_; 
v_depth_boxed_473_ = lean_unbox_usize(v_depth_468_);
lean_dec(v_depth_468_);
v_res_474_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___redArg(v_depth_boxed_473_, v_keys_469_, v_vals_470_, v_i_471_, v_entries_472_);
lean_dec_ref(v_vals_470_);
lean_dec_ref(v_keys_469_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg___boxed(lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
size_t v_x_5695__boxed_480_; size_t v_x_5696__boxed_481_; lean_object* v_res_482_; 
v_x_5695__boxed_480_ = lean_unbox_usize(v_x_476_);
lean_dec(v_x_476_);
v_x_5696__boxed_481_ = lean_unbox_usize(v_x_477_);
lean_dec(v_x_477_);
v_res_482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg(v_x_475_, v_x_5695__boxed_480_, v_x_5696__boxed_481_, v_x_478_, v_x_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint64_t v___x_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_486_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_484_);
v___x_487_ = lean_uint64_to_usize(v___x_486_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg(v_x_483_, v___x_487_, v___x_488_, v_x_484_, v_x_485_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___redArg(lean_object* v_b_490_, lean_object* v_acc_491_, lean_object* v_i_492_){
_start:
{
lean_object* v___y_494_; lean_object* v_keyArray_502_; lean_object* v_valueArray_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_keyArray_502_ = lean_ctor_get(v_b_490_, 1);
v_valueArray_503_ = lean_ctor_get(v_b_490_, 2);
v___x_504_ = lean_array_get_size(v_keyArray_502_);
v___x_505_ = lean_nat_dec_lt(v_i_492_, v___x_504_);
if (v___x_505_ == 0)
{
lean_dec(v_i_492_);
return v_acc_491_;
}
else
{
lean_object* v___x_506_; uint8_t v_isSome_507_; 
v___x_506_ = lean_array_fget_borrowed(v_keyArray_502_, v_i_492_);
v_isSome_507_ = lean_noption_is_some(v___x_506_);
if (v_isSome_507_ == 0)
{
goto v___jp_498_;
}
else
{
lean_object* v___x_508_; uint8_t v_isSome_509_; 
v___x_508_ = lean_array_fget_borrowed(v_valueArray_503_, v_i_492_);
v_isSome_509_ = lean_noption_is_some(v___x_508_);
if (v_isSome_509_ == 0)
{
goto v___jp_498_;
}
else
{
lean_object* v_val_510_; lean_object* v_val_511_; lean_object* v_i_513_; lean_object* v___x_518_; 
lean_inc(v___x_506_);
v_val_510_ = lean_noption_get(v___x_506_);
lean_inc(v___x_508_);
v_val_511_ = lean_noption_get(v___x_508_);
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_acc_491_, v_val_510_);
switch(lean_obj_tag(v___x_518_))
{
case 0:
{
lean_object* v_index_519_; lean_object* v_size_520_; lean_object* v___x_521_; 
v_index_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_index_519_);
lean_dec_ref_known(v___x_518_, 3);
v_size_520_ = lean_ctor_get(v_acc_491_, 0);
lean_inc(v_size_520_);
v___x_521_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_491_, v_size_520_, v_index_519_, v_val_510_, v_val_511_);
lean_dec(v_index_519_);
v___y_494_ = v___x_521_;
goto v___jp_493_;
}
case 1:
{
lean_object* v_index_522_; 
v_index_522_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_index_522_);
lean_dec_ref_known(v___x_518_, 1);
v_i_513_ = v_index_522_;
goto v___jp_512_;
}
default: 
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_491_, v___x_523_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_index_525_; 
v_index_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_index_525_);
lean_dec_ref_known(v___x_524_, 1);
v_i_513_ = v_index_525_;
goto v___jp_512_;
}
else
{
lean_dec(v_val_511_);
lean_dec(v_val_510_);
v___y_494_ = v_acc_491_;
goto v___jp_493_;
}
}
}
v___jp_512_:
{
lean_object* v_size_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_size_514_ = lean_ctor_get(v_acc_491_, 0);
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_size_514_, v___x_515_);
v___x_517_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_491_, v___x_516_, v_i_513_, v_val_510_, v_val_511_);
lean_dec(v_i_513_);
v___y_494_ = v___x_517_;
goto v___jp_493_;
}
}
}
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_add(v_i_492_, v___x_495_);
lean_dec(v_i_492_);
v_acc_491_ = v___y_494_;
v_i_492_ = v___x_496_;
goto _start;
}
v___jp_498_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_i_492_, v___x_499_);
lean_dec(v_i_492_);
v_i_492_ = v___x_500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_526_, lean_object* v_acc_527_, lean_object* v_i_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___redArg(v_b_526_, v_acc_527_, v_i_528_);
lean_dec_ref(v_b_526_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___redArg(lean_object* v_init_530_, lean_object* v_b_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___redArg(v_b_531_, v_init_530_, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___redArg___boxed(lean_object* v_init_534_, lean_object* v_b_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___redArg(v_init_534_, v_b_535_);
lean_dec_ref(v_b_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_m_537_){
_start:
{
lean_object* v_keyArray_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_cellCount_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_target_545_; lean_object* v___x_546_; 
v_keyArray_538_ = lean_ctor_get(v_m_537_, 1);
v___x_539_ = lean_array_get_size(v_keyArray_538_);
v___x_540_ = lean_unsigned_to_nat(2u);
v_cellCount_541_ = lean_nat_mul(v___x_539_, v___x_540_);
v___x_542_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_541_);
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_541_);
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_541_);
v_target_545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_545_, 0, v___x_542_);
lean_ctor_set(v_target_545_, 1, v___x_543_);
lean_ctor_set(v_target_545_, 2, v___x_544_);
v___x_546_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___redArg(v_target_545_, v_m_537_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg___boxed(lean_object* v_m_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_m_547_);
lean_dec_ref(v_m_547_);
return v_res_548_;
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_549_; size_t v___x_550_; 
v___x_549_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_550_ = lean_ptr_addr(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_551_, lean_object* v_r_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_map_554_; lean_object* v_set_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_773_; 
v_map_554_ = lean_ctor_get(v_a_553_, 0);
v_set_555_ = lean_ctor_get(v_a_553_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_553_);
if (v_isSharedCheck_773_ == 0)
{
v___x_557_ = v_a_553_;
v_isShared_558_ = v_isSharedCheck_773_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_set_555_);
lean_inc(v_map_554_);
lean_dec(v_a_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_773_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___y_560_; lean_object* v___y_568_; lean_object* v_i_569_; lean_object* v___y_575_; lean_object* v___y_585_; lean_object* v_i_586_; lean_object* v___y_592_; lean_object* v___y_603_; lean_object* v___y_635_; lean_object* v_i_636_; lean_object* v___y_642_; lean_object* v___y_652_; lean_object* v_i_653_; lean_object* v___x_668_; uint64_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; lean_object* v___y_673_; lean_object* v___y_677_; lean_object* v_i_678_; lean_object* v___y_684_; lean_object* v___y_694_; lean_object* v_i_695_; size_t v___x_710_; size_t v___x_711_; uint8_t v___x_712_; 
v___x_668_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_669_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_552_);
v___x_670_ = lean_uint64_to_usize(v___x_669_);
v___x_671_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_555_, v___x_670_, v_r_552_, v___x_668_);
v___x_710_ = lean_ptr_addr(v___x_671_);
v___x_711_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_712_ = lean_usize_dec_eq(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_del_object(v___x_557_);
lean_dec_ref(v_r_552_);
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_554_, v_e_551_);
switch(lean_obj_tag(v___x_713_))
{
case 0:
{
lean_object* v_index_714_; lean_object* v_size_715_; lean_object* v___x_716_; 
v_index_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_index_714_);
lean_dec_ref_known(v___x_713_, 3);
v_size_715_ = lean_ctor_get(v_map_554_, 0);
lean_inc(v_size_715_);
lean_inc_ref(v___x_671_);
v___x_716_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_554_, v_size_715_, v_index_714_, v_e_551_, v___x_671_);
lean_dec(v_index_714_);
v___y_673_ = v___x_716_;
goto v___jp_672_;
}
case 1:
{
lean_object* v_index_717_; lean_object* v_size_718_; lean_object* v_keyArray_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_index_717_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_index_717_);
lean_dec_ref_known(v___x_713_, 1);
v_size_718_ = lean_ctor_get(v_map_554_, 0);
v_keyArray_719_ = lean_ctor_get(v_map_554_, 1);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_size_718_, v___x_720_);
v___x_722_ = lean_array_get_size(v_keyArray_719_);
v___x_723_ = lean_nat_dec_lt(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v___x_721_);
lean_dec(v_index_717_);
goto v___jp_700_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_724_ = lean_unsigned_to_nat(4u);
v___x_725_ = lean_nat_mul(v___x_721_, v___x_724_);
v___x_726_ = lean_unsigned_to_nat(3u);
v___x_727_ = lean_nat_mul(v___x_722_, v___x_726_);
v___x_728_ = lean_nat_dec_le(v___x_725_, v___x_727_);
lean_dec(v___x_727_);
lean_dec(v___x_725_);
if (v___x_728_ == 0)
{
lean_dec(v___x_721_);
lean_dec(v_index_717_);
goto v___jp_700_;
}
else
{
lean_object* v___x_729_; 
lean_inc_ref(v___x_671_);
v___x_729_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_554_, v___x_721_, v_index_717_, v_e_551_, v___x_671_);
lean_dec(v_index_717_);
v___y_673_ = v___x_729_;
goto v___jp_672_;
}
}
}
default: 
{
lean_object* v_size_730_; lean_object* v_keyArray_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_size_730_ = lean_ctor_get(v_map_554_, 0);
v_keyArray_731_ = lean_ctor_get(v_map_554_, 1);
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_size_730_, v___x_732_);
v___x_734_ = lean_array_get_size(v_keyArray_731_);
v___x_735_ = lean_nat_dec_lt(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_dec(v___x_733_);
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_map_554_);
lean_dec_ref(v_map_554_);
v___y_684_ = v___x_736_;
goto v___jp_683_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_737_ = lean_unsigned_to_nat(4u);
v___x_738_ = lean_nat_mul(v___x_733_, v___x_737_);
lean_dec(v___x_733_);
v___x_739_ = lean_unsigned_to_nat(3u);
v___x_740_ = lean_nat_mul(v___x_734_, v___x_739_);
v___x_741_ = lean_nat_dec_le(v___x_738_, v___x_740_);
lean_dec(v___x_740_);
lean_dec(v___x_738_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_map_554_);
lean_dec_ref(v_map_554_);
v___y_684_ = v___x_742_;
goto v___jp_683_;
}
else
{
v___y_684_ = v_map_554_;
goto v___jp_683_;
}
}
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec_ref(v___x_671_);
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_554_, v_e_551_);
switch(lean_obj_tag(v___x_743_))
{
case 0:
{
lean_object* v_index_744_; lean_object* v_size_745_; lean_object* v___x_746_; 
v_index_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_index_744_);
lean_dec_ref_known(v___x_743_, 3);
v_size_745_ = lean_ctor_get(v_map_554_, 0);
lean_inc(v_size_745_);
lean_inc_ref(v_r_552_);
v___x_746_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_554_, v_size_745_, v_index_744_, v_e_551_, v_r_552_);
lean_dec(v_index_744_);
v___y_603_ = v___x_746_;
goto v___jp_602_;
}
case 1:
{
lean_object* v_index_747_; lean_object* v_size_748_; lean_object* v_keyArray_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_index_747_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_index_747_);
lean_dec_ref_known(v___x_743_, 1);
v_size_748_ = lean_ctor_get(v_map_554_, 0);
v_keyArray_749_ = lean_ctor_get(v_map_554_, 1);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_size_748_, v___x_750_);
v___x_752_ = lean_array_get_size(v_keyArray_749_);
v___x_753_ = lean_nat_dec_lt(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v_index_747_);
goto v___jp_658_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_754_ = lean_unsigned_to_nat(4u);
v___x_755_ = lean_nat_mul(v___x_751_, v___x_754_);
v___x_756_ = lean_unsigned_to_nat(3u);
v___x_757_ = lean_nat_mul(v___x_752_, v___x_756_);
v___x_758_ = lean_nat_dec_le(v___x_755_, v___x_757_);
lean_dec(v___x_757_);
lean_dec(v___x_755_);
if (v___x_758_ == 0)
{
lean_dec(v___x_751_);
lean_dec(v_index_747_);
goto v___jp_658_;
}
else
{
lean_object* v___x_759_; 
lean_inc_ref(v_r_552_);
v___x_759_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_554_, v___x_751_, v_index_747_, v_e_551_, v_r_552_);
lean_dec(v_index_747_);
v___y_603_ = v___x_759_;
goto v___jp_602_;
}
}
}
default: 
{
lean_object* v_size_760_; lean_object* v_keyArray_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_size_760_ = lean_ctor_get(v_map_554_, 0);
v_keyArray_761_ = lean_ctor_get(v_map_554_, 1);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_size_760_, v___x_762_);
v___x_764_ = lean_array_get_size(v_keyArray_761_);
v___x_765_ = lean_nat_dec_lt(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_dec(v___x_763_);
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_map_554_);
lean_dec_ref(v_map_554_);
v___y_642_ = v___x_766_;
goto v___jp_641_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_767_ = lean_unsigned_to_nat(4u);
v___x_768_ = lean_nat_mul(v___x_763_, v___x_767_);
lean_dec(v___x_763_);
v___x_769_ = lean_unsigned_to_nat(3u);
v___x_770_ = lean_nat_mul(v___x_764_, v___x_769_);
v___x_771_ = lean_nat_dec_le(v___x_768_, v___x_770_);
lean_dec(v___x_770_);
lean_dec(v___x_768_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_map_554_);
lean_dec_ref(v_map_554_);
v___y_642_ = v___x_772_;
goto v___jp_641_;
}
else
{
v___y_642_ = v_map_554_;
goto v___jp_641_;
}
}
}
}
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = lean_box(0);
lean_inc_ref(v_r_552_);
v___x_562_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(v_set_555_, v_r_552_, v___x_561_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_562_);
lean_ctor_set(v___x_557_, 0, v___y_560_);
v___x_564_ = v___x_557_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___y_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_r_552_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
v___jp_567_:
{
lean_object* v_size_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_size_570_ = lean_ctor_get(v___y_568_, 0);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v_size_570_, v___x_571_);
lean_inc_ref_n(v_r_552_, 2);
v___x_573_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_568_, v___x_572_, v_i_569_, v_r_552_, v_r_552_);
lean_dec(v_i_569_);
v___y_560_ = v___x_573_;
goto v___jp_559_;
}
v___jp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___y_575_, v_r_552_);
switch(lean_obj_tag(v___x_576_))
{
case 0:
{
lean_object* v_index_577_; lean_object* v_size_578_; lean_object* v___x_579_; 
v_index_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_index_577_);
lean_dec_ref_known(v___x_576_, 3);
v_size_578_ = lean_ctor_get(v___y_575_, 0);
lean_inc(v_size_578_);
lean_inc_ref_n(v_r_552_, 2);
v___x_579_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_575_, v_size_578_, v_index_577_, v_r_552_, v_r_552_);
lean_dec(v_index_577_);
v___y_560_ = v___x_579_;
goto v___jp_559_;
}
case 1:
{
lean_object* v_index_580_; 
v_index_580_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_index_580_);
lean_dec_ref_known(v___x_576_, 1);
v___y_568_ = v___y_575_;
v_i_569_ = v_index_580_;
goto v___jp_567_;
}
default: 
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_575_, v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_index_583_; 
v_index_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_index_583_);
lean_dec_ref_known(v___x_582_, 1);
v___y_568_ = v___y_575_;
v_i_569_ = v_index_583_;
goto v___jp_567_;
}
else
{
v___y_560_ = v___y_575_;
goto v___jp_559_;
}
}
}
}
v___jp_584_:
{
lean_object* v_size_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_size_587_ = lean_ctor_get(v___y_585_, 0);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_size_587_, v___x_588_);
lean_inc_ref_n(v_r_552_, 2);
v___x_590_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_585_, v___x_589_, v_i_586_, v_r_552_, v_r_552_);
lean_dec(v_i_586_);
v___y_560_ = v___x_590_;
goto v___jp_559_;
}
v___jp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v___y_592_);
lean_dec_ref(v___y_592_);
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_593_, v_r_552_);
switch(lean_obj_tag(v___x_594_))
{
case 0:
{
lean_object* v_index_595_; lean_object* v_size_596_; lean_object* v___x_597_; 
v_index_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_index_595_);
lean_dec_ref_known(v___x_594_, 3);
v_size_596_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_size_596_);
lean_inc_ref_n(v_r_552_, 2);
v___x_597_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_593_, v_size_596_, v_index_595_, v_r_552_, v_r_552_);
lean_dec(v_index_595_);
v___y_560_ = v___x_597_;
goto v___jp_559_;
}
case 1:
{
lean_object* v_index_598_; 
v_index_598_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_index_598_);
lean_dec_ref_known(v___x_594_, 1);
v___y_585_ = v___x_593_;
v_i_586_ = v_index_598_;
goto v___jp_584_;
}
default: 
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_593_, v___x_599_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_index_601_; 
v_index_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_601_);
lean_dec_ref_known(v___x_600_, 1);
v___y_585_ = v___x_593_;
v_i_586_ = v_index_601_;
goto v___jp_584_;
}
else
{
v___y_560_ = v___x_593_;
goto v___jp_559_;
}
}
}
}
v___jp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___y_603_, v_r_552_);
switch(lean_obj_tag(v___x_604_))
{
case 0:
{
lean_object* v_index_605_; lean_object* v_size_606_; lean_object* v___x_607_; 
v_index_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_index_605_);
lean_dec_ref_known(v___x_604_, 3);
v_size_606_ = lean_ctor_get(v___y_603_, 0);
lean_inc(v_size_606_);
lean_inc_ref_n(v_r_552_, 2);
v___x_607_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_603_, v_size_606_, v_index_605_, v_r_552_, v_r_552_);
lean_dec(v_index_605_);
v___y_560_ = v___x_607_;
goto v___jp_559_;
}
case 1:
{
lean_object* v_index_608_; lean_object* v_size_609_; lean_object* v_keyArray_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_index_608_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_index_608_);
lean_dec_ref_known(v___x_604_, 1);
v_size_609_ = lean_ctor_get(v___y_603_, 0);
v_keyArray_610_ = lean_ctor_get(v___y_603_, 1);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_size_609_, v___x_611_);
v___x_613_ = lean_array_get_size(v_keyArray_610_);
v___x_614_ = lean_nat_dec_lt(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v___x_612_);
lean_dec(v_index_608_);
v___y_592_ = v___y_603_;
goto v___jp_591_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_615_ = lean_unsigned_to_nat(4u);
v___x_616_ = lean_nat_mul(v___x_612_, v___x_615_);
v___x_617_ = lean_unsigned_to_nat(3u);
v___x_618_ = lean_nat_mul(v___x_613_, v___x_617_);
v___x_619_ = lean_nat_dec_le(v___x_616_, v___x_618_);
lean_dec(v___x_618_);
lean_dec(v___x_616_);
if (v___x_619_ == 0)
{
lean_dec(v___x_612_);
lean_dec(v_index_608_);
v___y_592_ = v___y_603_;
goto v___jp_591_;
}
else
{
lean_object* v___x_620_; 
lean_inc_ref_n(v_r_552_, 2);
v___x_620_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_603_, v___x_612_, v_index_608_, v_r_552_, v_r_552_);
lean_dec(v_index_608_);
v___y_560_ = v___x_620_;
goto v___jp_559_;
}
}
}
default: 
{
lean_object* v_size_621_; lean_object* v_keyArray_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_size_621_ = lean_ctor_get(v___y_603_, 0);
v_keyArray_622_ = lean_ctor_get(v___y_603_, 1);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v_size_621_, v___x_623_);
v___x_625_ = lean_array_get_size(v_keyArray_622_);
v___x_626_ = lean_nat_dec_lt(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec(v___x_624_);
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v___y_603_);
lean_dec_ref(v___y_603_);
v___y_575_ = v___x_627_;
goto v___jp_574_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_628_ = lean_unsigned_to_nat(4u);
v___x_629_ = lean_nat_mul(v___x_624_, v___x_628_);
lean_dec(v___x_624_);
v___x_630_ = lean_unsigned_to_nat(3u);
v___x_631_ = lean_nat_mul(v___x_625_, v___x_630_);
v___x_632_ = lean_nat_dec_le(v___x_629_, v___x_631_);
lean_dec(v___x_631_);
lean_dec(v___x_629_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v___y_603_);
lean_dec_ref(v___y_603_);
v___y_575_ = v___x_633_;
goto v___jp_574_;
}
else
{
v___y_575_ = v___y_603_;
goto v___jp_574_;
}
}
}
}
}
v___jp_634_:
{
lean_object* v_size_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_size_637_ = lean_ctor_get(v___y_635_, 0);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_size_637_, v___x_638_);
lean_inc_ref(v_r_552_);
v___x_640_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_635_, v___x_639_, v_i_636_, v_e_551_, v_r_552_);
lean_dec(v_i_636_);
v___y_603_ = v___x_640_;
goto v___jp_602_;
}
v___jp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___y_642_, v_e_551_);
switch(lean_obj_tag(v___x_643_))
{
case 0:
{
lean_object* v_index_644_; lean_object* v_size_645_; lean_object* v___x_646_; 
v_index_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_index_644_);
lean_dec_ref_known(v___x_643_, 3);
v_size_645_ = lean_ctor_get(v___y_642_, 0);
lean_inc(v_size_645_);
lean_inc_ref(v_r_552_);
v___x_646_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_642_, v_size_645_, v_index_644_, v_e_551_, v_r_552_);
lean_dec(v_index_644_);
v___y_603_ = v___x_646_;
goto v___jp_602_;
}
case 1:
{
lean_object* v_index_647_; 
v_index_647_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_index_647_);
lean_dec_ref_known(v___x_643_, 1);
v___y_635_ = v___y_642_;
v_i_636_ = v_index_647_;
goto v___jp_634_;
}
default: 
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_642_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_index_650_; 
v_index_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_index_650_);
lean_dec_ref_known(v___x_649_, 1);
v___y_635_ = v___y_642_;
v_i_636_ = v_index_650_;
goto v___jp_634_;
}
else
{
lean_dec_ref(v_e_551_);
v___y_603_ = v___y_642_;
goto v___jp_602_;
}
}
}
}
v___jp_651_:
{
lean_object* v_size_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_size_654_ = lean_ctor_get(v___y_652_, 0);
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_add(v_size_654_, v___x_655_);
lean_inc_ref(v_r_552_);
v___x_657_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_652_, v___x_656_, v_i_653_, v_e_551_, v_r_552_);
lean_dec(v_i_653_);
v___y_603_ = v___x_657_;
goto v___jp_602_;
}
v___jp_658_:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_map_554_);
lean_dec_ref(v_map_554_);
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_659_, v_e_551_);
switch(lean_obj_tag(v___x_660_))
{
case 0:
{
lean_object* v_index_661_; lean_object* v_size_662_; lean_object* v___x_663_; 
v_index_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_index_661_);
lean_dec_ref_known(v___x_660_, 3);
v_size_662_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_size_662_);
lean_inc_ref(v_r_552_);
v___x_663_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_659_, v_size_662_, v_index_661_, v_e_551_, v_r_552_);
lean_dec(v_index_661_);
v___y_603_ = v___x_663_;
goto v___jp_602_;
}
case 1:
{
lean_object* v_index_664_; 
v_index_664_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_index_664_);
lean_dec_ref_known(v___x_660_, 1);
v___y_652_ = v___x_659_;
v_i_653_ = v_index_664_;
goto v___jp_651_;
}
default: 
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_659_, v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_index_667_; 
v_index_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_index_667_);
lean_dec_ref_known(v___x_666_, 1);
v___y_652_ = v___x_659_;
v_i_653_ = v_index_667_;
goto v___jp_651_;
}
else
{
lean_dec_ref(v_e_551_);
v___y_603_ = v___x_659_;
goto v___jp_602_;
}
}
}
}
v___jp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_673_);
lean_ctor_set(v___x_674_, 1, v_set_555_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_671_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
return v___x_675_;
}
v___jp_676_:
{
lean_object* v_size_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_size_679_ = lean_ctor_get(v___y_677_, 0);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_size_679_, v___x_680_);
lean_inc_ref(v___x_671_);
v___x_682_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_677_, v___x_681_, v_i_678_, v_e_551_, v___x_671_);
lean_dec(v_i_678_);
v___y_673_ = v___x_682_;
goto v___jp_672_;
}
v___jp_683_:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___y_684_, v_e_551_);
switch(lean_obj_tag(v___x_685_))
{
case 0:
{
lean_object* v_index_686_; lean_object* v_size_687_; lean_object* v___x_688_; 
v_index_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_index_686_);
lean_dec_ref_known(v___x_685_, 3);
v_size_687_ = lean_ctor_get(v___y_684_, 0);
lean_inc(v_size_687_);
lean_inc_ref(v___x_671_);
v___x_688_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_684_, v_size_687_, v_index_686_, v_e_551_, v___x_671_);
lean_dec(v_index_686_);
v___y_673_ = v___x_688_;
goto v___jp_672_;
}
case 1:
{
lean_object* v_index_689_; 
v_index_689_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_index_689_);
lean_dec_ref_known(v___x_685_, 1);
v___y_677_ = v___y_684_;
v_i_678_ = v_index_689_;
goto v___jp_676_;
}
default: 
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_684_, v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_index_692_; 
v_index_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_index_692_);
lean_dec_ref_known(v___x_691_, 1);
v___y_677_ = v___y_684_;
v_i_678_ = v_index_692_;
goto v___jp_676_;
}
else
{
lean_dec_ref(v_e_551_);
v___y_673_ = v___y_684_;
goto v___jp_672_;
}
}
}
}
v___jp_693_:
{
lean_object* v_size_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_size_696_ = lean_ctor_get(v___y_694_, 0);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_add(v_size_696_, v___x_697_);
lean_inc_ref(v___x_671_);
v___x_699_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_694_, v___x_698_, v_i_695_, v_e_551_, v___x_671_);
lean_dec(v_i_695_);
v___y_673_ = v___x_699_;
goto v___jp_672_;
}
v___jp_700_:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_map_554_);
lean_dec_ref(v_map_554_);
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_701_, v_e_551_);
switch(lean_obj_tag(v___x_702_))
{
case 0:
{
lean_object* v_index_703_; lean_object* v_size_704_; lean_object* v___x_705_; 
v_index_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_index_703_);
lean_dec_ref_known(v___x_702_, 3);
v_size_704_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_size_704_);
lean_inc_ref(v___x_671_);
v___x_705_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_701_, v_size_704_, v_index_703_, v_e_551_, v___x_671_);
lean_dec(v_index_703_);
v___y_673_ = v___x_705_;
goto v___jp_672_;
}
case 1:
{
lean_object* v_index_706_; 
v_index_706_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_index_706_);
lean_dec_ref_known(v___x_702_, 1);
v___y_694_ = v___x_701_;
v_i_695_ = v_index_706_;
goto v___jp_693_;
}
default: 
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_701_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_index_709_; 
v_index_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_index_709_);
lean_dec_ref_known(v___x_708_, 1);
v___y_694_ = v___x_701_;
v_i_695_ = v_index_709_;
goto v___jp_693_;
}
else
{
lean_dec_ref(v_e_551_);
v___y_673_ = v___x_701_;
goto v___jp_672_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_774_, lean_object* v_r_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_774_, v_r_775_, v_a_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_779_, lean_object* v_r_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_779_, v_r_780_, v_a_781_, v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, size_t v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_785_, v_x_786_, v_x_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
size_t v_x_6316__boxed_795_; lean_object* v_res_796_; 
v_x_6316__boxed_795_ = lean_unbox_usize(v_x_792_);
lean_dec(v_x_792_);
v_res_796_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_790_, v_x_791_, v_x_6316__boxed_795_, v_x_793_, v_x_794_);
lean_dec_ref(v_x_794_);
lean_dec_ref(v_x_793_);
lean_dec_ref(v_x_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_797_, lean_object* v_m_798_, lean_object* v_query_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_798_, v_query_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___boxed(lean_object* v_00_u03b2_801_, lean_object* v_m_802_, lean_object* v_query_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(v_00_u03b2_801_, v_m_802_, v_query_803_);
lean_dec_ref(v_query_803_);
lean_dec_ref(v_m_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_805_, lean_object* v_m_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_m_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___boxed(lean_object* v_00_u03b2_808_, lean_object* v_m_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(v_00_u03b2_808_, v_m_809_);
lean_dec_ref(v_m_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3(lean_object* v_00_u03b2_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(v_x_812_, v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_816_, lean_object* v_keys_817_, lean_object* v_vals_818_, lean_object* v_heq_819_, lean_object* v_i_820_, lean_object* v_k_821_, lean_object* v_k_u2080_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_817_, v_i_820_, v_k_821_, v_k_u2080_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_k_829_, lean_object* v_k_u2080_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_824_, v_keys_825_, v_vals_826_, v_heq_827_, v_i_828_, v_k_829_, v_k_u2080_830_);
lean_dec_ref(v_k_u2080_830_);
lean_dec_ref(v_k_829_);
lean_dec_ref(v_vals_826_);
lean_dec_ref(v_keys_825_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_832_, lean_object* v_m_833_, lean_object* v_query_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_m_833_, v_query_834_, v_x_835_, v_x_836_, v_x_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_840_, lean_object* v_m_841_, lean_object* v_query_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_840_, v_m_841_, v_query_842_, v_x_843_, v_x_844_, v_x_845_, v_x_846_);
lean_dec_ref(v_query_842_);
lean_dec_ref(v_m_841_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4(lean_object* v_00_u03b2_848_, lean_object* v_init_849_, lean_object* v_b_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___redArg(v_init_849_, v_b_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4___boxed(lean_object* v_00_u03b2_852_, lean_object* v_init_853_, lean_object* v_b_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4(v_00_u03b2_852_, v_init_853_, v_b_854_);
lean_dec_ref(v_b_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6(lean_object* v_00_u03b2_856_, lean_object* v_x_857_, size_t v_x_858_, size_t v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___redArg(v_x_857_, v_x_858_, v_x_859_, v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6___boxed(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
size_t v_x_6360__boxed_869_; size_t v_x_6361__boxed_870_; lean_object* v_res_871_; 
v_x_6360__boxed_869_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_x_6361__boxed_870_ = lean_unbox_usize(v_x_866_);
lean_dec(v_x_866_);
v_res_871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6(v_00_u03b2_863_, v_x_864_, v_x_6360__boxed_869_, v_x_6361__boxed_870_, v_x_867_, v_x_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_872_, lean_object* v_b_873_, lean_object* v_acc_874_, lean_object* v_i_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___redArg(v_b_873_, v_acc_874_, v_i_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_877_, lean_object* v_b_878_, lean_object* v_acc_879_, lean_object* v_i_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__4_spec__5(v_00_u03b2_877_, v_b_878_, v_acc_879_, v_i_880_);
lean_dec_ref(v_b_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_882_, lean_object* v_n_883_, lean_object* v_k_884_, lean_object* v_v_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8___redArg(v_n_883_, v_k_884_, v_v_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_887_, size_t v_depth_888_, lean_object* v_keys_889_, lean_object* v_vals_890_, lean_object* v_heq_891_, lean_object* v_i_892_, lean_object* v_entries_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___redArg(v_depth_888_, v_keys_889_, v_vals_890_, v_i_892_, v_entries_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9___boxed(lean_object* v_00_u03b2_895_, lean_object* v_depth_896_, lean_object* v_keys_897_, lean_object* v_vals_898_, lean_object* v_heq_899_, lean_object* v_i_900_, lean_object* v_entries_901_){
_start:
{
size_t v_depth_boxed_902_; lean_object* v_res_903_; 
v_depth_boxed_902_ = lean_unbox_usize(v_depth_896_);
lean_dec(v_depth_896_);
v_res_903_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__9(v_00_u03b2_895_, v_depth_boxed_902_, v_keys_897_, v_vals_898_, v_heq_899_, v_i_900_, v_entries_901_);
lean_dec_ref(v_vals_898_);
lean_dec_ref(v_keys_897_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3_spec__6_spec__8_spec__9___redArg(v_x_905_, v_x_906_, v_x_907_, v_x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_912_, lean_object* v_k_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_map_916_; lean_object* v_set_917_; lean_object* v___f_918_; lean_object* v___f_919_; lean_object* v___x_920_; 
v_map_916_ = lean_ctor_get(v_a_915_, 0);
v_set_917_ = lean_ctor_get(v_a_915_, 1);
v___f_918_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_919_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_912_);
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_918_, v___f_919_, v_map_916_, v_e_912_);
if (lean_obj_tag(v___x_920_) == 1)
{
lean_object* v_val_921_; lean_object* v___x_922_; 
lean_dec_ref(v_k_913_);
lean_dec_ref(v_e_912_);
v_val_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_val_921_);
lean_ctor_set(v___x_922_, 1, v_a_915_);
return v___x_922_;
}
else
{
lean_object* v___f_923_; lean_object* v___x_924_; uint64_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; size_t v___x_928_; size_t v___x_929_; uint8_t v___x_930_; 
lean_dec(v___x_920_);
v___f_923_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_924_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_925_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_912_);
v___x_926_ = lean_uint64_to_usize(v___x_925_);
lean_inc_ref(v_e_912_);
lean_inc_ref(v_set_917_);
v___x_927_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_923_, v_set_917_, v___x_926_, v_e_912_, v___x_924_);
v___x_928_ = lean_ptr_addr(v___x_927_);
v___x_929_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_930_ = lean_usize_dec_eq(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec_ref(v_k_913_);
lean_dec_ref(v_e_912_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_927_);
lean_ctor_set(v___x_931_, 1, v_a_915_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; 
lean_dec(v___x_927_);
lean_inc_ref(v_a_914_);
v___x_932_ = lean_apply_2(v_k_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v_a_934_; lean_object* v___x_935_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
v_a_934_ = lean_ctor_get(v___x_932_, 1);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_932_, 2);
v___x_935_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_912_, v_a_933_, v_a_934_);
return v___x_935_;
}
else
{
lean_dec_ref(v_e_912_);
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_936_, lean_object* v_k_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_936_, v_k_937_, v_a_938_, v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_m_941_, lean_object* v_query_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_941_, v_query_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_index_944_; lean_object* v_key_945_; lean_object* v_value_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_index_944_ = lean_ctor_get(v___x_943_, 0);
v_key_945_ = lean_ctor_get(v___x_943_, 1);
v_value_946_ = lean_ctor_get(v___x_943_, 2);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_943_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_value_946_);
lean_inc(v_key_945_);
lean_inc(v_index_944_);
lean_dec(v___x_943_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_index_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_key_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_value_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v___x_954_; 
lean_dec(v___x_943_);
v___x_954_ = lean_box(1);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_m_955_, lean_object* v_query_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_m_955_, v_query_956_);
lean_dec_ref(v_query_956_);
lean_dec_ref(v_m_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_m_958_, v_a_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_value_961_; lean_object* v___x_962_; 
v_value_961_ = lean_ctor_get(v___x_960_, 2);
lean_inc(v_value_961_);
lean_dec_ref_known(v___x_960_, 3);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v_value_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_box(0);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_964_, v_a_965_);
lean_dec_ref(v_a_965_);
lean_dec_ref(v_m_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_i_969_, lean_object* v_k_970_){
_start:
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = lean_array_get_size(v_keys_967_);
v___x_972_ = lean_nat_dec_lt(v_i_969_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
lean_dec(v_i_969_);
v___x_973_ = lean_box(0);
return v___x_973_;
}
else
{
lean_object* v_k_x27_974_; uint8_t v___x_975_; 
v_k_x27_974_ = lean_array_fget_borrowed(v_keys_967_, v_i_969_);
v___x_975_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_970_, v_k_x27_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_add(v_i_969_, v___x_976_);
lean_dec(v_i_969_);
v_i_969_ = v___x_977_;
goto _start;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_array_fget_borrowed(v_vals_968_, v_i_969_);
lean_dec(v_i_969_);
lean_inc(v___x_979_);
lean_inc(v_k_x27_974_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_k_x27_974_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_982_, lean_object* v_vals_983_, lean_object* v_i_984_, lean_object* v_k_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_982_, v_vals_983_, v_i_984_, v_k_985_);
lean_dec_ref(v_k_985_);
lean_dec_ref(v_vals_983_);
lean_dec_ref(v_keys_982_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_987_, size_t v_x_988_, lean_object* v_x_989_){
_start:
{
if (lean_obj_tag(v_x_987_) == 0)
{
lean_object* v_es_990_; lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v_j_994_; lean_object* v___x_995_; 
v_es_990_ = lean_ctor_get(v_x_987_, 0);
v___x_991_ = lean_box(2);
v___x_992_ = ((size_t)31ULL);
v___x_993_ = lean_usize_land(v_x_988_, v___x_992_);
v_j_994_ = lean_usize_to_nat(v___x_993_);
v___x_995_ = lean_array_get_borrowed(v___x_991_, v_es_990_, v_j_994_);
lean_dec(v_j_994_);
switch(lean_obj_tag(v___x_995_))
{
case 0:
{
lean_object* v_key_996_; lean_object* v_val_997_; uint8_t v___x_998_; 
v_key_996_ = lean_ctor_get(v___x_995_, 0);
v_val_997_ = lean_ctor_get(v___x_995_, 1);
v___x_998_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_989_, v_key_996_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(0);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_inc(v_val_997_);
lean_inc(v_key_996_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_key_996_);
lean_ctor_set(v___x_1000_, 1, v_val_997_);
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
case 1:
{
lean_object* v_node_1002_; size_t v___x_1003_; size_t v___x_1004_; 
v_node_1002_ = lean_ctor_get(v___x_995_, 0);
v___x_1003_ = ((size_t)5ULL);
v___x_1004_ = lean_usize_shift_right(v_x_988_, v___x_1003_);
v_x_987_ = v_node_1002_;
v_x_988_ = v___x_1004_;
goto _start;
}
default: 
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_box(0);
return v___x_1006_;
}
}
}
else
{
lean_object* v_ks_1007_; lean_object* v_vs_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_ks_1007_ = lean_ctor_get(v_x_987_, 0);
v_vs_1008_ = lean_ctor_get(v_x_987_, 1);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_1007_, v_vs_1008_, v___x_1009_, v_x_989_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
size_t v_x_11024__boxed_1014_; lean_object* v_res_1015_; 
v_x_11024__boxed_1014_ = lean_unbox_usize(v_x_1012_);
lean_dec(v_x_1012_);
v_res_1015_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1011_, v_x_11024__boxed_1014_, v_x_1013_);
lean_dec_ref(v_x_1013_);
lean_dec_ref(v_x_1011_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
uint64_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1017_);
v___x_1019_ = lean_uint64_to_usize(v___x_1018_);
v___x_1020_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1016_, v___x_1019_, v_x_1017_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1021_, v_x_1022_);
lean_dec_ref(v_x_1022_);
lean_dec_ref(v_x_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___y_1028_; lean_object* v___y_1033_; lean_object* v___y_1038_; lean_object* v___y_1043_; 
switch(lean_obj_tag(v_e_1024_))
{
case 4:
{
lean_object* v_declName_1047_; lean_object* v_map_1048_; lean_object* v_set_1049_; lean_object* v___x_1050_; 
v_declName_1047_ = lean_ctor_get(v_e_1024_, 0);
v_map_1048_ = lean_ctor_get(v_a_1026_, 0);
v_set_1049_ = lean_ctor_get(v_a_1026_, 1);
v___x_1050_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1049_, v_e_1024_);
if (lean_obj_tag(v___x_1050_) == 0)
{
uint8_t v___x_1051_; 
lean_inc(v_declName_1047_);
lean_inc_ref(v_a_1025_);
v___x_1051_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1025_, v_declName_1047_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
lean_inc_ref(v_set_1049_);
lean_inc_ref(v_map_1048_);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; lean_object* v_unused_1063_; 
v_unused_1062_ = lean_ctor_get(v_a_1026_, 1);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_a_1026_, 0);
lean_dec(v_unused_1063_);
v___x_1053_ = v_a_1026_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v_a_1026_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1055_ = lean_box(0);
lean_inc_ref(v_e_1024_);
v___x_1056_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(v_set_1049_, v_e_1024_, v___x_1055_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1056_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_map_1048_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_e_1024_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
return v___x_1059_;
}
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec_ref_known(v_e_1024_, 2);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_1026_);
return v___x_1065_;
}
}
else
{
lean_object* v_val_1066_; lean_object* v_fst_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref_known(v_e_1024_, 2);
v_val_1066_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v___x_1050_, 1);
v_fst_1067_ = lean_ctor_get(v_val_1066_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_val_1066_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v_val_1066_, 1);
lean_dec(v_unused_1075_);
v___x_1069_ = v_val_1066_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_fst_1067_);
lean_dec(v_val_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v_a_1026_);
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_fst_1067_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_a_1026_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
case 5:
{
lean_object* v_fn_1076_; lean_object* v_arg_1077_; lean_object* v_map_1078_; lean_object* v_set_1079_; lean_object* v___x_1080_; 
v_fn_1076_ = lean_ctor_get(v_e_1024_, 0);
v_arg_1077_ = lean_ctor_get(v_e_1024_, 1);
v_map_1078_ = lean_ctor_get(v_a_1026_, 0);
v_set_1079_ = lean_ctor_get(v_a_1026_, 1);
v___x_1080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1078_, v_e_1024_);
if (lean_obj_tag(v___x_1080_) == 1)
{
lean_object* v_val_1081_; lean_object* v___x_1082_; 
lean_dec_ref_known(v_e_1024_, 2);
v_val_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_val_1081_);
lean_ctor_set(v___x_1082_, 1, v_a_1026_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; uint64_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; uint8_t v___x_1089_; 
lean_dec(v___x_1080_);
v___x_1083_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1084_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1024_);
v___x_1085_ = lean_uint64_to_usize(v___x_1084_);
v___x_1086_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1079_, v___x_1085_, v_e_1024_, v___x_1083_);
v___x_1087_ = lean_ptr_addr(v___x_1086_);
v___x_1088_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1089_ = lean_usize_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec_ref_known(v_e_1024_, 2);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1086_);
lean_ctor_set(v___x_1090_, 1, v_a_1026_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
lean_dec_ref(v___x_1086_);
lean_inc_ref(v_fn_1076_);
v___x_1091_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_1076_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_a_1093_; lean_object* v___x_1094_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
v_a_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1091_, 2);
lean_inc_ref(v_arg_1077_);
v___x_1094_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_1077_, v_a_1025_, v_a_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v_a_1096_; uint8_t v___y_1098_; size_t v___x_1102_; size_t v___x_1103_; uint8_t v___x_1104_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
v_a_1096_ = lean_ctor_get(v___x_1094_, 1);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1094_, 2);
v___x_1102_ = lean_ptr_addr(v_fn_1076_);
v___x_1103_ = lean_ptr_addr(v_a_1092_);
v___x_1104_ = lean_usize_dec_eq(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
v___y_1098_ = v___x_1104_;
goto v___jp_1097_;
}
else
{
size_t v___x_1105_; size_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1105_ = lean_ptr_addr(v_arg_1077_);
v___x_1106_ = lean_ptr_addr(v_a_1095_);
v___x_1107_ = lean_usize_dec_eq(v___x_1105_, v___x_1106_);
v___y_1098_ = v___x_1107_;
goto v___jp_1097_;
}
v___jp_1097_:
{
if (v___y_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = l_Lean_Expr_app___override(v_a_1092_, v_a_1095_);
v___x_1100_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1099_, v_a_1096_);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; 
lean_dec(v_a_1095_);
lean_dec(v_a_1092_);
lean_inc_ref(v_e_1024_);
v___x_1101_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_e_1024_, v_a_1096_);
return v___x_1101_;
}
}
}
else
{
lean_dec(v_a_1092_);
v___y_1038_ = v___x_1094_;
goto v___jp_1037_;
}
}
else
{
v___y_1038_ = v___x_1091_;
goto v___jp_1037_;
}
}
}
}
case 6:
{
lean_object* v_binderName_1108_; lean_object* v_binderType_1109_; lean_object* v_body_1110_; uint8_t v_binderInfo_1111_; lean_object* v_map_1112_; lean_object* v_set_1113_; lean_object* v___x_1114_; 
v_binderName_1108_ = lean_ctor_get(v_e_1024_, 0);
v_binderType_1109_ = lean_ctor_get(v_e_1024_, 1);
v_body_1110_ = lean_ctor_get(v_e_1024_, 2);
v_binderInfo_1111_ = lean_ctor_get_uint8(v_e_1024_, sizeof(void*)*3 + 8);
v_map_1112_ = lean_ctor_get(v_a_1026_, 0);
v_set_1113_ = lean_ctor_get(v_a_1026_, 1);
v___x_1114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1112_, v_e_1024_);
if (lean_obj_tag(v___x_1114_) == 1)
{
lean_object* v_val_1115_; lean_object* v___x_1116_; 
lean_dec_ref_known(v_e_1024_, 3);
v_val_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_val_1115_);
lean_ctor_set(v___x_1116_, 1, v_a_1026_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; uint64_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; uint8_t v___x_1123_; 
lean_dec(v___x_1114_);
v___x_1117_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1118_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1024_);
v___x_1119_ = lean_uint64_to_usize(v___x_1118_);
v___x_1120_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1113_, v___x_1119_, v_e_1024_, v___x_1117_);
v___x_1121_ = lean_ptr_addr(v___x_1120_);
v___x_1122_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1123_ = lean_usize_dec_eq(v___x_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref_known(v_e_1024_, 3);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1120_);
lean_ctor_set(v___x_1124_, 1, v_a_1026_);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; 
lean_dec_ref(v___x_1120_);
lean_inc_ref(v_binderType_1109_);
v___x_1125_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_1109_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
v_a_1127_ = lean_ctor_get(v___x_1125_, 1);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1125_, 2);
lean_inc_ref(v_body_1110_);
v___x_1128_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_1110_, v_a_1025_, v_a_1127_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v_a_1130_; uint8_t v___y_1132_; size_t v___x_1139_; size_t v___x_1140_; uint8_t v___x_1141_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
v_a_1130_ = lean_ctor_get(v___x_1128_, 1);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1128_, 2);
v___x_1139_ = lean_ptr_addr(v_binderType_1109_);
v___x_1140_ = lean_ptr_addr(v_a_1126_);
v___x_1141_ = lean_usize_dec_eq(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
v___y_1132_ = v___x_1141_;
goto v___jp_1131_;
}
else
{
size_t v___x_1142_; size_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_ptr_addr(v_body_1110_);
v___x_1143_ = lean_ptr_addr(v_a_1129_);
v___x_1144_ = lean_usize_dec_eq(v___x_1142_, v___x_1143_);
v___y_1132_ = v___x_1144_;
goto v___jp_1131_;
}
v___jp_1131_:
{
if (v___y_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_inc(v_binderName_1108_);
v___x_1133_ = l_Lean_Expr_lam___override(v_binderName_1108_, v_a_1126_, v_a_1129_, v_binderInfo_1111_);
v___x_1134_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1133_, v_a_1130_);
return v___x_1134_;
}
else
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1111_, v_binderInfo_1111_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_inc(v_binderName_1108_);
v___x_1136_ = l_Lean_Expr_lam___override(v_binderName_1108_, v_a_1126_, v_a_1129_, v_binderInfo_1111_);
v___x_1137_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1136_, v_a_1130_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; 
lean_dec(v_a_1129_);
lean_dec(v_a_1126_);
lean_inc_ref(v_e_1024_);
v___x_1138_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_e_1024_, v_a_1130_);
return v___x_1138_;
}
}
}
}
else
{
lean_dec(v_a_1126_);
v___y_1033_ = v___x_1128_;
goto v___jp_1032_;
}
}
else
{
v___y_1033_ = v___x_1125_;
goto v___jp_1032_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1145_; lean_object* v_binderType_1146_; lean_object* v_body_1147_; uint8_t v_binderInfo_1148_; lean_object* v_map_1149_; lean_object* v_set_1150_; lean_object* v___x_1151_; 
v_binderName_1145_ = lean_ctor_get(v_e_1024_, 0);
v_binderType_1146_ = lean_ctor_get(v_e_1024_, 1);
v_body_1147_ = lean_ctor_get(v_e_1024_, 2);
v_binderInfo_1148_ = lean_ctor_get_uint8(v_e_1024_, sizeof(void*)*3 + 8);
v_map_1149_ = lean_ctor_get(v_a_1026_, 0);
v_set_1150_ = lean_ctor_get(v_a_1026_, 1);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1149_, v_e_1024_);
if (lean_obj_tag(v___x_1151_) == 1)
{
lean_object* v_val_1152_; lean_object* v___x_1153_; 
lean_dec_ref_known(v_e_1024_, 3);
v_val_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_val_1152_);
lean_ctor_set(v___x_1153_, 1, v_a_1026_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; uint64_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; uint8_t v___x_1160_; 
lean_dec(v___x_1151_);
v___x_1154_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1155_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1024_);
v___x_1156_ = lean_uint64_to_usize(v___x_1155_);
v___x_1157_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1150_, v___x_1156_, v_e_1024_, v___x_1154_);
v___x_1158_ = lean_ptr_addr(v___x_1157_);
v___x_1159_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1160_ = lean_usize_dec_eq(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref_known(v_e_1024_, 3);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1157_);
lean_ctor_set(v___x_1161_, 1, v_a_1026_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; 
lean_dec_ref(v___x_1157_);
lean_inc_ref(v_binderType_1146_);
v___x_1162_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_1146_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_a_1164_; lean_object* v___x_1165_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
v_a_1164_ = lean_ctor_get(v___x_1162_, 1);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1162_, 2);
lean_inc_ref(v_body_1147_);
v___x_1165_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_1147_, v_a_1025_, v_a_1164_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_a_1167_; uint8_t v___y_1169_; size_t v___x_1176_; size_t v___x_1177_; uint8_t v___x_1178_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
v_a_1167_ = lean_ctor_get(v___x_1165_, 1);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1165_, 2);
v___x_1176_ = lean_ptr_addr(v_binderType_1146_);
v___x_1177_ = lean_ptr_addr(v_a_1163_);
v___x_1178_ = lean_usize_dec_eq(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
v___y_1169_ = v___x_1178_;
goto v___jp_1168_;
}
else
{
size_t v___x_1179_; size_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = lean_ptr_addr(v_body_1147_);
v___x_1180_ = lean_ptr_addr(v_a_1166_);
v___x_1181_ = lean_usize_dec_eq(v___x_1179_, v___x_1180_);
v___y_1169_ = v___x_1181_;
goto v___jp_1168_;
}
v___jp_1168_:
{
if (v___y_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_inc(v_binderName_1145_);
v___x_1170_ = l_Lean_Expr_forallE___override(v_binderName_1145_, v_a_1163_, v_a_1166_, v_binderInfo_1148_);
v___x_1171_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1170_, v_a_1167_);
return v___x_1171_;
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1148_, v_binderInfo_1148_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc(v_binderName_1145_);
v___x_1173_ = l_Lean_Expr_forallE___override(v_binderName_1145_, v_a_1163_, v_a_1166_, v_binderInfo_1148_);
v___x_1174_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1173_, v_a_1167_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; 
lean_dec(v_a_1166_);
lean_dec(v_a_1163_);
lean_inc_ref(v_e_1024_);
v___x_1175_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_e_1024_, v_a_1167_);
return v___x_1175_;
}
}
}
}
else
{
lean_dec(v_a_1163_);
v___y_1043_ = v___x_1165_;
goto v___jp_1042_;
}
}
else
{
v___y_1043_ = v___x_1162_;
goto v___jp_1042_;
}
}
}
}
case 8:
{
lean_object* v_declName_1182_; lean_object* v_type_1183_; lean_object* v_value_1184_; lean_object* v_body_1185_; uint8_t v_nondep_1186_; lean_object* v_map_1187_; lean_object* v_set_1188_; lean_object* v___x_1189_; 
v_declName_1182_ = lean_ctor_get(v_e_1024_, 0);
v_type_1183_ = lean_ctor_get(v_e_1024_, 1);
v_value_1184_ = lean_ctor_get(v_e_1024_, 2);
v_body_1185_ = lean_ctor_get(v_e_1024_, 3);
v_nondep_1186_ = lean_ctor_get_uint8(v_e_1024_, sizeof(void*)*4 + 8);
v_map_1187_ = lean_ctor_get(v_a_1026_, 0);
v_set_1188_ = lean_ctor_get(v_a_1026_, 1);
v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1187_, v_e_1024_);
if (lean_obj_tag(v___x_1189_) == 1)
{
lean_object* v_val_1190_; lean_object* v___x_1191_; 
lean_dec_ref_known(v_e_1024_, 4);
v_val_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_val_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_val_1190_);
lean_ctor_set(v___x_1191_, 1, v_a_1026_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; uint64_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; uint8_t v___x_1198_; 
lean_dec(v___x_1189_);
v___x_1192_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1193_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1024_);
v___x_1194_ = lean_uint64_to_usize(v___x_1193_);
v___x_1195_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1188_, v___x_1194_, v_e_1024_, v___x_1192_);
v___x_1196_ = lean_ptr_addr(v___x_1195_);
v___x_1197_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1198_ = lean_usize_dec_eq(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref_known(v_e_1024_, 4);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1195_);
lean_ctor_set(v___x_1199_, 1, v_a_1026_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; 
lean_dec_ref(v___x_1195_);
lean_inc_ref(v_type_1183_);
v___x_1200_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_1183_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_a_1202_; lean_object* v___x_1203_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
v_a_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1200_, 2);
lean_inc_ref(v_value_1184_);
v___x_1203_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_1184_, v_a_1025_, v_a_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v_a_1205_; lean_object* v___x_1206_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
v_a_1205_ = lean_ctor_get(v___x_1203_, 1);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1203_, 2);
lean_inc_ref(v_body_1185_);
v___x_1206_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_1185_, v_a_1025_, v_a_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v_a_1208_; uint8_t v___y_1210_; size_t v___x_1219_; size_t v___x_1220_; uint8_t v___x_1221_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
v_a_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1206_, 2);
v___x_1219_ = lean_ptr_addr(v_type_1183_);
v___x_1220_ = lean_ptr_addr(v_a_1201_);
v___x_1221_ = lean_usize_dec_eq(v___x_1219_, v___x_1220_);
if (v___x_1221_ == 0)
{
v___y_1210_ = v___x_1221_;
goto v___jp_1209_;
}
else
{
size_t v___x_1222_; size_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = lean_ptr_addr(v_value_1184_);
v___x_1223_ = lean_ptr_addr(v_a_1204_);
v___x_1224_ = lean_usize_dec_eq(v___x_1222_, v___x_1223_);
v___y_1210_ = v___x_1224_;
goto v___jp_1209_;
}
v___jp_1209_:
{
if (v___y_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_inc(v_declName_1182_);
v___x_1211_ = l_Lean_Expr_letE___override(v_declName_1182_, v_a_1201_, v_a_1204_, v_a_1207_, v_nondep_1186_);
v___x_1212_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1211_, v_a_1208_);
return v___x_1212_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1213_ = lean_ptr_addr(v_body_1185_);
v___x_1214_ = lean_ptr_addr(v_a_1207_);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_inc(v_declName_1182_);
v___x_1216_ = l_Lean_Expr_letE___override(v_declName_1182_, v_a_1201_, v_a_1204_, v_a_1207_, v_nondep_1186_);
v___x_1217_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1216_, v_a_1208_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; 
lean_dec(v_a_1207_);
lean_dec(v_a_1204_);
lean_dec(v_a_1201_);
lean_inc_ref(v_e_1024_);
v___x_1218_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_e_1024_, v_a_1208_);
return v___x_1218_;
}
}
}
}
else
{
lean_dec(v_a_1204_);
lean_dec(v_a_1201_);
v___y_1028_ = v___x_1206_;
goto v___jp_1027_;
}
}
else
{
lean_dec(v_a_1201_);
v___y_1028_ = v___x_1203_;
goto v___jp_1027_;
}
}
else
{
v___y_1028_ = v___x_1200_;
goto v___jp_1027_;
}
}
}
}
case 10:
{
lean_object* v_data_1225_; lean_object* v_expr_1226_; lean_object* v_map_1227_; lean_object* v_set_1228_; lean_object* v___x_1229_; 
v_data_1225_ = lean_ctor_get(v_e_1024_, 0);
v_expr_1226_ = lean_ctor_get(v_e_1024_, 1);
v_map_1227_ = lean_ctor_get(v_a_1026_, 0);
v_set_1228_ = lean_ctor_get(v_a_1026_, 1);
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1227_, v_e_1024_);
if (lean_obj_tag(v___x_1229_) == 1)
{
lean_object* v_val_1230_; lean_object* v___x_1231_; 
lean_dec_ref_known(v_e_1024_, 2);
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_val_1230_);
lean_ctor_set(v___x_1231_, 1, v_a_1026_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; uint64_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; uint8_t v___x_1238_; 
lean_dec(v___x_1229_);
v___x_1232_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1233_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1024_);
v___x_1234_ = lean_uint64_to_usize(v___x_1233_);
v___x_1235_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1228_, v___x_1234_, v_e_1024_, v___x_1232_);
v___x_1236_ = lean_ptr_addr(v___x_1235_);
v___x_1237_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1238_ = lean_usize_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref_known(v_e_1024_, 2);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1235_);
lean_ctor_set(v___x_1239_, 1, v_a_1026_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v___x_1235_);
lean_inc_ref(v_expr_1226_);
v___x_1240_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1226_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v_a_1242_; size_t v___x_1243_; size_t v___x_1244_; uint8_t v___x_1245_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
v_a_1242_ = lean_ctor_get(v___x_1240_, 1);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1240_, 2);
v___x_1243_ = lean_ptr_addr(v_expr_1226_);
v___x_1244_ = lean_ptr_addr(v_a_1241_);
v___x_1245_ = lean_usize_dec_eq(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_inc(v_data_1225_);
v___x_1246_ = l_Lean_Expr_mdata___override(v_data_1225_, v_a_1241_);
v___x_1247_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1246_, v_a_1242_);
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; 
lean_dec(v_a_1241_);
lean_inc_ref(v_e_1024_);
v___x_1248_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_e_1024_, v_a_1242_);
return v___x_1248_;
}
}
else
{
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1249_; lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1249_);
v_a_1250_ = lean_ctor_get(v___x_1240_, 1);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1240_, 2);
v___x_1251_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_a_1249_, v_a_1250_);
return v___x_1251_;
}
else
{
lean_dec_ref_known(v_e_1024_, 2);
return v___x_1240_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1252_; lean_object* v_idx_1253_; lean_object* v_struct_1254_; lean_object* v_map_1255_; lean_object* v_set_1256_; lean_object* v___x_1257_; 
v_typeName_1252_ = lean_ctor_get(v_e_1024_, 0);
v_idx_1253_ = lean_ctor_get(v_e_1024_, 1);
v_struct_1254_ = lean_ctor_get(v_e_1024_, 2);
v_map_1255_ = lean_ctor_get(v_a_1026_, 0);
v_set_1256_ = lean_ctor_get(v_a_1026_, 1);
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1255_, v_e_1024_);
if (lean_obj_tag(v___x_1257_) == 1)
{
lean_object* v_val_1258_; lean_object* v___x_1259_; 
lean_dec_ref_known(v_e_1024_, 3);
v_val_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_val_1258_);
lean_ctor_set(v___x_1259_, 1, v_a_1026_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; uint64_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; uint8_t v___x_1266_; 
lean_dec(v___x_1257_);
v___x_1260_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1261_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1024_);
v___x_1262_ = lean_uint64_to_usize(v___x_1261_);
v___x_1263_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1256_, v___x_1262_, v_e_1024_, v___x_1260_);
v___x_1264_ = lean_ptr_addr(v___x_1263_);
v___x_1265_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1266_ = lean_usize_dec_eq(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref_known(v_e_1024_, 3);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1263_);
lean_ctor_set(v___x_1267_, 1, v_a_1026_);
return v___x_1267_;
}
else
{
uint8_t v_checkProj_1268_; 
lean_dec_ref(v___x_1263_);
v_checkProj_1268_ = lean_ctor_get_uint8(v_a_1025_, sizeof(void*)*1 + 1);
if (v_checkProj_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_inc_ref(v_struct_1254_);
v___x_1269_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1254_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v_a_1271_; size_t v___x_1272_; size_t v___x_1273_; uint8_t v___x_1274_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
v_a_1271_ = lean_ctor_get(v___x_1269_, 1);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1269_, 2);
v___x_1272_ = lean_ptr_addr(v_struct_1254_);
v___x_1273_ = lean_ptr_addr(v_a_1270_);
v___x_1274_ = lean_usize_dec_eq(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_inc(v_idx_1253_);
lean_inc(v_typeName_1252_);
v___x_1275_ = l_Lean_Expr_proj___override(v_typeName_1252_, v_idx_1253_, v_a_1270_);
v___x_1276_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v___x_1275_, v_a_1271_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; 
lean_dec(v_a_1270_);
lean_inc_ref(v_e_1024_);
v___x_1277_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_e_1024_, v_a_1271_);
return v___x_1277_;
}
}
else
{
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1278_; lean_object* v_a_1279_; lean_object* v___x_1280_; 
v_a_1278_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1278_);
v_a_1279_ = lean_ctor_get(v___x_1269_, 1);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1269_, 2);
v___x_1280_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_a_1278_, v_a_1279_);
return v___x_1280_;
}
else
{
lean_dec_ref_known(v_e_1024_, 3);
return v___x_1269_;
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec_ref_known(v_e_1024_, 3);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_a_1026_);
return v___x_1282_;
}
}
}
}
default: 
{
lean_object* v_map_1283_; lean_object* v_set_1284_; lean_object* v___x_1285_; 
v_map_1283_ = lean_ctor_get(v_a_1026_, 0);
v_set_1284_ = lean_ctor_get(v_a_1026_, 1);
v___x_1285_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1284_, v_e_1024_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1295_; 
lean_inc_ref(v_set_1284_);
lean_inc_ref(v_map_1283_);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1296_ = lean_ctor_get(v_a_1026_, 1);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_a_1026_, 0);
lean_dec(v_unused_1297_);
v___x_1287_ = v_a_1026_;
v_isShared_1288_ = v_isSharedCheck_1295_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v_a_1026_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1295_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1289_ = lean_box(0);
lean_inc_ref(v_e_1024_);
v___x_1290_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(v_set_1284_, v_e_1024_, v___x_1289_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1290_);
v___x_1292_ = v___x_1287_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_map_1283_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v_e_1024_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
return v___x_1293_;
}
}
}
else
{
lean_object* v_val_1298_; lean_object* v_fst_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_e_1024_);
v_val_1298_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v___x_1285_, 1);
v_fst_1299_ = lean_ctor_get(v_val_1298_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_val_1298_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_val_1298_, 1);
lean_dec(v_unused_1307_);
v___x_1301_ = v_val_1298_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_fst_1299_);
lean_dec(v_val_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v_a_1026_);
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_fst_1299_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_a_1026_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
v___jp_1027_:
{
if (lean_obj_tag(v___y_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1029_ = lean_ctor_get(v___y_1028_, 0);
lean_inc(v_a_1029_);
v_a_1030_ = lean_ctor_get(v___y_1028_, 1);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___y_1028_, 2);
v___x_1031_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_a_1029_, v_a_1030_);
return v___x_1031_;
}
else
{
lean_dec_ref(v_e_1024_);
return v___y_1028_;
}
}
v___jp_1032_:
{
if (lean_obj_tag(v___y_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1034_ = lean_ctor_get(v___y_1033_, 0);
lean_inc(v_a_1034_);
v_a_1035_ = lean_ctor_get(v___y_1033_, 1);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___y_1033_, 2);
v___x_1036_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_a_1034_, v_a_1035_);
return v___x_1036_;
}
else
{
lean_dec_ref(v_e_1024_);
return v___y_1033_;
}
}
v___jp_1037_:
{
if (lean_obj_tag(v___y_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1039_ = lean_ctor_get(v___y_1038_, 0);
lean_inc(v_a_1039_);
v_a_1040_ = lean_ctor_get(v___y_1038_, 1);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___y_1038_, 2);
v___x_1041_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_a_1039_, v_a_1040_);
return v___x_1041_;
}
else
{
lean_dec_ref(v_e_1024_);
return v___y_1038_;
}
}
v___jp_1042_:
{
if (lean_obj_tag(v___y_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v_a_1045_; lean_object* v___x_1046_; 
v_a_1044_ = lean_ctor_get(v___y_1043_, 0);
lean_inc(v_a_1044_);
v_a_1045_ = lean_ctor_get(v___y_1043_, 1);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___y_1043_, 2);
v___x_1046_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_1024_, v_a_1044_, v_a_1045_);
return v___x_1046_;
}
else
{
lean_dec_ref(v_e_1024_);
return v___y_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1308_, v_a_1309_, v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1313_, v_x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1316_, v_x_1317_, v_x_1318_);
lean_dec_ref(v_x_1318_);
lean_dec_ref(v_x_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1320_, lean_object* v_m_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1321_, v_a_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1324_, lean_object* v_m_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1324_, v_m_1325_, v_a_1326_);
lean_dec_ref(v_a_1326_);
lean_dec_ref(v_m_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1328_, lean_object* v_x_1329_, size_t v_x_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1329_, v_x_1330_, v_x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v_x_11670__boxed_1337_; lean_object* v_res_1338_; 
v_x_11670__boxed_1337_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_res_1338_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1333_, v_x_1334_, v_x_11670__boxed_1337_, v_x_1336_);
lean_dec_ref(v_x_1336_);
lean_dec_ref(v_x_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1339_, lean_object* v_m_1340_, lean_object* v_query_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_m_1340_, v_query_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1343_, lean_object* v_m_1344_, lean_object* v_query_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1343_, v_m_1344_, v_query_1345_);
lean_dec_ref(v_query_1345_);
lean_dec_ref(v_m_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1347_, lean_object* v_keys_1348_, lean_object* v_vals_1349_, lean_object* v_heq_1350_, lean_object* v_i_1351_, lean_object* v_k_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1348_, v_vals_1349_, v_i_1351_, v_k_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1354_, lean_object* v_keys_1355_, lean_object* v_vals_1356_, lean_object* v_heq_1357_, lean_object* v_i_1358_, lean_object* v_k_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1354_, v_keys_1355_, v_vals_1356_, v_heq_1357_, v_i_1358_, v_k_1359_);
lean_dec_ref(v_k_1359_);
lean_dec_ref(v_vals_1356_);
lean_dec_ref(v_keys_1355_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1361_, lean_object* v_cache_1362_, lean_object* v_ctx_1363_, lean_object* v_s_1364_){
_start:
{
lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; 
v___f_1365_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1366_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1361_);
v___x_1367_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1365_, v___f_1366_, v_s_1364_, v_e_1361_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_cache_1362_);
lean_ctor_set(v___x_1368_, 1, v_s_1364_);
v___x_1369_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1361_, v_ctx_1363_, v___x_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 1);
v_a_1371_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1373_ = v___x_1369_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1370_);
lean_inc(v_a_1371_);
lean_dec(v___x_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_set_1375_; lean_object* v___x_1377_; 
v_set_1375_ = lean_ctor_get(v_a_1370_, 1);
lean_inc_ref(v_set_1375_);
lean_dec(v_a_1370_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v_set_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1371_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_set_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1389_; 
v_a_1380_ = lean_ctor_get(v___x_1369_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; 
v_unused_1390_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1390_);
v___x_1382_ = v___x_1369_;
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1369_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_map_1384_; lean_object* v_set_1385_; lean_object* v___x_1387_; 
v_map_1384_ = lean_ctor_get(v_a_1380_, 0);
lean_inc_ref(v_map_1384_);
v_set_1385_ = lean_ctor_get(v_a_1380_, 1);
lean_inc_ref(v_set_1385_);
lean_dec(v_a_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v_set_1385_);
lean_ctor_set(v___x_1382_, 0, v_map_1384_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_map_1384_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_set_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_val_1391_; lean_object* v_fst_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_cache_1362_);
lean_dec_ref(v_e_1361_);
v_val_1391_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___x_1367_, 1);
v_fst_1392_ = lean_ctor_get(v_val_1391_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_val_1391_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_val_1391_, 1);
lean_dec(v_unused_1400_);
v___x_1394_ = v_val_1391_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_fst_1392_);
lean_dec(v_val_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v_s_1364_);
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_fst_1392_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_s_1364_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1401_, lean_object* v_cache_1402_, lean_object* v_ctx_1403_, lean_object* v_s_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1401_, v_cache_1402_, v_ctx_1403_, v_s_1404_);
lean_dec_ref(v_ctx_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1408_; uint64_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1408_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1409_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1406_);
v___x_1410_ = lean_uint64_to_usize(v___x_1409_);
v___x_1411_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1407_, v___x_1410_, v_e_1406_, v___x_1408_);
v___x_1412_ = lean_ptr_addr(v___x_1411_);
v___x_1413_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref(v_e_1406_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1411_);
lean_ctor_set(v___x_1415_, 1, v_a_1407_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v___x_1411_);
v___x_1416_ = lean_box(0);
lean_inc_ref(v_e_1406_);
v___x_1417_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(v_a_1407_, v_e_1406_, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_e_1406_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1419_, v_a_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1423_, v_a_1424_, v_a_1425_);
lean_dec_ref(v_a_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1427_, lean_object* v_k_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v___f_1431_; lean_object* v___x_1432_; uint64_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; uint8_t v___x_1438_; 
v___f_1431_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1432_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1433_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1427_);
v___x_1434_ = lean_uint64_to_usize(v___x_1433_);
lean_inc_ref(v_a_1430_);
v___x_1435_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1431_, v_a_1430_, v___x_1434_, v_e_1427_, v___x_1432_);
v___x_1436_ = lean_ptr_addr(v___x_1435_);
v___x_1437_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1438_ = lean_usize_dec_eq(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_dec_ref(v_k_1428_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1435_);
lean_ctor_set(v___x_1439_, 1, v_a_1430_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec(v___x_1435_);
lean_inc_ref(v_a_1429_);
v___x_1440_ = lean_apply_2(v_k_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v_a_1442_; lean_object* v___x_1443_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
v_a_1442_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1440_, 2);
v___x_1443_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1441_, v_a_1442_);
return v___x_1443_;
}
else
{
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1444_, lean_object* v_k_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1444_, v_k_1445_, v_a_1446_, v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1448_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v_cellCount_1449_; lean_object* v___x_1450_; 
v_cellCount_1449_ = lean_unsigned_to_nat(16u);
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v_cellCount_1451_; lean_object* v___x_1452_; 
v_cellCount_1451_ = lean_unsigned_to_nat(16u);
v___x_1452_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1453_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1454_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v___x_1454_);
lean_ctor_set(v___x_1456_, 2, v___x_1453_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___y_1461_; lean_object* v___y_1466_; lean_object* v___y_1471_; lean_object* v___y_1476_; 
switch(lean_obj_tag(v_e_1457_))
{
case 4:
{
lean_object* v_declName_1480_; lean_object* v___x_1481_; uint64_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v_declName_1480_ = lean_ctor_get(v_e_1457_, 0);
v___x_1481_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1482_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1457_);
v___x_1483_ = lean_uint64_to_usize(v___x_1482_);
v___x_1484_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1459_, v___x_1483_, v_e_1457_, v___x_1481_);
v___x_1485_ = lean_ptr_addr(v___x_1484_);
v___x_1486_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
lean_dec_ref_known(v_e_1457_, 2);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1484_);
lean_ctor_set(v___x_1488_, 1, v_a_1459_);
return v___x_1488_;
}
else
{
uint8_t v___x_1489_; 
lean_dec_ref(v___x_1484_);
lean_inc(v_declName_1480_);
lean_inc_ref(v_a_1458_);
v___x_1489_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1458_, v_declName_1480_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_box(0);
lean_inc_ref(v_e_1457_);
v___x_1491_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__3___redArg(v_a_1459_, v_e_1457_, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_e_1457_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref_known(v_e_1457_, 2);
v___x_1493_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2);
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v_a_1459_);
return v___x_1494_;
}
}
}
case 5:
{
lean_object* v_fn_1495_; lean_object* v_arg_1496_; lean_object* v___x_1497_; uint64_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; uint8_t v___x_1503_; 
v_fn_1495_ = lean_ctor_get(v_e_1457_, 0);
v_arg_1496_ = lean_ctor_get(v_e_1457_, 1);
v___x_1497_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1498_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1457_);
v___x_1499_ = lean_uint64_to_usize(v___x_1498_);
v___x_1500_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1459_, v___x_1499_, v_e_1457_, v___x_1497_);
v___x_1501_ = lean_ptr_addr(v___x_1500_);
v___x_1502_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1503_ = lean_usize_dec_eq(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_dec_ref_known(v_e_1457_, 2);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1500_);
lean_ctor_set(v___x_1504_, 1, v_a_1459_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; 
lean_dec_ref(v___x_1500_);
lean_inc_ref(v_fn_1495_);
v___x_1505_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1495_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v_a_1507_; lean_object* v___x_1508_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
v_a_1507_ = lean_ctor_get(v___x_1505_, 1);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1505_, 2);
lean_inc_ref(v_arg_1496_);
v___x_1508_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1496_, v_a_1458_, v_a_1507_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v_a_1510_; uint8_t v___y_1512_; size_t v___x_1516_; size_t v___x_1517_; uint8_t v___x_1518_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
v_a_1510_ = lean_ctor_get(v___x_1508_, 1);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1508_, 2);
v___x_1516_ = lean_ptr_addr(v_fn_1495_);
v___x_1517_ = lean_ptr_addr(v_a_1506_);
v___x_1518_ = lean_usize_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
v___y_1512_ = v___x_1518_;
goto v___jp_1511_;
}
else
{
size_t v___x_1519_; size_t v___x_1520_; uint8_t v___x_1521_; 
v___x_1519_ = lean_ptr_addr(v_arg_1496_);
v___x_1520_ = lean_ptr_addr(v_a_1509_);
v___x_1521_ = lean_usize_dec_eq(v___x_1519_, v___x_1520_);
v___y_1512_ = v___x_1521_;
goto v___jp_1511_;
}
v___jp_1511_:
{
if (v___y_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref_known(v_e_1457_, 2);
v___x_1513_ = l_Lean_Expr_app___override(v_a_1506_, v_a_1509_);
v___x_1514_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1513_, v_a_1510_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_a_1509_);
lean_dec(v_a_1506_);
v___x_1515_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1457_, v_a_1510_);
return v___x_1515_;
}
}
}
else
{
lean_dec(v_a_1506_);
lean_dec_ref_known(v_e_1457_, 2);
v___y_1471_ = v___x_1508_;
goto v___jp_1470_;
}
}
else
{
lean_dec_ref_known(v_e_1457_, 2);
v___y_1471_ = v___x_1505_;
goto v___jp_1470_;
}
}
}
case 6:
{
lean_object* v_binderName_1522_; lean_object* v_binderType_1523_; lean_object* v_body_1524_; uint8_t v_binderInfo_1525_; lean_object* v___x_1526_; uint64_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; uint8_t v___x_1532_; 
v_binderName_1522_ = lean_ctor_get(v_e_1457_, 0);
v_binderType_1523_ = lean_ctor_get(v_e_1457_, 1);
v_body_1524_ = lean_ctor_get(v_e_1457_, 2);
v_binderInfo_1525_ = lean_ctor_get_uint8(v_e_1457_, sizeof(void*)*3 + 8);
v___x_1526_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1527_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1457_);
v___x_1528_ = lean_uint64_to_usize(v___x_1527_);
v___x_1529_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1459_, v___x_1528_, v_e_1457_, v___x_1526_);
v___x_1530_ = lean_ptr_addr(v___x_1529_);
v___x_1531_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1532_ = lean_usize_dec_eq(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_dec_ref_known(v_e_1457_, 3);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1529_);
lean_ctor_set(v___x_1533_, 1, v_a_1459_);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; 
lean_dec_ref(v___x_1529_);
lean_inc_ref(v_binderType_1523_);
v___x_1534_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1523_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
v_a_1536_ = lean_ctor_get(v___x_1534_, 1);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1534_, 2);
lean_inc_ref(v_body_1524_);
v___x_1537_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1524_, v_a_1458_, v_a_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v_a_1539_; uint8_t v___y_1541_; size_t v___x_1548_; size_t v___x_1549_; uint8_t v___x_1550_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
v_a_1539_ = lean_ctor_get(v___x_1537_, 1);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1537_, 2);
v___x_1548_ = lean_ptr_addr(v_binderType_1523_);
v___x_1549_ = lean_ptr_addr(v_a_1535_);
v___x_1550_ = lean_usize_dec_eq(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
v___y_1541_ = v___x_1550_;
goto v___jp_1540_;
}
else
{
size_t v___x_1551_; size_t v___x_1552_; uint8_t v___x_1553_; 
v___x_1551_ = lean_ptr_addr(v_body_1524_);
v___x_1552_ = lean_ptr_addr(v_a_1538_);
v___x_1553_ = lean_usize_dec_eq(v___x_1551_, v___x_1552_);
v___y_1541_ = v___x_1553_;
goto v___jp_1540_;
}
v___jp_1540_:
{
if (v___y_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_inc(v_binderName_1522_);
lean_dec_ref_known(v_e_1457_, 3);
v___x_1542_ = l_Lean_Expr_lam___override(v_binderName_1522_, v_a_1535_, v_a_1538_, v_binderInfo_1525_);
v___x_1543_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1542_, v_a_1539_);
return v___x_1543_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1525_, v_binderInfo_1525_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc(v_binderName_1522_);
lean_dec_ref_known(v_e_1457_, 3);
v___x_1545_ = l_Lean_Expr_lam___override(v_binderName_1522_, v_a_1535_, v_a_1538_, v_binderInfo_1525_);
v___x_1546_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1545_, v_a_1539_);
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; 
lean_dec(v_a_1538_);
lean_dec(v_a_1535_);
v___x_1547_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1457_, v_a_1539_);
return v___x_1547_;
}
}
}
}
else
{
lean_dec(v_a_1535_);
lean_dec_ref_known(v_e_1457_, 3);
v___y_1466_ = v___x_1537_;
goto v___jp_1465_;
}
}
else
{
lean_dec_ref_known(v_e_1457_, 3);
v___y_1466_ = v___x_1534_;
goto v___jp_1465_;
}
}
}
case 7:
{
lean_object* v_binderName_1554_; lean_object* v_binderType_1555_; lean_object* v_body_1556_; uint8_t v_binderInfo_1557_; lean_object* v___x_1558_; uint64_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; size_t v___x_1562_; size_t v___x_1563_; uint8_t v___x_1564_; 
v_binderName_1554_ = lean_ctor_get(v_e_1457_, 0);
v_binderType_1555_ = lean_ctor_get(v_e_1457_, 1);
v_body_1556_ = lean_ctor_get(v_e_1457_, 2);
v_binderInfo_1557_ = lean_ctor_get_uint8(v_e_1457_, sizeof(void*)*3 + 8);
v___x_1558_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1559_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1457_);
v___x_1560_ = lean_uint64_to_usize(v___x_1559_);
v___x_1561_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1459_, v___x_1560_, v_e_1457_, v___x_1558_);
v___x_1562_ = lean_ptr_addr(v___x_1561_);
v___x_1563_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1564_ = lean_usize_dec_eq(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref_known(v_e_1457_, 3);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1561_);
lean_ctor_set(v___x_1565_, 1, v_a_1459_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; 
lean_dec_ref(v___x_1561_);
lean_inc_ref(v_binderType_1555_);
v___x_1566_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1555_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v_a_1568_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
v_a_1568_ = lean_ctor_get(v___x_1566_, 1);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1566_, 2);
lean_inc_ref(v_body_1556_);
v___x_1569_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1556_, v_a_1458_, v_a_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_a_1571_; uint8_t v___y_1573_; size_t v___x_1580_; size_t v___x_1581_; uint8_t v___x_1582_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
v_a_1571_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1569_, 2);
v___x_1580_ = lean_ptr_addr(v_binderType_1555_);
v___x_1581_ = lean_ptr_addr(v_a_1567_);
v___x_1582_ = lean_usize_dec_eq(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
v___y_1573_ = v___x_1582_;
goto v___jp_1572_;
}
else
{
size_t v___x_1583_; size_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1583_ = lean_ptr_addr(v_body_1556_);
v___x_1584_ = lean_ptr_addr(v_a_1570_);
v___x_1585_ = lean_usize_dec_eq(v___x_1583_, v___x_1584_);
v___y_1573_ = v___x_1585_;
goto v___jp_1572_;
}
v___jp_1572_:
{
if (v___y_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_inc(v_binderName_1554_);
lean_dec_ref_known(v_e_1457_, 3);
v___x_1574_ = l_Lean_Expr_forallE___override(v_binderName_1554_, v_a_1567_, v_a_1570_, v_binderInfo_1557_);
v___x_1575_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1574_, v_a_1571_);
return v___x_1575_;
}
else
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1557_, v_binderInfo_1557_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_inc(v_binderName_1554_);
lean_dec_ref_known(v_e_1457_, 3);
v___x_1577_ = l_Lean_Expr_forallE___override(v_binderName_1554_, v_a_1567_, v_a_1570_, v_binderInfo_1557_);
v___x_1578_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1577_, v_a_1571_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; 
lean_dec(v_a_1570_);
lean_dec(v_a_1567_);
v___x_1579_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1457_, v_a_1571_);
return v___x_1579_;
}
}
}
}
else
{
lean_dec(v_a_1567_);
lean_dec_ref_known(v_e_1457_, 3);
v___y_1476_ = v___x_1569_;
goto v___jp_1475_;
}
}
else
{
lean_dec_ref_known(v_e_1457_, 3);
v___y_1476_ = v___x_1566_;
goto v___jp_1475_;
}
}
}
case 8:
{
lean_object* v_declName_1586_; lean_object* v_type_1587_; lean_object* v_value_1588_; lean_object* v_body_1589_; uint8_t v_nondep_1590_; lean_object* v___x_1591_; uint64_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; uint8_t v___x_1597_; 
v_declName_1586_ = lean_ctor_get(v_e_1457_, 0);
v_type_1587_ = lean_ctor_get(v_e_1457_, 1);
v_value_1588_ = lean_ctor_get(v_e_1457_, 2);
v_body_1589_ = lean_ctor_get(v_e_1457_, 3);
v_nondep_1590_ = lean_ctor_get_uint8(v_e_1457_, sizeof(void*)*4 + 8);
v___x_1591_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1592_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1457_);
v___x_1593_ = lean_uint64_to_usize(v___x_1592_);
v___x_1594_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1459_, v___x_1593_, v_e_1457_, v___x_1591_);
v___x_1595_ = lean_ptr_addr(v___x_1594_);
v___x_1596_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1597_ = lean_usize_dec_eq(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref_known(v_e_1457_, 4);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1594_);
lean_ctor_set(v___x_1598_, 1, v_a_1459_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; 
lean_dec_ref(v___x_1594_);
lean_inc_ref(v_type_1587_);
v___x_1599_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1587_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v_a_1601_; lean_object* v___x_1602_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
v_a_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1599_, 2);
lean_inc_ref(v_value_1588_);
v___x_1602_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1588_, v_a_1458_, v_a_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v_a_1604_; lean_object* v___x_1605_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
v_a_1604_ = lean_ctor_get(v___x_1602_, 1);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1602_, 2);
lean_inc_ref(v_body_1589_);
v___x_1605_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1589_, v_a_1458_, v_a_1604_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v_a_1607_; uint8_t v___y_1609_; size_t v___x_1618_; size_t v___x_1619_; uint8_t v___x_1620_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
v_a_1607_ = lean_ctor_get(v___x_1605_, 1);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1605_, 2);
v___x_1618_ = lean_ptr_addr(v_type_1587_);
v___x_1619_ = lean_ptr_addr(v_a_1600_);
v___x_1620_ = lean_usize_dec_eq(v___x_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
v___y_1609_ = v___x_1620_;
goto v___jp_1608_;
}
else
{
size_t v___x_1621_; size_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1621_ = lean_ptr_addr(v_value_1588_);
v___x_1622_ = lean_ptr_addr(v_a_1603_);
v___x_1623_ = lean_usize_dec_eq(v___x_1621_, v___x_1622_);
v___y_1609_ = v___x_1623_;
goto v___jp_1608_;
}
v___jp_1608_:
{
if (v___y_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_inc(v_declName_1586_);
lean_dec_ref_known(v_e_1457_, 4);
v___x_1610_ = l_Lean_Expr_letE___override(v_declName_1586_, v_a_1600_, v_a_1603_, v_a_1606_, v_nondep_1590_);
v___x_1611_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1610_, v_a_1607_);
return v___x_1611_;
}
else
{
size_t v___x_1612_; size_t v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = lean_ptr_addr(v_body_1589_);
v___x_1613_ = lean_ptr_addr(v_a_1606_);
v___x_1614_ = lean_usize_dec_eq(v___x_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_inc(v_declName_1586_);
lean_dec_ref_known(v_e_1457_, 4);
v___x_1615_ = l_Lean_Expr_letE___override(v_declName_1586_, v_a_1600_, v_a_1603_, v_a_1606_, v_nondep_1590_);
v___x_1616_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1615_, v_a_1607_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; 
lean_dec(v_a_1606_);
lean_dec(v_a_1603_);
lean_dec(v_a_1600_);
v___x_1617_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1457_, v_a_1607_);
return v___x_1617_;
}
}
}
}
else
{
lean_dec(v_a_1603_);
lean_dec(v_a_1600_);
lean_dec_ref_known(v_e_1457_, 4);
v___y_1461_ = v___x_1605_;
goto v___jp_1460_;
}
}
else
{
lean_dec(v_a_1600_);
lean_dec_ref_known(v_e_1457_, 4);
v___y_1461_ = v___x_1602_;
goto v___jp_1460_;
}
}
else
{
lean_dec_ref_known(v_e_1457_, 4);
v___y_1461_ = v___x_1599_;
goto v___jp_1460_;
}
}
}
case 10:
{
lean_object* v_data_1624_; lean_object* v_expr_1625_; lean_object* v___x_1626_; uint64_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; uint8_t v___x_1632_; 
v_data_1624_ = lean_ctor_get(v_e_1457_, 0);
v_expr_1625_ = lean_ctor_get(v_e_1457_, 1);
v___x_1626_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1627_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1457_);
v___x_1628_ = lean_uint64_to_usize(v___x_1627_);
v___x_1629_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1459_, v___x_1628_, v_e_1457_, v___x_1626_);
v___x_1630_ = lean_ptr_addr(v___x_1629_);
v___x_1631_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1632_ = lean_usize_dec_eq(v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref_known(v_e_1457_, 2);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1629_);
lean_ctor_set(v___x_1633_, 1, v_a_1459_);
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; 
lean_dec_ref(v___x_1629_);
lean_inc_ref(v_expr_1625_);
v___x_1634_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1625_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_a_1636_; size_t v___x_1637_; size_t v___x_1638_; uint8_t v___x_1639_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
v_a_1636_ = lean_ctor_get(v___x_1634_, 1);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1634_, 2);
v___x_1637_ = lean_ptr_addr(v_expr_1625_);
v___x_1638_ = lean_ptr_addr(v_a_1635_);
v___x_1639_ = lean_usize_dec_eq(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc(v_data_1624_);
lean_dec_ref_known(v_e_1457_, 2);
v___x_1640_ = l_Lean_Expr_mdata___override(v_data_1624_, v_a_1635_);
v___x_1641_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1640_, v_a_1636_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_a_1635_);
v___x_1642_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1457_, v_a_1636_);
return v___x_1642_;
}
}
else
{
lean_dec_ref_known(v_e_1457_, 2);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1643_; lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1643_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1643_);
v_a_1644_ = lean_ctor_get(v___x_1634_, 1);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1634_, 2);
v___x_1645_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1643_, v_a_1644_);
return v___x_1645_;
}
else
{
return v___x_1634_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1646_; lean_object* v_idx_1647_; lean_object* v_struct_1648_; lean_object* v___x_1649_; uint64_t v___x_1650_; size_t v___x_1651_; lean_object* v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; uint8_t v___x_1655_; 
v_typeName_1646_ = lean_ctor_get(v_e_1457_, 0);
v_idx_1647_ = lean_ctor_get(v_e_1457_, 1);
v_struct_1648_ = lean_ctor_get(v_e_1457_, 2);
v___x_1649_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1650_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1457_);
v___x_1651_ = lean_uint64_to_usize(v___x_1650_);
v___x_1652_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1459_, v___x_1651_, v_e_1457_, v___x_1649_);
v___x_1653_ = lean_ptr_addr(v___x_1652_);
v___x_1654_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1655_ = lean_usize_dec_eq(v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec_ref_known(v_e_1457_, 3);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1652_);
lean_ctor_set(v___x_1656_, 1, v_a_1459_);
return v___x_1656_;
}
else
{
uint8_t v_checkProj_1657_; 
lean_dec_ref(v___x_1652_);
v_checkProj_1657_ = lean_ctor_get_uint8(v_a_1458_, sizeof(void*)*1 + 1);
if (v_checkProj_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_inc_ref(v_struct_1648_);
v___x_1658_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1648_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_a_1660_; size_t v___x_1661_; size_t v___x_1662_; uint8_t v___x_1663_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
v_a_1660_ = lean_ctor_get(v___x_1658_, 1);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1658_, 2);
v___x_1661_ = lean_ptr_addr(v_struct_1648_);
v___x_1662_ = lean_ptr_addr(v_a_1659_);
v___x_1663_ = lean_usize_dec_eq(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_inc(v_idx_1647_);
lean_inc(v_typeName_1646_);
lean_dec_ref_known(v_e_1457_, 3);
v___x_1664_ = l_Lean_Expr_proj___override(v_typeName_1646_, v_idx_1647_, v_a_1659_);
v___x_1665_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1664_, v_a_1660_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_a_1659_);
v___x_1666_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1457_, v_a_1660_);
return v___x_1666_;
}
}
else
{
lean_dec_ref_known(v_e_1457_, 3);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1667_; lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1667_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1667_);
v_a_1668_ = lean_ctor_get(v___x_1658_, 1);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1658_, 2);
v___x_1669_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1667_, v_a_1668_);
return v___x_1669_;
}
else
{
return v___x_1658_;
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref_known(v_e_1457_, 3);
v___x_1670_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__2);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v_a_1459_);
return v___x_1671_;
}
}
}
default: 
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1457_, v_a_1459_);
return v___x_1672_;
}
}
v___jp_1460_:
{
if (lean_obj_tag(v___y_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___y_1461_, 0);
lean_inc(v_a_1462_);
v_a_1463_ = lean_ctor_get(v___y_1461_, 1);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___y_1461_, 2);
v___x_1464_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1462_, v_a_1463_);
return v___x_1464_;
}
else
{
return v___y_1461_;
}
}
v___jp_1465_:
{
if (lean_obj_tag(v___y_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v_a_1468_; lean_object* v___x_1469_; 
v_a_1467_ = lean_ctor_get(v___y_1466_, 0);
lean_inc(v_a_1467_);
v_a_1468_ = lean_ctor_get(v___y_1466_, 1);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___y_1466_, 2);
v___x_1469_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1467_, v_a_1468_);
return v___x_1469_;
}
else
{
return v___y_1466_;
}
}
v___jp_1470_:
{
if (lean_obj_tag(v___y_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1472_ = lean_ctor_get(v___y_1471_, 0);
lean_inc(v_a_1472_);
v_a_1473_ = lean_ctor_get(v___y_1471_, 1);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___y_1471_, 2);
v___x_1474_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1472_, v_a_1473_);
return v___x_1474_;
}
else
{
return v___y_1471_;
}
}
v___jp_1475_:
{
if (lean_obj_tag(v___y_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1477_ = lean_ctor_get(v___y_1476_, 0);
lean_inc(v_a_1477_);
v_a_1478_ = lean_ctor_get(v___y_1476_, 1);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___y_1476_, 2);
v___x_1479_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1477_, v_a_1478_);
return v___x_1479_;
}
else
{
return v___y_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1673_, v_a_1674_, v_a_1675_);
lean_dec_ref(v_a_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1677_, v_a_1678_, v_a_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1681_, v_a_1682_, v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1684_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReducibilityAttrs(uint8_t builtin);
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0;
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
static const lean_closure_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v_value_43_; lean_object* v_body_44_; uint8_t v_nondep_45_; uint64_t v___y_47_; 
v_value_43_ = lean_ctor_get(v_e_27_, 2);
v_body_44_ = lean_ctor_get(v_e_27_, 3);
v_nondep_45_ = lean_ctor_get_uint8(v_e_27_, sizeof(void*)*4 + 8);
if (v_nondep_45_ == 0)
{
uint64_t v___x_52_; 
v___x_52_ = 19ULL;
v___y_47_ = v___x_52_;
goto v___jp_46_;
}
else
{
uint64_t v___x_53_; 
v___x_53_ = 17ULL;
v___y_47_ = v___x_53_;
goto v___jp_46_;
}
v___jp_46_:
{
uint64_t v___x_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; 
v___x_48_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_value_43_);
v___x_49_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_body_44_);
v___x_50_ = lean_uint64_mix_hash(v___x_48_, v___x_49_);
v___x_51_ = lean_uint64_mix_hash(v___y_47_, v___x_50_);
return v___x_51_;
}
}
case 10:
{
lean_object* v_expr_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; 
v_expr_54_ = lean_ctor_get(v_e_27_, 1);
v___x_55_ = 13ULL;
v___x_56_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_expr_54_);
v___x_57_ = lean_uint64_mix_hash(v___x_55_, v___x_56_);
return v___x_57_;
}
case 11:
{
lean_object* v_typeName_58_; lean_object* v_idx_59_; lean_object* v_struct_60_; uint64_t v___y_62_; 
v_typeName_58_ = lean_ctor_get(v_e_27_, 0);
v_idx_59_ = lean_ctor_get(v_e_27_, 1);
v_struct_60_ = lean_ctor_get(v_e_27_, 2);
if (lean_obj_tag(v_typeName_58_) == 0)
{
uint64_t v___x_67_; 
v___x_67_ = 1723ULL;
v___y_62_ = v___x_67_;
goto v___jp_61_;
}
else
{
uint64_t v_hash_68_; 
v_hash_68_ = lean_ctor_get_uint64(v_typeName_58_, sizeof(void*)*2);
v___y_62_ = v_hash_68_;
goto v___jp_61_;
}
v___jp_61_:
{
uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; 
v___x_63_ = lean_uint64_of_nat(v_idx_59_);
v___x_64_ = lean_uint64_mix_hash(v___y_62_, v___x_63_);
v___x_65_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_struct_60_);
v___x_66_ = lean_uint64_mix_hash(v___x_64_, v___x_65_);
return v___x_66_;
}
}
default: 
{
uint64_t v___x_69_; 
v___x_69_ = l_Lean_Expr_hash(v_e_27_);
return v___x_69_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object* v_e_70_){
_start:
{
uint64_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_70_);
lean_dec_ref(v_e_70_);
v_r_72_ = lean_box_uint64(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object* v_e_u2081_73_, lean_object* v_e_u2082_74_){
_start:
{
switch(lean_obj_tag(v_e_u2081_73_))
{
case 5:
{
if (lean_obj_tag(v_e_u2082_74_) == 5)
{
lean_object* v_fn_75_; lean_object* v_arg_76_; lean_object* v_fn_77_; lean_object* v_arg_78_; size_t v___x_79_; size_t v___x_80_; uint8_t v___x_81_; 
v_fn_75_ = lean_ctor_get(v_e_u2081_73_, 0);
v_arg_76_ = lean_ctor_get(v_e_u2081_73_, 1);
v_fn_77_ = lean_ctor_get(v_e_u2082_74_, 0);
v_arg_78_ = lean_ctor_get(v_e_u2082_74_, 1);
v___x_79_ = lean_ptr_addr(v_fn_75_);
v___x_80_ = lean_ptr_addr(v_fn_77_);
v___x_81_ = lean_usize_dec_eq(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
return v___x_81_;
}
else
{
size_t v___x_82_; size_t v___x_83_; uint8_t v___x_84_; 
v___x_82_ = lean_ptr_addr(v_arg_76_);
v___x_83_ = lean_ptr_addr(v_arg_78_);
v___x_84_ = lean_usize_dec_eq(v___x_82_, v___x_83_);
return v___x_84_;
}
}
else
{
uint8_t v___x_85_; 
v___x_85_ = 0;
return v___x_85_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_74_) == 6)
{
lean_object* v_binderType_86_; lean_object* v_body_87_; lean_object* v_binderType_88_; lean_object* v_body_89_; size_t v___x_90_; size_t v___x_91_; uint8_t v___x_92_; 
v_binderType_86_ = lean_ctor_get(v_e_u2081_73_, 1);
v_body_87_ = lean_ctor_get(v_e_u2081_73_, 2);
v_binderType_88_ = lean_ctor_get(v_e_u2082_74_, 1);
v_body_89_ = lean_ctor_get(v_e_u2082_74_, 2);
v___x_90_ = lean_ptr_addr(v_binderType_86_);
v___x_91_ = lean_ptr_addr(v_binderType_88_);
v___x_92_ = lean_usize_dec_eq(v___x_90_, v___x_91_);
if (v___x_92_ == 0)
{
return v___x_92_;
}
else
{
size_t v___x_93_; size_t v___x_94_; uint8_t v___x_95_; 
v___x_93_ = lean_ptr_addr(v_body_87_);
v___x_94_ = lean_ptr_addr(v_body_89_);
v___x_95_ = lean_usize_dec_eq(v___x_93_, v___x_94_);
return v___x_95_;
}
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_74_) == 7)
{
lean_object* v_binderType_97_; lean_object* v_body_98_; lean_object* v_binderType_99_; lean_object* v_body_100_; size_t v___x_101_; size_t v___x_102_; uint8_t v___x_103_; 
v_binderType_97_ = lean_ctor_get(v_e_u2081_73_, 1);
v_body_98_ = lean_ctor_get(v_e_u2081_73_, 2);
v_binderType_99_ = lean_ctor_get(v_e_u2082_74_, 1);
v_body_100_ = lean_ctor_get(v_e_u2082_74_, 2);
v___x_101_ = lean_ptr_addr(v_binderType_97_);
v___x_102_ = lean_ptr_addr(v_binderType_99_);
v___x_103_ = lean_usize_dec_eq(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
return v___x_103_;
}
else
{
size_t v___x_104_; size_t v___x_105_; uint8_t v___x_106_; 
v___x_104_ = lean_ptr_addr(v_body_98_);
v___x_105_ = lean_ptr_addr(v_body_100_);
v___x_106_ = lean_usize_dec_eq(v___x_104_, v___x_105_);
return v___x_106_;
}
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_74_) == 8)
{
lean_object* v_value_108_; lean_object* v_body_109_; uint8_t v_nondep_110_; lean_object* v_value_111_; lean_object* v_body_112_; uint8_t v_nondep_113_; 
v_value_108_ = lean_ctor_get(v_e_u2081_73_, 2);
v_body_109_ = lean_ctor_get(v_e_u2081_73_, 3);
v_nondep_110_ = lean_ctor_get_uint8(v_e_u2081_73_, sizeof(void*)*4 + 8);
v_value_111_ = lean_ctor_get(v_e_u2082_74_, 2);
v_body_112_ = lean_ctor_get(v_e_u2082_74_, 3);
v_nondep_113_ = lean_ctor_get_uint8(v_e_u2082_74_, sizeof(void*)*4 + 8);
if (v_nondep_113_ == 0)
{
if (v_nondep_110_ == 0)
{
goto v___jp_114_;
}
else
{
return v_nondep_113_;
}
}
else
{
if (v_nondep_110_ == 0)
{
return v_nondep_110_;
}
else
{
goto v___jp_114_;
}
}
v___jp_114_:
{
size_t v___x_115_; size_t v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_ptr_addr(v_value_108_);
v___x_116_ = lean_ptr_addr(v_value_111_);
v___x_117_ = lean_usize_dec_eq(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
size_t v___x_118_; size_t v___x_119_; uint8_t v___x_120_; 
v___x_118_ = lean_ptr_addr(v_body_109_);
v___x_119_ = lean_ptr_addr(v_body_112_);
v___x_120_ = lean_usize_dec_eq(v___x_118_, v___x_119_);
return v___x_120_;
}
}
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_74_) == 10)
{
lean_object* v_data_122_; lean_object* v_expr_123_; lean_object* v_data_124_; lean_object* v_expr_125_; size_t v___x_126_; size_t v___x_127_; uint8_t v___x_128_; 
v_data_122_ = lean_ctor_get(v_e_u2081_73_, 0);
v_expr_123_ = lean_ctor_get(v_e_u2081_73_, 1);
v_data_124_ = lean_ctor_get(v_e_u2082_74_, 0);
v_expr_125_ = lean_ctor_get(v_e_u2082_74_, 1);
v___x_126_ = lean_ptr_addr(v_expr_123_);
v___x_127_ = lean_ptr_addr(v_expr_125_);
v___x_128_ = lean_usize_dec_eq(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = l_Lean_KVMap_eqv(v_data_122_, v_data_124_);
return v___x_129_;
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_74_) == 11)
{
lean_object* v_typeName_131_; lean_object* v_idx_132_; lean_object* v_struct_133_; lean_object* v_typeName_134_; lean_object* v_idx_135_; lean_object* v_struct_136_; uint8_t v___y_138_; uint8_t v___x_142_; 
v_typeName_131_ = lean_ctor_get(v_e_u2081_73_, 0);
v_idx_132_ = lean_ctor_get(v_e_u2081_73_, 1);
v_struct_133_ = lean_ctor_get(v_e_u2081_73_, 2);
v_typeName_134_ = lean_ctor_get(v_e_u2082_74_, 0);
v_idx_135_ = lean_ctor_get(v_e_u2082_74_, 1);
v_struct_136_ = lean_ctor_get(v_e_u2082_74_, 2);
v___x_142_ = lean_name_eq(v_typeName_131_, v_typeName_134_);
if (v___x_142_ == 0)
{
v___y_138_ = v___x_142_;
goto v___jp_137_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = lean_nat_dec_eq(v_idx_132_, v_idx_135_);
v___y_138_ = v___x_143_;
goto v___jp_137_;
}
v___jp_137_:
{
if (v___y_138_ == 0)
{
return v___y_138_;
}
else
{
size_t v___x_139_; size_t v___x_140_; uint8_t v___x_141_; 
v___x_139_ = lean_ptr_addr(v_struct_133_);
v___x_140_ = lean_ptr_addr(v_struct_136_);
v___x_141_ = lean_usize_dec_eq(v___x_139_, v___x_140_);
return v___x_141_;
}
}
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
default: 
{
uint8_t v___x_145_; 
v___x_145_ = lean_expr_eqv(v_e_u2081_73_, v_e_u2082_74_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object* v_e_u2081_146_, lean_object* v_e_u2082_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_e_u2081_146_, v_e_u2082_147_);
lean_dec_ref(v_e_u2082_147_);
lean_dec_ref(v_e_u2081_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_167_){
_start:
{
uint8_t v___y_169_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__5));
v___x_173_ = lean_name_eq(v_declName_167_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__7));
v___x_175_ = lean_name_eq(v_declName_167_, v___x_174_);
v___y_169_ = v___x_175_;
goto v___jp_168_;
}
else
{
v___y_169_ = v___x_173_;
goto v___jp_168_;
}
v___jp_168_:
{
if (v___y_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_171_ = lean_name_eq(v_declName_167_, v___x_170_);
return v___x_171_;
}
else
{
return v___y_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_176_);
lean_dec(v_declName_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object* v_env_179_, lean_object* v_declName_180_){
_start:
{
uint8_t v___x_181_; 
lean_inc(v_declName_180_);
lean_inc_ref(v_env_179_);
v___x_181_ = l_Lean_getReducibilityStatusCore(v_env_179_, v_declName_180_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; 
v___x_182_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_180_);
if (v___x_182_ == 0)
{
uint8_t v___x_183_; 
v___x_183_ = l_Lean_Environment_isProjectionFn(v_env_179_, v_declName_180_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; 
v___x_184_ = 1;
return v___x_184_;
}
else
{
return v___x_182_;
}
}
else
{
uint8_t v___x_185_; 
lean_dec(v_declName_180_);
lean_dec_ref(v_env_179_);
v___x_185_ = 0;
return v___x_185_;
}
}
else
{
uint8_t v___x_186_; 
lean_dec(v_declName_180_);
lean_dec_ref(v_env_179_);
v___x_186_ = 0;
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object* v_env_187_, lean_object* v_declName_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_187_, v_declName_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_191_){
_start:
{
uint64_t v___x_192_; 
v___x_192_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_193_){
_start:
{
uint64_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_193_);
lean_dec_ref(v_k_193_);
v_r_195_ = lean_box_uint64(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_198_, lean_object* v_k_u2082_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_198_, v_k_u2082_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_201_, lean_object* v_k_u2082_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_201_, v_k_u2082_202_);
lean_dec_ref(v_k_u2082_202_);
lean_dec_ref(v_k_u2081_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object* v_ctx_207_, lean_object* v_declName_208_){
_start:
{
uint8_t v_checkReducible_209_; 
v_checkReducible_209_ = lean_ctor_get_uint8(v_ctx_207_, sizeof(void*)*1);
if (v_checkReducible_209_ == 0)
{
lean_dec(v_declName_208_);
lean_dec_ref(v_ctx_207_);
return v_checkReducible_209_;
}
else
{
lean_object* v_env_210_; uint8_t v___x_211_; 
v_env_210_ = lean_ctor_get(v_ctx_207_, 0);
lean_inc_ref(v_env_210_);
lean_dec_ref(v_ctx_207_);
v___x_211_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_210_, v_declName_208_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object* v_ctx_212_, lean_object* v_declName_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_212_, v_declName_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_box(0);
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_221_ = l_Lean_mkConst(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_223_, lean_object* v_i_224_, lean_object* v_k_225_, lean_object* v_k_u2080_226_){
_start:
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = lean_array_get_size(v_keys_223_);
v___x_228_ = lean_nat_dec_lt(v_i_224_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec(v_i_224_);
lean_inc_ref(v_k_u2080_226_);
return v_k_u2080_226_;
}
else
{
lean_object* v_k_x27_229_; uint8_t v___x_230_; 
v_k_x27_229_ = lean_array_fget_borrowed(v_keys_223_, v_i_224_);
v___x_230_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_225_, v_k_x27_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_i_224_, v___x_231_);
lean_dec(v_i_224_);
v_i_224_ = v___x_232_;
goto _start;
}
else
{
lean_dec(v_i_224_);
lean_inc(v_k_x27_229_);
return v_k_x27_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_234_, lean_object* v_i_235_, lean_object* v_k_236_, lean_object* v_k_u2080_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_234_, v_i_235_, v_k_236_, v_k_u2080_237_);
lean_dec_ref(v_k_u2080_237_);
lean_dec_ref(v_k_236_);
lean_dec_ref(v_keys_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_239_, size_t v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v_es_243_; lean_object* v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v_j_247_; lean_object* v___x_248_; 
v_es_243_ = lean_ctor_get(v_x_239_, 0);
v___x_244_ = lean_box(2);
v___x_245_ = ((size_t)31ULL);
v___x_246_ = lean_usize_land(v_x_240_, v___x_245_);
v_j_247_ = lean_usize_to_nat(v___x_246_);
v___x_248_ = lean_array_get_borrowed(v___x_244_, v_es_243_, v_j_247_);
lean_dec(v_j_247_);
switch(lean_obj_tag(v___x_248_))
{
case 0:
{
lean_object* v_key_249_; uint8_t v___x_250_; 
v_key_249_ = lean_ctor_get(v___x_248_, 0);
v___x_250_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_241_, v_key_249_);
if (v___x_250_ == 0)
{
lean_inc_ref(v_x_242_);
return v_x_242_;
}
else
{
lean_inc(v_key_249_);
return v_key_249_;
}
}
case 1:
{
lean_object* v_node_251_; size_t v___x_252_; size_t v___x_253_; 
v_node_251_ = lean_ctor_get(v___x_248_, 0);
v___x_252_ = ((size_t)5ULL);
v___x_253_ = lean_usize_shift_right(v_x_240_, v___x_252_);
v_x_239_ = v_node_251_;
v_x_240_ = v___x_253_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_242_);
return v_x_242_;
}
}
}
else
{
lean_object* v_ks_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_ks_255_ = lean_ctor_get(v_x_239_, 0);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_255_, v___x_256_, v_x_241_, v_x_242_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
size_t v_x_1943__boxed_262_; lean_object* v_res_263_; 
v_x_1943__boxed_262_ = lean_unbox_usize(v_x_259_);
lean_dec(v_x_259_);
v_res_263_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_258_, v_x_1943__boxed_262_, v_x_260_, v_x_261_);
lean_dec_ref(v_x_261_);
lean_dec_ref(v_x_260_);
lean_dec_ref(v_x_258_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
lean_object* v_ks_268_; lean_object* v_vs_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_293_; 
v_ks_268_ = lean_ctor_get(v_x_264_, 0);
v_vs_269_ = lean_ctor_get(v_x_264_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_293_ == 0)
{
v___x_271_ = v_x_264_;
v_isShared_272_ = v_isSharedCheck_293_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_vs_269_);
lean_inc(v_ks_268_);
lean_dec(v_x_264_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_293_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_array_get_size(v_ks_268_);
v___x_274_ = lean_nat_dec_lt(v_x_265_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
lean_dec(v_x_265_);
v___x_275_ = lean_array_push(v_ks_268_, v_x_266_);
v___x_276_ = lean_array_push(v_vs_269_, v_x_267_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_276_);
lean_ctor_set(v___x_271_, 0, v___x_275_);
v___x_278_ = v___x_271_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
else
{
lean_object* v_k_x27_280_; uint8_t v___x_281_; 
v_k_x27_280_ = lean_array_fget_borrowed(v_ks_268_, v_x_265_);
v___x_281_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_266_, v_k_x27_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_283_; 
if (v_isShared_272_ == 0)
{
v___x_283_ = v___x_271_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_ks_268_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_vs_269_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_x_265_, v___x_284_);
lean_dec(v_x_265_);
v_x_264_ = v___x_283_;
v_x_265_ = v___x_285_;
goto _start;
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_288_ = lean_array_fset(v_ks_268_, v_x_265_, v_x_266_);
v___x_289_ = lean_array_fset(v_vs_269_, v_x_265_, v_x_267_);
lean_dec(v_x_265_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_289_);
lean_ctor_set(v___x_271_, 0, v___x_288_);
v___x_291_ = v___x_271_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_294_, lean_object* v_k_295_, lean_object* v_v_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_294_, v___x_297_, v_k_295_, v_v_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_300_, size_t v_x_301_, size_t v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v_es_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v_j_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_es_305_ = lean_ctor_get(v_x_300_, 0);
v___x_306_ = ((size_t)31ULL);
v___x_307_ = lean_usize_land(v_x_301_, v___x_306_);
v_j_308_ = lean_usize_to_nat(v___x_307_);
v___x_309_ = lean_array_get_size(v_es_305_);
v___x_310_ = lean_nat_dec_lt(v_j_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_dec(v_j_308_);
lean_dec(v_x_304_);
lean_dec_ref(v_x_303_);
return v_x_300_;
}
else
{
lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_349_; 
lean_inc_ref(v_es_305_);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v_x_300_, 0);
lean_dec(v_unused_350_);
v___x_312_ = v_x_300_;
v_isShared_313_ = v_isSharedCheck_349_;
goto v_resetjp_311_;
}
else
{
lean_dec(v_x_300_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_349_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_v_314_; lean_object* v___x_315_; lean_object* v_xs_x27_316_; lean_object* v___y_318_; 
v_v_314_ = lean_array_fget(v_es_305_, v_j_308_);
v___x_315_ = lean_box(0);
v_xs_x27_316_ = lean_array_fset(v_es_305_, v_j_308_, v___x_315_);
switch(lean_obj_tag(v_v_314_))
{
case 0:
{
lean_object* v_key_323_; lean_object* v_val_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_334_; 
v_key_323_ = lean_ctor_get(v_v_314_, 0);
v_val_324_ = lean_ctor_get(v_v_314_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_v_314_);
if (v_isSharedCheck_334_ == 0)
{
v___x_326_ = v_v_314_;
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_val_324_);
lean_inc(v_key_323_);
lean_dec(v_v_314_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
uint8_t v___x_328_; 
v___x_328_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_303_, v_key_323_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_del_object(v___x_326_);
v___x_329_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_323_, v_val_324_, v_x_303_, v_x_304_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___y_318_ = v___x_330_;
goto v___jp_317_;
}
else
{
lean_object* v___x_332_; 
lean_dec(v_val_324_);
lean_dec(v_key_323_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v_x_304_);
lean_ctor_set(v___x_326_, 0, v_x_303_);
v___x_332_ = v___x_326_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_x_303_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_x_304_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
v___y_318_ = v___x_332_;
goto v___jp_317_;
}
}
}
}
case 1:
{
lean_object* v_node_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_347_; 
v_node_335_ = lean_ctor_get(v_v_314_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_v_314_);
if (v_isSharedCheck_347_ == 0)
{
v___x_337_ = v_v_314_;
v_isShared_338_ = v_isSharedCheck_347_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_node_335_);
lean_dec(v_v_314_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_347_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_339_ = ((size_t)5ULL);
v___x_340_ = lean_usize_shift_right(v_x_301_, v___x_339_);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_x_302_, v___x_341_);
v___x_343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_335_, v___x_340_, v___x_342_, v_x_303_, v_x_304_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_343_);
v___x_345_ = v___x_337_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
v___y_318_ = v___x_345_;
goto v___jp_317_;
}
}
}
default: 
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_x_303_);
lean_ctor_set(v___x_348_, 1, v_x_304_);
v___y_318_ = v___x_348_;
goto v___jp_317_;
}
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_array_fset(v_xs_x27_316_, v_j_308_, v___y_318_);
lean_dec(v_j_308_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_319_);
v___x_321_ = v___x_312_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
else
{
lean_object* v_ks_351_; lean_object* v_vs_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_370_; 
v_ks_351_ = lean_ctor_get(v_x_300_, 0);
v_vs_352_ = lean_ctor_get(v_x_300_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_370_ == 0)
{
v___x_354_ = v_x_300_;
v_isShared_355_ = v_isSharedCheck_370_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_vs_352_);
lean_inc(v_ks_351_);
lean_dec(v_x_300_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_370_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_ks_351_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_vs_352_);
v___x_357_ = v_reuseFailAlloc_369_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v_newNode_358_; size_t v___x_359_; uint8_t v___x_360_; 
v_newNode_358_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_357_, v_x_303_, v_x_304_);
v___x_359_ = ((size_t)7ULL);
v___x_360_ = lean_usize_dec_le(v___x_359_, v_x_302_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_358_);
v___x_362_ = lean_unsigned_to_nat(4u);
v___x_363_ = lean_nat_dec_lt(v___x_361_, v___x_362_);
lean_dec(v___x_361_);
if (v___x_363_ == 0)
{
lean_object* v_ks_364_; lean_object* v_vs_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_ks_364_ = lean_ctor_get(v_newNode_358_, 0);
lean_inc_ref(v_ks_364_);
v_vs_365_ = lean_ctor_get(v_newNode_358_, 1);
lean_inc_ref(v_vs_365_);
lean_dec_ref(v_newNode_358_);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_302_, v_ks_364_, v_vs_365_, v___x_366_, v___x_367_);
lean_dec_ref(v_vs_365_);
lean_dec_ref(v_ks_364_);
return v___x_368_;
}
else
{
return v_newNode_358_;
}
}
else
{
return v_newNode_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_371_, lean_object* v_keys_372_, lean_object* v_vals_373_, lean_object* v_i_374_, lean_object* v_entries_375_){
_start:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_array_get_size(v_keys_372_);
v___x_377_ = lean_nat_dec_lt(v_i_374_, v___x_376_);
if (v___x_377_ == 0)
{
lean_dec(v_i_374_);
return v_entries_375_;
}
else
{
lean_object* v_k_378_; lean_object* v_v_379_; uint64_t v___x_380_; size_t v_h_381_; size_t v___x_382_; lean_object* v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v_h_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_k_378_ = lean_array_fget_borrowed(v_keys_372_, v_i_374_);
v_v_379_ = lean_array_fget_borrowed(v_vals_373_, v_i_374_);
v___x_380_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_378_);
v_h_381_ = lean_uint64_to_usize(v___x_380_);
v___x_382_ = ((size_t)5ULL);
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_sub(v_depth_371_, v___x_384_);
v___x_386_ = lean_usize_mul(v___x_382_, v___x_385_);
v_h_387_ = lean_usize_shift_right(v_h_381_, v___x_386_);
v___x_388_ = lean_nat_add(v_i_374_, v___x_383_);
lean_dec(v_i_374_);
lean_inc(v_v_379_);
lean_inc(v_k_378_);
v___x_389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_375_, v_h_387_, v_depth_371_, v_k_378_, v_v_379_);
v_i_374_ = v___x_388_;
v_entries_375_ = v___x_389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_391_, lean_object* v_keys_392_, lean_object* v_vals_393_, lean_object* v_i_394_, lean_object* v_entries_395_){
_start:
{
size_t v_depth_boxed_396_; lean_object* v_res_397_; 
v_depth_boxed_396_ = lean_unbox_usize(v_depth_391_);
lean_dec(v_depth_391_);
v_res_397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_396_, v_keys_392_, v_vals_393_, v_i_394_, v_entries_395_);
lean_dec_ref(v_vals_393_);
lean_dec_ref(v_keys_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
size_t v_x_2061__boxed_403_; size_t v_x_2062__boxed_404_; lean_object* v_res_405_; 
v_x_2061__boxed_403_ = lean_unbox_usize(v_x_399_);
lean_dec(v_x_399_);
v_x_2062__boxed_404_ = lean_unbox_usize(v_x_400_);
lean_dec(v_x_400_);
v_res_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_398_, v_x_2061__boxed_403_, v_x_2062__boxed_404_, v_x_401_, v_x_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
uint64_t v___x_409_; size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; 
v___x_409_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_407_);
v___x_410_ = lean_uint64_to_usize(v___x_409_);
v___x_411_ = ((size_t)1ULL);
v___x_412_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_406_, v___x_410_, v___x_411_, v_x_407_, v_x_408_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_413_, lean_object* v_b_414_, lean_object* v_x_415_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_dec(v_b_414_);
lean_dec_ref(v_a_413_);
return v_x_415_;
}
else
{
lean_object* v_key_416_; lean_object* v_value_417_; lean_object* v_tail_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_432_; 
v_key_416_ = lean_ctor_get(v_x_415_, 0);
v_value_417_ = lean_ctor_get(v_x_415_, 1);
v_tail_418_ = lean_ctor_get(v_x_415_, 2);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_432_ == 0)
{
v___x_420_ = v_x_415_;
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_tail_418_);
lean_inc(v_value_417_);
lean_inc(v_key_416_);
lean_dec(v_x_415_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_432_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
size_t v___x_422_; size_t v___x_423_; uint8_t v___x_424_; 
v___x_422_ = lean_ptr_addr(v_key_416_);
v___x_423_ = lean_ptr_addr(v_a_413_);
v___x_424_ = lean_usize_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_413_, v_b_414_, v_tail_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 2, v___x_425_);
v___x_427_ = v___x_420_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_key_416_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_value_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
else
{
lean_object* v___x_430_; 
lean_dec(v_value_417_);
lean_dec(v_key_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v_b_414_);
lean_ctor_set(v___x_420_, 0, v_a_413_);
v___x_430_ = v___x_420_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_b_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_tail_418_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
return v_x_433_;
}
else
{
lean_object* v_key_435_; lean_object* v_value_436_; lean_object* v_tail_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_463_; 
v_key_435_ = lean_ctor_get(v_x_434_, 0);
v_value_436_ = lean_ctor_get(v_x_434_, 1);
v_tail_437_ = lean_ctor_get(v_x_434_, 2);
v_isSharedCheck_463_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_463_ == 0)
{
v___x_439_ = v_x_434_;
v_isShared_440_ = v_isSharedCheck_463_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_tail_437_);
lean_inc(v_value_436_);
lean_inc(v_key_435_);
lean_dec(v_x_434_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_463_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v_fold_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_441_ = lean_array_get_size(v_x_433_);
v___x_442_ = lean_ptr_addr(v_key_435_);
v___x_443_ = ((size_t)3ULL);
v___x_444_ = lean_usize_shift_right(v___x_442_, v___x_443_);
v___x_445_ = lean_usize_to_uint64(v___x_444_);
v___x_446_ = 32ULL;
v___x_447_ = lean_uint64_shift_right(v___x_445_, v___x_446_);
v_fold_448_ = lean_uint64_xor(v___x_445_, v___x_447_);
v___x_449_ = 16ULL;
v___x_450_ = lean_uint64_shift_right(v_fold_448_, v___x_449_);
v___x_451_ = lean_uint64_xor(v_fold_448_, v___x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = lean_usize_of_nat(v___x_441_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_land(v___x_452_, v___x_455_);
v___x_457_ = lean_array_uget_borrowed(v_x_433_, v___x_456_);
lean_inc(v___x_457_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 2, v___x_457_);
v___x_459_ = v___x_439_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_key_435_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_value_436_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v___x_457_);
v___x_459_ = v_reuseFailAlloc_462_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; 
v___x_460_ = lean_array_uset(v_x_433_, v___x_456_, v___x_459_);
v_x_433_ = v___x_460_;
v_x_434_ = v_tail_437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_464_, lean_object* v_source_465_, lean_object* v_target_466_){
_start:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_array_get_size(v_source_465_);
v___x_468_ = lean_nat_dec_lt(v_i_464_, v___x_467_);
if (v___x_468_ == 0)
{
lean_dec_ref(v_source_465_);
lean_dec(v_i_464_);
return v_target_466_;
}
else
{
lean_object* v_es_469_; lean_object* v___x_470_; lean_object* v_source_471_; lean_object* v_target_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_es_469_ = lean_array_fget(v_source_465_, v_i_464_);
v___x_470_ = lean_box(0);
v_source_471_ = lean_array_fset(v_source_465_, v_i_464_, v___x_470_);
v_target_472_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_466_, v_es_469_);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_i_464_, v___x_473_);
lean_dec(v_i_464_);
v_i_464_ = v___x_474_;
v_source_465_ = v_source_471_;
v_target_466_ = v_target_472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_nbuckets_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_477_ = lean_array_get_size(v_data_476_);
v___x_478_ = lean_unsigned_to_nat(2u);
v_nbuckets_479_ = lean_nat_mul(v___x_477_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_box(0);
v___x_482_ = lean_mk_array(v_nbuckets_479_, v___x_481_);
v___x_483_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_480_, v_data_476_, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
uint8_t v___x_486_; 
v___x_486_ = 0;
return v___x_486_;
}
else
{
lean_object* v_key_487_; lean_object* v_tail_488_; size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v_key_487_ = lean_ctor_get(v_x_485_, 0);
v_tail_488_ = lean_ctor_get(v_x_485_, 2);
v___x_489_ = lean_ptr_addr(v_key_487_);
v___x_490_ = lean_ptr_addr(v_a_484_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
v_x_485_ = v_tail_488_;
goto _start;
}
else
{
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_493_, lean_object* v_x_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_493_, v_x_494_);
lean_dec(v_x_494_);
lean_dec_ref(v_a_493_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_497_, lean_object* v_a_498_, lean_object* v_b_499_){
_start:
{
lean_object* v_size_500_; lean_object* v_buckets_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_547_; 
v_size_500_ = lean_ctor_get(v_m_497_, 0);
v_buckets_501_ = lean_ctor_get(v_m_497_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_m_497_);
if (v_isSharedCheck_547_ == 0)
{
v___x_503_ = v_m_497_;
v_isShared_504_ = v_isSharedCheck_547_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_buckets_501_);
lean_inc(v_size_500_);
lean_dec(v_m_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_547_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v_fold_512_; uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; lean_object* v_bkt_521_; uint8_t v___x_522_; 
v___x_505_ = lean_array_get_size(v_buckets_501_);
v___x_506_ = lean_ptr_addr(v_a_498_);
v___x_507_ = ((size_t)3ULL);
v___x_508_ = lean_usize_shift_right(v___x_506_, v___x_507_);
v___x_509_ = lean_usize_to_uint64(v___x_508_);
v___x_510_ = 32ULL;
v___x_511_ = lean_uint64_shift_right(v___x_509_, v___x_510_);
v_fold_512_ = lean_uint64_xor(v___x_509_, v___x_511_);
v___x_513_ = 16ULL;
v___x_514_ = lean_uint64_shift_right(v_fold_512_, v___x_513_);
v___x_515_ = lean_uint64_xor(v_fold_512_, v___x_514_);
v___x_516_ = lean_uint64_to_usize(v___x_515_);
v___x_517_ = lean_usize_of_nat(v___x_505_);
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_sub(v___x_517_, v___x_518_);
v___x_520_ = lean_usize_land(v___x_516_, v___x_519_);
v_bkt_521_ = lean_array_uget_borrowed(v_buckets_501_, v___x_520_);
v___x_522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_498_, v_bkt_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v_size_x27_524_; lean_object* v___x_525_; lean_object* v_buckets_x27_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v_size_x27_524_ = lean_nat_add(v_size_500_, v___x_523_);
lean_dec(v_size_500_);
lean_inc(v_bkt_521_);
v___x_525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_525_, 0, v_a_498_);
lean_ctor_set(v___x_525_, 1, v_b_499_);
lean_ctor_set(v___x_525_, 2, v_bkt_521_);
v_buckets_x27_526_ = lean_array_uset(v_buckets_501_, v___x_520_, v___x_525_);
v___x_527_ = lean_unsigned_to_nat(4u);
v___x_528_ = lean_nat_mul(v_size_x27_524_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(3u);
v___x_530_ = lean_nat_div(v___x_528_, v___x_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_array_get_size(v_buckets_x27_526_);
v___x_532_ = lean_nat_dec_le(v___x_530_, v___x_531_);
lean_dec(v___x_530_);
if (v___x_532_ == 0)
{
lean_object* v_val_533_; lean_object* v___x_535_; 
v_val_533_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_526_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_val_533_);
lean_ctor_set(v___x_503_, 0, v_size_x27_524_);
v___x_535_ = v___x_503_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_size_x27_524_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_val_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v___x_538_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_buckets_x27_526_);
lean_ctor_set(v___x_503_, 0, v_size_x27_524_);
v___x_538_ = v___x_503_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_size_x27_524_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_buckets_x27_526_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_object* v___x_540_; lean_object* v_buckets_x27_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
lean_inc(v_bkt_521_);
v___x_540_ = lean_box(0);
v_buckets_x27_541_ = lean_array_uset(v_buckets_501_, v___x_520_, v___x_540_);
v___x_542_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_498_, v_b_499_, v_bkt_521_);
v___x_543_ = lean_array_uset(v_buckets_x27_541_, v___x_520_, v___x_542_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_543_);
v___x_545_ = v___x_503_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_size_500_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_548_; size_t v___x_549_; 
v___x_548_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_549_ = lean_ptr_addr(v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_550_, lean_object* v_r_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_map_553_; lean_object* v_set_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_578_; 
v_map_553_ = lean_ctor_get(v_a_552_, 0);
v_set_554_ = lean_ctor_get(v_a_552_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_a_552_);
if (v_isSharedCheck_578_ == 0)
{
v___x_556_ = v_a_552_;
v_isShared_557_ = v_isSharedCheck_578_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_set_554_);
lean_inc(v_map_553_);
lean_dec(v_a_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_578_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; uint64_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; size_t v___x_562_; size_t v___x_563_; uint8_t v___x_564_; 
v___x_558_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_559_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_551_);
v___x_560_ = lean_uint64_to_usize(v___x_559_);
v___x_561_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_554_, v___x_560_, v_r_551_, v___x_558_);
v___x_562_ = lean_ptr_addr(v___x_561_);
v___x_563_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_564_ = lean_usize_dec_eq(v___x_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_567_; 
lean_dec_ref(v_r_551_);
lean_inc_ref(v___x_561_);
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_553_, v_e_550_, v___x_561_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_565_);
v___x_567_ = v___x_556_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_set_554_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_561_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec_ref(v___x_561_);
lean_inc_ref_n(v_r_551_, 4);
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_553_, v_e_550_, v_r_551_);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_570_, v_r_551_, v_r_551_);
v___x_572_ = lean_box(0);
v___x_573_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_554_, v_r_551_, v___x_572_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___x_573_);
lean_ctor_set(v___x_556_, 0, v___x_571_);
v___x_575_ = v___x_556_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_r_551_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_579_, lean_object* v_r_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_579_, v_r_580_, v_a_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_584_, lean_object* v_r_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_584_, v_r_585_, v_a_586_, v_a_587_);
lean_dec_ref(v_a_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_589_, lean_object* v_x_590_, size_t v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_590_, v_x_591_, v_x_592_, v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
size_t v_x_2512__boxed_600_; lean_object* v_res_601_; 
v_x_2512__boxed_600_ = lean_unbox_usize(v_x_597_);
lean_dec(v_x_597_);
v_res_601_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_595_, v_x_596_, v_x_2512__boxed_600_, v_x_598_, v_x_599_);
lean_dec_ref(v_x_599_);
lean_dec_ref(v_x_598_);
lean_dec_ref(v_x_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_602_, lean_object* v_m_603_, lean_object* v_a_604_, lean_object* v_b_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_603_, v_a_604_, v_b_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_608_, v_x_609_, v_x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_612_, lean_object* v_keys_613_, lean_object* v_vals_614_, lean_object* v_heq_615_, lean_object* v_i_616_, lean_object* v_k_617_, lean_object* v_k_u2080_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_613_, v_i_616_, v_k_617_, v_k_u2080_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_620_, lean_object* v_keys_621_, lean_object* v_vals_622_, lean_object* v_heq_623_, lean_object* v_i_624_, lean_object* v_k_625_, lean_object* v_k_u2080_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_620_, v_keys_621_, v_vals_622_, v_heq_623_, v_i_624_, v_k_625_, v_k_u2080_626_);
lean_dec_ref(v_k_u2080_626_);
lean_dec_ref(v_k_625_);
lean_dec_ref(v_vals_622_);
lean_dec_ref(v_keys_621_);
return v_res_627_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_628_, lean_object* v_a_629_, lean_object* v_x_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_632_, lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_632_, v_a_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec_ref(v_a_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_637_, lean_object* v_data_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_640_, lean_object* v_a_641_, lean_object* v_b_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_641_, v_b_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_645_, lean_object* v_x_646_, size_t v_x_647_, size_t v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_646_, v_x_647_, v_x_648_, v_x_649_, v_x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
size_t v_x_2549__boxed_658_; size_t v_x_2550__boxed_659_; lean_object* v_res_660_; 
v_x_2549__boxed_658_ = lean_unbox_usize(v_x_654_);
lean_dec(v_x_654_);
v_x_2550__boxed_659_ = lean_unbox_usize(v_x_655_);
lean_dec(v_x_655_);
v_res_660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_652_, v_x_653_, v_x_2549__boxed_658_, v_x_2550__boxed_659_, v_x_656_, v_x_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_661_, lean_object* v_i_662_, lean_object* v_source_663_, lean_object* v_target_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_662_, v_source_663_, v_target_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_666_, lean_object* v_n_667_, lean_object* v_k_668_, lean_object* v_v_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_667_, v_k_668_, v_v_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_671_, size_t v_depth_672_, lean_object* v_keys_673_, lean_object* v_vals_674_, lean_object* v_heq_675_, lean_object* v_i_676_, lean_object* v_entries_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_672_, v_keys_673_, v_vals_674_, v_i_676_, v_entries_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_679_, lean_object* v_depth_680_, lean_object* v_keys_681_, lean_object* v_vals_682_, lean_object* v_heq_683_, lean_object* v_i_684_, lean_object* v_entries_685_){
_start:
{
size_t v_depth_boxed_686_; lean_object* v_res_687_; 
v_depth_boxed_686_ = lean_unbox_usize(v_depth_680_);
lean_dec(v_depth_680_);
v_res_687_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_679_, v_depth_boxed_686_, v_keys_681_, v_vals_682_, v_heq_683_, v_i_684_, v_entries_685_);
lean_dec_ref(v_vals_682_);
lean_dec_ref(v_keys_681_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_689_, v_x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_693_, v_x_694_, v_x_695_, v_x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_700_, lean_object* v_k_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_map_704_; lean_object* v_set_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___x_708_; 
v_map_704_ = lean_ctor_get(v_a_703_, 0);
v_set_705_ = lean_ctor_get(v_a_703_, 1);
v___f_706_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_707_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_700_);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_706_, v___f_707_, v_map_704_, v_e_700_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_710_; 
lean_dec_ref(v_k_701_);
lean_dec_ref(v_e_700_);
v_val_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_val_709_);
lean_ctor_set(v___x_710_, 1, v_a_703_);
return v___x_710_;
}
else
{
lean_object* v___f_711_; lean_object* v___x_712_; uint64_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; size_t v___x_716_; size_t v___x_717_; uint8_t v___x_718_; 
lean_dec(v___x_708_);
v___f_711_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_712_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_713_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_700_);
v___x_714_ = lean_uint64_to_usize(v___x_713_);
lean_inc_ref(v_e_700_);
lean_inc_ref(v_set_705_);
v___x_715_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_711_, v_set_705_, v___x_714_, v_e_700_, v___x_712_);
v___x_716_ = lean_ptr_addr(v___x_715_);
v___x_717_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_718_ = lean_usize_dec_eq(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec_ref(v_k_701_);
lean_dec_ref(v_e_700_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_715_);
lean_ctor_set(v___x_719_, 1, v_a_703_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; 
lean_dec(v___x_715_);
lean_inc_ref(v_a_702_);
v___x_720_ = lean_apply_2(v_k_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
v_a_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_720_, 2);
v___x_723_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_700_, v_a_721_, v_a_722_);
return v___x_723_;
}
else
{
lean_dec_ref(v_e_700_);
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_724_, lean_object* v_k_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_724_, v_k_725_, v_a_726_, v_a_727_);
lean_dec_ref(v_a_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_729_, lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 0)
{
lean_object* v___x_731_; 
v___x_731_ = lean_box(0);
return v___x_731_;
}
else
{
lean_object* v_key_732_; lean_object* v_value_733_; lean_object* v_tail_734_; size_t v___x_735_; size_t v___x_736_; uint8_t v___x_737_; 
v_key_732_ = lean_ctor_get(v_x_730_, 0);
v_value_733_ = lean_ctor_get(v_x_730_, 1);
v_tail_734_ = lean_ctor_get(v_x_730_, 2);
v___x_735_ = lean_ptr_addr(v_key_732_);
v___x_736_ = lean_ptr_addr(v_a_729_);
v___x_737_ = lean_usize_dec_eq(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
v_x_730_ = v_tail_734_;
goto _start;
}
else
{
lean_object* v___x_739_; 
lean_inc(v_value_733_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_value_733_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_740_, lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_740_, v_x_741_);
lean_dec(v_x_741_);
lean_dec_ref(v_a_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_buckets_745_; lean_object* v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v___x_752_; uint64_t v_fold_753_; uint64_t v___x_754_; uint64_t v___x_755_; uint64_t v___x_756_; size_t v___x_757_; size_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_buckets_745_ = lean_ctor_get(v_m_743_, 1);
v___x_746_ = lean_array_get_size(v_buckets_745_);
v___x_747_ = lean_ptr_addr(v_a_744_);
v___x_748_ = ((size_t)3ULL);
v___x_749_ = lean_usize_shift_right(v___x_747_, v___x_748_);
v___x_750_ = lean_usize_to_uint64(v___x_749_);
v___x_751_ = 32ULL;
v___x_752_ = lean_uint64_shift_right(v___x_750_, v___x_751_);
v_fold_753_ = lean_uint64_xor(v___x_750_, v___x_752_);
v___x_754_ = 16ULL;
v___x_755_ = lean_uint64_shift_right(v_fold_753_, v___x_754_);
v___x_756_ = lean_uint64_xor(v_fold_753_, v___x_755_);
v___x_757_ = lean_uint64_to_usize(v___x_756_);
v___x_758_ = lean_usize_of_nat(v___x_746_);
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_sub(v___x_758_, v___x_759_);
v___x_761_ = lean_usize_land(v___x_757_, v___x_760_);
v___x_762_ = lean_array_uget_borrowed(v_buckets_745_, v___x_761_);
v___x_763_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_744_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_764_, v_a_765_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_m_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_i_769_, lean_object* v_k_770_){
_start:
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_array_get_size(v_keys_767_);
v___x_772_ = lean_nat_dec_lt(v_i_769_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
lean_dec(v_i_769_);
v___x_773_ = lean_box(0);
return v___x_773_;
}
else
{
lean_object* v_k_x27_774_; uint8_t v___x_775_; 
v_k_x27_774_ = lean_array_fget_borrowed(v_keys_767_, v_i_769_);
v___x_775_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_770_, v_k_x27_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_nat_add(v_i_769_, v___x_776_);
lean_dec(v_i_769_);
v_i_769_ = v___x_777_;
goto _start;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_array_fget_borrowed(v_vals_768_, v_i_769_);
lean_dec(v_i_769_);
lean_inc(v___x_779_);
lean_inc(v_k_x27_774_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_k_x27_774_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_782_, lean_object* v_vals_783_, lean_object* v_i_784_, lean_object* v_k_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_782_, v_vals_783_, v_i_784_, v_k_785_);
lean_dec_ref(v_k_785_);
lean_dec_ref(v_vals_783_);
lean_dec_ref(v_keys_782_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_787_, size_t v_x_788_, lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_787_) == 0)
{
lean_object* v_es_790_; lean_object* v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_j_794_; lean_object* v___x_795_; 
v_es_790_ = lean_ctor_get(v_x_787_, 0);
v___x_791_ = lean_box(2);
v___x_792_ = ((size_t)31ULL);
v___x_793_ = lean_usize_land(v_x_788_, v___x_792_);
v_j_794_ = lean_usize_to_nat(v___x_793_);
v___x_795_ = lean_array_get_borrowed(v___x_791_, v_es_790_, v_j_794_);
lean_dec(v_j_794_);
switch(lean_obj_tag(v___x_795_))
{
case 0:
{
lean_object* v_key_796_; lean_object* v_val_797_; uint8_t v___x_798_; 
v_key_796_ = lean_ctor_get(v___x_795_, 0);
v_val_797_ = lean_ctor_get(v___x_795_, 1);
v___x_798_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_789_, v_key_796_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(0);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_inc(v_val_797_);
lean_inc(v_key_796_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_key_796_);
lean_ctor_set(v___x_800_, 1, v_val_797_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
case 1:
{
lean_object* v_node_802_; size_t v___x_803_; size_t v___x_804_; 
v_node_802_ = lean_ctor_get(v___x_795_, 0);
v___x_803_ = ((size_t)5ULL);
v___x_804_ = lean_usize_shift_right(v_x_788_, v___x_803_);
v_x_787_ = v_node_802_;
v_x_788_ = v___x_804_;
goto _start;
}
default: 
{
lean_object* v___x_806_; 
v___x_806_ = lean_box(0);
return v___x_806_;
}
}
}
else
{
lean_object* v_ks_807_; lean_object* v_vs_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_ks_807_ = lean_ctor_get(v_x_787_, 0);
v_vs_808_ = lean_ctor_get(v_x_787_, 1);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_807_, v_vs_808_, v___x_809_, v_x_789_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
size_t v_x_11055__boxed_814_; lean_object* v_res_815_; 
v_x_11055__boxed_814_ = lean_unbox_usize(v_x_812_);
lean_dec(v_x_812_);
v_res_815_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_811_, v_x_11055__boxed_814_, v_x_813_);
lean_dec_ref(v_x_813_);
lean_dec_ref(v_x_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
uint64_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; 
v___x_818_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_817_);
v___x_819_ = lean_uint64_to_usize(v___x_818_);
v___x_820_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_816_, v___x_819_, v_x_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_821_, v_x_822_);
lean_dec_ref(v_x_822_);
lean_dec_ref(v_x_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___y_828_; lean_object* v___y_833_; lean_object* v___y_838_; lean_object* v___y_843_; 
switch(lean_obj_tag(v_e_824_))
{
case 4:
{
lean_object* v_declName_847_; lean_object* v_map_848_; lean_object* v_set_849_; lean_object* v___x_850_; 
v_declName_847_ = lean_ctor_get(v_e_824_, 0);
v_map_848_ = lean_ctor_get(v_a_826_, 0);
v_set_849_ = lean_ctor_get(v_a_826_, 1);
v___x_850_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_849_, v_e_824_);
if (lean_obj_tag(v___x_850_) == 0)
{
uint8_t v___x_851_; 
lean_inc(v_declName_847_);
lean_inc_ref(v_a_825_);
v___x_851_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_825_, v_declName_847_);
if (v___x_851_ == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_861_; 
lean_inc_ref(v_set_849_);
lean_inc_ref(v_map_848_);
v_isSharedCheck_861_ = !lean_is_exclusive(v_a_826_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; lean_object* v_unused_863_; 
v_unused_862_ = lean_ctor_get(v_a_826_, 1);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_a_826_, 0);
lean_dec(v_unused_863_);
v___x_853_ = v_a_826_;
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
else
{
lean_dec(v_a_826_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = lean_box(0);
lean_inc_ref(v_e_824_);
v___x_856_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_849_, v_e_824_, v___x_855_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_856_);
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_map_848_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_860_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_e_824_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
return v___x_859_;
}
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref_known(v_e_824_, 2);
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_a_826_);
return v___x_865_;
}
}
else
{
lean_object* v_val_866_; lean_object* v_fst_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref_known(v_e_824_, 2);
v_val_866_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v___x_850_, 1);
v_fst_867_ = lean_ctor_get(v_val_866_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_val_866_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v_val_866_, 1);
lean_dec(v_unused_875_);
v___x_869_ = v_val_866_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_fst_867_);
lean_dec(v_val_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v_a_826_);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fst_867_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_a_826_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
case 5:
{
lean_object* v_fn_876_; lean_object* v_arg_877_; lean_object* v_map_878_; lean_object* v_set_879_; lean_object* v___x_880_; 
v_fn_876_ = lean_ctor_get(v_e_824_, 0);
v_arg_877_ = lean_ctor_get(v_e_824_, 1);
v_map_878_ = lean_ctor_get(v_a_826_, 0);
v_set_879_ = lean_ctor_get(v_a_826_, 1);
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_878_, v_e_824_);
if (lean_obj_tag(v___x_880_) == 1)
{
lean_object* v_val_881_; lean_object* v___x_882_; 
lean_dec_ref_known(v_e_824_, 2);
v_val_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_val_881_);
lean_ctor_set(v___x_882_, 1, v_a_826_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; uint64_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; size_t v___x_887_; size_t v___x_888_; uint8_t v___x_889_; 
lean_dec(v___x_880_);
v___x_883_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_884_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_824_);
v___x_885_ = lean_uint64_to_usize(v___x_884_);
v___x_886_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_879_, v___x_885_, v_e_824_, v___x_883_);
v___x_887_ = lean_ptr_addr(v___x_886_);
v___x_888_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_889_ = lean_usize_dec_eq(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec_ref_known(v_e_824_, 2);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_886_);
lean_ctor_set(v___x_890_, 1, v_a_826_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; 
lean_dec_ref(v___x_886_);
lean_inc_ref(v_fn_876_);
v___x_891_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_876_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
v_a_893_ = lean_ctor_get(v___x_891_, 1);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_891_, 2);
lean_inc_ref(v_arg_877_);
v___x_894_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_877_, v_a_825_, v_a_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_a_896_; size_t v___x_897_; size_t v___x_898_; uint8_t v___x_899_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
v_a_896_ = lean_ctor_get(v___x_894_, 1);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_894_, 2);
v___x_897_ = lean_ptr_addr(v_fn_876_);
v___x_898_ = lean_ptr_addr(v_a_892_);
v___x_899_ = lean_usize_dec_eq(v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = l_Lean_Expr_app___override(v_a_892_, v_a_895_);
v___x_901_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_900_, v_a_896_);
return v___x_901_;
}
else
{
size_t v___x_902_; size_t v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_ptr_addr(v_arg_877_);
v___x_903_ = lean_ptr_addr(v_a_895_);
v___x_904_ = lean_usize_dec_eq(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = l_Lean_Expr_app___override(v_a_892_, v_a_895_);
v___x_906_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_905_, v_a_896_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; 
lean_dec(v_a_895_);
lean_dec(v_a_892_);
lean_inc_ref(v_e_824_);
v___x_907_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_e_824_, v_a_896_);
return v___x_907_;
}
}
}
else
{
lean_dec(v_a_892_);
v___y_828_ = v___x_894_;
goto v___jp_827_;
}
}
else
{
v___y_828_ = v___x_891_;
goto v___jp_827_;
}
}
}
}
case 6:
{
lean_object* v_binderName_908_; lean_object* v_binderType_909_; lean_object* v_body_910_; uint8_t v_binderInfo_911_; lean_object* v_map_912_; lean_object* v_set_913_; lean_object* v___x_914_; 
v_binderName_908_ = lean_ctor_get(v_e_824_, 0);
v_binderType_909_ = lean_ctor_get(v_e_824_, 1);
v_body_910_ = lean_ctor_get(v_e_824_, 2);
v_binderInfo_911_ = lean_ctor_get_uint8(v_e_824_, sizeof(void*)*3 + 8);
v_map_912_ = lean_ctor_get(v_a_826_, 0);
v_set_913_ = lean_ctor_get(v_a_826_, 1);
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_912_, v_e_824_);
if (lean_obj_tag(v___x_914_) == 1)
{
lean_object* v_val_915_; lean_object* v___x_916_; 
lean_dec_ref_known(v_e_824_, 3);
v_val_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_val_915_);
lean_ctor_set(v___x_916_, 1, v_a_826_);
return v___x_916_;
}
else
{
lean_object* v___x_917_; uint64_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; size_t v___x_921_; size_t v___x_922_; uint8_t v___x_923_; 
lean_dec(v___x_914_);
v___x_917_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_918_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_824_);
v___x_919_ = lean_uint64_to_usize(v___x_918_);
v___x_920_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_913_, v___x_919_, v_e_824_, v___x_917_);
v___x_921_ = lean_ptr_addr(v___x_920_);
v___x_922_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_923_ = lean_usize_dec_eq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec_ref_known(v_e_824_, 3);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_920_);
lean_ctor_set(v___x_924_, 1, v_a_826_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; 
lean_dec_ref(v___x_920_);
lean_inc_ref(v_binderType_909_);
v___x_925_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_909_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
v_a_927_ = lean_ctor_get(v___x_925_, 1);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_925_, 2);
lean_inc_ref(v_body_910_);
v___x_928_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_910_, v_a_825_, v_a_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_a_930_; size_t v___x_931_; size_t v___x_932_; uint8_t v___x_933_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
v_a_930_ = lean_ctor_get(v___x_928_, 1);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_928_, 2);
v___x_931_ = lean_ptr_addr(v_binderType_909_);
v___x_932_ = lean_ptr_addr(v_a_926_);
v___x_933_ = lean_usize_dec_eq(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_inc(v_binderName_908_);
v___x_934_ = l_Lean_Expr_lam___override(v_binderName_908_, v_a_926_, v_a_929_, v_binderInfo_911_);
v___x_935_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_934_, v_a_930_);
return v___x_935_;
}
else
{
size_t v___x_936_; size_t v___x_937_; uint8_t v___x_938_; 
v___x_936_ = lean_ptr_addr(v_body_910_);
v___x_937_ = lean_ptr_addr(v_a_929_);
v___x_938_ = lean_usize_dec_eq(v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_inc(v_binderName_908_);
v___x_939_ = l_Lean_Expr_lam___override(v_binderName_908_, v_a_926_, v_a_929_, v_binderInfo_911_);
v___x_940_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_939_, v_a_930_);
return v___x_940_;
}
else
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_911_, v_binderInfo_911_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_inc(v_binderName_908_);
v___x_942_ = l_Lean_Expr_lam___override(v_binderName_908_, v_a_926_, v_a_929_, v_binderInfo_911_);
v___x_943_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_942_, v_a_930_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; 
lean_dec(v_a_929_);
lean_dec(v_a_926_);
lean_inc_ref(v_e_824_);
v___x_944_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_e_824_, v_a_930_);
return v___x_944_;
}
}
}
}
else
{
lean_dec(v_a_926_);
v___y_833_ = v___x_928_;
goto v___jp_832_;
}
}
else
{
v___y_833_ = v___x_925_;
goto v___jp_832_;
}
}
}
}
case 7:
{
lean_object* v_binderName_945_; lean_object* v_binderType_946_; lean_object* v_body_947_; uint8_t v_binderInfo_948_; lean_object* v_map_949_; lean_object* v_set_950_; lean_object* v___x_951_; 
v_binderName_945_ = lean_ctor_get(v_e_824_, 0);
v_binderType_946_ = lean_ctor_get(v_e_824_, 1);
v_body_947_ = lean_ctor_get(v_e_824_, 2);
v_binderInfo_948_ = lean_ctor_get_uint8(v_e_824_, sizeof(void*)*3 + 8);
v_map_949_ = lean_ctor_get(v_a_826_, 0);
v_set_950_ = lean_ctor_get(v_a_826_, 1);
v___x_951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_949_, v_e_824_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_val_952_; lean_object* v___x_953_; 
lean_dec_ref_known(v_e_824_, 3);
v_val_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_val_952_);
lean_ctor_set(v___x_953_, 1, v_a_826_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; uint64_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; size_t v___x_958_; size_t v___x_959_; uint8_t v___x_960_; 
lean_dec(v___x_951_);
v___x_954_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_955_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_824_);
v___x_956_ = lean_uint64_to_usize(v___x_955_);
v___x_957_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_950_, v___x_956_, v_e_824_, v___x_954_);
v___x_958_ = lean_ptr_addr(v___x_957_);
v___x_959_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_960_ = lean_usize_dec_eq(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
lean_dec_ref_known(v_e_824_, 3);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_957_);
lean_ctor_set(v___x_961_, 1, v_a_826_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; 
lean_dec_ref(v___x_957_);
lean_inc_ref(v_binderType_946_);
v___x_962_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_946_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
v_a_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_962_, 2);
lean_inc_ref(v_body_947_);
v___x_965_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_947_, v_a_825_, v_a_964_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v_a_967_; size_t v___x_968_; size_t v___x_969_; uint8_t v___x_970_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
v_a_967_ = lean_ctor_get(v___x_965_, 1);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_965_, 2);
v___x_968_ = lean_ptr_addr(v_binderType_946_);
v___x_969_ = lean_ptr_addr(v_a_963_);
v___x_970_ = lean_usize_dec_eq(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_inc(v_binderName_945_);
v___x_971_ = l_Lean_Expr_forallE___override(v_binderName_945_, v_a_963_, v_a_966_, v_binderInfo_948_);
v___x_972_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_971_, v_a_967_);
return v___x_972_;
}
else
{
size_t v___x_973_; size_t v___x_974_; uint8_t v___x_975_; 
v___x_973_ = lean_ptr_addr(v_body_947_);
v___x_974_ = lean_ptr_addr(v_a_966_);
v___x_975_ = lean_usize_dec_eq(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_inc(v_binderName_945_);
v___x_976_ = l_Lean_Expr_forallE___override(v_binderName_945_, v_a_963_, v_a_966_, v_binderInfo_948_);
v___x_977_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_976_, v_a_967_);
return v___x_977_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_948_, v_binderInfo_948_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_inc(v_binderName_945_);
v___x_979_ = l_Lean_Expr_forallE___override(v_binderName_945_, v_a_963_, v_a_966_, v_binderInfo_948_);
v___x_980_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_979_, v_a_967_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; 
lean_dec(v_a_966_);
lean_dec(v_a_963_);
lean_inc_ref(v_e_824_);
v___x_981_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_e_824_, v_a_967_);
return v___x_981_;
}
}
}
}
else
{
lean_dec(v_a_963_);
v___y_838_ = v___x_965_;
goto v___jp_837_;
}
}
else
{
v___y_838_ = v___x_962_;
goto v___jp_837_;
}
}
}
}
case 8:
{
lean_object* v_declName_982_; lean_object* v_type_983_; lean_object* v_value_984_; lean_object* v_body_985_; uint8_t v_nondep_986_; lean_object* v_map_987_; lean_object* v_set_988_; lean_object* v___x_989_; 
v_declName_982_ = lean_ctor_get(v_e_824_, 0);
v_type_983_ = lean_ctor_get(v_e_824_, 1);
v_value_984_ = lean_ctor_get(v_e_824_, 2);
v_body_985_ = lean_ctor_get(v_e_824_, 3);
v_nondep_986_ = lean_ctor_get_uint8(v_e_824_, sizeof(void*)*4 + 8);
v_map_987_ = lean_ctor_get(v_a_826_, 0);
v_set_988_ = lean_ctor_get(v_a_826_, 1);
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_987_, v_e_824_);
if (lean_obj_tag(v___x_989_) == 1)
{
lean_object* v_val_990_; lean_object* v___x_991_; 
lean_dec_ref_known(v_e_824_, 4);
v_val_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_val_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_val_990_);
lean_ctor_set(v___x_991_, 1, v_a_826_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; uint64_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; size_t v___x_996_; size_t v___x_997_; uint8_t v___x_998_; 
lean_dec(v___x_989_);
v___x_992_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_993_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_824_);
v___x_994_ = lean_uint64_to_usize(v___x_993_);
v___x_995_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_988_, v___x_994_, v_e_824_, v___x_992_);
v___x_996_ = lean_ptr_addr(v___x_995_);
v___x_997_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_998_ = lean_usize_dec_eq(v___x_996_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_dec_ref_known(v_e_824_, 4);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_995_);
lean_ctor_set(v___x_999_, 1, v_a_826_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; 
lean_dec_ref(v___x_995_);
lean_inc_ref(v_type_983_);
v___x_1000_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_983_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
v_a_1002_ = lean_ctor_get(v___x_1000_, 1);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1000_, 2);
lean_inc_ref(v_value_984_);
v___x_1003_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_984_, v_a_825_, v_a_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
v_a_1005_ = lean_ctor_get(v___x_1003_, 1);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1003_, 2);
lean_inc_ref(v_body_985_);
v___x_1006_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_985_, v_a_825_, v_a_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v_a_1008_; size_t v___x_1009_; size_t v___x_1010_; uint8_t v___x_1011_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
v_a_1008_ = lean_ctor_get(v___x_1006_, 1);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1006_, 2);
v___x_1009_ = lean_ptr_addr(v_type_983_);
v___x_1010_ = lean_ptr_addr(v_a_1001_);
v___x_1011_ = lean_usize_dec_eq(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_inc(v_declName_982_);
v___x_1012_ = l_Lean_Expr_letE___override(v_declName_982_, v_a_1001_, v_a_1004_, v_a_1007_, v_nondep_986_);
v___x_1013_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_1012_, v_a_1008_);
return v___x_1013_;
}
else
{
size_t v___x_1014_; size_t v___x_1015_; uint8_t v___x_1016_; 
v___x_1014_ = lean_ptr_addr(v_value_984_);
v___x_1015_ = lean_ptr_addr(v_a_1004_);
v___x_1016_ = lean_usize_dec_eq(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_inc(v_declName_982_);
v___x_1017_ = l_Lean_Expr_letE___override(v_declName_982_, v_a_1001_, v_a_1004_, v_a_1007_, v_nondep_986_);
v___x_1018_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_1017_, v_a_1008_);
return v___x_1018_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; uint8_t v___x_1021_; 
v___x_1019_ = lean_ptr_addr(v_body_985_);
v___x_1020_ = lean_ptr_addr(v_a_1007_);
v___x_1021_ = lean_usize_dec_eq(v___x_1019_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_inc(v_declName_982_);
v___x_1022_ = l_Lean_Expr_letE___override(v_declName_982_, v_a_1001_, v_a_1004_, v_a_1007_, v_nondep_986_);
v___x_1023_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_1022_, v_a_1008_);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; 
lean_dec(v_a_1007_);
lean_dec(v_a_1004_);
lean_dec(v_a_1001_);
lean_inc_ref(v_e_824_);
v___x_1024_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_e_824_, v_a_1008_);
return v___x_1024_;
}
}
}
}
else
{
lean_dec(v_a_1004_);
lean_dec(v_a_1001_);
v___y_843_ = v___x_1006_;
goto v___jp_842_;
}
}
else
{
lean_dec(v_a_1001_);
v___y_843_ = v___x_1003_;
goto v___jp_842_;
}
}
else
{
v___y_843_ = v___x_1000_;
goto v___jp_842_;
}
}
}
}
case 10:
{
lean_object* v_data_1025_; lean_object* v_expr_1026_; lean_object* v_map_1027_; lean_object* v_set_1028_; lean_object* v___x_1029_; 
v_data_1025_ = lean_ctor_get(v_e_824_, 0);
v_expr_1026_ = lean_ctor_get(v_e_824_, 1);
v_map_1027_ = lean_ctor_get(v_a_826_, 0);
v_set_1028_ = lean_ctor_get(v_a_826_, 1);
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1027_, v_e_824_);
if (lean_obj_tag(v___x_1029_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1031_; 
lean_dec_ref_known(v_e_824_, 2);
v_val_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_val_1030_);
lean_ctor_set(v___x_1031_, 1, v_a_826_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; uint64_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; uint8_t v___x_1038_; 
lean_dec(v___x_1029_);
v___x_1032_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1033_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_824_);
v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
v___x_1035_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1028_, v___x_1034_, v_e_824_, v___x_1032_);
v___x_1036_ = lean_ptr_addr(v___x_1035_);
v___x_1037_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1038_ = lean_usize_dec_eq(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref_known(v_e_824_, 2);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1035_);
lean_ctor_set(v___x_1039_, 1, v_a_826_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; 
lean_dec_ref(v___x_1035_);
lean_inc_ref(v_expr_1026_);
v___x_1040_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1026_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v_a_1042_; size_t v___x_1043_; size_t v___x_1044_; uint8_t v___x_1045_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
v_a_1042_ = lean_ctor_get(v___x_1040_, 1);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1040_, 2);
v___x_1043_ = lean_ptr_addr(v_expr_1026_);
v___x_1044_ = lean_ptr_addr(v_a_1041_);
v___x_1045_ = lean_usize_dec_eq(v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_inc(v_data_1025_);
v___x_1046_ = l_Lean_Expr_mdata___override(v_data_1025_, v_a_1041_);
v___x_1047_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_1046_, v_a_1042_);
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; 
lean_dec(v_a_1041_);
lean_inc_ref(v_e_824_);
v___x_1048_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_e_824_, v_a_1042_);
return v___x_1048_;
}
}
else
{
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1049_; lean_object* v_a_1050_; lean_object* v___x_1051_; 
v_a_1049_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1049_);
v_a_1050_ = lean_ctor_get(v___x_1040_, 1);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1040_, 2);
v___x_1051_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_a_1049_, v_a_1050_);
return v___x_1051_;
}
else
{
lean_dec_ref_known(v_e_824_, 2);
return v___x_1040_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1052_; lean_object* v_idx_1053_; lean_object* v_struct_1054_; lean_object* v_map_1055_; lean_object* v_set_1056_; lean_object* v___x_1057_; 
v_typeName_1052_ = lean_ctor_get(v_e_824_, 0);
v_idx_1053_ = lean_ctor_get(v_e_824_, 1);
v_struct_1054_ = lean_ctor_get(v_e_824_, 2);
v_map_1055_ = lean_ctor_get(v_a_826_, 0);
v_set_1056_ = lean_ctor_get(v_a_826_, 1);
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1055_, v_e_824_);
if (lean_obj_tag(v___x_1057_) == 1)
{
lean_object* v_val_1058_; lean_object* v___x_1059_; 
lean_dec_ref_known(v_e_824_, 3);
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_val_1058_);
lean_ctor_set(v___x_1059_, 1, v_a_826_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; uint64_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; uint8_t v___x_1066_; 
lean_dec(v___x_1057_);
v___x_1060_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1061_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_824_);
v___x_1062_ = lean_uint64_to_usize(v___x_1061_);
v___x_1063_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1056_, v___x_1062_, v_e_824_, v___x_1060_);
v___x_1064_ = lean_ptr_addr(v___x_1063_);
v___x_1065_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1066_ = lean_usize_dec_eq(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_dec_ref_known(v_e_824_, 3);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1063_);
lean_ctor_set(v___x_1067_, 1, v_a_826_);
return v___x_1067_;
}
else
{
uint8_t v_checkProj_1068_; 
lean_dec_ref(v___x_1063_);
v_checkProj_1068_ = lean_ctor_get_uint8(v_a_825_, sizeof(void*)*1 + 1);
if (v_checkProj_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_inc_ref(v_struct_1054_);
v___x_1069_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1054_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_a_1071_; size_t v___x_1072_; size_t v___x_1073_; uint8_t v___x_1074_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
v_a_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1072_ = lean_ptr_addr(v_struct_1054_);
v___x_1073_ = lean_ptr_addr(v_a_1070_);
v___x_1074_ = lean_usize_dec_eq(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_inc(v_idx_1053_);
lean_inc(v_typeName_1052_);
v___x_1075_ = l_Lean_Expr_proj___override(v_typeName_1052_, v_idx_1053_, v_a_1070_);
v___x_1076_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v___x_1075_, v_a_1071_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_a_1070_);
lean_inc_ref(v_e_824_);
v___x_1077_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_e_824_, v_a_1071_);
return v___x_1077_;
}
}
else
{
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1078_);
v_a_1079_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1080_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_a_1078_, v_a_1079_);
return v___x_1080_;
}
else
{
lean_dec_ref_known(v_e_824_, 3);
return v___x_1069_;
}
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref_known(v_e_824_, 3);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_a_826_);
return v___x_1082_;
}
}
}
}
default: 
{
lean_object* v_map_1083_; lean_object* v_set_1084_; lean_object* v___x_1085_; 
v_map_1083_ = lean_ctor_get(v_a_826_, 0);
v_set_1084_ = lean_ctor_get(v_a_826_, 1);
v___x_1085_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1084_, v_e_824_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1095_; 
lean_inc_ref(v_set_1084_);
lean_inc_ref(v_map_1083_);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_a_826_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; lean_object* v_unused_1097_; 
v_unused_1096_ = lean_ctor_get(v_a_826_, 1);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_a_826_, 0);
lean_dec(v_unused_1097_);
v___x_1087_ = v_a_826_;
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v_a_826_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = lean_box(0);
lean_inc_ref(v_e_824_);
v___x_1090_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1084_, v_e_824_, v___x_1089_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v___x_1090_);
v___x_1092_ = v___x_1087_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_map_1083_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_e_824_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
return v___x_1093_;
}
}
}
else
{
lean_object* v_val_1098_; lean_object* v_fst_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_e_824_);
v_val_1098_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1098_);
lean_dec_ref_known(v___x_1085_, 1);
v_fst_1099_ = lean_ctor_get(v_val_1098_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_val_1098_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v_val_1098_, 1);
lean_dec(v_unused_1107_);
v___x_1101_ = v_val_1098_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_fst_1099_);
lean_dec(v_val_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_a_826_);
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_fst_1099_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_a_826_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
v___jp_827_:
{
if (lean_obj_tag(v___y_828_) == 0)
{
lean_object* v_a_829_; lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_829_ = lean_ctor_get(v___y_828_, 0);
lean_inc(v_a_829_);
v_a_830_ = lean_ctor_get(v___y_828_, 1);
lean_inc(v_a_830_);
lean_dec_ref_known(v___y_828_, 2);
v___x_831_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_a_829_, v_a_830_);
return v___x_831_;
}
else
{
lean_dec_ref(v_e_824_);
return v___y_828_;
}
}
v___jp_832_:
{
if (lean_obj_tag(v___y_833_) == 0)
{
lean_object* v_a_834_; lean_object* v_a_835_; lean_object* v___x_836_; 
v_a_834_ = lean_ctor_get(v___y_833_, 0);
lean_inc(v_a_834_);
v_a_835_ = lean_ctor_get(v___y_833_, 1);
lean_inc(v_a_835_);
lean_dec_ref_known(v___y_833_, 2);
v___x_836_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_a_834_, v_a_835_);
return v___x_836_;
}
else
{
lean_dec_ref(v_e_824_);
return v___y_833_;
}
}
v___jp_837_:
{
if (lean_obj_tag(v___y_838_) == 0)
{
lean_object* v_a_839_; lean_object* v_a_840_; lean_object* v___x_841_; 
v_a_839_ = lean_ctor_get(v___y_838_, 0);
lean_inc(v_a_839_);
v_a_840_ = lean_ctor_get(v___y_838_, 1);
lean_inc(v_a_840_);
lean_dec_ref_known(v___y_838_, 2);
v___x_841_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_a_839_, v_a_840_);
return v___x_841_;
}
else
{
lean_dec_ref(v_e_824_);
return v___y_838_;
}
}
v___jp_842_:
{
if (lean_obj_tag(v___y_843_) == 0)
{
lean_object* v_a_844_; lean_object* v_a_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___y_843_, 0);
lean_inc(v_a_844_);
v_a_845_ = lean_ctor_get(v___y_843_, 1);
lean_inc(v_a_845_);
lean_dec_ref_known(v___y_843_, 2);
v___x_846_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_824_, v_a_844_, v_a_845_);
return v___x_846_;
}
else
{
lean_dec_ref(v_e_824_);
return v___y_843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1108_, v_a_1109_, v_a_1110_);
lean_dec_ref(v_a_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1113_, v_x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1116_, v_x_1117_, v_x_1118_);
lean_dec_ref(v_x_1118_);
lean_dec_ref(v_x_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1121_, v_a_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1124_, lean_object* v_m_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1124_, v_m_1125_, v_a_1126_);
lean_dec_ref(v_a_1126_);
lean_dec_ref(v_m_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, size_t v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1129_, v_x_1130_, v_x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
size_t v_x_11701__boxed_1137_; lean_object* v_res_1138_; 
v_x_11701__boxed_1137_ = lean_unbox_usize(v_x_1135_);
lean_dec(v_x_1135_);
v_res_1138_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1133_, v_x_1134_, v_x_11701__boxed_1137_, v_x_1136_);
lean_dec_ref(v_x_1136_);
lean_dec_ref(v_x_1134_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1139_, lean_object* v_a_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1143_, lean_object* v_a_1144_, lean_object* v_x_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1143_, v_a_1144_, v_x_1145_);
lean_dec(v_x_1145_);
lean_dec_ref(v_a_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1147_, lean_object* v_keys_1148_, lean_object* v_vals_1149_, lean_object* v_heq_1150_, lean_object* v_i_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1148_, v_vals_1149_, v_i_1151_, v_k_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_heq_1157_, lean_object* v_i_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1154_, v_keys_1155_, v_vals_1156_, v_heq_1157_, v_i_1158_, v_k_1159_);
lean_dec_ref(v_k_1159_);
lean_dec_ref(v_vals_1156_);
lean_dec_ref(v_keys_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1161_, lean_object* v_cache_1162_, lean_object* v_ctx_1163_, lean_object* v_s_1164_){
_start:
{
lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; 
v___f_1165_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1166_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1161_);
v___x_1167_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1165_, v___f_1166_, v_s_1164_, v_e_1161_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_cache_1162_);
lean_ctor_set(v___x_1168_, 1, v_s_1164_);
v___x_1169_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1161_, v_ctx_1163_, v___x_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1179_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 1);
v_a_1171_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1173_ = v___x_1169_;
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1170_);
lean_inc(v_a_1171_);
lean_dec(v___x_1169_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1179_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_set_1175_; lean_object* v___x_1177_; 
v_set_1175_ = lean_ctor_get(v_a_1170_, 1);
lean_inc_ref(v_set_1175_);
lean_dec(v_a_1170_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_set_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_set_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_a_1180_ = lean_ctor_get(v___x_1169_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v___x_1169_, 0);
lean_dec(v_unused_1190_);
v___x_1182_ = v___x_1169_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1169_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_map_1184_; lean_object* v_set_1185_; lean_object* v___x_1187_; 
v_map_1184_ = lean_ctor_get(v_a_1180_, 0);
lean_inc_ref(v_map_1184_);
v_set_1185_ = lean_ctor_get(v_a_1180_, 1);
lean_inc_ref(v_set_1185_);
lean_dec(v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v_set_1185_);
lean_ctor_set(v___x_1182_, 0, v_map_1184_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_map_1184_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_set_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_val_1191_; lean_object* v_fst_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_cache_1162_);
lean_dec_ref(v_e_1161_);
v_val_1191_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_val_1191_);
lean_dec_ref_known(v___x_1167_, 1);
v_fst_1192_ = lean_ctor_get(v_val_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_val_1191_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_val_1191_, 1);
lean_dec(v_unused_1200_);
v___x_1194_ = v_val_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_fst_1192_);
lean_dec(v_val_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v_s_1164_);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_fst_1192_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_s_1164_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1201_, lean_object* v_cache_1202_, lean_object* v_ctx_1203_, lean_object* v_s_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1201_, v_cache_1202_, v_ctx_1203_, v_s_1204_);
lean_dec_ref(v_ctx_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; uint64_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1209_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1206_);
v___x_1210_ = lean_uint64_to_usize(v___x_1209_);
v___x_1211_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1207_, v___x_1210_, v_e_1206_, v___x_1208_);
v___x_1212_ = lean_ptr_addr(v___x_1211_);
v___x_1213_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1214_ = lean_usize_dec_eq(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec_ref(v_e_1206_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1211_);
lean_ctor_set(v___x_1215_, 1, v_a_1207_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v___x_1211_);
v___x_1216_ = lean_box(0);
lean_inc_ref(v_e_1206_);
v___x_1217_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1207_, v_e_1206_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_e_1206_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1219_, v_a_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1223_, v_a_1224_, v_a_1225_);
lean_dec_ref(v_a_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1227_, lean_object* v_k_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___f_1231_; lean_object* v___x_1232_; uint64_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; uint8_t v___x_1238_; 
v___f_1231_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1232_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1233_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1227_);
v___x_1234_ = lean_uint64_to_usize(v___x_1233_);
lean_inc_ref(v_a_1230_);
v___x_1235_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1231_, v_a_1230_, v___x_1234_, v_e_1227_, v___x_1232_);
v___x_1236_ = lean_ptr_addr(v___x_1235_);
v___x_1237_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1238_ = lean_usize_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref(v_k_1228_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1235_);
lean_ctor_set(v___x_1239_, 1, v_a_1230_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; 
lean_dec(v___x_1235_);
lean_inc_ref(v_a_1229_);
v___x_1240_ = lean_apply_2(v_k_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1243_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
v_a_1242_ = lean_ctor_get(v___x_1240_, 1);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1240_, 2);
v___x_1243_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1241_, v_a_1242_);
return v___x_1243_;
}
else
{
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1244_, lean_object* v_k_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1244_, v_k_1245_, v_a_1246_, v_a_1247_);
lean_dec_ref(v_a_1246_);
return v_res_1248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_unsigned_to_nat(16u);
v___x_1251_ = lean_mk_array(v___x_1250_, v___x_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___y_1259_; lean_object* v___y_1264_; lean_object* v___y_1269_; lean_object* v___y_1274_; 
switch(lean_obj_tag(v_e_1255_))
{
case 4:
{
lean_object* v_declName_1278_; lean_object* v___x_1279_; uint64_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; uint8_t v___x_1285_; 
v_declName_1278_ = lean_ctor_get(v_e_1255_, 0);
v___x_1279_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1280_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1255_);
v___x_1281_ = lean_uint64_to_usize(v___x_1280_);
v___x_1282_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1257_, v___x_1281_, v_e_1255_, v___x_1279_);
v___x_1283_ = lean_ptr_addr(v___x_1282_);
v___x_1284_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1285_ = lean_usize_dec_eq(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_dec_ref_known(v_e_1255_, 2);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1282_);
lean_ctor_set(v___x_1286_, 1, v_a_1257_);
return v___x_1286_;
}
else
{
uint8_t v___x_1287_; 
lean_dec_ref(v___x_1282_);
lean_inc(v_declName_1278_);
lean_inc_ref(v_a_1256_);
v___x_1287_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1256_, v_declName_1278_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
lean_inc_ref(v_e_1255_);
v___x_1289_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1257_, v_e_1255_, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_e_1255_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref_known(v_e_1255_, 2);
v___x_1291_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_a_1257_);
return v___x_1292_;
}
}
}
case 5:
{
lean_object* v_fn_1293_; lean_object* v_arg_1294_; lean_object* v___x_1295_; uint64_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; uint8_t v___x_1301_; 
v_fn_1293_ = lean_ctor_get(v_e_1255_, 0);
v_arg_1294_ = lean_ctor_get(v_e_1255_, 1);
v___x_1295_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1255_);
v___x_1297_ = lean_uint64_to_usize(v___x_1296_);
v___x_1298_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1257_, v___x_1297_, v_e_1255_, v___x_1295_);
v___x_1299_ = lean_ptr_addr(v___x_1298_);
v___x_1300_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1301_ = lean_usize_dec_eq(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref_known(v_e_1255_, 2);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1298_);
lean_ctor_set(v___x_1302_, 1, v_a_1257_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; 
lean_dec_ref(v___x_1298_);
lean_inc_ref(v_fn_1293_);
v___x_1303_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1293_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v_a_1305_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
v_a_1305_ = lean_ctor_get(v___x_1303_, 1);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1303_, 2);
lean_inc_ref(v_arg_1294_);
v___x_1306_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1294_, v_a_1256_, v_a_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v_a_1308_; size_t v___x_1309_; size_t v___x_1310_; uint8_t v___x_1311_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
v_a_1308_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1306_, 2);
v___x_1309_ = lean_ptr_addr(v_fn_1293_);
v___x_1310_ = lean_ptr_addr(v_a_1304_);
v___x_1311_ = lean_usize_dec_eq(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref_known(v_e_1255_, 2);
v___x_1312_ = l_Lean_Expr_app___override(v_a_1304_, v_a_1307_);
v___x_1313_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1312_, v_a_1308_);
return v___x_1313_;
}
else
{
size_t v___x_1314_; size_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_ptr_addr(v_arg_1294_);
v___x_1315_ = lean_ptr_addr(v_a_1307_);
v___x_1316_ = lean_usize_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref_known(v_e_1255_, 2);
v___x_1317_ = l_Lean_Expr_app___override(v_a_1304_, v_a_1307_);
v___x_1318_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1317_, v_a_1308_);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; 
lean_dec(v_a_1307_);
lean_dec(v_a_1304_);
v___x_1319_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1255_, v_a_1308_);
return v___x_1319_;
}
}
}
else
{
lean_dec(v_a_1304_);
lean_dec_ref_known(v_e_1255_, 2);
v___y_1259_ = v___x_1306_;
goto v___jp_1258_;
}
}
else
{
lean_dec_ref_known(v_e_1255_, 2);
v___y_1259_ = v___x_1303_;
goto v___jp_1258_;
}
}
}
case 6:
{
lean_object* v_binderName_1320_; lean_object* v_binderType_1321_; lean_object* v_body_1322_; uint8_t v_binderInfo_1323_; lean_object* v___x_1324_; uint64_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; uint8_t v___x_1330_; 
v_binderName_1320_ = lean_ctor_get(v_e_1255_, 0);
v_binderType_1321_ = lean_ctor_get(v_e_1255_, 1);
v_body_1322_ = lean_ctor_get(v_e_1255_, 2);
v_binderInfo_1323_ = lean_ctor_get_uint8(v_e_1255_, sizeof(void*)*3 + 8);
v___x_1324_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1325_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1255_);
v___x_1326_ = lean_uint64_to_usize(v___x_1325_);
v___x_1327_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1257_, v___x_1326_, v_e_1255_, v___x_1324_);
v___x_1328_ = lean_ptr_addr(v___x_1327_);
v___x_1329_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1330_ = lean_usize_dec_eq(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
lean_dec_ref_known(v_e_1255_, 3);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1327_);
lean_ctor_set(v___x_1331_, 1, v_a_1257_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; 
lean_dec_ref(v___x_1327_);
lean_inc_ref(v_binderType_1321_);
v___x_1332_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1321_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v_a_1334_; lean_object* v___x_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
v_a_1334_ = lean_ctor_get(v___x_1332_, 1);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1332_, 2);
lean_inc_ref(v_body_1322_);
v___x_1335_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1322_, v_a_1256_, v_a_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_a_1337_; size_t v___x_1338_; size_t v___x_1339_; uint8_t v___x_1340_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
v_a_1337_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1335_, 2);
v___x_1338_ = lean_ptr_addr(v_binderType_1321_);
v___x_1339_ = lean_ptr_addr(v_a_1333_);
v___x_1340_ = lean_usize_dec_eq(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_inc(v_binderName_1320_);
lean_dec_ref_known(v_e_1255_, 3);
v___x_1341_ = l_Lean_Expr_lam___override(v_binderName_1320_, v_a_1333_, v_a_1336_, v_binderInfo_1323_);
v___x_1342_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1341_, v_a_1337_);
return v___x_1342_;
}
else
{
size_t v___x_1343_; size_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1343_ = lean_ptr_addr(v_body_1322_);
v___x_1344_ = lean_ptr_addr(v_a_1336_);
v___x_1345_ = lean_usize_dec_eq(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_inc(v_binderName_1320_);
lean_dec_ref_known(v_e_1255_, 3);
v___x_1346_ = l_Lean_Expr_lam___override(v_binderName_1320_, v_a_1333_, v_a_1336_, v_binderInfo_1323_);
v___x_1347_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1346_, v_a_1337_);
return v___x_1347_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1323_, v_binderInfo_1323_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_inc(v_binderName_1320_);
lean_dec_ref_known(v_e_1255_, 3);
v___x_1349_ = l_Lean_Expr_lam___override(v_binderName_1320_, v_a_1333_, v_a_1336_, v_binderInfo_1323_);
v___x_1350_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1349_, v_a_1337_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; 
lean_dec(v_a_1336_);
lean_dec(v_a_1333_);
v___x_1351_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1255_, v_a_1337_);
return v___x_1351_;
}
}
}
}
else
{
lean_dec(v_a_1333_);
lean_dec_ref_known(v_e_1255_, 3);
v___y_1264_ = v___x_1335_;
goto v___jp_1263_;
}
}
else
{
lean_dec_ref_known(v_e_1255_, 3);
v___y_1264_ = v___x_1332_;
goto v___jp_1263_;
}
}
}
case 7:
{
lean_object* v_binderName_1352_; lean_object* v_binderType_1353_; lean_object* v_body_1354_; uint8_t v_binderInfo_1355_; lean_object* v___x_1356_; uint64_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; uint8_t v___x_1362_; 
v_binderName_1352_ = lean_ctor_get(v_e_1255_, 0);
v_binderType_1353_ = lean_ctor_get(v_e_1255_, 1);
v_body_1354_ = lean_ctor_get(v_e_1255_, 2);
v_binderInfo_1355_ = lean_ctor_get_uint8(v_e_1255_, sizeof(void*)*3 + 8);
v___x_1356_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1357_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1255_);
v___x_1358_ = lean_uint64_to_usize(v___x_1357_);
v___x_1359_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1257_, v___x_1358_, v_e_1255_, v___x_1356_);
v___x_1360_ = lean_ptr_addr(v___x_1359_);
v___x_1361_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1362_ = lean_usize_dec_eq(v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref_known(v_e_1255_, 3);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1359_);
lean_ctor_set(v___x_1363_, 1, v_a_1257_);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; 
lean_dec_ref(v___x_1359_);
lean_inc_ref(v_binderType_1353_);
v___x_1364_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1353_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
v_a_1366_ = lean_ctor_get(v___x_1364_, 1);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1364_, 2);
lean_inc_ref(v_body_1354_);
v___x_1367_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1354_, v_a_1256_, v_a_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v_a_1369_; size_t v___x_1370_; size_t v___x_1371_; uint8_t v___x_1372_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
v_a_1369_ = lean_ctor_get(v___x_1367_, 1);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1367_, 2);
v___x_1370_ = lean_ptr_addr(v_binderType_1353_);
v___x_1371_ = lean_ptr_addr(v_a_1365_);
v___x_1372_ = lean_usize_dec_eq(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_inc(v_binderName_1352_);
lean_dec_ref_known(v_e_1255_, 3);
v___x_1373_ = l_Lean_Expr_forallE___override(v_binderName_1352_, v_a_1365_, v_a_1368_, v_binderInfo_1355_);
v___x_1374_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1373_, v_a_1369_);
return v___x_1374_;
}
else
{
size_t v___x_1375_; size_t v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_ptr_addr(v_body_1354_);
v___x_1376_ = lean_ptr_addr(v_a_1368_);
v___x_1377_ = lean_usize_dec_eq(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_inc(v_binderName_1352_);
lean_dec_ref_known(v_e_1255_, 3);
v___x_1378_ = l_Lean_Expr_forallE___override(v_binderName_1352_, v_a_1365_, v_a_1368_, v_binderInfo_1355_);
v___x_1379_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1378_, v_a_1369_);
return v___x_1379_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1355_, v_binderInfo_1355_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_inc(v_binderName_1352_);
lean_dec_ref_known(v_e_1255_, 3);
v___x_1381_ = l_Lean_Expr_forallE___override(v_binderName_1352_, v_a_1365_, v_a_1368_, v_binderInfo_1355_);
v___x_1382_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1381_, v_a_1369_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; 
lean_dec(v_a_1368_);
lean_dec(v_a_1365_);
v___x_1383_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1255_, v_a_1369_);
return v___x_1383_;
}
}
}
}
else
{
lean_dec(v_a_1365_);
lean_dec_ref_known(v_e_1255_, 3);
v___y_1269_ = v___x_1367_;
goto v___jp_1268_;
}
}
else
{
lean_dec_ref_known(v_e_1255_, 3);
v___y_1269_ = v___x_1364_;
goto v___jp_1268_;
}
}
}
case 8:
{
lean_object* v_declName_1384_; lean_object* v_type_1385_; lean_object* v_value_1386_; lean_object* v_body_1387_; uint8_t v_nondep_1388_; lean_object* v___x_1389_; uint64_t v___x_1390_; size_t v___x_1391_; lean_object* v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; uint8_t v___x_1395_; 
v_declName_1384_ = lean_ctor_get(v_e_1255_, 0);
v_type_1385_ = lean_ctor_get(v_e_1255_, 1);
v_value_1386_ = lean_ctor_get(v_e_1255_, 2);
v_body_1387_ = lean_ctor_get(v_e_1255_, 3);
v_nondep_1388_ = lean_ctor_get_uint8(v_e_1255_, sizeof(void*)*4 + 8);
v___x_1389_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1390_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1255_);
v___x_1391_ = lean_uint64_to_usize(v___x_1390_);
v___x_1392_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1257_, v___x_1391_, v_e_1255_, v___x_1389_);
v___x_1393_ = lean_ptr_addr(v___x_1392_);
v___x_1394_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1395_ = lean_usize_dec_eq(v___x_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref_known(v_e_1255_, 4);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1392_);
lean_ctor_set(v___x_1396_, 1, v_a_1257_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; 
lean_dec_ref(v___x_1392_);
lean_inc_ref(v_type_1385_);
v___x_1397_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1385_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_a_1399_; lean_object* v___x_1400_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
v_a_1399_ = lean_ctor_get(v___x_1397_, 1);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1397_, 2);
lean_inc_ref(v_value_1386_);
v___x_1400_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1386_, v_a_1256_, v_a_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
v_a_1402_ = lean_ctor_get(v___x_1400_, 1);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1400_, 2);
lean_inc_ref(v_body_1387_);
v___x_1403_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1387_, v_a_1256_, v_a_1402_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v_a_1405_; size_t v___x_1406_; size_t v___x_1407_; uint8_t v___x_1408_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
v_a_1405_ = lean_ctor_get(v___x_1403_, 1);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1403_, 2);
v___x_1406_ = lean_ptr_addr(v_type_1385_);
v___x_1407_ = lean_ptr_addr(v_a_1398_);
v___x_1408_ = lean_usize_dec_eq(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_inc(v_declName_1384_);
lean_dec_ref_known(v_e_1255_, 4);
v___x_1409_ = l_Lean_Expr_letE___override(v_declName_1384_, v_a_1398_, v_a_1401_, v_a_1404_, v_nondep_1388_);
v___x_1410_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1409_, v_a_1405_);
return v___x_1410_;
}
else
{
size_t v___x_1411_; size_t v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = lean_ptr_addr(v_value_1386_);
v___x_1412_ = lean_ptr_addr(v_a_1401_);
v___x_1413_ = lean_usize_dec_eq(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_inc(v_declName_1384_);
lean_dec_ref_known(v_e_1255_, 4);
v___x_1414_ = l_Lean_Expr_letE___override(v_declName_1384_, v_a_1398_, v_a_1401_, v_a_1404_, v_nondep_1388_);
v___x_1415_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1414_, v_a_1405_);
return v___x_1415_;
}
else
{
size_t v___x_1416_; size_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_ptr_addr(v_body_1387_);
v___x_1417_ = lean_ptr_addr(v_a_1404_);
v___x_1418_ = lean_usize_dec_eq(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_inc(v_declName_1384_);
lean_dec_ref_known(v_e_1255_, 4);
v___x_1419_ = l_Lean_Expr_letE___override(v_declName_1384_, v_a_1398_, v_a_1401_, v_a_1404_, v_nondep_1388_);
v___x_1420_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1419_, v_a_1405_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; 
lean_dec(v_a_1404_);
lean_dec(v_a_1401_);
lean_dec(v_a_1398_);
v___x_1421_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1255_, v_a_1405_);
return v___x_1421_;
}
}
}
}
else
{
lean_dec(v_a_1401_);
lean_dec(v_a_1398_);
lean_dec_ref_known(v_e_1255_, 4);
v___y_1274_ = v___x_1403_;
goto v___jp_1273_;
}
}
else
{
lean_dec(v_a_1398_);
lean_dec_ref_known(v_e_1255_, 4);
v___y_1274_ = v___x_1400_;
goto v___jp_1273_;
}
}
else
{
lean_dec_ref_known(v_e_1255_, 4);
v___y_1274_ = v___x_1397_;
goto v___jp_1273_;
}
}
}
case 10:
{
lean_object* v_data_1422_; lean_object* v_expr_1423_; lean_object* v___x_1424_; uint64_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v_data_1422_ = lean_ctor_get(v_e_1255_, 0);
v_expr_1423_ = lean_ctor_get(v_e_1255_, 1);
v___x_1424_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1425_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1255_);
v___x_1426_ = lean_uint64_to_usize(v___x_1425_);
v___x_1427_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1257_, v___x_1426_, v_e_1255_, v___x_1424_);
v___x_1428_ = lean_ptr_addr(v___x_1427_);
v___x_1429_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1430_ = lean_usize_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref_known(v_e_1255_, 2);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1427_);
lean_ctor_set(v___x_1431_, 1, v_a_1257_);
return v___x_1431_;
}
else
{
lean_object* v___x_1432_; 
lean_dec_ref(v___x_1427_);
lean_inc_ref(v_expr_1423_);
v___x_1432_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1423_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v_a_1434_; size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
v_a_1434_ = lean_ctor_get(v___x_1432_, 1);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1432_, 2);
v___x_1435_ = lean_ptr_addr(v_expr_1423_);
v___x_1436_ = lean_ptr_addr(v_a_1433_);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_inc(v_data_1422_);
lean_dec_ref_known(v_e_1255_, 2);
v___x_1438_ = l_Lean_Expr_mdata___override(v_data_1422_, v_a_1433_);
v___x_1439_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1438_, v_a_1434_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_a_1433_);
v___x_1440_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1255_, v_a_1434_);
return v___x_1440_;
}
}
else
{
lean_dec_ref_known(v_e_1255_, 2);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1441_; lean_object* v_a_1442_; lean_object* v___x_1443_; 
v_a_1441_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1441_);
v_a_1442_ = lean_ctor_get(v___x_1432_, 1);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1432_, 2);
v___x_1443_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1441_, v_a_1442_);
return v___x_1443_;
}
else
{
return v___x_1432_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1444_; lean_object* v_idx_1445_; lean_object* v_struct_1446_; lean_object* v___x_1447_; uint64_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; uint8_t v___x_1453_; 
v_typeName_1444_ = lean_ctor_get(v_e_1255_, 0);
v_idx_1445_ = lean_ctor_get(v_e_1255_, 1);
v_struct_1446_ = lean_ctor_get(v_e_1255_, 2);
v___x_1447_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1448_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1255_);
v___x_1449_ = lean_uint64_to_usize(v___x_1448_);
v___x_1450_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1257_, v___x_1449_, v_e_1255_, v___x_1447_);
v___x_1451_ = lean_ptr_addr(v___x_1450_);
v___x_1452_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1453_ = lean_usize_dec_eq(v___x_1451_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec_ref_known(v_e_1255_, 3);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1450_);
lean_ctor_set(v___x_1454_, 1, v_a_1257_);
return v___x_1454_;
}
else
{
uint8_t v_checkProj_1455_; 
lean_dec_ref(v___x_1450_);
v_checkProj_1455_ = lean_ctor_get_uint8(v_a_1256_, sizeof(void*)*1 + 1);
if (v_checkProj_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_inc_ref(v_struct_1446_);
v___x_1456_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1446_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v_a_1458_; size_t v___x_1459_; size_t v___x_1460_; uint8_t v___x_1461_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
v_a_1458_ = lean_ctor_get(v___x_1456_, 1);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1456_, 2);
v___x_1459_ = lean_ptr_addr(v_struct_1446_);
v___x_1460_ = lean_ptr_addr(v_a_1457_);
v___x_1461_ = lean_usize_dec_eq(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_inc(v_idx_1445_);
lean_inc(v_typeName_1444_);
lean_dec_ref_known(v_e_1255_, 3);
v___x_1462_ = l_Lean_Expr_proj___override(v_typeName_1444_, v_idx_1445_, v_a_1457_);
v___x_1463_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1462_, v_a_1458_);
return v___x_1463_;
}
else
{
lean_object* v___x_1464_; 
lean_dec(v_a_1457_);
v___x_1464_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1255_, v_a_1458_);
return v___x_1464_;
}
}
else
{
lean_dec_ref_known(v_e_1255_, 3);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1465_; lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1465_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1465_);
v_a_1466_ = lean_ctor_get(v___x_1456_, 1);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1456_, 2);
v___x_1467_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1465_, v_a_1466_);
return v___x_1467_;
}
else
{
return v___x_1456_;
}
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref_known(v_e_1255_, 3);
v___x_1468_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_a_1257_);
return v___x_1469_;
}
}
}
default: 
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1255_, v_a_1257_);
return v___x_1470_;
}
}
v___jp_1258_:
{
if (lean_obj_tag(v___y_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1260_ = lean_ctor_get(v___y_1259_, 0);
lean_inc(v_a_1260_);
v_a_1261_ = lean_ctor_get(v___y_1259_, 1);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___y_1259_, 2);
v___x_1262_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1260_, v_a_1261_);
return v___x_1262_;
}
else
{
return v___y_1259_;
}
}
v___jp_1263_:
{
if (lean_obj_tag(v___y_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1265_ = lean_ctor_get(v___y_1264_, 0);
lean_inc(v_a_1265_);
v_a_1266_ = lean_ctor_get(v___y_1264_, 1);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___y_1264_, 2);
v___x_1267_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1265_, v_a_1266_);
return v___x_1267_;
}
else
{
return v___y_1264_;
}
}
v___jp_1268_:
{
if (lean_obj_tag(v___y_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1270_ = lean_ctor_get(v___y_1269_, 0);
lean_inc(v_a_1270_);
v_a_1271_ = lean_ctor_get(v___y_1269_, 1);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___y_1269_, 2);
v___x_1272_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1270_, v_a_1271_);
return v___x_1272_;
}
else
{
return v___y_1269_;
}
}
v___jp_1273_:
{
if (lean_obj_tag(v___y_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v_a_1276_; lean_object* v___x_1277_; 
v_a_1275_ = lean_ctor_get(v___y_1274_, 0);
lean_inc(v_a_1275_);
v_a_1276_ = lean_ctor_get(v___y_1274_, 1);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___y_1274_, 2);
v___x_1277_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1275_, v_a_1276_);
return v___x_1277_;
}
else
{
return v___y_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1471_, v_a_1472_, v_a_1473_);
lean_dec_ref(v_a_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1475_, v_a_1476_, v_a_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1479_, v_a_1480_, v_a_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1482_;
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

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
if (v_nondep_110_ == 0)
{
if (v_nondep_113_ == 0)
{
goto v___jp_114_;
}
else
{
return v_nondep_110_;
}
}
else
{
if (v_nondep_113_ == 0)
{
return v_nondep_113_;
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
size_t v_x_2094__boxed_262_; lean_object* v_res_263_; 
v_x_2094__boxed_262_ = lean_unbox_usize(v_x_259_);
lean_dec(v_x_259_);
v_res_263_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_258_, v_x_2094__boxed_262_, v_x_260_, v_x_261_);
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
lean_object* v_ks_351_; lean_object* v_vs_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_372_; 
v_ks_351_ = lean_ctor_get(v_x_300_, 0);
v_vs_352_ = lean_ctor_get(v_x_300_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_372_ == 0)
{
v___x_354_ = v_x_300_;
v_isShared_355_ = v_isSharedCheck_372_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_vs_352_);
lean_inc(v_ks_351_);
lean_dec(v_x_300_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_372_;
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
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_ks_351_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_vs_352_);
v___x_357_ = v_reuseFailAlloc_371_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v_newNode_358_; uint8_t v___y_360_; size_t v___x_366_; uint8_t v___x_367_; 
v_newNode_358_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_357_, v_x_303_, v_x_304_);
v___x_366_ = ((size_t)7ULL);
v___x_367_ = lean_usize_dec_le(v___x_366_, v_x_302_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_358_);
v___x_369_ = lean_unsigned_to_nat(4u);
v___x_370_ = lean_nat_dec_lt(v___x_368_, v___x_369_);
lean_dec(v___x_368_);
v___y_360_ = v___x_370_;
goto v___jp_359_;
}
else
{
v___y_360_ = v___x_367_;
goto v___jp_359_;
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v_ks_361_; lean_object* v_vs_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_ks_361_ = lean_ctor_get(v_newNode_358_, 0);
lean_inc_ref(v_ks_361_);
v_vs_362_ = lean_ctor_get(v_newNode_358_, 1);
lean_inc_ref(v_vs_362_);
lean_dec_ref(v_newNode_358_);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_302_, v_ks_361_, v_vs_362_, v___x_363_, v___x_364_);
lean_dec_ref(v_vs_362_);
lean_dec_ref(v_ks_361_);
return v___x_365_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_373_, lean_object* v_keys_374_, lean_object* v_vals_375_, lean_object* v_i_376_, lean_object* v_entries_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_array_get_size(v_keys_374_);
v___x_379_ = lean_nat_dec_lt(v_i_376_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec(v_i_376_);
return v_entries_377_;
}
else
{
lean_object* v_k_380_; lean_object* v_v_381_; uint64_t v___x_382_; size_t v_h_383_; size_t v___x_384_; lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v_h_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_k_380_ = lean_array_fget_borrowed(v_keys_374_, v_i_376_);
v_v_381_ = lean_array_fget_borrowed(v_vals_375_, v_i_376_);
v___x_382_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_380_);
v_h_383_ = lean_uint64_to_usize(v___x_382_);
v___x_384_ = ((size_t)5ULL);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_sub(v_depth_373_, v___x_386_);
v___x_388_ = lean_usize_mul(v___x_384_, v___x_387_);
v_h_389_ = lean_usize_shift_right(v_h_383_, v___x_388_);
v___x_390_ = lean_nat_add(v_i_376_, v___x_385_);
lean_dec(v_i_376_);
lean_inc(v_v_381_);
lean_inc(v_k_380_);
v___x_391_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_377_, v_h_389_, v_depth_373_, v_k_380_, v_v_381_);
v_i_376_ = v___x_390_;
v_entries_377_ = v___x_391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_393_, lean_object* v_keys_394_, lean_object* v_vals_395_, lean_object* v_i_396_, lean_object* v_entries_397_){
_start:
{
size_t v_depth_boxed_398_; lean_object* v_res_399_; 
v_depth_boxed_398_ = lean_unbox_usize(v_depth_393_);
lean_dec(v_depth_393_);
v_res_399_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_398_, v_keys_394_, v_vals_395_, v_i_396_, v_entries_397_);
lean_dec_ref(v_vals_395_);
lean_dec_ref(v_keys_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
size_t v_x_2212__boxed_405_; size_t v_x_2213__boxed_406_; lean_object* v_res_407_; 
v_x_2212__boxed_405_ = lean_unbox_usize(v_x_401_);
lean_dec(v_x_401_);
v_x_2213__boxed_406_ = lean_unbox_usize(v_x_402_);
lean_dec(v_x_402_);
v_res_407_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_400_, v_x_2212__boxed_405_, v_x_2213__boxed_406_, v_x_403_, v_x_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
uint64_t v___x_411_; size_t v___x_412_; size_t v___x_413_; lean_object* v___x_414_; 
v___x_411_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_409_);
v___x_412_ = lean_uint64_to_usize(v___x_411_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_408_, v___x_412_, v___x_413_, v_x_409_, v_x_410_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_415_, lean_object* v_b_416_, lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_dec(v_b_416_);
lean_dec_ref(v_a_415_);
return v_x_417_;
}
else
{
lean_object* v_key_418_; lean_object* v_value_419_; lean_object* v_tail_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_434_; 
v_key_418_ = lean_ctor_get(v_x_417_, 0);
v_value_419_ = lean_ctor_get(v_x_417_, 1);
v_tail_420_ = lean_ctor_get(v_x_417_, 2);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_422_ = v_x_417_;
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_tail_420_);
lean_inc(v_value_419_);
lean_inc(v_key_418_);
lean_dec(v_x_417_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
size_t v___x_424_; size_t v___x_425_; uint8_t v___x_426_; 
v___x_424_ = lean_ptr_addr(v_key_418_);
v___x_425_ = lean_ptr_addr(v_a_415_);
v___x_426_ = lean_usize_dec_eq(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_415_, v_b_416_, v_tail_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 2, v___x_427_);
v___x_429_ = v___x_422_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_key_418_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_value_419_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_object* v___x_432_; 
lean_dec(v_value_419_);
lean_dec(v_key_418_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v_b_416_);
lean_ctor_set(v___x_422_, 0, v_a_415_);
v___x_432_ = v___x_422_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_b_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_tail_420_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_436_) == 0)
{
return v_x_435_;
}
else
{
lean_object* v_key_437_; lean_object* v_value_438_; lean_object* v_tail_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_465_; 
v_key_437_ = lean_ctor_get(v_x_436_, 0);
v_value_438_ = lean_ctor_get(v_x_436_, 1);
v_tail_439_ = lean_ctor_get(v_x_436_, 2);
v_isSharedCheck_465_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_465_ == 0)
{
v___x_441_ = v_x_436_;
v_isShared_442_ = v_isSharedCheck_465_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_tail_439_);
lean_inc(v_value_438_);
lean_inc(v_key_437_);
lean_dec(v_x_436_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_465_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v_fold_450_; uint64_t v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_443_ = lean_array_get_size(v_x_435_);
v___x_444_ = lean_ptr_addr(v_key_437_);
v___x_445_ = ((size_t)3ULL);
v___x_446_ = lean_usize_shift_right(v___x_444_, v___x_445_);
v___x_447_ = lean_usize_to_uint64(v___x_446_);
v___x_448_ = 32ULL;
v___x_449_ = lean_uint64_shift_right(v___x_447_, v___x_448_);
v_fold_450_ = lean_uint64_xor(v___x_447_, v___x_449_);
v___x_451_ = 16ULL;
v___x_452_ = lean_uint64_shift_right(v_fold_450_, v___x_451_);
v___x_453_ = lean_uint64_xor(v_fold_450_, v___x_452_);
v___x_454_ = lean_uint64_to_usize(v___x_453_);
v___x_455_ = lean_usize_of_nat(v___x_443_);
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_sub(v___x_455_, v___x_456_);
v___x_458_ = lean_usize_land(v___x_454_, v___x_457_);
v___x_459_ = lean_array_uget_borrowed(v_x_435_, v___x_458_);
lean_inc(v___x_459_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 2, v___x_459_);
v___x_461_ = v___x_441_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_key_437_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_value_438_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___x_459_);
v___x_461_ = v_reuseFailAlloc_464_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = lean_array_uset(v_x_435_, v___x_458_, v___x_461_);
v_x_435_ = v___x_462_;
v_x_436_ = v_tail_439_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_466_, lean_object* v_source_467_, lean_object* v_target_468_){
_start:
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_array_get_size(v_source_467_);
v___x_470_ = lean_nat_dec_lt(v_i_466_, v___x_469_);
if (v___x_470_ == 0)
{
lean_dec_ref(v_source_467_);
lean_dec(v_i_466_);
return v_target_468_;
}
else
{
lean_object* v_es_471_; lean_object* v___x_472_; lean_object* v_source_473_; lean_object* v_target_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_es_471_ = lean_array_fget(v_source_467_, v_i_466_);
v___x_472_ = lean_box(0);
v_source_473_ = lean_array_fset(v_source_467_, v_i_466_, v___x_472_);
v_target_474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_468_, v_es_471_);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_add(v_i_466_, v___x_475_);
lean_dec(v_i_466_);
v_i_466_ = v___x_476_;
v_source_467_ = v_source_473_;
v_target_468_ = v_target_474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_nbuckets_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_479_ = lean_array_get_size(v_data_478_);
v___x_480_ = lean_unsigned_to_nat(2u);
v_nbuckets_481_ = lean_nat_mul(v___x_479_, v___x_480_);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_box(0);
v___x_484_ = lean_mk_array(v_nbuckets_481_, v___x_483_);
v___x_485_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_482_, v_data_478_, v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_486_, lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
uint8_t v___x_488_; 
v___x_488_ = 0;
return v___x_488_;
}
else
{
lean_object* v_key_489_; lean_object* v_tail_490_; size_t v___x_491_; size_t v___x_492_; uint8_t v___x_493_; 
v_key_489_ = lean_ctor_get(v_x_487_, 0);
v_tail_490_ = lean_ctor_get(v_x_487_, 2);
v___x_491_ = lean_ptr_addr(v_key_489_);
v___x_492_ = lean_ptr_addr(v_a_486_);
v___x_493_ = lean_usize_dec_eq(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
v_x_487_ = v_tail_490_;
goto _start;
}
else
{
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_495_, lean_object* v_x_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_495_, v_x_496_);
lean_dec(v_x_496_);
lean_dec_ref(v_a_495_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_499_, lean_object* v_a_500_, lean_object* v_b_501_){
_start:
{
lean_object* v_size_502_; lean_object* v_buckets_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_549_; 
v_size_502_ = lean_ctor_get(v_m_499_, 0);
v_buckets_503_ = lean_ctor_get(v_m_499_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_m_499_);
if (v_isSharedCheck_549_ == 0)
{
v___x_505_ = v_m_499_;
v_isShared_506_ = v_isSharedCheck_549_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_buckets_503_);
lean_inc(v_size_502_);
lean_dec(v_m_499_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_549_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v_fold_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v_bkt_523_; uint8_t v___x_524_; 
v___x_507_ = lean_array_get_size(v_buckets_503_);
v___x_508_ = lean_ptr_addr(v_a_500_);
v___x_509_ = ((size_t)3ULL);
v___x_510_ = lean_usize_shift_right(v___x_508_, v___x_509_);
v___x_511_ = lean_usize_to_uint64(v___x_510_);
v___x_512_ = 32ULL;
v___x_513_ = lean_uint64_shift_right(v___x_511_, v___x_512_);
v_fold_514_ = lean_uint64_xor(v___x_511_, v___x_513_);
v___x_515_ = 16ULL;
v___x_516_ = lean_uint64_shift_right(v_fold_514_, v___x_515_);
v___x_517_ = lean_uint64_xor(v_fold_514_, v___x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = lean_usize_of_nat(v___x_507_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_sub(v___x_519_, v___x_520_);
v___x_522_ = lean_usize_land(v___x_518_, v___x_521_);
v_bkt_523_ = lean_array_uget_borrowed(v_buckets_503_, v___x_522_);
v___x_524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_500_, v_bkt_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v_size_x27_526_; lean_object* v___x_527_; lean_object* v_buckets_x27_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v_size_x27_526_ = lean_nat_add(v_size_502_, v___x_525_);
lean_dec(v_size_502_);
lean_inc(v_bkt_523_);
v___x_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_527_, 0, v_a_500_);
lean_ctor_set(v___x_527_, 1, v_b_501_);
lean_ctor_set(v___x_527_, 2, v_bkt_523_);
v_buckets_x27_528_ = lean_array_uset(v_buckets_503_, v___x_522_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(4u);
v___x_530_ = lean_nat_mul(v_size_x27_526_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(3u);
v___x_532_ = lean_nat_div(v___x_530_, v___x_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_array_get_size(v_buckets_x27_528_);
v___x_534_ = lean_nat_dec_le(v___x_532_, v___x_533_);
lean_dec(v___x_532_);
if (v___x_534_ == 0)
{
lean_object* v_val_535_; lean_object* v___x_537_; 
v_val_535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_528_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v_val_535_);
lean_ctor_set(v___x_505_, 0, v_size_x27_526_);
v___x_537_ = v___x_505_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_val_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
lean_object* v___x_540_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v_buckets_x27_528_);
lean_ctor_set(v___x_505_, 0, v_size_x27_526_);
v___x_540_ = v___x_505_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_size_x27_526_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_buckets_x27_528_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v___x_542_; lean_object* v_buckets_x27_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
lean_inc(v_bkt_523_);
v___x_542_ = lean_box(0);
v_buckets_x27_543_ = lean_array_uset(v_buckets_503_, v___x_522_, v___x_542_);
v___x_544_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_500_, v_b_501_, v_bkt_523_);
v___x_545_ = lean_array_uset(v_buckets_x27_543_, v___x_522_, v___x_544_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v___x_545_);
v___x_547_ = v___x_505_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_size_502_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_550_; size_t v___x_551_; 
v___x_550_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_551_ = lean_ptr_addr(v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_552_, lean_object* v_r_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_map_555_; lean_object* v_set_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_580_; 
v_map_555_ = lean_ctor_get(v_a_554_, 0);
v_set_556_ = lean_ctor_get(v_a_554_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_580_ == 0)
{
v___x_558_ = v_a_554_;
v_isShared_559_ = v_isSharedCheck_580_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_set_556_);
lean_inc(v_map_555_);
lean_dec(v_a_554_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_580_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; uint64_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; size_t v___x_564_; size_t v___x_565_; uint8_t v___x_566_; 
v___x_560_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_561_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_553_);
v___x_562_ = lean_uint64_to_usize(v___x_561_);
v___x_563_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_556_, v___x_562_, v_r_553_, v___x_560_);
v___x_564_ = lean_ptr_addr(v___x_563_);
v___x_565_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_566_ = lean_usize_dec_eq(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_569_; 
lean_dec_ref(v_r_553_);
lean_inc_ref(v___x_563_);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_555_, v_e_552_, v___x_563_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_567_);
v___x_569_ = v___x_558_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_set_556_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_563_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
lean_dec_ref(v___x_563_);
lean_inc_ref_n(v_r_553_, 4);
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_555_, v_e_552_, v_r_553_);
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_572_, v_r_553_, v_r_553_);
v___x_574_ = lean_box(0);
v___x_575_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_556_, v_r_553_, v___x_574_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_575_);
lean_ctor_set(v___x_558_, 0, v___x_573_);
v___x_577_ = v___x_558_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_579_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_r_553_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_581_, lean_object* v_r_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_581_, v_r_582_, v_a_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_586_, lean_object* v_r_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_586_, v_r_587_, v_a_588_, v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_591_, lean_object* v_x_592_, size_t v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_592_, v_x_593_, v_x_594_, v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_597_, lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
size_t v_x_2667__boxed_602_; lean_object* v_res_603_; 
v_x_2667__boxed_602_ = lean_unbox_usize(v_x_599_);
lean_dec(v_x_599_);
v_res_603_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_597_, v_x_598_, v_x_2667__boxed_602_, v_x_600_, v_x_601_);
lean_dec_ref(v_x_601_);
lean_dec_ref(v_x_600_);
lean_dec_ref(v_x_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_604_, lean_object* v_m_605_, lean_object* v_a_606_, lean_object* v_b_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_605_, v_a_606_, v_b_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_610_, v_x_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_keys_615_, lean_object* v_vals_616_, lean_object* v_heq_617_, lean_object* v_i_618_, lean_object* v_k_619_, lean_object* v_k_u2080_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_615_, v_i_618_, v_k_619_, v_k_u2080_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_622_, lean_object* v_keys_623_, lean_object* v_vals_624_, lean_object* v_heq_625_, lean_object* v_i_626_, lean_object* v_k_627_, lean_object* v_k_u2080_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_622_, v_keys_623_, v_vals_624_, v_heq_625_, v_i_626_, v_k_627_, v_k_u2080_628_);
lean_dec_ref(v_k_u2080_628_);
lean_dec_ref(v_k_627_);
lean_dec_ref(v_vals_624_);
lean_dec_ref(v_keys_623_);
return v_res_629_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_630_, lean_object* v_a_631_, lean_object* v_x_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_634_, lean_object* v_a_635_, lean_object* v_x_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_634_, v_a_635_, v_x_636_);
lean_dec(v_x_636_);
lean_dec_ref(v_a_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_639_, lean_object* v_data_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_642_, lean_object* v_a_643_, lean_object* v_b_644_, lean_object* v_x_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_643_, v_b_644_, v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_647_, lean_object* v_x_648_, size_t v_x_649_, size_t v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_648_, v_x_649_, v_x_650_, v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
size_t v_x_2704__boxed_660_; size_t v_x_2705__boxed_661_; lean_object* v_res_662_; 
v_x_2704__boxed_660_ = lean_unbox_usize(v_x_656_);
lean_dec(v_x_656_);
v_x_2705__boxed_661_ = lean_unbox_usize(v_x_657_);
lean_dec(v_x_657_);
v_res_662_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_654_, v_x_655_, v_x_2704__boxed_660_, v_x_2705__boxed_661_, v_x_658_, v_x_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_663_, lean_object* v_i_664_, lean_object* v_source_665_, lean_object* v_target_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_664_, v_source_665_, v_target_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_668_, lean_object* v_n_669_, lean_object* v_k_670_, lean_object* v_v_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_669_, v_k_670_, v_v_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_673_, size_t v_depth_674_, lean_object* v_keys_675_, lean_object* v_vals_676_, lean_object* v_heq_677_, lean_object* v_i_678_, lean_object* v_entries_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_674_, v_keys_675_, v_vals_676_, v_i_678_, v_entries_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_681_, lean_object* v_depth_682_, lean_object* v_keys_683_, lean_object* v_vals_684_, lean_object* v_heq_685_, lean_object* v_i_686_, lean_object* v_entries_687_){
_start:
{
size_t v_depth_boxed_688_; lean_object* v_res_689_; 
v_depth_boxed_688_ = lean_unbox_usize(v_depth_682_);
lean_dec(v_depth_682_);
v_res_689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_681_, v_depth_boxed_688_, v_keys_683_, v_vals_684_, v_heq_685_, v_i_686_, v_entries_687_);
lean_dec_ref(v_vals_684_);
lean_dec_ref(v_keys_683_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_691_, v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_695_, v_x_696_, v_x_697_, v_x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_702_, lean_object* v_k_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_map_706_; lean_object* v_set_707_; lean_object* v___f_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v_map_706_ = lean_ctor_get(v_a_705_, 0);
v_set_707_ = lean_ctor_get(v_a_705_, 1);
v___f_708_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_709_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_702_);
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_708_, v___f_709_, v_map_706_, v_e_702_);
if (lean_obj_tag(v___x_710_) == 1)
{
lean_object* v_val_711_; lean_object* v___x_712_; 
lean_dec_ref(v_k_703_);
lean_dec_ref(v_e_702_);
v_val_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_val_711_);
lean_ctor_set(v___x_712_, 1, v_a_705_);
return v___x_712_;
}
else
{
lean_object* v___f_713_; lean_object* v___x_714_; uint64_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; size_t v___x_718_; size_t v___x_719_; uint8_t v___x_720_; 
lean_dec(v___x_710_);
v___f_713_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_714_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_715_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_702_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
lean_inc_ref(v_e_702_);
lean_inc_ref(v_set_707_);
v___x_717_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_713_, v_set_707_, v___x_716_, v_e_702_, v___x_714_);
v___x_718_ = lean_ptr_addr(v___x_717_);
v___x_719_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_720_ = lean_usize_dec_eq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec_ref(v_k_703_);
lean_dec_ref(v_e_702_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_717_);
lean_ctor_set(v___x_721_, 1, v_a_705_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
lean_dec(v___x_717_);
lean_inc_ref(v_a_704_);
v___x_722_ = lean_apply_2(v_k_703_, v_a_704_, v_a_705_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
v_a_724_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_722_, 2);
v___x_725_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_702_, v_a_723_, v_a_724_);
return v___x_725_;
}
else
{
lean_dec_ref(v_e_702_);
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_726_, lean_object* v_k_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_726_, v_k_727_, v_a_728_, v_a_729_);
lean_dec_ref(v_a_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_731_, lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_box(0);
return v___x_733_;
}
else
{
lean_object* v_key_734_; lean_object* v_value_735_; lean_object* v_tail_736_; size_t v___x_737_; size_t v___x_738_; uint8_t v___x_739_; 
v_key_734_ = lean_ctor_get(v_x_732_, 0);
v_value_735_ = lean_ctor_get(v_x_732_, 1);
v_tail_736_ = lean_ctor_get(v_x_732_, 2);
v___x_737_ = lean_ptr_addr(v_key_734_);
v___x_738_ = lean_ptr_addr(v_a_731_);
v___x_739_ = lean_usize_dec_eq(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
v_x_732_ = v_tail_736_;
goto _start;
}
else
{
lean_object* v___x_741_; 
lean_inc(v_value_735_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_value_735_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_742_, v_x_743_);
lean_dec(v_x_743_);
lean_dec_ref(v_a_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_buckets_747_; lean_object* v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v_fold_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_buckets_747_ = lean_ctor_get(v_m_745_, 1);
v___x_748_ = lean_array_get_size(v_buckets_747_);
v___x_749_ = lean_ptr_addr(v_a_746_);
v___x_750_ = ((size_t)3ULL);
v___x_751_ = lean_usize_shift_right(v___x_749_, v___x_750_);
v___x_752_ = lean_usize_to_uint64(v___x_751_);
v___x_753_ = 32ULL;
v___x_754_ = lean_uint64_shift_right(v___x_752_, v___x_753_);
v_fold_755_ = lean_uint64_xor(v___x_752_, v___x_754_);
v___x_756_ = 16ULL;
v___x_757_ = lean_uint64_shift_right(v_fold_755_, v___x_756_);
v___x_758_ = lean_uint64_xor(v_fold_755_, v___x_757_);
v___x_759_ = lean_uint64_to_usize(v___x_758_);
v___x_760_ = lean_usize_of_nat(v___x_748_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_sub(v___x_760_, v___x_761_);
v___x_763_ = lean_usize_land(v___x_759_, v___x_762_);
v___x_764_ = lean_array_uget_borrowed(v_buckets_747_, v___x_763_);
v___x_765_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_746_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_766_, v_a_767_);
lean_dec_ref(v_a_767_);
lean_dec_ref(v_m_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_769_, lean_object* v_vals_770_, lean_object* v_i_771_, lean_object* v_k_772_){
_start:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_array_get_size(v_keys_769_);
v___x_774_ = lean_nat_dec_lt(v_i_771_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v_i_771_);
v___x_775_ = lean_box(0);
return v___x_775_;
}
else
{
lean_object* v_k_x27_776_; uint8_t v___x_777_; 
v_k_x27_776_ = lean_array_fget_borrowed(v_keys_769_, v_i_771_);
v___x_777_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_772_, v_k_x27_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_nat_add(v_i_771_, v___x_778_);
lean_dec(v_i_771_);
v_i_771_ = v___x_779_;
goto _start;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_array_fget_borrowed(v_vals_770_, v_i_771_);
lean_dec(v_i_771_);
lean_inc(v___x_781_);
lean_inc(v_k_x27_776_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_k_x27_776_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_i_786_, lean_object* v_k_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_784_, v_vals_785_, v_i_786_, v_k_787_);
lean_dec_ref(v_k_787_);
lean_dec_ref(v_vals_785_);
lean_dec_ref(v_keys_784_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_789_, size_t v_x_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_object* v_es_792_; lean_object* v___x_793_; size_t v___x_794_; size_t v___x_795_; lean_object* v_j_796_; lean_object* v___x_797_; 
v_es_792_ = lean_ctor_get(v_x_789_, 0);
v___x_793_ = lean_box(2);
v___x_794_ = ((size_t)31ULL);
v___x_795_ = lean_usize_land(v_x_790_, v___x_794_);
v_j_796_ = lean_usize_to_nat(v___x_795_);
v___x_797_ = lean_array_get_borrowed(v___x_793_, v_es_792_, v_j_796_);
lean_dec(v_j_796_);
switch(lean_obj_tag(v___x_797_))
{
case 0:
{
lean_object* v_key_798_; lean_object* v_val_799_; uint8_t v___x_800_; 
v_key_798_ = lean_ctor_get(v___x_797_, 0);
v_val_799_ = lean_ctor_get(v___x_797_, 1);
v___x_800_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_791_, v_key_798_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
v___x_801_ = lean_box(0);
return v___x_801_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc(v_val_799_);
lean_inc(v_key_798_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_key_798_);
lean_ctor_set(v___x_802_, 1, v_val_799_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
case 1:
{
lean_object* v_node_804_; size_t v___x_805_; size_t v___x_806_; 
v_node_804_ = lean_ctor_get(v___x_797_, 0);
v___x_805_ = ((size_t)5ULL);
v___x_806_ = lean_usize_shift_right(v_x_790_, v___x_805_);
v_x_789_ = v_node_804_;
v_x_790_ = v___x_806_;
goto _start;
}
default: 
{
lean_object* v___x_808_; 
v___x_808_ = lean_box(0);
return v___x_808_;
}
}
}
else
{
lean_object* v_ks_809_; lean_object* v_vs_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_ks_809_ = lean_ctor_get(v_x_789_, 0);
v_vs_810_ = lean_ctor_get(v_x_789_, 1);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_809_, v_vs_810_, v___x_811_, v_x_791_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
size_t v_x_11089__boxed_816_; lean_object* v_res_817_; 
v_x_11089__boxed_816_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_res_817_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_813_, v_x_11089__boxed_816_, v_x_815_);
lean_dec_ref(v_x_815_);
lean_dec_ref(v_x_813_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
uint64_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v___x_820_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_819_);
v___x_821_ = lean_uint64_to_usize(v___x_820_);
v___x_822_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_818_, v___x_821_, v_x_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_823_, v_x_824_);
lean_dec_ref(v_x_824_);
lean_dec_ref(v_x_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___y_830_; lean_object* v___y_835_; lean_object* v___y_840_; lean_object* v___y_845_; 
switch(lean_obj_tag(v_e_826_))
{
case 4:
{
lean_object* v_declName_849_; lean_object* v_map_850_; lean_object* v_set_851_; lean_object* v___x_852_; 
v_declName_849_ = lean_ctor_get(v_e_826_, 0);
v_map_850_ = lean_ctor_get(v_a_828_, 0);
v_set_851_ = lean_ctor_get(v_a_828_, 1);
v___x_852_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_851_, v_e_826_);
if (lean_obj_tag(v___x_852_) == 0)
{
uint8_t v___x_853_; 
lean_inc(v_declName_849_);
lean_inc_ref(v_a_827_);
v___x_853_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_827_, v_declName_849_);
if (v___x_853_ == 0)
{
lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_863_; 
lean_inc_ref(v_set_851_);
lean_inc_ref(v_map_850_);
v_isSharedCheck_863_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; lean_object* v_unused_865_; 
v_unused_864_ = lean_ctor_get(v_a_828_, 1);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_a_828_, 0);
lean_dec(v_unused_865_);
v___x_855_ = v_a_828_;
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
else
{
lean_dec(v_a_828_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = lean_box(0);
lean_inc_ref(v_e_826_);
v___x_858_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_851_, v_e_826_, v___x_857_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_map_850_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_862_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_e_826_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
return v___x_861_;
}
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref_known(v_e_826_, 2);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v_a_828_);
return v___x_867_;
}
}
else
{
lean_object* v_val_868_; lean_object* v_fst_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref_known(v_e_826_, 2);
v_val_868_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v___x_852_, 1);
v_fst_869_ = lean_ctor_get(v_val_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v_val_868_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; 
v_unused_877_ = lean_ctor_get(v_val_868_, 1);
lean_dec(v_unused_877_);
v___x_871_ = v_val_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_fst_869_);
lean_dec(v_val_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v_a_828_);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_fst_869_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_a_828_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
case 5:
{
lean_object* v_fn_878_; lean_object* v_arg_879_; lean_object* v_map_880_; lean_object* v_set_881_; lean_object* v___x_882_; 
v_fn_878_ = lean_ctor_get(v_e_826_, 0);
v_arg_879_ = lean_ctor_get(v_e_826_, 1);
v_map_880_ = lean_ctor_get(v_a_828_, 0);
v_set_881_ = lean_ctor_get(v_a_828_, 1);
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_880_, v_e_826_);
if (lean_obj_tag(v___x_882_) == 1)
{
lean_object* v_val_883_; lean_object* v___x_884_; 
lean_dec_ref_known(v_e_826_, 2);
v_val_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_val_883_);
lean_ctor_set(v___x_884_, 1, v_a_828_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; uint64_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; size_t v___x_889_; size_t v___x_890_; uint8_t v___x_891_; 
lean_dec(v___x_882_);
v___x_885_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_886_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_826_);
v___x_887_ = lean_uint64_to_usize(v___x_886_);
v___x_888_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_881_, v___x_887_, v_e_826_, v___x_885_);
v___x_889_ = lean_ptr_addr(v___x_888_);
v___x_890_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_891_ = lean_usize_dec_eq(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec_ref_known(v_e_826_, 2);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_888_);
lean_ctor_set(v___x_892_, 1, v_a_828_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v___x_888_);
lean_inc_ref(v_fn_878_);
v___x_893_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_878_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
v_a_895_ = lean_ctor_get(v___x_893_, 1);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_893_, 2);
lean_inc_ref(v_arg_879_);
v___x_896_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_879_, v_a_827_, v_a_895_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_a_898_; uint8_t v___y_900_; size_t v___x_904_; size_t v___x_905_; uint8_t v___x_906_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
v_a_898_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_896_, 2);
v___x_904_ = lean_ptr_addr(v_fn_878_);
v___x_905_ = lean_ptr_addr(v_a_894_);
v___x_906_ = lean_usize_dec_eq(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
v___y_900_ = v___x_906_;
goto v___jp_899_;
}
else
{
size_t v___x_907_; size_t v___x_908_; uint8_t v___x_909_; 
v___x_907_ = lean_ptr_addr(v_arg_879_);
v___x_908_ = lean_ptr_addr(v_a_897_);
v___x_909_ = lean_usize_dec_eq(v___x_907_, v___x_908_);
v___y_900_ = v___x_909_;
goto v___jp_899_;
}
v___jp_899_:
{
if (v___y_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = l_Lean_Expr_app___override(v_a_894_, v_a_897_);
v___x_902_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_901_, v_a_898_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
lean_dec(v_a_897_);
lean_dec(v_a_894_);
lean_inc_ref(v_e_826_);
v___x_903_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_e_826_, v_a_898_);
return v___x_903_;
}
}
}
else
{
lean_dec(v_a_894_);
v___y_840_ = v___x_896_;
goto v___jp_839_;
}
}
else
{
v___y_840_ = v___x_893_;
goto v___jp_839_;
}
}
}
}
case 6:
{
lean_object* v_binderName_910_; lean_object* v_binderType_911_; lean_object* v_body_912_; uint8_t v_binderInfo_913_; lean_object* v_map_914_; lean_object* v_set_915_; lean_object* v___x_916_; 
v_binderName_910_ = lean_ctor_get(v_e_826_, 0);
v_binderType_911_ = lean_ctor_get(v_e_826_, 1);
v_body_912_ = lean_ctor_get(v_e_826_, 2);
v_binderInfo_913_ = lean_ctor_get_uint8(v_e_826_, sizeof(void*)*3 + 8);
v_map_914_ = lean_ctor_get(v_a_828_, 0);
v_set_915_ = lean_ctor_get(v_a_828_, 1);
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_914_, v_e_826_);
if (lean_obj_tag(v___x_916_) == 1)
{
lean_object* v_val_917_; lean_object* v___x_918_; 
lean_dec_ref_known(v_e_826_, 3);
v_val_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_val_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_val_917_);
lean_ctor_set(v___x_918_, 1, v_a_828_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; uint64_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; size_t v___x_923_; size_t v___x_924_; uint8_t v___x_925_; 
lean_dec(v___x_916_);
v___x_919_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_920_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_826_);
v___x_921_ = lean_uint64_to_usize(v___x_920_);
v___x_922_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_915_, v___x_921_, v_e_826_, v___x_919_);
v___x_923_ = lean_ptr_addr(v___x_922_);
v___x_924_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_925_ = lean_usize_dec_eq(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec_ref_known(v_e_826_, 3);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_922_);
lean_ctor_set(v___x_926_, 1, v_a_828_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v___x_922_);
lean_inc_ref(v_binderType_911_);
v___x_927_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_911_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v_a_929_; lean_object* v___x_930_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
v_a_929_ = lean_ctor_get(v___x_927_, 1);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_927_, 2);
lean_inc_ref(v_body_912_);
v___x_930_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_912_, v_a_827_, v_a_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v_a_932_; uint8_t v___y_934_; size_t v___x_941_; size_t v___x_942_; uint8_t v___x_943_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
v_a_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_930_, 2);
v___x_941_ = lean_ptr_addr(v_binderType_911_);
v___x_942_ = lean_ptr_addr(v_a_928_);
v___x_943_ = lean_usize_dec_eq(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
v___y_934_ = v___x_943_;
goto v___jp_933_;
}
else
{
size_t v___x_944_; size_t v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_ptr_addr(v_body_912_);
v___x_945_ = lean_ptr_addr(v_a_931_);
v___x_946_ = lean_usize_dec_eq(v___x_944_, v___x_945_);
v___y_934_ = v___x_946_;
goto v___jp_933_;
}
v___jp_933_:
{
if (v___y_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_inc(v_binderName_910_);
v___x_935_ = l_Lean_Expr_lam___override(v_binderName_910_, v_a_928_, v_a_931_, v_binderInfo_913_);
v___x_936_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_935_, v_a_932_);
return v___x_936_;
}
else
{
uint8_t v___x_937_; 
v___x_937_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_913_, v_binderInfo_913_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_inc(v_binderName_910_);
v___x_938_ = l_Lean_Expr_lam___override(v_binderName_910_, v_a_928_, v_a_931_, v_binderInfo_913_);
v___x_939_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_938_, v_a_932_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; 
lean_dec(v_a_931_);
lean_dec(v_a_928_);
lean_inc_ref(v_e_826_);
v___x_940_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_e_826_, v_a_932_);
return v___x_940_;
}
}
}
}
else
{
lean_dec(v_a_928_);
v___y_835_ = v___x_930_;
goto v___jp_834_;
}
}
else
{
v___y_835_ = v___x_927_;
goto v___jp_834_;
}
}
}
}
case 7:
{
lean_object* v_binderName_947_; lean_object* v_binderType_948_; lean_object* v_body_949_; uint8_t v_binderInfo_950_; lean_object* v_map_951_; lean_object* v_set_952_; lean_object* v___x_953_; 
v_binderName_947_ = lean_ctor_get(v_e_826_, 0);
v_binderType_948_ = lean_ctor_get(v_e_826_, 1);
v_body_949_ = lean_ctor_get(v_e_826_, 2);
v_binderInfo_950_ = lean_ctor_get_uint8(v_e_826_, sizeof(void*)*3 + 8);
v_map_951_ = lean_ctor_get(v_a_828_, 0);
v_set_952_ = lean_ctor_get(v_a_828_, 1);
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_951_, v_e_826_);
if (lean_obj_tag(v___x_953_) == 1)
{
lean_object* v_val_954_; lean_object* v___x_955_; 
lean_dec_ref_known(v_e_826_, 3);
v_val_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_val_954_);
lean_ctor_set(v___x_955_, 1, v_a_828_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; uint64_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; size_t v___x_960_; size_t v___x_961_; uint8_t v___x_962_; 
lean_dec(v___x_953_);
v___x_956_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_957_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_826_);
v___x_958_ = lean_uint64_to_usize(v___x_957_);
v___x_959_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_952_, v___x_958_, v_e_826_, v___x_956_);
v___x_960_ = lean_ptr_addr(v___x_959_);
v___x_961_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_962_ = lean_usize_dec_eq(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec_ref_known(v_e_826_, 3);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
lean_ctor_set(v___x_963_, 1, v_a_828_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; 
lean_dec_ref(v___x_959_);
lean_inc_ref(v_binderType_948_);
v___x_964_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_948_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v___x_967_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
v_a_966_ = lean_ctor_get(v___x_964_, 1);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_964_, 2);
lean_inc_ref(v_body_949_);
v___x_967_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_949_, v_a_827_, v_a_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v_a_969_; uint8_t v___y_971_; size_t v___x_978_; size_t v___x_979_; uint8_t v___x_980_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
v_a_969_ = lean_ctor_get(v___x_967_, 1);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_967_, 2);
v___x_978_ = lean_ptr_addr(v_binderType_948_);
v___x_979_ = lean_ptr_addr(v_a_965_);
v___x_980_ = lean_usize_dec_eq(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
v___y_971_ = v___x_980_;
goto v___jp_970_;
}
else
{
size_t v___x_981_; size_t v___x_982_; uint8_t v___x_983_; 
v___x_981_ = lean_ptr_addr(v_body_949_);
v___x_982_ = lean_ptr_addr(v_a_968_);
v___x_983_ = lean_usize_dec_eq(v___x_981_, v___x_982_);
v___y_971_ = v___x_983_;
goto v___jp_970_;
}
v___jp_970_:
{
if (v___y_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc(v_binderName_947_);
v___x_972_ = l_Lean_Expr_forallE___override(v_binderName_947_, v_a_965_, v_a_968_, v_binderInfo_950_);
v___x_973_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_972_, v_a_969_);
return v___x_973_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_950_, v_binderInfo_950_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_inc(v_binderName_947_);
v___x_975_ = l_Lean_Expr_forallE___override(v_binderName_947_, v_a_965_, v_a_968_, v_binderInfo_950_);
v___x_976_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_975_, v_a_969_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; 
lean_dec(v_a_968_);
lean_dec(v_a_965_);
lean_inc_ref(v_e_826_);
v___x_977_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_e_826_, v_a_969_);
return v___x_977_;
}
}
}
}
else
{
lean_dec(v_a_965_);
v___y_845_ = v___x_967_;
goto v___jp_844_;
}
}
else
{
v___y_845_ = v___x_964_;
goto v___jp_844_;
}
}
}
}
case 8:
{
lean_object* v_declName_984_; lean_object* v_type_985_; lean_object* v_value_986_; lean_object* v_body_987_; uint8_t v_nondep_988_; lean_object* v_map_989_; lean_object* v_set_990_; lean_object* v___x_991_; 
v_declName_984_ = lean_ctor_get(v_e_826_, 0);
v_type_985_ = lean_ctor_get(v_e_826_, 1);
v_value_986_ = lean_ctor_get(v_e_826_, 2);
v_body_987_ = lean_ctor_get(v_e_826_, 3);
v_nondep_988_ = lean_ctor_get_uint8(v_e_826_, sizeof(void*)*4 + 8);
v_map_989_ = lean_ctor_get(v_a_828_, 0);
v_set_990_ = lean_ctor_get(v_a_828_, 1);
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_989_, v_e_826_);
if (lean_obj_tag(v___x_991_) == 1)
{
lean_object* v_val_992_; lean_object* v___x_993_; 
lean_dec_ref_known(v_e_826_, 4);
v_val_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v_val_992_);
lean_ctor_set(v___x_993_, 1, v_a_828_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; uint64_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; size_t v___x_998_; size_t v___x_999_; uint8_t v___x_1000_; 
lean_dec(v___x_991_);
v___x_994_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_995_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_826_);
v___x_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_990_, v___x_996_, v_e_826_, v___x_994_);
v___x_998_ = lean_ptr_addr(v___x_997_);
v___x_999_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1000_ = lean_usize_dec_eq(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_dec_ref_known(v_e_826_, 4);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_997_);
lean_ctor_set(v___x_1001_, 1, v_a_828_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; 
lean_dec_ref(v___x_997_);
lean_inc_ref(v_type_985_);
v___x_1002_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_985_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
v_a_1004_ = lean_ctor_get(v___x_1002_, 1);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1002_, 2);
lean_inc_ref(v_value_986_);
v___x_1005_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_986_, v_a_827_, v_a_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
v_a_1007_ = lean_ctor_get(v___x_1005_, 1);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1005_, 2);
lean_inc_ref(v_body_987_);
v___x_1008_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_987_, v_a_827_, v_a_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v_a_1010_; uint8_t v___y_1012_; size_t v___x_1021_; size_t v___x_1022_; uint8_t v___x_1023_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
v_a_1010_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1008_, 2);
v___x_1021_ = lean_ptr_addr(v_type_985_);
v___x_1022_ = lean_ptr_addr(v_a_1003_);
v___x_1023_ = lean_usize_dec_eq(v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
v___y_1012_ = v___x_1023_;
goto v___jp_1011_;
}
else
{
size_t v___x_1024_; size_t v___x_1025_; uint8_t v___x_1026_; 
v___x_1024_ = lean_ptr_addr(v_value_986_);
v___x_1025_ = lean_ptr_addr(v_a_1006_);
v___x_1026_ = lean_usize_dec_eq(v___x_1024_, v___x_1025_);
v___y_1012_ = v___x_1026_;
goto v___jp_1011_;
}
v___jp_1011_:
{
if (v___y_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_inc(v_declName_984_);
v___x_1013_ = l_Lean_Expr_letE___override(v_declName_984_, v_a_1003_, v_a_1006_, v_a_1009_, v_nondep_988_);
v___x_1014_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_1013_, v_a_1010_);
return v___x_1014_;
}
else
{
size_t v___x_1015_; size_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1015_ = lean_ptr_addr(v_body_987_);
v___x_1016_ = lean_ptr_addr(v_a_1009_);
v___x_1017_ = lean_usize_dec_eq(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_inc(v_declName_984_);
v___x_1018_ = l_Lean_Expr_letE___override(v_declName_984_, v_a_1003_, v_a_1006_, v_a_1009_, v_nondep_988_);
v___x_1019_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_1018_, v_a_1010_);
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; 
lean_dec(v_a_1009_);
lean_dec(v_a_1006_);
lean_dec(v_a_1003_);
lean_inc_ref(v_e_826_);
v___x_1020_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_e_826_, v_a_1010_);
return v___x_1020_;
}
}
}
}
else
{
lean_dec(v_a_1006_);
lean_dec(v_a_1003_);
v___y_830_ = v___x_1008_;
goto v___jp_829_;
}
}
else
{
lean_dec(v_a_1003_);
v___y_830_ = v___x_1005_;
goto v___jp_829_;
}
}
else
{
v___y_830_ = v___x_1002_;
goto v___jp_829_;
}
}
}
}
case 10:
{
lean_object* v_data_1027_; lean_object* v_expr_1028_; lean_object* v_map_1029_; lean_object* v_set_1030_; lean_object* v___x_1031_; 
v_data_1027_ = lean_ctor_get(v_e_826_, 0);
v_expr_1028_ = lean_ctor_get(v_e_826_, 1);
v_map_1029_ = lean_ctor_get(v_a_828_, 0);
v_set_1030_ = lean_ctor_get(v_a_828_, 1);
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1029_, v_e_826_);
if (lean_obj_tag(v___x_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1033_; 
lean_dec_ref_known(v_e_826_, 2);
v_val_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_val_1032_);
lean_ctor_set(v___x_1033_, 1, v_a_828_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; uint8_t v___x_1040_; 
lean_dec(v___x_1031_);
v___x_1034_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1035_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_826_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1030_, v___x_1036_, v_e_826_, v___x_1034_);
v___x_1038_ = lean_ptr_addr(v___x_1037_);
v___x_1039_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1040_ = lean_usize_dec_eq(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref_known(v_e_826_, 2);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1037_);
lean_ctor_set(v___x_1041_, 1, v_a_828_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref(v___x_1037_);
lean_inc_ref(v_expr_1028_);
v___x_1042_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1028_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_a_1044_; size_t v___x_1045_; size_t v___x_1046_; uint8_t v___x_1047_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
v_a_1044_ = lean_ctor_get(v___x_1042_, 1);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1042_, 2);
v___x_1045_ = lean_ptr_addr(v_expr_1028_);
v___x_1046_ = lean_ptr_addr(v_a_1043_);
v___x_1047_ = lean_usize_dec_eq(v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_inc(v_data_1027_);
v___x_1048_ = l_Lean_Expr_mdata___override(v_data_1027_, v_a_1043_);
v___x_1049_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_1048_, v_a_1044_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
lean_dec(v_a_1043_);
lean_inc_ref(v_e_826_);
v___x_1050_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_e_826_, v_a_1044_);
return v___x_1050_;
}
}
else
{
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1053_; 
v_a_1051_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1051_);
v_a_1052_ = lean_ctor_get(v___x_1042_, 1);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1042_, 2);
v___x_1053_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_a_1051_, v_a_1052_);
return v___x_1053_;
}
else
{
lean_dec_ref_known(v_e_826_, 2);
return v___x_1042_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1054_; lean_object* v_idx_1055_; lean_object* v_struct_1056_; lean_object* v_map_1057_; lean_object* v_set_1058_; lean_object* v___x_1059_; 
v_typeName_1054_ = lean_ctor_get(v_e_826_, 0);
v_idx_1055_ = lean_ctor_get(v_e_826_, 1);
v_struct_1056_ = lean_ctor_get(v_e_826_, 2);
v_map_1057_ = lean_ctor_get(v_a_828_, 0);
v_set_1058_ = lean_ctor_get(v_a_828_, 1);
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1057_, v_e_826_);
if (lean_obj_tag(v___x_1059_) == 1)
{
lean_object* v_val_1060_; lean_object* v___x_1061_; 
lean_dec_ref_known(v_e_826_, 3);
v_val_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_val_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_val_1060_);
lean_ctor_set(v___x_1061_, 1, v_a_828_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; uint64_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; uint8_t v___x_1068_; 
lean_dec(v___x_1059_);
v___x_1062_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1063_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_826_);
v___x_1064_ = lean_uint64_to_usize(v___x_1063_);
v___x_1065_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1058_, v___x_1064_, v_e_826_, v___x_1062_);
v___x_1066_ = lean_ptr_addr(v___x_1065_);
v___x_1067_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1068_ = lean_usize_dec_eq(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec_ref_known(v_e_826_, 3);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1065_);
lean_ctor_set(v___x_1069_, 1, v_a_828_);
return v___x_1069_;
}
else
{
uint8_t v_checkProj_1070_; 
lean_dec_ref(v___x_1065_);
v_checkProj_1070_ = lean_ctor_get_uint8(v_a_827_, sizeof(void*)*1 + 1);
if (v_checkProj_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_inc_ref(v_struct_1056_);
v___x_1071_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1056_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_a_1073_; size_t v___x_1074_; size_t v___x_1075_; uint8_t v___x_1076_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
v_a_1073_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1071_, 2);
v___x_1074_ = lean_ptr_addr(v_struct_1056_);
v___x_1075_ = lean_ptr_addr(v_a_1072_);
v___x_1076_ = lean_usize_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc(v_idx_1055_);
lean_inc(v_typeName_1054_);
v___x_1077_ = l_Lean_Expr_proj___override(v_typeName_1054_, v_idx_1055_, v_a_1072_);
v___x_1078_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v___x_1077_, v_a_1073_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; 
lean_dec(v_a_1072_);
lean_inc_ref(v_e_826_);
v___x_1079_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_e_826_, v_a_1073_);
return v___x_1079_;
}
}
else
{
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1080_; lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1080_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1080_);
v_a_1081_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1071_, 2);
v___x_1082_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_a_1080_, v_a_1081_);
return v___x_1082_;
}
else
{
lean_dec_ref_known(v_e_826_, 3);
return v___x_1071_;
}
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref_known(v_e_826_, 3);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_828_);
return v___x_1084_;
}
}
}
}
default: 
{
lean_object* v_map_1085_; lean_object* v_set_1086_; lean_object* v___x_1087_; 
v_map_1085_ = lean_ctor_get(v_a_828_, 0);
v_set_1086_ = lean_ctor_get(v_a_828_, 1);
v___x_1087_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1086_, v_e_826_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1097_; 
lean_inc_ref(v_set_1086_);
lean_inc_ref(v_map_1085_);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; lean_object* v_unused_1099_; 
v_unused_1098_ = lean_ctor_get(v_a_828_, 1);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_a_828_, 0);
lean_dec(v_unused_1099_);
v___x_1089_ = v_a_828_;
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v_a_828_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1097_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1091_ = lean_box(0);
lean_inc_ref(v_e_826_);
v___x_1092_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1086_, v_e_826_, v___x_1091_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_map_1085_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_e_826_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
return v___x_1095_;
}
}
}
else
{
lean_object* v_val_1100_; lean_object* v_fst_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_e_826_);
v_val_1100_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_val_1100_);
lean_dec_ref_known(v___x_1087_, 1);
v_fst_1101_ = lean_ctor_get(v_val_1100_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_val_1100_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v_val_1100_, 1);
lean_dec(v_unused_1109_);
v___x_1103_ = v_val_1100_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_fst_1101_);
lean_dec(v_val_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 1, v_a_828_);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_fst_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_a_828_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
v___jp_829_:
{
if (lean_obj_tag(v___y_830_) == 0)
{
lean_object* v_a_831_; lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_831_ = lean_ctor_get(v___y_830_, 0);
lean_inc(v_a_831_);
v_a_832_ = lean_ctor_get(v___y_830_, 1);
lean_inc(v_a_832_);
lean_dec_ref_known(v___y_830_, 2);
v___x_833_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_a_831_, v_a_832_);
return v___x_833_;
}
else
{
lean_dec_ref(v_e_826_);
return v___y_830_;
}
}
v___jp_834_:
{
if (lean_obj_tag(v___y_835_) == 0)
{
lean_object* v_a_836_; lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_836_ = lean_ctor_get(v___y_835_, 0);
lean_inc(v_a_836_);
v_a_837_ = lean_ctor_get(v___y_835_, 1);
lean_inc(v_a_837_);
lean_dec_ref_known(v___y_835_, 2);
v___x_838_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_a_836_, v_a_837_);
return v___x_838_;
}
else
{
lean_dec_ref(v_e_826_);
return v___y_835_;
}
}
v___jp_839_:
{
if (lean_obj_tag(v___y_840_) == 0)
{
lean_object* v_a_841_; lean_object* v_a_842_; lean_object* v___x_843_; 
v_a_841_ = lean_ctor_get(v___y_840_, 0);
lean_inc(v_a_841_);
v_a_842_ = lean_ctor_get(v___y_840_, 1);
lean_inc(v_a_842_);
lean_dec_ref_known(v___y_840_, 2);
v___x_843_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_a_841_, v_a_842_);
return v___x_843_;
}
else
{
lean_dec_ref(v_e_826_);
return v___y_840_;
}
}
v___jp_844_:
{
if (lean_obj_tag(v___y_845_) == 0)
{
lean_object* v_a_846_; lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_846_ = lean_ctor_get(v___y_845_, 0);
lean_inc(v_a_846_);
v_a_847_ = lean_ctor_get(v___y_845_, 1);
lean_inc(v_a_847_);
lean_dec_ref_known(v___y_845_, 2);
v___x_848_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_826_, v_a_846_, v_a_847_);
return v___x_848_;
}
else
{
lean_dec_ref(v_e_826_);
return v___y_845_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1110_, v_a_1111_, v_a_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1115_, v_x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1118_, v_x_1119_, v_x_1120_);
lean_dec_ref(v_x_1120_);
lean_dec_ref(v_x_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1122_, lean_object* v_m_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1123_, v_a_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_m_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1126_, v_m_1127_, v_a_1128_);
lean_dec_ref(v_a_1128_);
lean_dec_ref(v_m_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1130_, lean_object* v_x_1131_, size_t v_x_1132_, lean_object* v_x_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1131_, v_x_1132_, v_x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
size_t v_x_11735__boxed_1139_; lean_object* v_res_1140_; 
v_x_11735__boxed_1139_ = lean_unbox_usize(v_x_1137_);
lean_dec(v_x_1137_);
v_res_1140_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1135_, v_x_1136_, v_x_11735__boxed_1139_, v_x_1138_);
lean_dec_ref(v_x_1138_);
lean_dec_ref(v_x_1136_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1141_, lean_object* v_a_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1142_, v_x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1145_, lean_object* v_a_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1145_, v_a_1146_, v_x_1147_);
lean_dec(v_x_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1149_, lean_object* v_keys_1150_, lean_object* v_vals_1151_, lean_object* v_heq_1152_, lean_object* v_i_1153_, lean_object* v_k_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1150_, v_vals_1151_, v_i_1153_, v_k_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1156_, lean_object* v_keys_1157_, lean_object* v_vals_1158_, lean_object* v_heq_1159_, lean_object* v_i_1160_, lean_object* v_k_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1156_, v_keys_1157_, v_vals_1158_, v_heq_1159_, v_i_1160_, v_k_1161_);
lean_dec_ref(v_k_1161_);
lean_dec_ref(v_vals_1158_);
lean_dec_ref(v_keys_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1163_, lean_object* v_cache_1164_, lean_object* v_ctx_1165_, lean_object* v_s_1166_){
_start:
{
lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; 
v___f_1167_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1168_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1163_);
v___x_1169_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1167_, v___f_1168_, v_s_1166_, v_e_1163_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_cache_1164_);
lean_ctor_set(v___x_1170_, 1, v_s_1166_);
v___x_1171_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1163_, v_ctx_1165_, v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 1);
v_a_1173_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v___x_1171_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1173_);
lean_dec(v___x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_set_1177_; lean_object* v___x_1179_; 
v_set_1177_ = lean_ctor_get(v_a_1172_, 1);
lean_inc_ref(v_set_1177_);
lean_dec(v_a_1172_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_set_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_set_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1191_; 
v_a_1182_ = lean_ctor_get(v___x_1171_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v___x_1171_, 0);
lean_dec(v_unused_1192_);
v___x_1184_ = v___x_1171_;
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1171_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_map_1186_; lean_object* v_set_1187_; lean_object* v___x_1189_; 
v_map_1186_ = lean_ctor_get(v_a_1182_, 0);
lean_inc_ref(v_map_1186_);
v_set_1187_ = lean_ctor_get(v_a_1182_, 1);
lean_inc_ref(v_set_1187_);
lean_dec(v_a_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 1, v_set_1187_);
lean_ctor_set(v___x_1184_, 0, v_map_1186_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_map_1186_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_set_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_val_1193_; lean_object* v_fst_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_cache_1164_);
lean_dec_ref(v_e_1163_);
v_val_1193_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1169_, 1);
v_fst_1194_ = lean_ctor_get(v_val_1193_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_val_1193_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_val_1193_, 1);
lean_dec(v_unused_1202_);
v___x_1196_ = v_val_1193_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_fst_1194_);
lean_dec(v_val_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v_s_1166_);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_fst_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_s_1166_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1203_, lean_object* v_cache_1204_, lean_object* v_ctx_1205_, lean_object* v_s_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1203_, v_cache_1204_, v_ctx_1205_, v_s_1206_);
lean_dec_ref(v_ctx_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1210_; uint64_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1210_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1211_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1208_);
v___x_1212_ = lean_uint64_to_usize(v___x_1211_);
v___x_1213_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1209_, v___x_1212_, v_e_1208_, v___x_1210_);
v___x_1214_ = lean_ptr_addr(v___x_1213_);
v___x_1215_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1216_ = lean_usize_dec_eq(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
lean_dec_ref(v_e_1208_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1213_);
lean_ctor_set(v___x_1217_, 1, v_a_1209_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v___x_1213_);
v___x_1218_ = lean_box(0);
lean_inc_ref(v_e_1208_);
v___x_1219_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1209_, v_e_1208_, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_e_1208_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1221_, v_a_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1225_, v_a_1226_, v_a_1227_);
lean_dec_ref(v_a_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1229_, lean_object* v_k_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___f_1233_; lean_object* v___x_1234_; uint64_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; uint8_t v___x_1240_; 
v___f_1233_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1234_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1235_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1229_);
v___x_1236_ = lean_uint64_to_usize(v___x_1235_);
lean_inc_ref(v_a_1232_);
v___x_1237_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1233_, v_a_1232_, v___x_1236_, v_e_1229_, v___x_1234_);
v___x_1238_ = lean_ptr_addr(v___x_1237_);
v___x_1239_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1240_ = lean_usize_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_dec_ref(v_k_1230_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1237_);
lean_ctor_set(v___x_1241_, 1, v_a_1232_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v___x_1237_);
lean_inc_ref(v_a_1231_);
v___x_1242_ = lean_apply_2(v_k_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
v_a_1244_ = lean_ctor_get(v___x_1242_, 1);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1242_, 2);
v___x_1245_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1243_, v_a_1244_);
return v___x_1245_;
}
else
{
return v___x_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1246_, lean_object* v_k_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1246_, v_k_1247_, v_a_1248_, v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_unsigned_to_nat(16u);
v___x_1253_ = lean_mk_array(v___x_1252_, v___x_1251_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v___x_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___y_1261_; lean_object* v___y_1266_; lean_object* v___y_1271_; lean_object* v___y_1276_; 
switch(lean_obj_tag(v_e_1257_))
{
case 4:
{
lean_object* v_declName_1280_; lean_object* v___x_1281_; uint64_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; uint8_t v___x_1287_; 
v_declName_1280_ = lean_ctor_get(v_e_1257_, 0);
v___x_1281_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1282_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1257_);
v___x_1283_ = lean_uint64_to_usize(v___x_1282_);
v___x_1284_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1259_, v___x_1283_, v_e_1257_, v___x_1281_);
v___x_1285_ = lean_ptr_addr(v___x_1284_);
v___x_1286_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1287_ = lean_usize_dec_eq(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
lean_dec_ref_known(v_e_1257_, 2);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1284_);
lean_ctor_set(v___x_1288_, 1, v_a_1259_);
return v___x_1288_;
}
else
{
uint8_t v___x_1289_; 
lean_dec_ref(v___x_1284_);
lean_inc(v_declName_1280_);
lean_inc_ref(v_a_1258_);
v___x_1289_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1258_, v_declName_1280_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(0);
lean_inc_ref(v_e_1257_);
v___x_1291_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1259_, v_e_1257_, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_e_1257_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref_known(v_e_1257_, 2);
v___x_1293_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_a_1259_);
return v___x_1294_;
}
}
}
case 5:
{
lean_object* v_fn_1295_; lean_object* v_arg_1296_; lean_object* v___x_1297_; uint64_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; uint8_t v___x_1303_; 
v_fn_1295_ = lean_ctor_get(v_e_1257_, 0);
v_arg_1296_ = lean_ctor_get(v_e_1257_, 1);
v___x_1297_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1298_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1257_);
v___x_1299_ = lean_uint64_to_usize(v___x_1298_);
v___x_1300_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1259_, v___x_1299_, v_e_1257_, v___x_1297_);
v___x_1301_ = lean_ptr_addr(v___x_1300_);
v___x_1302_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1303_ = lean_usize_dec_eq(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec_ref_known(v_e_1257_, 2);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1300_);
lean_ctor_set(v___x_1304_, 1, v_a_1259_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; 
lean_dec_ref(v___x_1300_);
lean_inc_ref(v_fn_1295_);
v___x_1305_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1295_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v_a_1307_; lean_object* v___x_1308_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
v_a_1307_ = lean_ctor_get(v___x_1305_, 1);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1305_, 2);
lean_inc_ref(v_arg_1296_);
v___x_1308_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1296_, v_a_1258_, v_a_1307_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v_a_1310_; uint8_t v___y_1312_; size_t v___x_1316_; size_t v___x_1317_; uint8_t v___x_1318_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
v_a_1310_ = lean_ctor_get(v___x_1308_, 1);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1308_, 2);
v___x_1316_ = lean_ptr_addr(v_fn_1295_);
v___x_1317_ = lean_ptr_addr(v_a_1306_);
v___x_1318_ = lean_usize_dec_eq(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
v___y_1312_ = v___x_1318_;
goto v___jp_1311_;
}
else
{
size_t v___x_1319_; size_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_ptr_addr(v_arg_1296_);
v___x_1320_ = lean_ptr_addr(v_a_1309_);
v___x_1321_ = lean_usize_dec_eq(v___x_1319_, v___x_1320_);
v___y_1312_ = v___x_1321_;
goto v___jp_1311_;
}
v___jp_1311_:
{
if (v___y_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec_ref_known(v_e_1257_, 2);
v___x_1313_ = l_Lean_Expr_app___override(v_a_1306_, v_a_1309_);
v___x_1314_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1313_, v_a_1310_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; 
lean_dec(v_a_1309_);
lean_dec(v_a_1306_);
v___x_1315_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1257_, v_a_1310_);
return v___x_1315_;
}
}
}
else
{
lean_dec(v_a_1306_);
lean_dec_ref_known(v_e_1257_, 2);
v___y_1271_ = v___x_1308_;
goto v___jp_1270_;
}
}
else
{
lean_dec_ref_known(v_e_1257_, 2);
v___y_1271_ = v___x_1305_;
goto v___jp_1270_;
}
}
}
case 6:
{
lean_object* v_binderName_1322_; lean_object* v_binderType_1323_; lean_object* v_body_1324_; uint8_t v_binderInfo_1325_; lean_object* v___x_1326_; uint64_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; uint8_t v___x_1332_; 
v_binderName_1322_ = lean_ctor_get(v_e_1257_, 0);
v_binderType_1323_ = lean_ctor_get(v_e_1257_, 1);
v_body_1324_ = lean_ctor_get(v_e_1257_, 2);
v_binderInfo_1325_ = lean_ctor_get_uint8(v_e_1257_, sizeof(void*)*3 + 8);
v___x_1326_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1327_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1257_);
v___x_1328_ = lean_uint64_to_usize(v___x_1327_);
v___x_1329_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1259_, v___x_1328_, v_e_1257_, v___x_1326_);
v___x_1330_ = lean_ptr_addr(v___x_1329_);
v___x_1331_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1332_ = lean_usize_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref_known(v_e_1257_, 3);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1329_);
lean_ctor_set(v___x_1333_, 1, v_a_1259_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; 
lean_dec_ref(v___x_1329_);
lean_inc_ref(v_binderType_1323_);
v___x_1334_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1323_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v_a_1336_; lean_object* v___x_1337_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
v_a_1336_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1334_, 2);
lean_inc_ref(v_body_1324_);
v___x_1337_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1324_, v_a_1258_, v_a_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v_a_1339_; uint8_t v___y_1341_; size_t v___x_1348_; size_t v___x_1349_; uint8_t v___x_1350_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
v_a_1339_ = lean_ctor_get(v___x_1337_, 1);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1337_, 2);
v___x_1348_ = lean_ptr_addr(v_binderType_1323_);
v___x_1349_ = lean_ptr_addr(v_a_1335_);
v___x_1350_ = lean_usize_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
v___y_1341_ = v___x_1350_;
goto v___jp_1340_;
}
else
{
size_t v___x_1351_; size_t v___x_1352_; uint8_t v___x_1353_; 
v___x_1351_ = lean_ptr_addr(v_body_1324_);
v___x_1352_ = lean_ptr_addr(v_a_1338_);
v___x_1353_ = lean_usize_dec_eq(v___x_1351_, v___x_1352_);
v___y_1341_ = v___x_1353_;
goto v___jp_1340_;
}
v___jp_1340_:
{
if (v___y_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_inc(v_binderName_1322_);
lean_dec_ref_known(v_e_1257_, 3);
v___x_1342_ = l_Lean_Expr_lam___override(v_binderName_1322_, v_a_1335_, v_a_1338_, v_binderInfo_1325_);
v___x_1343_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1342_, v_a_1339_);
return v___x_1343_;
}
else
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1325_, v_binderInfo_1325_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_inc(v_binderName_1322_);
lean_dec_ref_known(v_e_1257_, 3);
v___x_1345_ = l_Lean_Expr_lam___override(v_binderName_1322_, v_a_1335_, v_a_1338_, v_binderInfo_1325_);
v___x_1346_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1345_, v_a_1339_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v_a_1338_);
lean_dec(v_a_1335_);
v___x_1347_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1257_, v_a_1339_);
return v___x_1347_;
}
}
}
}
else
{
lean_dec(v_a_1335_);
lean_dec_ref_known(v_e_1257_, 3);
v___y_1266_ = v___x_1337_;
goto v___jp_1265_;
}
}
else
{
lean_dec_ref_known(v_e_1257_, 3);
v___y_1266_ = v___x_1334_;
goto v___jp_1265_;
}
}
}
case 7:
{
lean_object* v_binderName_1354_; lean_object* v_binderType_1355_; lean_object* v_body_1356_; uint8_t v_binderInfo_1357_; lean_object* v___x_1358_; uint64_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v_binderName_1354_ = lean_ctor_get(v_e_1257_, 0);
v_binderType_1355_ = lean_ctor_get(v_e_1257_, 1);
v_body_1356_ = lean_ctor_get(v_e_1257_, 2);
v_binderInfo_1357_ = lean_ctor_get_uint8(v_e_1257_, sizeof(void*)*3 + 8);
v___x_1358_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1359_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1257_);
v___x_1360_ = lean_uint64_to_usize(v___x_1359_);
v___x_1361_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1259_, v___x_1360_, v_e_1257_, v___x_1358_);
v___x_1362_ = lean_ptr_addr(v___x_1361_);
v___x_1363_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1364_ = lean_usize_dec_eq(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref_known(v_e_1257_, 3);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1361_);
lean_ctor_set(v___x_1365_, 1, v_a_1259_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; 
lean_dec_ref(v___x_1361_);
lean_inc_ref(v_binderType_1355_);
v___x_1366_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1355_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
v_a_1368_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1366_, 2);
lean_inc_ref(v_body_1356_);
v___x_1369_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1356_, v_a_1258_, v_a_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_a_1371_; uint8_t v___y_1373_; size_t v___x_1380_; size_t v___x_1381_; uint8_t v___x_1382_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
v_a_1371_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1369_, 2);
v___x_1380_ = lean_ptr_addr(v_binderType_1355_);
v___x_1381_ = lean_ptr_addr(v_a_1367_);
v___x_1382_ = lean_usize_dec_eq(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
v___y_1373_ = v___x_1382_;
goto v___jp_1372_;
}
else
{
size_t v___x_1383_; size_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = lean_ptr_addr(v_body_1356_);
v___x_1384_ = lean_ptr_addr(v_a_1370_);
v___x_1385_ = lean_usize_dec_eq(v___x_1383_, v___x_1384_);
v___y_1373_ = v___x_1385_;
goto v___jp_1372_;
}
v___jp_1372_:
{
if (v___y_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc(v_binderName_1354_);
lean_dec_ref_known(v_e_1257_, 3);
v___x_1374_ = l_Lean_Expr_forallE___override(v_binderName_1354_, v_a_1367_, v_a_1370_, v_binderInfo_1357_);
v___x_1375_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1374_, v_a_1371_);
return v___x_1375_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1357_, v_binderInfo_1357_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_inc(v_binderName_1354_);
lean_dec_ref_known(v_e_1257_, 3);
v___x_1377_ = l_Lean_Expr_forallE___override(v_binderName_1354_, v_a_1367_, v_a_1370_, v_binderInfo_1357_);
v___x_1378_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1377_, v_a_1371_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; 
lean_dec(v_a_1370_);
lean_dec(v_a_1367_);
v___x_1379_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1257_, v_a_1371_);
return v___x_1379_;
}
}
}
}
else
{
lean_dec(v_a_1367_);
lean_dec_ref_known(v_e_1257_, 3);
v___y_1276_ = v___x_1369_;
goto v___jp_1275_;
}
}
else
{
lean_dec_ref_known(v_e_1257_, 3);
v___y_1276_ = v___x_1366_;
goto v___jp_1275_;
}
}
}
case 8:
{
lean_object* v_declName_1386_; lean_object* v_type_1387_; lean_object* v_value_1388_; lean_object* v_body_1389_; uint8_t v_nondep_1390_; lean_object* v___x_1391_; uint64_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; size_t v___x_1395_; size_t v___x_1396_; uint8_t v___x_1397_; 
v_declName_1386_ = lean_ctor_get(v_e_1257_, 0);
v_type_1387_ = lean_ctor_get(v_e_1257_, 1);
v_value_1388_ = lean_ctor_get(v_e_1257_, 2);
v_body_1389_ = lean_ctor_get(v_e_1257_, 3);
v_nondep_1390_ = lean_ctor_get_uint8(v_e_1257_, sizeof(void*)*4 + 8);
v___x_1391_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1392_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1257_);
v___x_1393_ = lean_uint64_to_usize(v___x_1392_);
v___x_1394_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1259_, v___x_1393_, v_e_1257_, v___x_1391_);
v___x_1395_ = lean_ptr_addr(v___x_1394_);
v___x_1396_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1397_ = lean_usize_dec_eq(v___x_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_dec_ref_known(v_e_1257_, 4);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1394_);
lean_ctor_set(v___x_1398_, 1, v_a_1259_);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; 
lean_dec_ref(v___x_1394_);
lean_inc_ref(v_type_1387_);
v___x_1399_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1387_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_a_1401_; lean_object* v___x_1402_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
v_a_1401_ = lean_ctor_get(v___x_1399_, 1);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1399_, 2);
lean_inc_ref(v_value_1388_);
v___x_1402_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1388_, v_a_1258_, v_a_1401_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
v_a_1404_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1402_, 2);
lean_inc_ref(v_body_1389_);
v___x_1405_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1389_, v_a_1258_, v_a_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_a_1407_; uint8_t v___y_1409_; size_t v___x_1418_; size_t v___x_1419_; uint8_t v___x_1420_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
v_a_1407_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1405_, 2);
v___x_1418_ = lean_ptr_addr(v_type_1387_);
v___x_1419_ = lean_ptr_addr(v_a_1400_);
v___x_1420_ = lean_usize_dec_eq(v___x_1418_, v___x_1419_);
if (v___x_1420_ == 0)
{
v___y_1409_ = v___x_1420_;
goto v___jp_1408_;
}
else
{
size_t v___x_1421_; size_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = lean_ptr_addr(v_value_1388_);
v___x_1422_ = lean_ptr_addr(v_a_1403_);
v___x_1423_ = lean_usize_dec_eq(v___x_1421_, v___x_1422_);
v___y_1409_ = v___x_1423_;
goto v___jp_1408_;
}
v___jp_1408_:
{
if (v___y_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_inc(v_declName_1386_);
lean_dec_ref_known(v_e_1257_, 4);
v___x_1410_ = l_Lean_Expr_letE___override(v_declName_1386_, v_a_1400_, v_a_1403_, v_a_1406_, v_nondep_1390_);
v___x_1411_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1410_, v_a_1407_);
return v___x_1411_;
}
else
{
size_t v___x_1412_; size_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = lean_ptr_addr(v_body_1389_);
v___x_1413_ = lean_ptr_addr(v_a_1406_);
v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_inc(v_declName_1386_);
lean_dec_ref_known(v_e_1257_, 4);
v___x_1415_ = l_Lean_Expr_letE___override(v_declName_1386_, v_a_1400_, v_a_1403_, v_a_1406_, v_nondep_1390_);
v___x_1416_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1415_, v_a_1407_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_a_1406_);
lean_dec(v_a_1403_);
lean_dec(v_a_1400_);
v___x_1417_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1257_, v_a_1407_);
return v___x_1417_;
}
}
}
}
else
{
lean_dec(v_a_1403_);
lean_dec(v_a_1400_);
lean_dec_ref_known(v_e_1257_, 4);
v___y_1261_ = v___x_1405_;
goto v___jp_1260_;
}
}
else
{
lean_dec(v_a_1400_);
lean_dec_ref_known(v_e_1257_, 4);
v___y_1261_ = v___x_1402_;
goto v___jp_1260_;
}
}
else
{
lean_dec_ref_known(v_e_1257_, 4);
v___y_1261_ = v___x_1399_;
goto v___jp_1260_;
}
}
}
case 10:
{
lean_object* v_data_1424_; lean_object* v_expr_1425_; lean_object* v___x_1426_; uint64_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; size_t v___x_1430_; size_t v___x_1431_; uint8_t v___x_1432_; 
v_data_1424_ = lean_ctor_get(v_e_1257_, 0);
v_expr_1425_ = lean_ctor_get(v_e_1257_, 1);
v___x_1426_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1427_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1257_);
v___x_1428_ = lean_uint64_to_usize(v___x_1427_);
v___x_1429_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1259_, v___x_1428_, v_e_1257_, v___x_1426_);
v___x_1430_ = lean_ptr_addr(v___x_1429_);
v___x_1431_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1432_ = lean_usize_dec_eq(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref_known(v_e_1257_, 2);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1429_);
lean_ctor_set(v___x_1433_, 1, v_a_1259_);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; 
lean_dec_ref(v___x_1429_);
lean_inc_ref(v_expr_1425_);
v___x_1434_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1425_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_a_1436_; size_t v___x_1437_; size_t v___x_1438_; uint8_t v___x_1439_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
v_a_1436_ = lean_ctor_get(v___x_1434_, 1);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1434_, 2);
v___x_1437_ = lean_ptr_addr(v_expr_1425_);
v___x_1438_ = lean_ptr_addr(v_a_1435_);
v___x_1439_ = lean_usize_dec_eq(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_inc(v_data_1424_);
lean_dec_ref_known(v_e_1257_, 2);
v___x_1440_ = l_Lean_Expr_mdata___override(v_data_1424_, v_a_1435_);
v___x_1441_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1440_, v_a_1436_);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; 
lean_dec(v_a_1435_);
v___x_1442_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1257_, v_a_1436_);
return v___x_1442_;
}
}
else
{
lean_dec_ref_known(v_e_1257_, 2);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1443_; lean_object* v_a_1444_; lean_object* v___x_1445_; 
v_a_1443_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1443_);
v_a_1444_ = lean_ctor_get(v___x_1434_, 1);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1434_, 2);
v___x_1445_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1443_, v_a_1444_);
return v___x_1445_;
}
else
{
return v___x_1434_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1446_; lean_object* v_idx_1447_; lean_object* v_struct_1448_; lean_object* v___x_1449_; uint64_t v___x_1450_; size_t v___x_1451_; lean_object* v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; uint8_t v___x_1455_; 
v_typeName_1446_ = lean_ctor_get(v_e_1257_, 0);
v_idx_1447_ = lean_ctor_get(v_e_1257_, 1);
v_struct_1448_ = lean_ctor_get(v_e_1257_, 2);
v___x_1449_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1450_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1257_);
v___x_1451_ = lean_uint64_to_usize(v___x_1450_);
v___x_1452_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1259_, v___x_1451_, v_e_1257_, v___x_1449_);
v___x_1453_ = lean_ptr_addr(v___x_1452_);
v___x_1454_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1455_ = lean_usize_dec_eq(v___x_1453_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref_known(v_e_1257_, 3);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1452_);
lean_ctor_set(v___x_1456_, 1, v_a_1259_);
return v___x_1456_;
}
else
{
uint8_t v_checkProj_1457_; 
lean_dec_ref(v___x_1452_);
v_checkProj_1457_ = lean_ctor_get_uint8(v_a_1258_, sizeof(void*)*1 + 1);
if (v_checkProj_1457_ == 0)
{
lean_object* v___x_1458_; 
lean_inc_ref(v_struct_1448_);
v___x_1458_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1448_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v_a_1460_; size_t v___x_1461_; size_t v___x_1462_; uint8_t v___x_1463_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
v_a_1460_ = lean_ctor_get(v___x_1458_, 1);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1458_, 2);
v___x_1461_ = lean_ptr_addr(v_struct_1448_);
v___x_1462_ = lean_ptr_addr(v_a_1459_);
v___x_1463_ = lean_usize_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_inc(v_idx_1447_);
lean_inc(v_typeName_1446_);
lean_dec_ref_known(v_e_1257_, 3);
v___x_1464_ = l_Lean_Expr_proj___override(v_typeName_1446_, v_idx_1447_, v_a_1459_);
v___x_1465_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1464_, v_a_1460_);
return v___x_1465_;
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_a_1459_);
v___x_1466_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1257_, v_a_1460_);
return v___x_1466_;
}
}
else
{
lean_dec_ref_known(v_e_1257_, 3);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1467_; lean_object* v_a_1468_; lean_object* v___x_1469_; 
v_a_1467_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1467_);
v_a_1468_ = lean_ctor_get(v___x_1458_, 1);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1458_, 2);
v___x_1469_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1467_, v_a_1468_);
return v___x_1469_;
}
else
{
return v___x_1458_;
}
}
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref_known(v_e_1257_, 3);
v___x_1470_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v_a_1259_);
return v___x_1471_;
}
}
}
default: 
{
lean_object* v___x_1472_; 
v___x_1472_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1257_, v_a_1259_);
return v___x_1472_;
}
}
v___jp_1260_:
{
if (lean_obj_tag(v___y_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v_a_1263_; lean_object* v___x_1264_; 
v_a_1262_ = lean_ctor_get(v___y_1261_, 0);
lean_inc(v_a_1262_);
v_a_1263_ = lean_ctor_get(v___y_1261_, 1);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___y_1261_, 2);
v___x_1264_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1262_, v_a_1263_);
return v___x_1264_;
}
else
{
return v___y_1261_;
}
}
v___jp_1265_:
{
if (lean_obj_tag(v___y_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1267_ = lean_ctor_get(v___y_1266_, 0);
lean_inc(v_a_1267_);
v_a_1268_ = lean_ctor_get(v___y_1266_, 1);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___y_1266_, 2);
v___x_1269_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1267_, v_a_1268_);
return v___x_1269_;
}
else
{
return v___y_1266_;
}
}
v___jp_1270_:
{
if (lean_obj_tag(v___y_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___y_1271_, 0);
lean_inc(v_a_1272_);
v_a_1273_ = lean_ctor_get(v___y_1271_, 1);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___y_1271_, 2);
v___x_1274_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1272_, v_a_1273_);
return v___x_1274_;
}
else
{
return v___y_1271_;
}
}
v___jp_1275_:
{
if (lean_obj_tag(v___y_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1277_ = lean_ctor_get(v___y_1276_, 0);
lean_inc(v_a_1277_);
v_a_1278_ = lean_ctor_get(v___y_1276_, 1);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___y_1276_, 2);
v___x_1279_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1277_, v_a_1278_);
return v___x_1279_;
}
else
{
return v___y_1276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1473_, v_a_1474_, v_a_1475_);
lean_dec_ref(v_a_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1477_, v_a_1478_, v_a_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1481_, v_a_1482_, v_a_1483_);
lean_dec_ref(v_a_1482_);
return v_res_1484_;
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

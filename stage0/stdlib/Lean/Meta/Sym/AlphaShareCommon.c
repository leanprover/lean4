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
size_t v_x_2094__boxed_253_; lean_object* v_res_254_; 
v_x_2094__boxed_253_ = lean_unbox_usize(v_x_250_);
lean_dec(v_x_250_);
v_res_254_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_249_, v_x_2094__boxed_253_, v_x_251_, v_x_252_);
lean_dec_ref(v_x_252_);
lean_dec_ref(v_x_251_);
lean_dec_ref(v_x_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_ks_259_; lean_object* v_vs_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_284_; 
v_ks_259_ = lean_ctor_get(v_x_255_, 0);
v_vs_260_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_284_ == 0)
{
v___x_262_ = v_x_255_;
v_isShared_263_ = v_isSharedCheck_284_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_vs_260_);
lean_inc(v_ks_259_);
lean_dec(v_x_255_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_284_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_array_get_size(v_ks_259_);
v___x_265_ = lean_nat_dec_lt(v_x_256_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_x_256_);
v___x_266_ = lean_array_push(v_ks_259_, v_x_257_);
v___x_267_ = lean_array_push(v_vs_260_, v_x_258_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_267_);
lean_ctor_set(v___x_262_, 0, v___x_266_);
v___x_269_ = v___x_262_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
else
{
lean_object* v_k_x27_271_; uint8_t v___x_272_; 
v_k_x27_271_ = lean_array_fget_borrowed(v_ks_259_, v_x_256_);
v___x_272_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_257_, v_k_x27_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_274_; 
if (v_isShared_263_ == 0)
{
v___x_274_ = v___x_262_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_ks_259_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_vs_260_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_x_256_, v___x_275_);
lean_dec(v_x_256_);
v_x_255_ = v___x_274_;
v_x_256_ = v___x_276_;
goto _start;
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = lean_array_fset(v_ks_259_, v_x_256_, v_x_257_);
v___x_280_ = lean_array_fset(v_vs_260_, v_x_256_, v_x_258_);
lean_dec(v_x_256_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_280_);
lean_ctor_set(v___x_262_, 0, v___x_279_);
v___x_282_ = v___x_262_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_285_, lean_object* v_k_286_, lean_object* v_v_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_285_, v___x_288_, v_k_286_, v_v_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_291_, size_t v_x_292_, size_t v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v_es_296_; size_t v___x_297_; size_t v___x_298_; lean_object* v_j_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_es_296_ = lean_ctor_get(v_x_291_, 0);
v___x_297_ = ((size_t)31ULL);
v___x_298_ = lean_usize_land(v_x_292_, v___x_297_);
v_j_299_ = lean_usize_to_nat(v___x_298_);
v___x_300_ = lean_array_get_size(v_es_296_);
v___x_301_ = lean_nat_dec_lt(v_j_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec(v_j_299_);
lean_dec(v_x_295_);
lean_dec_ref(v_x_294_);
return v_x_291_;
}
else
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_340_; 
lean_inc_ref(v_es_296_);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_291_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_x_291_, 0);
lean_dec(v_unused_341_);
v___x_303_ = v_x_291_;
v_isShared_304_ = v_isSharedCheck_340_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_x_291_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_340_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_v_305_; lean_object* v___x_306_; lean_object* v_xs_x27_307_; lean_object* v___y_309_; 
v_v_305_ = lean_array_fget(v_es_296_, v_j_299_);
v___x_306_ = lean_box(0);
v_xs_x27_307_ = lean_array_fset(v_es_296_, v_j_299_, v___x_306_);
switch(lean_obj_tag(v_v_305_))
{
case 0:
{
lean_object* v_key_314_; lean_object* v_val_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_325_; 
v_key_314_ = lean_ctor_get(v_v_305_, 0);
v_val_315_ = lean_ctor_get(v_v_305_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_v_305_);
if (v_isSharedCheck_325_ == 0)
{
v___x_317_ = v_v_305_;
v_isShared_318_ = v_isSharedCheck_325_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_val_315_);
lean_inc(v_key_314_);
lean_dec(v_v_305_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_325_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
uint8_t v___x_319_; 
v___x_319_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_294_, v_key_314_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_del_object(v___x_317_);
v___x_320_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_314_, v_val_315_, v_x_294_, v_x_295_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
v___y_309_ = v___x_321_;
goto v___jp_308_;
}
else
{
lean_object* v___x_323_; 
lean_dec(v_val_315_);
lean_dec(v_key_314_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v_x_295_);
lean_ctor_set(v___x_317_, 0, v_x_294_);
v___x_323_ = v___x_317_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_x_294_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_x_295_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v___y_309_ = v___x_323_;
goto v___jp_308_;
}
}
}
}
case 1:
{
lean_object* v_node_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_338_; 
v_node_326_ = lean_ctor_get(v_v_305_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_v_305_);
if (v_isSharedCheck_338_ == 0)
{
v___x_328_ = v_v_305_;
v_isShared_329_ = v_isSharedCheck_338_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_node_326_);
lean_dec(v_v_305_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_338_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
size_t v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_330_ = ((size_t)5ULL);
v___x_331_ = lean_usize_shift_right(v_x_292_, v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_x_293_, v___x_332_);
v___x_334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_326_, v___x_331_, v___x_333_, v_x_294_, v_x_295_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_334_);
v___x_336_ = v___x_328_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v___y_309_ = v___x_336_;
goto v___jp_308_;
}
}
}
default: 
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_x_294_);
lean_ctor_set(v___x_339_, 1, v_x_295_);
v___y_309_ = v___x_339_;
goto v___jp_308_;
}
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_array_fset(v_xs_x27_307_, v_j_299_, v___y_309_);
lean_dec(v_j_299_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_310_);
v___x_312_ = v___x_303_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
else
{
lean_object* v_ks_342_; lean_object* v_vs_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_363_; 
v_ks_342_ = lean_ctor_get(v_x_291_, 0);
v_vs_343_ = lean_ctor_get(v_x_291_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_291_);
if (v_isSharedCheck_363_ == 0)
{
v___x_345_ = v_x_291_;
v_isShared_346_ = v_isSharedCheck_363_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_vs_343_);
lean_inc(v_ks_342_);
lean_dec(v_x_291_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_363_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_ks_342_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_vs_343_);
v___x_348_ = v_reuseFailAlloc_362_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v_newNode_349_; uint8_t v___y_351_; size_t v___x_357_; uint8_t v___x_358_; 
v_newNode_349_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_348_, v_x_294_, v_x_295_);
v___x_357_ = ((size_t)7ULL);
v___x_358_ = lean_usize_dec_le(v___x_357_, v_x_293_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_349_);
v___x_360_ = lean_unsigned_to_nat(4u);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
v___y_351_ = v___x_361_;
goto v___jp_350_;
}
else
{
v___y_351_ = v___x_358_;
goto v___jp_350_;
}
v___jp_350_:
{
if (v___y_351_ == 0)
{
lean_object* v_ks_352_; lean_object* v_vs_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_ks_352_ = lean_ctor_get(v_newNode_349_, 0);
lean_inc_ref(v_ks_352_);
v_vs_353_ = lean_ctor_get(v_newNode_349_, 1);
lean_inc_ref(v_vs_353_);
lean_dec_ref(v_newNode_349_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_293_, v_ks_352_, v_vs_353_, v___x_354_, v___x_355_);
lean_dec_ref(v_vs_353_);
lean_dec_ref(v_ks_352_);
return v___x_356_;
}
else
{
return v_newNode_349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_i_367_, lean_object* v_entries_368_){
_start:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_array_get_size(v_keys_365_);
v___x_370_ = lean_nat_dec_lt(v_i_367_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec(v_i_367_);
return v_entries_368_;
}
else
{
lean_object* v_k_371_; lean_object* v_v_372_; uint64_t v___x_373_; size_t v_h_374_; size_t v___x_375_; lean_object* v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v_h_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_k_371_ = lean_array_fget_borrowed(v_keys_365_, v_i_367_);
v_v_372_ = lean_array_fget_borrowed(v_vals_366_, v_i_367_);
v___x_373_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_371_);
v_h_374_ = lean_uint64_to_usize(v___x_373_);
v___x_375_ = ((size_t)5ULL);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_sub(v_depth_364_, v___x_377_);
v___x_379_ = lean_usize_mul(v___x_375_, v___x_378_);
v_h_380_ = lean_usize_shift_right(v_h_374_, v___x_379_);
v___x_381_ = lean_nat_add(v_i_367_, v___x_376_);
lean_dec(v_i_367_);
lean_inc(v_v_372_);
lean_inc(v_k_371_);
v___x_382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_368_, v_h_380_, v_depth_364_, v_k_371_, v_v_372_);
v_i_367_ = v___x_381_;
v_entries_368_ = v___x_382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_384_, lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_i_387_, lean_object* v_entries_388_){
_start:
{
size_t v_depth_boxed_389_; lean_object* v_res_390_; 
v_depth_boxed_389_ = lean_unbox_usize(v_depth_384_);
lean_dec(v_depth_384_);
v_res_390_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_389_, v_keys_385_, v_vals_386_, v_i_387_, v_entries_388_);
lean_dec_ref(v_vals_386_);
lean_dec_ref(v_keys_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
size_t v_x_2212__boxed_396_; size_t v_x_2213__boxed_397_; lean_object* v_res_398_; 
v_x_2212__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_x_2213__boxed_397_ = lean_unbox_usize(v_x_393_);
lean_dec(v_x_393_);
v_res_398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_391_, v_x_2212__boxed_396_, v_x_2213__boxed_397_, v_x_394_, v_x_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
uint64_t v___x_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___x_402_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_400_);
v___x_403_ = lean_uint64_to_usize(v___x_402_);
v___x_404_ = ((size_t)1ULL);
v___x_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_399_, v___x_403_, v___x_404_, v_x_400_, v_x_401_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_406_, lean_object* v_b_407_, lean_object* v_x_408_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_dec(v_b_407_);
lean_dec_ref(v_a_406_);
return v_x_408_;
}
else
{
lean_object* v_key_409_; lean_object* v_value_410_; lean_object* v_tail_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_425_; 
v_key_409_ = lean_ctor_get(v_x_408_, 0);
v_value_410_ = lean_ctor_get(v_x_408_, 1);
v_tail_411_ = lean_ctor_get(v_x_408_, 2);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_408_);
if (v_isSharedCheck_425_ == 0)
{
v___x_413_ = v_x_408_;
v_isShared_414_ = v_isSharedCheck_425_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_tail_411_);
lean_inc(v_value_410_);
lean_inc(v_key_409_);
lean_dec(v_x_408_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_425_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_ptr_addr(v_key_409_);
v___x_416_ = lean_ptr_addr(v_a_406_);
v___x_417_ = lean_usize_dec_eq(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_406_, v_b_407_, v_tail_411_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 2, v___x_418_);
v___x_420_ = v___x_413_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_key_409_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_value_410_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v___x_423_; 
lean_dec(v_value_410_);
lean_dec(v_key_409_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_b_407_);
lean_ctor_set(v___x_413_, 0, v_a_406_);
v___x_423_ = v___x_413_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_406_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_b_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_tail_411_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
return v_x_426_;
}
else
{
lean_object* v_key_428_; lean_object* v_value_429_; lean_object* v_tail_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_456_; 
v_key_428_ = lean_ctor_get(v_x_427_, 0);
v_value_429_ = lean_ctor_get(v_x_427_, 1);
v_tail_430_ = lean_ctor_get(v_x_427_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_427_);
if (v_isSharedCheck_456_ == 0)
{
v___x_432_ = v_x_427_;
v_isShared_433_ = v_isSharedCheck_456_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_tail_430_);
lean_inc(v_value_429_);
lean_inc(v_key_428_);
lean_dec(v_x_427_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_456_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; uint64_t v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v_fold_441_; uint64_t v___x_442_; uint64_t v___x_443_; uint64_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_434_ = lean_array_get_size(v_x_426_);
v___x_435_ = lean_ptr_addr(v_key_428_);
v___x_436_ = ((size_t)3ULL);
v___x_437_ = lean_usize_shift_right(v___x_435_, v___x_436_);
v___x_438_ = lean_usize_to_uint64(v___x_437_);
v___x_439_ = 32ULL;
v___x_440_ = lean_uint64_shift_right(v___x_438_, v___x_439_);
v_fold_441_ = lean_uint64_xor(v___x_438_, v___x_440_);
v___x_442_ = 16ULL;
v___x_443_ = lean_uint64_shift_right(v_fold_441_, v___x_442_);
v___x_444_ = lean_uint64_xor(v_fold_441_, v___x_443_);
v___x_445_ = lean_uint64_to_usize(v___x_444_);
v___x_446_ = lean_usize_of_nat(v___x_434_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_sub(v___x_446_, v___x_447_);
v___x_449_ = lean_usize_land(v___x_445_, v___x_448_);
v___x_450_ = lean_array_uget_borrowed(v_x_426_, v___x_449_);
lean_inc(v___x_450_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 2, v___x_450_);
v___x_452_ = v___x_432_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_key_428_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_value_429_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v___x_450_);
v___x_452_ = v_reuseFailAlloc_455_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = lean_array_uset(v_x_426_, v___x_449_, v___x_452_);
v_x_426_ = v___x_453_;
v_x_427_ = v_tail_430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_457_, lean_object* v_source_458_, lean_object* v_target_459_){
_start:
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_array_get_size(v_source_458_);
v___x_461_ = lean_nat_dec_lt(v_i_457_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec_ref(v_source_458_);
lean_dec(v_i_457_);
return v_target_459_;
}
else
{
lean_object* v_es_462_; lean_object* v___x_463_; lean_object* v_source_464_; lean_object* v_target_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_es_462_ = lean_array_fget(v_source_458_, v_i_457_);
v___x_463_ = lean_box(0);
v_source_464_ = lean_array_fset(v_source_458_, v_i_457_, v___x_463_);
v_target_465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_459_, v_es_462_);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_i_457_, v___x_466_);
lean_dec(v_i_457_);
v_i_457_ = v___x_467_;
v_source_458_ = v_source_464_;
v_target_459_ = v_target_465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_nbuckets_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = lean_array_get_size(v_data_469_);
v___x_471_ = lean_unsigned_to_nat(2u);
v_nbuckets_472_ = lean_nat_mul(v___x_470_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_box(0);
v___x_475_ = lean_mk_array(v_nbuckets_472_, v___x_474_);
v___x_476_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_473_, v_data_469_, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
uint8_t v___x_479_; 
v___x_479_ = 0;
return v___x_479_;
}
else
{
lean_object* v_key_480_; lean_object* v_tail_481_; size_t v___x_482_; size_t v___x_483_; uint8_t v___x_484_; 
v_key_480_ = lean_ctor_get(v_x_478_, 0);
v_tail_481_ = lean_ctor_get(v_x_478_, 2);
v___x_482_ = lean_ptr_addr(v_key_480_);
v___x_483_ = lean_ptr_addr(v_a_477_);
v___x_484_ = lean_usize_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
v_x_478_ = v_tail_481_;
goto _start;
}
else
{
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_486_, lean_object* v_x_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_486_, v_x_487_);
lean_dec(v_x_487_);
lean_dec_ref(v_a_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_490_, lean_object* v_a_491_, lean_object* v_b_492_){
_start:
{
lean_object* v_size_493_; lean_object* v_buckets_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_540_; 
v_size_493_ = lean_ctor_get(v_m_490_, 0);
v_buckets_494_ = lean_ctor_get(v_m_490_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_m_490_);
if (v_isSharedCheck_540_ == 0)
{
v___x_496_ = v_m_490_;
v_isShared_497_ = v_isSharedCheck_540_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_buckets_494_);
lean_inc(v_size_493_);
lean_dec(v_m_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_540_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; uint64_t v_fold_505_; uint64_t v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; size_t v___x_509_; size_t v___x_510_; size_t v___x_511_; size_t v___x_512_; size_t v___x_513_; lean_object* v_bkt_514_; uint8_t v___x_515_; 
v___x_498_ = lean_array_get_size(v_buckets_494_);
v___x_499_ = lean_ptr_addr(v_a_491_);
v___x_500_ = ((size_t)3ULL);
v___x_501_ = lean_usize_shift_right(v___x_499_, v___x_500_);
v___x_502_ = lean_usize_to_uint64(v___x_501_);
v___x_503_ = 32ULL;
v___x_504_ = lean_uint64_shift_right(v___x_502_, v___x_503_);
v_fold_505_ = lean_uint64_xor(v___x_502_, v___x_504_);
v___x_506_ = 16ULL;
v___x_507_ = lean_uint64_shift_right(v_fold_505_, v___x_506_);
v___x_508_ = lean_uint64_xor(v_fold_505_, v___x_507_);
v___x_509_ = lean_uint64_to_usize(v___x_508_);
v___x_510_ = lean_usize_of_nat(v___x_498_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_sub(v___x_510_, v___x_511_);
v___x_513_ = lean_usize_land(v___x_509_, v___x_512_);
v_bkt_514_ = lean_array_uget_borrowed(v_buckets_494_, v___x_513_);
v___x_515_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_491_, v_bkt_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v_size_x27_517_; lean_object* v___x_518_; lean_object* v_buckets_x27_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v_size_x27_517_ = lean_nat_add(v_size_493_, v___x_516_);
lean_dec(v_size_493_);
lean_inc(v_bkt_514_);
v___x_518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_518_, 0, v_a_491_);
lean_ctor_set(v___x_518_, 1, v_b_492_);
lean_ctor_set(v___x_518_, 2, v_bkt_514_);
v_buckets_x27_519_ = lean_array_uset(v_buckets_494_, v___x_513_, v___x_518_);
v___x_520_ = lean_unsigned_to_nat(4u);
v___x_521_ = lean_nat_mul(v_size_x27_517_, v___x_520_);
v___x_522_ = lean_unsigned_to_nat(3u);
v___x_523_ = lean_nat_div(v___x_521_, v___x_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_array_get_size(v_buckets_x27_519_);
v___x_525_ = lean_nat_dec_le(v___x_523_, v___x_524_);
lean_dec(v___x_523_);
if (v___x_525_ == 0)
{
lean_object* v_val_526_; lean_object* v___x_528_; 
v_val_526_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_519_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_val_526_);
lean_ctor_set(v___x_496_, 0, v_size_x27_517_);
v___x_528_ = v___x_496_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_size_x27_517_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_val_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v___x_531_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_buckets_x27_519_);
lean_ctor_set(v___x_496_, 0, v_size_x27_517_);
v___x_531_ = v___x_496_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_size_x27_517_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_buckets_x27_519_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v___x_533_; lean_object* v_buckets_x27_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
lean_inc(v_bkt_514_);
v___x_533_ = lean_box(0);
v_buckets_x27_534_ = lean_array_uset(v_buckets_494_, v___x_513_, v___x_533_);
v___x_535_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_491_, v_b_492_, v_bkt_514_);
v___x_536_ = lean_array_uset(v_buckets_x27_534_, v___x_513_, v___x_535_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_536_);
v___x_538_ = v___x_496_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_size_493_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_541_; size_t v___x_542_; 
v___x_541_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_542_ = lean_ptr_addr(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_543_, lean_object* v_r_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_map_546_; lean_object* v_set_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_571_; 
v_map_546_ = lean_ctor_get(v_a_545_, 0);
v_set_547_ = lean_ctor_get(v_a_545_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_571_ == 0)
{
v___x_549_ = v_a_545_;
v_isShared_550_ = v_isSharedCheck_571_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_set_547_);
lean_inc(v_map_546_);
lean_dec(v_a_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_571_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; uint64_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v___x_551_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_552_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_544_);
v___x_553_ = lean_uint64_to_usize(v___x_552_);
v___x_554_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_547_, v___x_553_, v_r_544_, v___x_551_);
v___x_555_ = lean_ptr_addr(v___x_554_);
v___x_556_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
lean_dec_ref(v_r_544_);
lean_inc_ref(v___x_554_);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_546_, v_e_543_, v___x_554_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_558_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_set_547_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_554_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec_ref(v___x_554_);
lean_inc_ref_n(v_r_544_, 4);
v___x_563_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_546_, v_e_543_, v_r_544_);
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_563_, v_r_544_, v_r_544_);
v___x_565_ = lean_box(0);
v___x_566_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_547_, v_r_544_, v___x_565_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_566_);
lean_ctor_set(v___x_549_, 0, v___x_564_);
v___x_568_ = v___x_549_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_566_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_r_544_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_572_, lean_object* v_r_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_572_, v_r_573_, v_a_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_577_, lean_object* v_r_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_577_, v_r_578_, v_a_579_, v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_582_, lean_object* v_x_583_, size_t v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_583_, v_x_584_, v_x_585_, v_x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
size_t v_x_2667__boxed_593_; lean_object* v_res_594_; 
v_x_2667__boxed_593_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_594_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_588_, v_x_589_, v_x_2667__boxed_593_, v_x_591_, v_x_592_);
lean_dec_ref(v_x_592_);
lean_dec_ref(v_x_591_);
lean_dec_ref(v_x_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_595_, lean_object* v_m_596_, lean_object* v_a_597_, lean_object* v_b_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_596_, v_a_597_, v_b_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_601_, v_x_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_heq_608_, lean_object* v_i_609_, lean_object* v_k_610_, lean_object* v_k_u2080_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_606_, v_i_609_, v_k_610_, v_k_u2080_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_613_, lean_object* v_keys_614_, lean_object* v_vals_615_, lean_object* v_heq_616_, lean_object* v_i_617_, lean_object* v_k_618_, lean_object* v_k_u2080_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_613_, v_keys_614_, v_vals_615_, v_heq_616_, v_i_617_, v_k_618_, v_k_u2080_619_);
lean_dec_ref(v_k_u2080_619_);
lean_dec_ref(v_k_618_);
lean_dec_ref(v_vals_615_);
lean_dec_ref(v_keys_614_);
return v_res_620_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_621_, lean_object* v_a_622_, lean_object* v_x_623_){
_start:
{
uint8_t v___x_624_; 
v___x_624_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_622_, v_x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_625_, lean_object* v_a_626_, lean_object* v_x_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_625_, v_a_626_, v_x_627_);
lean_dec(v_x_627_);
lean_dec_ref(v_a_626_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_630_, lean_object* v_data_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_b_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_634_, v_b_635_, v_x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_638_, lean_object* v_x_639_, size_t v_x_640_, size_t v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_639_, v_x_640_, v_x_641_, v_x_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
size_t v_x_2704__boxed_651_; size_t v_x_2705__boxed_652_; lean_object* v_res_653_; 
v_x_2704__boxed_651_ = lean_unbox_usize(v_x_647_);
lean_dec(v_x_647_);
v_x_2705__boxed_652_ = lean_unbox_usize(v_x_648_);
lean_dec(v_x_648_);
v_res_653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_645_, v_x_646_, v_x_2704__boxed_651_, v_x_2705__boxed_652_, v_x_649_, v_x_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_654_, lean_object* v_i_655_, lean_object* v_source_656_, lean_object* v_target_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_655_, v_source_656_, v_target_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_659_, lean_object* v_n_660_, lean_object* v_k_661_, lean_object* v_v_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_660_, v_k_661_, v_v_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_664_, size_t v_depth_665_, lean_object* v_keys_666_, lean_object* v_vals_667_, lean_object* v_heq_668_, lean_object* v_i_669_, lean_object* v_entries_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_665_, v_keys_666_, v_vals_667_, v_i_669_, v_entries_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_672_, lean_object* v_depth_673_, lean_object* v_keys_674_, lean_object* v_vals_675_, lean_object* v_heq_676_, lean_object* v_i_677_, lean_object* v_entries_678_){
_start:
{
size_t v_depth_boxed_679_; lean_object* v_res_680_; 
v_depth_boxed_679_ = lean_unbox_usize(v_depth_673_);
lean_dec(v_depth_673_);
v_res_680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_672_, v_depth_boxed_679_, v_keys_674_, v_vals_675_, v_heq_676_, v_i_677_, v_entries_678_);
lean_dec_ref(v_vals_675_);
lean_dec_ref(v_keys_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_686_, v_x_687_, v_x_688_, v_x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_693_, lean_object* v_k_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_map_697_; lean_object* v_set_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___x_701_; 
v_map_697_ = lean_ctor_get(v_a_696_, 0);
v_set_698_ = lean_ctor_get(v_a_696_, 1);
v___f_699_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_700_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_693_);
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_699_, v___f_700_, v_map_697_, v_e_693_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v_val_702_; lean_object* v___x_703_; 
lean_dec_ref(v_k_694_);
lean_dec_ref(v_e_693_);
v_val_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_val_702_);
lean_ctor_set(v___x_703_, 1, v_a_696_);
return v___x_703_;
}
else
{
lean_object* v___f_704_; lean_object* v___x_705_; uint64_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; size_t v___x_709_; size_t v___x_710_; uint8_t v___x_711_; 
lean_dec(v___x_701_);
v___f_704_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_705_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_706_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_693_);
v___x_707_ = lean_uint64_to_usize(v___x_706_);
lean_inc_ref(v_e_693_);
lean_inc_ref(v_set_698_);
v___x_708_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_704_, v_set_698_, v___x_707_, v_e_693_, v___x_705_);
v___x_709_ = lean_ptr_addr(v___x_708_);
v___x_710_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_711_ = lean_usize_dec_eq(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_k_694_);
lean_dec_ref(v_e_693_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_708_);
lean_ctor_set(v___x_712_, 1, v_a_696_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; 
lean_dec(v___x_708_);
lean_inc_ref(v_a_695_);
v___x_713_ = lean_apply_2(v_k_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
v_a_715_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_713_, 2);
v___x_716_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_693_, v_a_714_, v_a_715_);
return v___x_716_;
}
else
{
lean_dec_ref(v_e_693_);
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_717_, lean_object* v_k_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_717_, v_k_718_, v_a_719_, v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_722_, lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_box(0);
return v___x_724_;
}
else
{
lean_object* v_key_725_; lean_object* v_value_726_; lean_object* v_tail_727_; size_t v___x_728_; size_t v___x_729_; uint8_t v___x_730_; 
v_key_725_ = lean_ctor_get(v_x_723_, 0);
v_value_726_ = lean_ctor_get(v_x_723_, 1);
v_tail_727_ = lean_ctor_get(v_x_723_, 2);
v___x_728_ = lean_ptr_addr(v_key_725_);
v___x_729_ = lean_ptr_addr(v_a_722_);
v___x_730_ = lean_usize_dec_eq(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
v_x_723_ = v_tail_727_;
goto _start;
}
else
{
lean_object* v___x_732_; 
lean_inc(v_value_726_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_value_726_);
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_733_, lean_object* v_x_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_733_, v_x_734_);
lean_dec(v_x_734_);
lean_dec_ref(v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_buckets_738_; lean_object* v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; uint64_t v___x_743_; uint64_t v___x_744_; uint64_t v___x_745_; uint64_t v_fold_746_; uint64_t v___x_747_; uint64_t v___x_748_; uint64_t v___x_749_; size_t v___x_750_; size_t v___x_751_; size_t v___x_752_; size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_buckets_738_ = lean_ctor_get(v_m_736_, 1);
v___x_739_ = lean_array_get_size(v_buckets_738_);
v___x_740_ = lean_ptr_addr(v_a_737_);
v___x_741_ = ((size_t)3ULL);
v___x_742_ = lean_usize_shift_right(v___x_740_, v___x_741_);
v___x_743_ = lean_usize_to_uint64(v___x_742_);
v___x_744_ = 32ULL;
v___x_745_ = lean_uint64_shift_right(v___x_743_, v___x_744_);
v_fold_746_ = lean_uint64_xor(v___x_743_, v___x_745_);
v___x_747_ = 16ULL;
v___x_748_ = lean_uint64_shift_right(v_fold_746_, v___x_747_);
v___x_749_ = lean_uint64_xor(v_fold_746_, v___x_748_);
v___x_750_ = lean_uint64_to_usize(v___x_749_);
v___x_751_ = lean_usize_of_nat(v___x_739_);
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_sub(v___x_751_, v___x_752_);
v___x_754_ = lean_usize_land(v___x_750_, v___x_753_);
v___x_755_ = lean_array_uget_borrowed(v_buckets_738_, v___x_754_);
v___x_756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_737_, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_757_, v_a_758_);
lean_dec_ref(v_a_758_);
lean_dec_ref(v_m_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_760_, lean_object* v_vals_761_, lean_object* v_i_762_, lean_object* v_k_763_){
_start:
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = lean_array_get_size(v_keys_760_);
v___x_765_ = lean_nat_dec_lt(v_i_762_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_dec(v_i_762_);
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
lean_object* v_k_x27_767_; uint8_t v___x_768_; 
v_k_x27_767_ = lean_array_fget_borrowed(v_keys_760_, v_i_762_);
v___x_768_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_763_, v_k_x27_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v_i_762_, v___x_769_);
lean_dec(v_i_762_);
v_i_762_ = v___x_770_;
goto _start;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_array_fget_borrowed(v_vals_761_, v_i_762_);
lean_dec(v_i_762_);
lean_inc(v___x_772_);
lean_inc(v_k_x27_767_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_k_x27_767_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_775_, lean_object* v_vals_776_, lean_object* v_i_777_, lean_object* v_k_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_775_, v_vals_776_, v_i_777_, v_k_778_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_vals_776_);
lean_dec_ref(v_keys_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_780_, size_t v_x_781_, lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v_es_783_; lean_object* v___x_784_; size_t v___x_785_; size_t v___x_786_; lean_object* v_j_787_; lean_object* v___x_788_; 
v_es_783_ = lean_ctor_get(v_x_780_, 0);
v___x_784_ = lean_box(2);
v___x_785_ = ((size_t)31ULL);
v___x_786_ = lean_usize_land(v_x_781_, v___x_785_);
v_j_787_ = lean_usize_to_nat(v___x_786_);
v___x_788_ = lean_array_get_borrowed(v___x_784_, v_es_783_, v_j_787_);
lean_dec(v_j_787_);
switch(lean_obj_tag(v___x_788_))
{
case 0:
{
lean_object* v_key_789_; lean_object* v_val_790_; uint8_t v___x_791_; 
v_key_789_ = lean_ctor_get(v___x_788_, 0);
v_val_790_ = lean_ctor_get(v___x_788_, 1);
v___x_791_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_782_, v_key_789_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_box(0);
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_inc(v_val_790_);
lean_inc(v_key_789_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_key_789_);
lean_ctor_set(v___x_793_, 1, v_val_790_);
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
case 1:
{
lean_object* v_node_795_; size_t v___x_796_; size_t v___x_797_; 
v_node_795_ = lean_ctor_get(v___x_788_, 0);
v___x_796_ = ((size_t)5ULL);
v___x_797_ = lean_usize_shift_right(v_x_781_, v___x_796_);
v_x_780_ = v_node_795_;
v_x_781_ = v___x_797_;
goto _start;
}
default: 
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(0);
return v___x_799_;
}
}
}
else
{
lean_object* v_ks_800_; lean_object* v_vs_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_ks_800_ = lean_ctor_get(v_x_780_, 0);
v_vs_801_ = lean_ctor_get(v_x_780_, 1);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_800_, v_vs_801_, v___x_802_, v_x_782_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
size_t v_x_11089__boxed_807_; lean_object* v_res_808_; 
v_x_11089__boxed_807_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_res_808_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_804_, v_x_11089__boxed_807_, v_x_806_);
lean_dec_ref(v_x_806_);
lean_dec_ref(v_x_804_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
uint64_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_810_);
v___x_812_ = lean_uint64_to_usize(v___x_811_);
v___x_813_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_809_, v___x_812_, v_x_810_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_814_, v_x_815_);
lean_dec_ref(v_x_815_);
lean_dec_ref(v_x_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___y_821_; lean_object* v___y_826_; lean_object* v___y_831_; lean_object* v___y_836_; 
switch(lean_obj_tag(v_e_817_))
{
case 4:
{
lean_object* v_declName_840_; lean_object* v_map_841_; lean_object* v_set_842_; lean_object* v___x_843_; 
v_declName_840_ = lean_ctor_get(v_e_817_, 0);
v_map_841_ = lean_ctor_get(v_a_819_, 0);
v_set_842_ = lean_ctor_get(v_a_819_, 1);
v___x_843_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_842_, v_e_817_);
if (lean_obj_tag(v___x_843_) == 0)
{
uint8_t v___x_844_; 
lean_inc(v_declName_840_);
lean_inc_ref(v_a_818_);
v___x_844_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_818_, v_declName_840_);
if (v___x_844_ == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_854_; 
lean_inc_ref(v_set_842_);
lean_inc_ref(v_map_841_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_855_ = lean_ctor_get(v_a_819_, 1);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_a_819_, 0);
lean_dec(v_unused_856_);
v___x_846_ = v_a_819_;
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_a_819_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = lean_box(0);
lean_inc_ref(v_e_817_);
v___x_849_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_842_, v_e_817_, v___x_848_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_map_841_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_853_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_e_817_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
return v___x_852_;
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref_known(v_e_817_, 2);
v___x_857_ = lean_box(0);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_a_819_);
return v___x_858_;
}
}
else
{
lean_object* v_val_859_; lean_object* v_fst_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref_known(v_e_817_, 2);
v_val_859_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v___x_843_, 1);
v_fst_860_ = lean_ctor_get(v_val_859_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_val_859_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v_val_859_, 1);
lean_dec(v_unused_868_);
v___x_862_ = v_val_859_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_fst_860_);
lean_dec(v_val_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_a_819_);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_fst_860_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_a_819_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
case 5:
{
lean_object* v_fn_869_; lean_object* v_arg_870_; lean_object* v_map_871_; lean_object* v_set_872_; lean_object* v___x_873_; 
v_fn_869_ = lean_ctor_get(v_e_817_, 0);
v_arg_870_ = lean_ctor_get(v_e_817_, 1);
v_map_871_ = lean_ctor_get(v_a_819_, 0);
v_set_872_ = lean_ctor_get(v_a_819_, 1);
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_871_, v_e_817_);
if (lean_obj_tag(v___x_873_) == 1)
{
lean_object* v_val_874_; lean_object* v___x_875_; 
lean_dec_ref_known(v_e_817_, 2);
v_val_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v_val_874_);
lean_ctor_set(v___x_875_, 1, v_a_819_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; uint64_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; size_t v___x_880_; size_t v___x_881_; uint8_t v___x_882_; 
lean_dec(v___x_873_);
v___x_876_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_877_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_817_);
v___x_878_ = lean_uint64_to_usize(v___x_877_);
v___x_879_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_872_, v___x_878_, v_e_817_, v___x_876_);
v___x_880_ = lean_ptr_addr(v___x_879_);
v___x_881_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_882_ = lean_usize_dec_eq(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
lean_dec_ref_known(v_e_817_, 2);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_879_);
lean_ctor_set(v___x_883_, 1, v_a_819_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; 
lean_dec_ref(v___x_879_);
lean_inc_ref(v_fn_869_);
v___x_884_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_869_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
v_a_886_ = lean_ctor_get(v___x_884_, 1);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_884_, 2);
lean_inc_ref(v_arg_870_);
v___x_887_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_870_, v_a_818_, v_a_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v_a_889_; uint8_t v___y_891_; size_t v___x_895_; size_t v___x_896_; uint8_t v___x_897_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
v_a_889_ = lean_ctor_get(v___x_887_, 1);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_887_, 2);
v___x_895_ = lean_ptr_addr(v_fn_869_);
v___x_896_ = lean_ptr_addr(v_a_885_);
v___x_897_ = lean_usize_dec_eq(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
v___y_891_ = v___x_897_;
goto v___jp_890_;
}
else
{
size_t v___x_898_; size_t v___x_899_; uint8_t v___x_900_; 
v___x_898_ = lean_ptr_addr(v_arg_870_);
v___x_899_ = lean_ptr_addr(v_a_888_);
v___x_900_ = lean_usize_dec_eq(v___x_898_, v___x_899_);
v___y_891_ = v___x_900_;
goto v___jp_890_;
}
v___jp_890_:
{
if (v___y_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = l_Lean_Expr_app___override(v_a_885_, v_a_888_);
v___x_893_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_892_, v_a_889_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
lean_dec(v_a_888_);
lean_dec(v_a_885_);
lean_inc_ref(v_e_817_);
v___x_894_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_e_817_, v_a_889_);
return v___x_894_;
}
}
}
else
{
lean_dec(v_a_885_);
v___y_831_ = v___x_887_;
goto v___jp_830_;
}
}
else
{
v___y_831_ = v___x_884_;
goto v___jp_830_;
}
}
}
}
case 6:
{
lean_object* v_binderName_901_; lean_object* v_binderType_902_; lean_object* v_body_903_; uint8_t v_binderInfo_904_; lean_object* v_map_905_; lean_object* v_set_906_; lean_object* v___x_907_; 
v_binderName_901_ = lean_ctor_get(v_e_817_, 0);
v_binderType_902_ = lean_ctor_get(v_e_817_, 1);
v_body_903_ = lean_ctor_get(v_e_817_, 2);
v_binderInfo_904_ = lean_ctor_get_uint8(v_e_817_, sizeof(void*)*3 + 8);
v_map_905_ = lean_ctor_get(v_a_819_, 0);
v_set_906_ = lean_ctor_get(v_a_819_, 1);
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_905_, v_e_817_);
if (lean_obj_tag(v___x_907_) == 1)
{
lean_object* v_val_908_; lean_object* v___x_909_; 
lean_dec_ref_known(v_e_817_, 3);
v_val_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_val_908_);
lean_dec_ref_known(v___x_907_, 1);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_val_908_);
lean_ctor_set(v___x_909_, 1, v_a_819_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; uint64_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; uint8_t v___x_916_; 
lean_dec(v___x_907_);
v___x_910_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_911_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_817_);
v___x_912_ = lean_uint64_to_usize(v___x_911_);
v___x_913_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_906_, v___x_912_, v_e_817_, v___x_910_);
v___x_914_ = lean_ptr_addr(v___x_913_);
v___x_915_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_916_ = lean_usize_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec_ref_known(v_e_817_, 3);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_913_);
lean_ctor_set(v___x_917_, 1, v_a_819_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; 
lean_dec_ref(v___x_913_);
lean_inc_ref(v_binderType_902_);
v___x_918_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_902_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v_a_920_; lean_object* v___x_921_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
v_a_920_ = lean_ctor_get(v___x_918_, 1);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_918_, 2);
lean_inc_ref(v_body_903_);
v___x_921_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_903_, v_a_818_, v_a_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v_a_923_; uint8_t v___y_925_; size_t v___x_932_; size_t v___x_933_; uint8_t v___x_934_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
v_a_923_ = lean_ctor_get(v___x_921_, 1);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_921_, 2);
v___x_932_ = lean_ptr_addr(v_binderType_902_);
v___x_933_ = lean_ptr_addr(v_a_919_);
v___x_934_ = lean_usize_dec_eq(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
v___y_925_ = v___x_934_;
goto v___jp_924_;
}
else
{
size_t v___x_935_; size_t v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_ptr_addr(v_body_903_);
v___x_936_ = lean_ptr_addr(v_a_922_);
v___x_937_ = lean_usize_dec_eq(v___x_935_, v___x_936_);
v___y_925_ = v___x_937_;
goto v___jp_924_;
}
v___jp_924_:
{
if (v___y_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_inc(v_binderName_901_);
v___x_926_ = l_Lean_Expr_lam___override(v_binderName_901_, v_a_919_, v_a_922_, v_binderInfo_904_);
v___x_927_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_926_, v_a_923_);
return v___x_927_;
}
else
{
uint8_t v___x_928_; 
v___x_928_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_904_, v_binderInfo_904_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc(v_binderName_901_);
v___x_929_ = l_Lean_Expr_lam___override(v_binderName_901_, v_a_919_, v_a_922_, v_binderInfo_904_);
v___x_930_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_929_, v_a_923_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; 
lean_dec(v_a_922_);
lean_dec(v_a_919_);
lean_inc_ref(v_e_817_);
v___x_931_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_e_817_, v_a_923_);
return v___x_931_;
}
}
}
}
else
{
lean_dec(v_a_919_);
v___y_826_ = v___x_921_;
goto v___jp_825_;
}
}
else
{
v___y_826_ = v___x_918_;
goto v___jp_825_;
}
}
}
}
case 7:
{
lean_object* v_binderName_938_; lean_object* v_binderType_939_; lean_object* v_body_940_; uint8_t v_binderInfo_941_; lean_object* v_map_942_; lean_object* v_set_943_; lean_object* v___x_944_; 
v_binderName_938_ = lean_ctor_get(v_e_817_, 0);
v_binderType_939_ = lean_ctor_get(v_e_817_, 1);
v_body_940_ = lean_ctor_get(v_e_817_, 2);
v_binderInfo_941_ = lean_ctor_get_uint8(v_e_817_, sizeof(void*)*3 + 8);
v_map_942_ = lean_ctor_get(v_a_819_, 0);
v_set_943_ = lean_ctor_get(v_a_819_, 1);
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_942_, v_e_817_);
if (lean_obj_tag(v___x_944_) == 1)
{
lean_object* v_val_945_; lean_object* v___x_946_; 
lean_dec_ref_known(v_e_817_, 3);
v_val_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_val_945_);
lean_ctor_set(v___x_946_, 1, v_a_819_);
return v___x_946_;
}
else
{
lean_object* v___x_947_; uint64_t v___x_948_; size_t v___x_949_; lean_object* v___x_950_; size_t v___x_951_; size_t v___x_952_; uint8_t v___x_953_; 
lean_dec(v___x_944_);
v___x_947_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_948_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_817_);
v___x_949_ = lean_uint64_to_usize(v___x_948_);
v___x_950_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_943_, v___x_949_, v_e_817_, v___x_947_);
v___x_951_ = lean_ptr_addr(v___x_950_);
v___x_952_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_953_ = lean_usize_dec_eq(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec_ref_known(v_e_817_, 3);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_950_);
lean_ctor_set(v___x_954_, 1, v_a_819_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; 
lean_dec_ref(v___x_950_);
lean_inc_ref(v_binderType_939_);
v___x_955_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_939_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_a_957_; lean_object* v___x_958_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
v_a_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_955_, 2);
lean_inc_ref(v_body_940_);
v___x_958_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_940_, v_a_818_, v_a_957_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_a_960_; uint8_t v___y_962_; size_t v___x_969_; size_t v___x_970_; uint8_t v___x_971_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
v_a_960_ = lean_ctor_get(v___x_958_, 1);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_958_, 2);
v___x_969_ = lean_ptr_addr(v_binderType_939_);
v___x_970_ = lean_ptr_addr(v_a_956_);
v___x_971_ = lean_usize_dec_eq(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
v___y_962_ = v___x_971_;
goto v___jp_961_;
}
else
{
size_t v___x_972_; size_t v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_ptr_addr(v_body_940_);
v___x_973_ = lean_ptr_addr(v_a_959_);
v___x_974_ = lean_usize_dec_eq(v___x_972_, v___x_973_);
v___y_962_ = v___x_974_;
goto v___jp_961_;
}
v___jp_961_:
{
if (v___y_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc(v_binderName_938_);
v___x_963_ = l_Lean_Expr_forallE___override(v_binderName_938_, v_a_956_, v_a_959_, v_binderInfo_941_);
v___x_964_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_963_, v_a_960_);
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_941_, v_binderInfo_941_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_inc(v_binderName_938_);
v___x_966_ = l_Lean_Expr_forallE___override(v_binderName_938_, v_a_956_, v_a_959_, v_binderInfo_941_);
v___x_967_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_966_, v_a_960_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; 
lean_dec(v_a_959_);
lean_dec(v_a_956_);
lean_inc_ref(v_e_817_);
v___x_968_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_e_817_, v_a_960_);
return v___x_968_;
}
}
}
}
else
{
lean_dec(v_a_956_);
v___y_836_ = v___x_958_;
goto v___jp_835_;
}
}
else
{
v___y_836_ = v___x_955_;
goto v___jp_835_;
}
}
}
}
case 8:
{
lean_object* v_declName_975_; lean_object* v_type_976_; lean_object* v_value_977_; lean_object* v_body_978_; uint8_t v_nondep_979_; lean_object* v_map_980_; lean_object* v_set_981_; lean_object* v___x_982_; 
v_declName_975_ = lean_ctor_get(v_e_817_, 0);
v_type_976_ = lean_ctor_get(v_e_817_, 1);
v_value_977_ = lean_ctor_get(v_e_817_, 2);
v_body_978_ = lean_ctor_get(v_e_817_, 3);
v_nondep_979_ = lean_ctor_get_uint8(v_e_817_, sizeof(void*)*4 + 8);
v_map_980_ = lean_ctor_get(v_a_819_, 0);
v_set_981_ = lean_ctor_get(v_a_819_, 1);
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_980_, v_e_817_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_val_983_; lean_object* v___x_984_; 
lean_dec_ref_known(v_e_817_, 4);
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_val_983_);
lean_ctor_set(v___x_984_, 1, v_a_819_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; uint64_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; size_t v___x_989_; size_t v___x_990_; uint8_t v___x_991_; 
lean_dec(v___x_982_);
v___x_985_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_986_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_817_);
v___x_987_ = lean_uint64_to_usize(v___x_986_);
v___x_988_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_981_, v___x_987_, v_e_817_, v___x_985_);
v___x_989_ = lean_ptr_addr(v___x_988_);
v___x_990_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_991_ = lean_usize_dec_eq(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec_ref_known(v_e_817_, 4);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_988_);
lean_ctor_set(v___x_992_, 1, v_a_819_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; 
lean_dec_ref(v___x_988_);
lean_inc_ref(v_type_976_);
v___x_993_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_976_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
v_a_995_ = lean_ctor_get(v___x_993_, 1);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_993_, 2);
lean_inc_ref(v_value_977_);
v___x_996_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_977_, v_a_818_, v_a_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
v_a_998_ = lean_ctor_get(v___x_996_, 1);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_996_, 2);
lean_inc_ref(v_body_978_);
v___x_999_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_978_, v_a_818_, v_a_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_a_1001_; uint8_t v___y_1003_; size_t v___x_1012_; size_t v___x_1013_; uint8_t v___x_1014_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
v_a_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_999_, 2);
v___x_1012_ = lean_ptr_addr(v_type_976_);
v___x_1013_ = lean_ptr_addr(v_a_994_);
v___x_1014_ = lean_usize_dec_eq(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
v___y_1003_ = v___x_1014_;
goto v___jp_1002_;
}
else
{
size_t v___x_1015_; size_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1015_ = lean_ptr_addr(v_value_977_);
v___x_1016_ = lean_ptr_addr(v_a_997_);
v___x_1017_ = lean_usize_dec_eq(v___x_1015_, v___x_1016_);
v___y_1003_ = v___x_1017_;
goto v___jp_1002_;
}
v___jp_1002_:
{
if (v___y_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_inc(v_declName_975_);
v___x_1004_ = l_Lean_Expr_letE___override(v_declName_975_, v_a_994_, v_a_997_, v_a_1000_, v_nondep_979_);
v___x_1005_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_1004_, v_a_1001_);
return v___x_1005_;
}
else
{
size_t v___x_1006_; size_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_ptr_addr(v_body_978_);
v___x_1007_ = lean_ptr_addr(v_a_1000_);
v___x_1008_ = lean_usize_dec_eq(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_inc(v_declName_975_);
v___x_1009_ = l_Lean_Expr_letE___override(v_declName_975_, v_a_994_, v_a_997_, v_a_1000_, v_nondep_979_);
v___x_1010_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_1009_, v_a_1001_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; 
lean_dec(v_a_1000_);
lean_dec(v_a_997_);
lean_dec(v_a_994_);
lean_inc_ref(v_e_817_);
v___x_1011_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_e_817_, v_a_1001_);
return v___x_1011_;
}
}
}
}
else
{
lean_dec(v_a_997_);
lean_dec(v_a_994_);
v___y_821_ = v___x_999_;
goto v___jp_820_;
}
}
else
{
lean_dec(v_a_994_);
v___y_821_ = v___x_996_;
goto v___jp_820_;
}
}
else
{
v___y_821_ = v___x_993_;
goto v___jp_820_;
}
}
}
}
case 10:
{
lean_object* v_data_1018_; lean_object* v_expr_1019_; lean_object* v_map_1020_; lean_object* v_set_1021_; lean_object* v___x_1022_; 
v_data_1018_ = lean_ctor_get(v_e_817_, 0);
v_expr_1019_ = lean_ctor_get(v_e_817_, 1);
v_map_1020_ = lean_ctor_get(v_a_819_, 0);
v_set_1021_ = lean_ctor_get(v_a_819_, 1);
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1020_, v_e_817_);
if (lean_obj_tag(v___x_1022_) == 1)
{
lean_object* v_val_1023_; lean_object* v___x_1024_; 
lean_dec_ref_known(v_e_817_, 2);
v_val_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_val_1023_);
lean_ctor_set(v___x_1024_, 1, v_a_819_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; uint64_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; uint8_t v___x_1031_; 
lean_dec(v___x_1022_);
v___x_1025_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1026_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_817_);
v___x_1027_ = lean_uint64_to_usize(v___x_1026_);
v___x_1028_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1021_, v___x_1027_, v_e_817_, v___x_1025_);
v___x_1029_ = lean_ptr_addr(v___x_1028_);
v___x_1030_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1031_ = lean_usize_dec_eq(v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; 
lean_dec_ref_known(v_e_817_, 2);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1028_);
lean_ctor_set(v___x_1032_, 1, v_a_819_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; 
lean_dec_ref(v___x_1028_);
lean_inc_ref(v_expr_1019_);
v___x_1033_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1019_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v_a_1035_; size_t v___x_1036_; size_t v___x_1037_; uint8_t v___x_1038_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
v_a_1035_ = lean_ctor_get(v___x_1033_, 1);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1033_, 2);
v___x_1036_ = lean_ptr_addr(v_expr_1019_);
v___x_1037_ = lean_ptr_addr(v_a_1034_);
v___x_1038_ = lean_usize_dec_eq(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_inc(v_data_1018_);
v___x_1039_ = l_Lean_Expr_mdata___override(v_data_1018_, v_a_1034_);
v___x_1040_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_1039_, v_a_1035_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; 
lean_dec(v_a_1034_);
lean_inc_ref(v_e_817_);
v___x_1041_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_e_817_, v_a_1035_);
return v___x_1041_;
}
}
else
{
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1042_; lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1042_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1042_);
v_a_1043_ = lean_ctor_get(v___x_1033_, 1);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1033_, 2);
v___x_1044_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_a_1042_, v_a_1043_);
return v___x_1044_;
}
else
{
lean_dec_ref_known(v_e_817_, 2);
return v___x_1033_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1045_; lean_object* v_idx_1046_; lean_object* v_struct_1047_; lean_object* v_map_1048_; lean_object* v_set_1049_; lean_object* v___x_1050_; 
v_typeName_1045_ = lean_ctor_get(v_e_817_, 0);
v_idx_1046_ = lean_ctor_get(v_e_817_, 1);
v_struct_1047_ = lean_ctor_get(v_e_817_, 2);
v_map_1048_ = lean_ctor_get(v_a_819_, 0);
v_set_1049_ = lean_ctor_get(v_a_819_, 1);
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1048_, v_e_817_);
if (lean_obj_tag(v___x_1050_) == 1)
{
lean_object* v_val_1051_; lean_object* v___x_1052_; 
lean_dec_ref_known(v_e_817_, 3);
v_val_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_val_1051_);
lean_ctor_set(v___x_1052_, 1, v_a_819_);
return v___x_1052_;
}
else
{
lean_object* v___x_1053_; uint64_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; uint8_t v___x_1059_; 
lean_dec(v___x_1050_);
v___x_1053_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1054_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_817_);
v___x_1055_ = lean_uint64_to_usize(v___x_1054_);
v___x_1056_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1049_, v___x_1055_, v_e_817_, v___x_1053_);
v___x_1057_ = lean_ptr_addr(v___x_1056_);
v___x_1058_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1059_ = lean_usize_dec_eq(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_dec_ref_known(v_e_817_, 3);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1056_);
lean_ctor_set(v___x_1060_, 1, v_a_819_);
return v___x_1060_;
}
else
{
uint8_t v_checkProj_1061_; 
lean_dec_ref(v___x_1056_);
v_checkProj_1061_ = lean_ctor_get_uint8(v_a_818_, sizeof(void*)*1 + 1);
if (v_checkProj_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_inc_ref(v_struct_1047_);
v___x_1062_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1047_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v_a_1064_; size_t v___x_1065_; size_t v___x_1066_; uint8_t v___x_1067_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
v_a_1064_ = lean_ctor_get(v___x_1062_, 1);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1062_, 2);
v___x_1065_ = lean_ptr_addr(v_struct_1047_);
v___x_1066_ = lean_ptr_addr(v_a_1063_);
v___x_1067_ = lean_usize_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_inc(v_idx_1046_);
lean_inc(v_typeName_1045_);
v___x_1068_ = l_Lean_Expr_proj___override(v_typeName_1045_, v_idx_1046_, v_a_1063_);
v___x_1069_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v___x_1068_, v_a_1064_);
return v___x_1069_;
}
else
{
lean_object* v___x_1070_; 
lean_dec(v_a_1063_);
lean_inc_ref(v_e_817_);
v___x_1070_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_e_817_, v_a_1064_);
return v___x_1070_;
}
}
else
{
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1071_; lean_object* v_a_1072_; lean_object* v___x_1073_; 
v_a_1071_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1071_);
v_a_1072_ = lean_ctor_get(v___x_1062_, 1);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1062_, 2);
v___x_1073_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_a_1071_, v_a_1072_);
return v___x_1073_;
}
else
{
lean_dec_ref_known(v_e_817_, 3);
return v___x_1062_;
}
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref_known(v_e_817_, 3);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_a_819_);
return v___x_1075_;
}
}
}
}
default: 
{
lean_object* v_map_1076_; lean_object* v_set_1077_; lean_object* v___x_1078_; 
v_map_1076_ = lean_ctor_get(v_a_819_, 0);
v_set_1077_ = lean_ctor_get(v_a_819_, 1);
v___x_1078_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1077_, v_e_817_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1088_; 
lean_inc_ref(v_set_1077_);
lean_inc_ref(v_map_1076_);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1089_ = lean_ctor_get(v_a_819_, 1);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_a_819_, 0);
lean_dec(v_unused_1090_);
v___x_1080_ = v_a_819_;
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_a_819_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1082_ = lean_box(0);
lean_inc_ref(v_e_817_);
v___x_1083_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1077_, v_e_817_, v___x_1082_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1083_);
v___x_1085_ = v___x_1080_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_map_1076_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_e_817_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
return v___x_1086_;
}
}
}
else
{
lean_object* v_val_1091_; lean_object* v_fst_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_e_817_);
v_val_1091_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v___x_1078_, 1);
v_fst_1092_ = lean_ctor_get(v_val_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_val_1091_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_val_1091_, 1);
lean_dec(v_unused_1100_);
v___x_1094_ = v_val_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_fst_1092_);
lean_dec(v_val_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_a_819_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1092_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_a_819_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
v___jp_820_:
{
if (lean_obj_tag(v___y_821_) == 0)
{
lean_object* v_a_822_; lean_object* v_a_823_; lean_object* v___x_824_; 
v_a_822_ = lean_ctor_get(v___y_821_, 0);
lean_inc(v_a_822_);
v_a_823_ = lean_ctor_get(v___y_821_, 1);
lean_inc(v_a_823_);
lean_dec_ref_known(v___y_821_, 2);
v___x_824_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_a_822_, v_a_823_);
return v___x_824_;
}
else
{
lean_dec_ref(v_e_817_);
return v___y_821_;
}
}
v___jp_825_:
{
if (lean_obj_tag(v___y_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_827_ = lean_ctor_get(v___y_826_, 0);
lean_inc(v_a_827_);
v_a_828_ = lean_ctor_get(v___y_826_, 1);
lean_inc(v_a_828_);
lean_dec_ref_known(v___y_826_, 2);
v___x_829_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_a_827_, v_a_828_);
return v___x_829_;
}
else
{
lean_dec_ref(v_e_817_);
return v___y_826_;
}
}
v___jp_830_:
{
if (lean_obj_tag(v___y_831_) == 0)
{
lean_object* v_a_832_; lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_832_ = lean_ctor_get(v___y_831_, 0);
lean_inc(v_a_832_);
v_a_833_ = lean_ctor_get(v___y_831_, 1);
lean_inc(v_a_833_);
lean_dec_ref_known(v___y_831_, 2);
v___x_834_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_a_832_, v_a_833_);
return v___x_834_;
}
else
{
lean_dec_ref(v_e_817_);
return v___y_831_;
}
}
v___jp_835_:
{
if (lean_obj_tag(v___y_836_) == 0)
{
lean_object* v_a_837_; lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_837_ = lean_ctor_get(v___y_836_, 0);
lean_inc(v_a_837_);
v_a_838_ = lean_ctor_get(v___y_836_, 1);
lean_inc(v_a_838_);
lean_dec_ref_known(v___y_836_, 2);
v___x_839_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_817_, v_a_837_, v_a_838_);
return v___x_839_;
}
else
{
lean_dec_ref(v_e_817_);
return v___y_836_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1101_, v_a_1102_, v_a_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1109_, v_x_1110_, v_x_1111_);
lean_dec_ref(v_x_1111_);
lean_dec_ref(v_x_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1113_, lean_object* v_m_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1114_, v_a_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_m_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1117_, v_m_1118_, v_a_1119_);
lean_dec_ref(v_a_1119_);
lean_dec_ref(v_m_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, size_t v_x_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1122_, v_x_1123_, v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
size_t v_x_11735__boxed_1130_; lean_object* v_res_1131_; 
v_x_11735__boxed_1130_ = lean_unbox_usize(v_x_1128_);
lean_dec(v_x_1128_);
v_res_1131_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1126_, v_x_1127_, v_x_11735__boxed_1130_, v_x_1129_);
lean_dec_ref(v_x_1129_);
lean_dec_ref(v_x_1127_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1132_, lean_object* v_a_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1133_, v_x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1136_, lean_object* v_a_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1136_, v_a_1137_, v_x_1138_);
lean_dec(v_x_1138_);
lean_dec_ref(v_a_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_heq_1143_, lean_object* v_i_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1141_, v_vals_1142_, v_i_1144_, v_k_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_keys_1148_, lean_object* v_vals_1149_, lean_object* v_heq_1150_, lean_object* v_i_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1147_, v_keys_1148_, v_vals_1149_, v_heq_1150_, v_i_1151_, v_k_1152_);
lean_dec_ref(v_k_1152_);
lean_dec_ref(v_vals_1149_);
lean_dec_ref(v_keys_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1154_, lean_object* v_cache_1155_, lean_object* v_ctx_1156_, lean_object* v_s_1157_){
_start:
{
lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; 
v___f_1158_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1159_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1154_);
v___x_1160_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1158_, v___f_1159_, v_s_1157_, v_e_1154_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_cache_1155_);
lean_ctor_set(v___x_1161_, 1, v_s_1157_);
v___x_1162_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1154_, v_ctx_1156_, v___x_1161_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 1);
v_a_1164_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1162_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1163_);
lean_inc(v_a_1164_);
lean_dec(v___x_1162_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_set_1168_; lean_object* v___x_1170_; 
v_set_1168_ = lean_ctor_get(v_a_1163_, 1);
lean_inc_ref(v_set_1168_);
lean_dec(v_a_1163_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_set_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_set_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1182_; 
v_a_1173_ = lean_ctor_get(v___x_1162_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1162_, 0);
lean_dec(v_unused_1183_);
v___x_1175_ = v___x_1162_;
v_isShared_1176_ = v_isSharedCheck_1182_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1162_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1182_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_map_1177_; lean_object* v_set_1178_; lean_object* v___x_1180_; 
v_map_1177_ = lean_ctor_get(v_a_1173_, 0);
lean_inc_ref(v_map_1177_);
v_set_1178_ = lean_ctor_get(v_a_1173_, 1);
lean_inc_ref(v_set_1178_);
lean_dec(v_a_1173_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_set_1178_);
lean_ctor_set(v___x_1175_, 0, v_map_1177_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_map_1177_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_set_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v_val_1184_; lean_object* v_fst_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_cache_1155_);
lean_dec_ref(v_e_1154_);
v_val_1184_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v___x_1160_, 1);
v_fst_1185_ = lean_ctor_get(v_val_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_val_1184_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_val_1184_, 1);
lean_dec(v_unused_1193_);
v___x_1187_ = v_val_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_fst_1185_);
lean_dec(v_val_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v_s_1157_);
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_fst_1185_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_s_1157_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1194_, lean_object* v_cache_1195_, lean_object* v_ctx_1196_, lean_object* v_s_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1194_, v_cache_1195_, v_ctx_1196_, v_s_1197_);
lean_dec_ref(v_ctx_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1201_; uint64_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1201_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1202_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1199_);
v___x_1203_ = lean_uint64_to_usize(v___x_1202_);
v___x_1204_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1200_, v___x_1203_, v_e_1199_, v___x_1201_);
v___x_1205_ = lean_ptr_addr(v___x_1204_);
v___x_1206_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1207_ = lean_usize_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_dec_ref(v_e_1199_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1204_);
lean_ctor_set(v___x_1208_, 1, v_a_1200_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref(v___x_1204_);
v___x_1209_ = lean_box(0);
lean_inc_ref(v_e_1199_);
v___x_1210_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1200_, v_e_1199_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_e_1199_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1212_, v_a_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1216_, v_a_1217_, v_a_1218_);
lean_dec_ref(v_a_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1220_, lean_object* v_k_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___f_1224_; lean_object* v___x_1225_; uint64_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; uint8_t v___x_1231_; 
v___f_1224_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1225_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1226_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1220_);
v___x_1227_ = lean_uint64_to_usize(v___x_1226_);
lean_inc_ref(v_a_1223_);
v___x_1228_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1224_, v_a_1223_, v___x_1227_, v_e_1220_, v___x_1225_);
v___x_1229_ = lean_ptr_addr(v___x_1228_);
v___x_1230_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1231_ = lean_usize_dec_eq(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec_ref(v_k_1221_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1228_);
lean_ctor_set(v___x_1232_, 1, v_a_1223_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; 
lean_dec(v___x_1228_);
lean_inc_ref(v_a_1222_);
v___x_1233_ = lean_apply_2(v_k_1221_, v_a_1222_, v_a_1223_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
v_a_1235_ = lean_ctor_get(v___x_1233_, 1);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1233_, 2);
v___x_1236_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1234_, v_a_1235_);
return v___x_1236_;
}
else
{
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1237_, lean_object* v_k_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1237_, v_k_1238_, v_a_1239_, v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_unsigned_to_nat(16u);
v___x_1244_ = lean_mk_array(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v___x_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___y_1252_; lean_object* v___y_1257_; lean_object* v___y_1262_; lean_object* v___y_1267_; 
switch(lean_obj_tag(v_e_1248_))
{
case 4:
{
lean_object* v_declName_1271_; lean_object* v___x_1272_; uint64_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; uint8_t v___x_1278_; 
v_declName_1271_ = lean_ctor_get(v_e_1248_, 0);
v___x_1272_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1273_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1248_);
v___x_1274_ = lean_uint64_to_usize(v___x_1273_);
v___x_1275_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1250_, v___x_1274_, v_e_1248_, v___x_1272_);
v___x_1276_ = lean_ptr_addr(v___x_1275_);
v___x_1277_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1278_ = lean_usize_dec_eq(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec_ref_known(v_e_1248_, 2);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1275_);
lean_ctor_set(v___x_1279_, 1, v_a_1250_);
return v___x_1279_;
}
else
{
uint8_t v___x_1280_; 
lean_dec_ref(v___x_1275_);
lean_inc(v_declName_1271_);
lean_inc_ref(v_a_1249_);
v___x_1280_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1249_, v_declName_1271_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_box(0);
lean_inc_ref(v_e_1248_);
v___x_1282_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1250_, v_e_1248_, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_e_1248_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref_known(v_e_1248_, 2);
v___x_1284_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_a_1250_);
return v___x_1285_;
}
}
}
case 5:
{
lean_object* v_fn_1286_; lean_object* v_arg_1287_; lean_object* v___x_1288_; uint64_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; uint8_t v___x_1294_; 
v_fn_1286_ = lean_ctor_get(v_e_1248_, 0);
v_arg_1287_ = lean_ctor_get(v_e_1248_, 1);
v___x_1288_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1289_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1248_);
v___x_1290_ = lean_uint64_to_usize(v___x_1289_);
v___x_1291_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1250_, v___x_1290_, v_e_1248_, v___x_1288_);
v___x_1292_ = lean_ptr_addr(v___x_1291_);
v___x_1293_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1294_ = lean_usize_dec_eq(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
lean_dec_ref_known(v_e_1248_, 2);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1291_);
lean_ctor_set(v___x_1295_, 1, v_a_1250_);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; 
lean_dec_ref(v___x_1291_);
lean_inc_ref(v_fn_1286_);
v___x_1296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1286_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v_a_1298_; lean_object* v___x_1299_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
v_a_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1296_, 2);
lean_inc_ref(v_arg_1287_);
v___x_1299_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1287_, v_a_1249_, v_a_1298_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v_a_1301_; uint8_t v___y_1303_; size_t v___x_1307_; size_t v___x_1308_; uint8_t v___x_1309_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
v_a_1301_ = lean_ctor_get(v___x_1299_, 1);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1299_, 2);
v___x_1307_ = lean_ptr_addr(v_fn_1286_);
v___x_1308_ = lean_ptr_addr(v_a_1297_);
v___x_1309_ = lean_usize_dec_eq(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
v___y_1303_ = v___x_1309_;
goto v___jp_1302_;
}
else
{
size_t v___x_1310_; size_t v___x_1311_; uint8_t v___x_1312_; 
v___x_1310_ = lean_ptr_addr(v_arg_1287_);
v___x_1311_ = lean_ptr_addr(v_a_1300_);
v___x_1312_ = lean_usize_dec_eq(v___x_1310_, v___x_1311_);
v___y_1303_ = v___x_1312_;
goto v___jp_1302_;
}
v___jp_1302_:
{
if (v___y_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref_known(v_e_1248_, 2);
v___x_1304_ = l_Lean_Expr_app___override(v_a_1297_, v_a_1300_);
v___x_1305_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1304_, v_a_1301_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; 
lean_dec(v_a_1300_);
lean_dec(v_a_1297_);
v___x_1306_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1248_, v_a_1301_);
return v___x_1306_;
}
}
}
else
{
lean_dec(v_a_1297_);
lean_dec_ref_known(v_e_1248_, 2);
v___y_1262_ = v___x_1299_;
goto v___jp_1261_;
}
}
else
{
lean_dec_ref_known(v_e_1248_, 2);
v___y_1262_ = v___x_1296_;
goto v___jp_1261_;
}
}
}
case 6:
{
lean_object* v_binderName_1313_; lean_object* v_binderType_1314_; lean_object* v_body_1315_; uint8_t v_binderInfo_1316_; lean_object* v___x_1317_; uint64_t v___x_1318_; size_t v___x_1319_; lean_object* v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; uint8_t v___x_1323_; 
v_binderName_1313_ = lean_ctor_get(v_e_1248_, 0);
v_binderType_1314_ = lean_ctor_get(v_e_1248_, 1);
v_body_1315_ = lean_ctor_get(v_e_1248_, 2);
v_binderInfo_1316_ = lean_ctor_get_uint8(v_e_1248_, sizeof(void*)*3 + 8);
v___x_1317_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1318_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1248_);
v___x_1319_ = lean_uint64_to_usize(v___x_1318_);
v___x_1320_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1250_, v___x_1319_, v_e_1248_, v___x_1317_);
v___x_1321_ = lean_ptr_addr(v___x_1320_);
v___x_1322_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1323_ = lean_usize_dec_eq(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref_known(v_e_1248_, 3);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1320_);
lean_ctor_set(v___x_1324_, 1, v_a_1250_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v___x_1320_);
lean_inc_ref(v_binderType_1314_);
v___x_1325_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1314_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v_a_1327_; lean_object* v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
v_a_1327_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1325_, 2);
lean_inc_ref(v_body_1315_);
v___x_1328_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1315_, v_a_1249_, v_a_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_a_1330_; uint8_t v___y_1332_; size_t v___x_1339_; size_t v___x_1340_; uint8_t v___x_1341_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
v_a_1330_ = lean_ctor_get(v___x_1328_, 1);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1328_, 2);
v___x_1339_ = lean_ptr_addr(v_binderType_1314_);
v___x_1340_ = lean_ptr_addr(v_a_1326_);
v___x_1341_ = lean_usize_dec_eq(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
v___y_1332_ = v___x_1341_;
goto v___jp_1331_;
}
else
{
size_t v___x_1342_; size_t v___x_1343_; uint8_t v___x_1344_; 
v___x_1342_ = lean_ptr_addr(v_body_1315_);
v___x_1343_ = lean_ptr_addr(v_a_1329_);
v___x_1344_ = lean_usize_dec_eq(v___x_1342_, v___x_1343_);
v___y_1332_ = v___x_1344_;
goto v___jp_1331_;
}
v___jp_1331_:
{
if (v___y_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_inc(v_binderName_1313_);
lean_dec_ref_known(v_e_1248_, 3);
v___x_1333_ = l_Lean_Expr_lam___override(v_binderName_1313_, v_a_1326_, v_a_1329_, v_binderInfo_1316_);
v___x_1334_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1333_, v_a_1330_);
return v___x_1334_;
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1316_, v_binderInfo_1316_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_inc(v_binderName_1313_);
lean_dec_ref_known(v_e_1248_, 3);
v___x_1336_ = l_Lean_Expr_lam___override(v_binderName_1313_, v_a_1326_, v_a_1329_, v_binderInfo_1316_);
v___x_1337_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1336_, v_a_1330_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; 
lean_dec(v_a_1329_);
lean_dec(v_a_1326_);
v___x_1338_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1248_, v_a_1330_);
return v___x_1338_;
}
}
}
}
else
{
lean_dec(v_a_1326_);
lean_dec_ref_known(v_e_1248_, 3);
v___y_1257_ = v___x_1328_;
goto v___jp_1256_;
}
}
else
{
lean_dec_ref_known(v_e_1248_, 3);
v___y_1257_ = v___x_1325_;
goto v___jp_1256_;
}
}
}
case 7:
{
lean_object* v_binderName_1345_; lean_object* v_binderType_1346_; lean_object* v_body_1347_; uint8_t v_binderInfo_1348_; lean_object* v___x_1349_; uint64_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; uint8_t v___x_1355_; 
v_binderName_1345_ = lean_ctor_get(v_e_1248_, 0);
v_binderType_1346_ = lean_ctor_get(v_e_1248_, 1);
v_body_1347_ = lean_ctor_get(v_e_1248_, 2);
v_binderInfo_1348_ = lean_ctor_get_uint8(v_e_1248_, sizeof(void*)*3 + 8);
v___x_1349_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1350_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1248_);
v___x_1351_ = lean_uint64_to_usize(v___x_1350_);
v___x_1352_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1250_, v___x_1351_, v_e_1248_, v___x_1349_);
v___x_1353_ = lean_ptr_addr(v___x_1352_);
v___x_1354_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1355_ = lean_usize_dec_eq(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_dec_ref_known(v_e_1248_, 3);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1352_);
lean_ctor_set(v___x_1356_, 1, v_a_1250_);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; 
lean_dec_ref(v___x_1352_);
lean_inc_ref(v_binderType_1346_);
v___x_1357_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1346_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v_a_1359_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
v_a_1359_ = lean_ctor_get(v___x_1357_, 1);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1357_, 2);
lean_inc_ref(v_body_1347_);
v___x_1360_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1347_, v_a_1249_, v_a_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_a_1362_; uint8_t v___y_1364_; size_t v___x_1371_; size_t v___x_1372_; uint8_t v___x_1373_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
v_a_1362_ = lean_ctor_get(v___x_1360_, 1);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1360_, 2);
v___x_1371_ = lean_ptr_addr(v_binderType_1346_);
v___x_1372_ = lean_ptr_addr(v_a_1358_);
v___x_1373_ = lean_usize_dec_eq(v___x_1371_, v___x_1372_);
if (v___x_1373_ == 0)
{
v___y_1364_ = v___x_1373_;
goto v___jp_1363_;
}
else
{
size_t v___x_1374_; size_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_ptr_addr(v_body_1347_);
v___x_1375_ = lean_ptr_addr(v_a_1361_);
v___x_1376_ = lean_usize_dec_eq(v___x_1374_, v___x_1375_);
v___y_1364_ = v___x_1376_;
goto v___jp_1363_;
}
v___jp_1363_:
{
if (v___y_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc(v_binderName_1345_);
lean_dec_ref_known(v_e_1248_, 3);
v___x_1365_ = l_Lean_Expr_forallE___override(v_binderName_1345_, v_a_1358_, v_a_1361_, v_binderInfo_1348_);
v___x_1366_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1365_, v_a_1362_);
return v___x_1366_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1348_, v_binderInfo_1348_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_inc(v_binderName_1345_);
lean_dec_ref_known(v_e_1248_, 3);
v___x_1368_ = l_Lean_Expr_forallE___override(v_binderName_1345_, v_a_1358_, v_a_1361_, v_binderInfo_1348_);
v___x_1369_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1368_, v_a_1362_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; 
lean_dec(v_a_1361_);
lean_dec(v_a_1358_);
v___x_1370_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1248_, v_a_1362_);
return v___x_1370_;
}
}
}
}
else
{
lean_dec(v_a_1358_);
lean_dec_ref_known(v_e_1248_, 3);
v___y_1267_ = v___x_1360_;
goto v___jp_1266_;
}
}
else
{
lean_dec_ref_known(v_e_1248_, 3);
v___y_1267_ = v___x_1357_;
goto v___jp_1266_;
}
}
}
case 8:
{
lean_object* v_declName_1377_; lean_object* v_type_1378_; lean_object* v_value_1379_; lean_object* v_body_1380_; uint8_t v_nondep_1381_; lean_object* v___x_1382_; uint64_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; uint8_t v___x_1388_; 
v_declName_1377_ = lean_ctor_get(v_e_1248_, 0);
v_type_1378_ = lean_ctor_get(v_e_1248_, 1);
v_value_1379_ = lean_ctor_get(v_e_1248_, 2);
v_body_1380_ = lean_ctor_get(v_e_1248_, 3);
v_nondep_1381_ = lean_ctor_get_uint8(v_e_1248_, sizeof(void*)*4 + 8);
v___x_1382_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1383_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1248_);
v___x_1384_ = lean_uint64_to_usize(v___x_1383_);
v___x_1385_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1250_, v___x_1384_, v_e_1248_, v___x_1382_);
v___x_1386_ = lean_ptr_addr(v___x_1385_);
v___x_1387_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1388_ = lean_usize_dec_eq(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref_known(v_e_1248_, 4);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1385_);
lean_ctor_set(v___x_1389_, 1, v_a_1250_);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; 
lean_dec_ref(v___x_1385_);
lean_inc_ref(v_type_1378_);
v___x_1390_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1378_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
v_a_1392_ = lean_ctor_get(v___x_1390_, 1);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1390_, 2);
lean_inc_ref(v_value_1379_);
v___x_1393_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1379_, v_a_1249_, v_a_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_a_1395_; lean_object* v___x_1396_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
v_a_1395_ = lean_ctor_get(v___x_1393_, 1);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1393_, 2);
lean_inc_ref(v_body_1380_);
v___x_1396_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1380_, v_a_1249_, v_a_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v_a_1398_; uint8_t v___y_1400_; size_t v___x_1409_; size_t v___x_1410_; uint8_t v___x_1411_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
v_a_1398_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1396_, 2);
v___x_1409_ = lean_ptr_addr(v_type_1378_);
v___x_1410_ = lean_ptr_addr(v_a_1391_);
v___x_1411_ = lean_usize_dec_eq(v___x_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
v___y_1400_ = v___x_1411_;
goto v___jp_1399_;
}
else
{
size_t v___x_1412_; size_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = lean_ptr_addr(v_value_1379_);
v___x_1413_ = lean_ptr_addr(v_a_1394_);
v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
v___y_1400_ = v___x_1414_;
goto v___jp_1399_;
}
v___jp_1399_:
{
if (v___y_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_inc(v_declName_1377_);
lean_dec_ref_known(v_e_1248_, 4);
v___x_1401_ = l_Lean_Expr_letE___override(v_declName_1377_, v_a_1391_, v_a_1394_, v_a_1397_, v_nondep_1381_);
v___x_1402_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1401_, v_a_1398_);
return v___x_1402_;
}
else
{
size_t v___x_1403_; size_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_ptr_addr(v_body_1380_);
v___x_1404_ = lean_ptr_addr(v_a_1397_);
v___x_1405_ = lean_usize_dec_eq(v___x_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_inc(v_declName_1377_);
lean_dec_ref_known(v_e_1248_, 4);
v___x_1406_ = l_Lean_Expr_letE___override(v_declName_1377_, v_a_1391_, v_a_1394_, v_a_1397_, v_nondep_1381_);
v___x_1407_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1406_, v_a_1398_);
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; 
lean_dec(v_a_1397_);
lean_dec(v_a_1394_);
lean_dec(v_a_1391_);
v___x_1408_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1248_, v_a_1398_);
return v___x_1408_;
}
}
}
}
else
{
lean_dec(v_a_1394_);
lean_dec(v_a_1391_);
lean_dec_ref_known(v_e_1248_, 4);
v___y_1252_ = v___x_1396_;
goto v___jp_1251_;
}
}
else
{
lean_dec(v_a_1391_);
lean_dec_ref_known(v_e_1248_, 4);
v___y_1252_ = v___x_1393_;
goto v___jp_1251_;
}
}
else
{
lean_dec_ref_known(v_e_1248_, 4);
v___y_1252_ = v___x_1390_;
goto v___jp_1251_;
}
}
}
case 10:
{
lean_object* v_data_1415_; lean_object* v_expr_1416_; lean_object* v___x_1417_; uint64_t v___x_1418_; size_t v___x_1419_; lean_object* v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; uint8_t v___x_1423_; 
v_data_1415_ = lean_ctor_get(v_e_1248_, 0);
v_expr_1416_ = lean_ctor_get(v_e_1248_, 1);
v___x_1417_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1418_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1248_);
v___x_1419_ = lean_uint64_to_usize(v___x_1418_);
v___x_1420_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1250_, v___x_1419_, v_e_1248_, v___x_1417_);
v___x_1421_ = lean_ptr_addr(v___x_1420_);
v___x_1422_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1423_ = lean_usize_dec_eq(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref_known(v_e_1248_, 2);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1420_);
lean_ctor_set(v___x_1424_, 1, v_a_1250_);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; 
lean_dec_ref(v___x_1420_);
lean_inc_ref(v_expr_1416_);
v___x_1425_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1416_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v_a_1427_; size_t v___x_1428_; size_t v___x_1429_; uint8_t v___x_1430_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
v_a_1427_ = lean_ctor_get(v___x_1425_, 1);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1425_, 2);
v___x_1428_ = lean_ptr_addr(v_expr_1416_);
v___x_1429_ = lean_ptr_addr(v_a_1426_);
v___x_1430_ = lean_usize_dec_eq(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_inc(v_data_1415_);
lean_dec_ref_known(v_e_1248_, 2);
v___x_1431_ = l_Lean_Expr_mdata___override(v_data_1415_, v_a_1426_);
v___x_1432_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1431_, v_a_1427_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_dec(v_a_1426_);
v___x_1433_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1248_, v_a_1427_);
return v___x_1433_;
}
}
else
{
lean_dec_ref_known(v_e_1248_, 2);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1434_; lean_object* v_a_1435_; lean_object* v___x_1436_; 
v_a_1434_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1434_);
v_a_1435_ = lean_ctor_get(v___x_1425_, 1);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1425_, 2);
v___x_1436_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1434_, v_a_1435_);
return v___x_1436_;
}
else
{
return v___x_1425_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1437_; lean_object* v_idx_1438_; lean_object* v_struct_1439_; lean_object* v___x_1440_; uint64_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; uint8_t v___x_1446_; 
v_typeName_1437_ = lean_ctor_get(v_e_1248_, 0);
v_idx_1438_ = lean_ctor_get(v_e_1248_, 1);
v_struct_1439_ = lean_ctor_get(v_e_1248_, 2);
v___x_1440_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1441_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1248_);
v___x_1442_ = lean_uint64_to_usize(v___x_1441_);
v___x_1443_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1250_, v___x_1442_, v_e_1248_, v___x_1440_);
v___x_1444_ = lean_ptr_addr(v___x_1443_);
v___x_1445_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1446_ = lean_usize_dec_eq(v___x_1444_, v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref_known(v_e_1248_, 3);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1443_);
lean_ctor_set(v___x_1447_, 1, v_a_1250_);
return v___x_1447_;
}
else
{
uint8_t v_checkProj_1448_; 
lean_dec_ref(v___x_1443_);
v_checkProj_1448_ = lean_ctor_get_uint8(v_a_1249_, sizeof(void*)*1 + 1);
if (v_checkProj_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_inc_ref(v_struct_1439_);
v___x_1449_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1439_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v_a_1451_; size_t v___x_1452_; size_t v___x_1453_; uint8_t v___x_1454_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
v_a_1451_ = lean_ctor_get(v___x_1449_, 1);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1449_, 2);
v___x_1452_ = lean_ptr_addr(v_struct_1439_);
v___x_1453_ = lean_ptr_addr(v_a_1450_);
v___x_1454_ = lean_usize_dec_eq(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_inc(v_idx_1438_);
lean_inc(v_typeName_1437_);
lean_dec_ref_known(v_e_1248_, 3);
v___x_1455_ = l_Lean_Expr_proj___override(v_typeName_1437_, v_idx_1438_, v_a_1450_);
v___x_1456_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1455_, v_a_1451_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; 
lean_dec(v_a_1450_);
v___x_1457_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1248_, v_a_1451_);
return v___x_1457_;
}
}
else
{
lean_dec_ref_known(v_e_1248_, 3);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1458_; lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1458_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1458_);
v_a_1459_ = lean_ctor_get(v___x_1449_, 1);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1449_, 2);
v___x_1460_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1458_, v_a_1459_);
return v___x_1460_;
}
else
{
return v___x_1449_;
}
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref_known(v_e_1248_, 3);
v___x_1461_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v_a_1250_);
return v___x_1462_;
}
}
}
default: 
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1248_, v_a_1250_);
return v___x_1463_;
}
}
v___jp_1251_:
{
if (lean_obj_tag(v___y_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1253_ = lean_ctor_get(v___y_1252_, 0);
lean_inc(v_a_1253_);
v_a_1254_ = lean_ctor_get(v___y_1252_, 1);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___y_1252_, 2);
v___x_1255_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1253_, v_a_1254_);
return v___x_1255_;
}
else
{
return v___y_1252_;
}
}
v___jp_1256_:
{
if (lean_obj_tag(v___y_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1258_ = lean_ctor_get(v___y_1257_, 0);
lean_inc(v_a_1258_);
v_a_1259_ = lean_ctor_get(v___y_1257_, 1);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___y_1257_, 2);
v___x_1260_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1258_, v_a_1259_);
return v___x_1260_;
}
else
{
return v___y_1257_;
}
}
v___jp_1261_:
{
if (lean_obj_tag(v___y_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1263_ = lean_ctor_get(v___y_1262_, 0);
lean_inc(v_a_1263_);
v_a_1264_ = lean_ctor_get(v___y_1262_, 1);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___y_1262_, 2);
v___x_1265_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1263_, v_a_1264_);
return v___x_1265_;
}
else
{
return v___y_1262_;
}
}
v___jp_1266_:
{
if (lean_obj_tag(v___y_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v_a_1269_; lean_object* v___x_1270_; 
v_a_1268_ = lean_ctor_get(v___y_1267_, 0);
lean_inc(v_a_1268_);
v_a_1269_ = lean_ctor_get(v___y_1267_, 1);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___y_1267_, 2);
v___x_1270_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1268_, v_a_1269_);
return v___x_1270_;
}
else
{
return v___y_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1464_, v_a_1465_, v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1468_, v_a_1469_, v_a_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1472_, v_a_1473_, v_a_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1475_;
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

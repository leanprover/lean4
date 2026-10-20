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
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Sym_isGrindGadget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l_Lean_Meta_Sym_isGrindGadget___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_isGrindGadget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_isGrindGadget___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
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
lean_object* v_typeName_131_; lean_object* v_idx_132_; lean_object* v_struct_133_; lean_object* v_typeName_134_; lean_object* v_idx_135_; lean_object* v_struct_136_; uint8_t v___x_137_; 
v_typeName_131_ = lean_ctor_get(v_e_u2081_73_, 0);
v_idx_132_ = lean_ctor_get(v_e_u2081_73_, 1);
v_struct_133_ = lean_ctor_get(v_e_u2081_73_, 2);
v_typeName_134_ = lean_ctor_get(v_e_u2082_74_, 0);
v_idx_135_ = lean_ctor_get(v_e_u2082_74_, 1);
v_struct_136_ = lean_ctor_get(v_e_u2082_74_, 2);
v___x_137_ = lean_name_eq(v_typeName_131_, v_typeName_134_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_eq(v_idx_132_, v_idx_135_);
if (v___x_138_ == 0)
{
return v___x_138_;
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
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
default: 
{
uint8_t v___x_143_; 
v___x_143_ = lean_expr_eqv(v_e_u2081_73_, v_e_u2082_74_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object* v_e_u2081_144_, lean_object* v_e_u2082_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_e_u2081_144_, v_e_u2082_145_);
lean_dec_ref(v_e_u2082_145_);
lean_dec_ref(v_e_u2081_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_167_ = lean_name_eq(v_declName_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__5));
v___x_169_ = lean_name_eq(v_declName_165_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__7));
v___x_171_ = lean_name_eq(v_declName_165_, v___x_170_);
return v___x_171_;
}
else
{
return v___x_169_;
}
}
else
{
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_172_);
lean_dec(v_declName_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object* v_env_175_, lean_object* v_declName_176_){
_start:
{
uint8_t v___x_177_; 
lean_inc(v_declName_176_);
lean_inc_ref(v_env_175_);
v___x_177_ = l_Lean_getReducibilityStatusCore(v_env_175_, v_declName_176_);
if (v___x_177_ == 0)
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_176_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; 
v___x_179_ = l_Lean_Environment_isProjectionFn(v_env_175_, v_declName_176_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 1;
return v___x_180_;
}
else
{
return v___x_178_;
}
}
else
{
uint8_t v___x_181_; 
lean_dec(v_declName_176_);
lean_dec_ref(v_env_175_);
v___x_181_ = 0;
return v___x_181_;
}
}
else
{
uint8_t v___x_182_; 
lean_dec(v_declName_176_);
lean_dec_ref(v_env_175_);
v___x_182_ = 0;
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object* v_env_183_, lean_object* v_declName_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_183_, v_declName_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_187_){
_start:
{
uint64_t v___x_188_; 
v___x_188_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_189_){
_start:
{
uint64_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_189_);
lean_dec_ref(v_k_189_);
v_r_191_ = lean_box_uint64(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_194_, lean_object* v_k_u2082_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_194_, v_k_u2082_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_197_, lean_object* v_k_u2082_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_197_, v_k_u2082_198_);
lean_dec_ref(v_k_u2082_198_);
lean_dec_ref(v_k_u2081_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object* v_ctx_203_, lean_object* v_declName_204_){
_start:
{
uint8_t v_checkReducible_205_; 
v_checkReducible_205_ = lean_ctor_get_uint8(v_ctx_203_, sizeof(void*)*1);
if (v_checkReducible_205_ == 0)
{
lean_dec(v_declName_204_);
lean_dec_ref(v_ctx_203_);
return v_checkReducible_205_;
}
else
{
lean_object* v_env_206_; uint8_t v___x_207_; 
v_env_206_ = lean_ctor_get(v_ctx_203_, 0);
lean_inc_ref(v_env_206_);
lean_dec_ref(v_ctx_203_);
v___x_207_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_206_, v_declName_204_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object* v_ctx_208_, lean_object* v_declName_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_208_, v_declName_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_box(0);
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_217_ = l_Lean_mkConst(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_219_, lean_object* v_i_220_, lean_object* v_k_221_, lean_object* v_k_u2080_222_){
_start:
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = lean_array_get_size(v_keys_219_);
v___x_224_ = lean_nat_dec_lt(v_i_220_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec(v_i_220_);
lean_inc_ref(v_k_u2080_222_);
return v_k_u2080_222_;
}
else
{
lean_object* v_k_x27_225_; uint8_t v___x_226_; 
v_k_x27_225_ = lean_array_fget_borrowed(v_keys_219_, v_i_220_);
v___x_226_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_221_, v_k_x27_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_i_220_, v___x_227_);
lean_dec(v_i_220_);
v_i_220_ = v___x_228_;
goto _start;
}
else
{
lean_dec(v_i_220_);
lean_inc(v_k_x27_225_);
return v_k_x27_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_230_, lean_object* v_i_231_, lean_object* v_k_232_, lean_object* v_k_u2080_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_230_, v_i_231_, v_k_232_, v_k_u2080_233_);
lean_dec_ref(v_k_u2080_233_);
lean_dec_ref(v_k_232_);
lean_dec_ref(v_keys_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_235_, size_t v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v_es_239_; lean_object* v___x_240_; size_t v___x_241_; size_t v___x_242_; lean_object* v_j_243_; lean_object* v___x_244_; 
v_es_239_ = lean_ctor_get(v_x_235_, 0);
v___x_240_ = lean_box(2);
v___x_241_ = ((size_t)31ULL);
v___x_242_ = lean_usize_land(v_x_236_, v___x_241_);
v_j_243_ = lean_usize_to_nat(v___x_242_);
v___x_244_ = lean_array_get_borrowed(v___x_240_, v_es_239_, v_j_243_);
lean_dec(v_j_243_);
switch(lean_obj_tag(v___x_244_))
{
case 0:
{
lean_object* v_key_245_; uint8_t v___x_246_; 
v_key_245_ = lean_ctor_get(v___x_244_, 0);
v___x_246_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_237_, v_key_245_);
if (v___x_246_ == 0)
{
lean_inc_ref(v_x_238_);
return v_x_238_;
}
else
{
lean_inc(v_key_245_);
return v_key_245_;
}
}
case 1:
{
lean_object* v_node_247_; size_t v___x_248_; size_t v___x_249_; 
v_node_247_ = lean_ctor_get(v___x_244_, 0);
v___x_248_ = ((size_t)5ULL);
v___x_249_ = lean_usize_shift_right(v_x_236_, v___x_248_);
v_x_235_ = v_node_247_;
v_x_236_ = v___x_249_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_238_);
return v_x_238_;
}
}
}
else
{
lean_object* v_ks_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_ks_251_ = lean_ctor_get(v_x_235_, 0);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_251_, v___x_252_, v_x_237_, v_x_238_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
size_t v_x_1948__boxed_258_; lean_object* v_res_259_; 
v_x_1948__boxed_258_ = lean_unbox_usize(v_x_255_);
lean_dec(v_x_255_);
v_res_259_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_254_, v_x_1948__boxed_258_, v_x_256_, v_x_257_);
lean_dec_ref(v_x_257_);
lean_dec_ref(v_x_256_);
lean_dec_ref(v_x_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_ks_264_; lean_object* v_vs_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_289_; 
v_ks_264_ = lean_ctor_get(v_x_260_, 0);
v_vs_265_ = lean_ctor_get(v_x_260_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_289_ == 0)
{
v___x_267_ = v_x_260_;
v_isShared_268_ = v_isSharedCheck_289_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_vs_265_);
lean_inc(v_ks_264_);
lean_dec(v_x_260_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_289_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_array_get_size(v_ks_264_);
v___x_270_ = lean_nat_dec_lt(v_x_261_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
lean_dec(v_x_261_);
v___x_271_ = lean_array_push(v_ks_264_, v_x_262_);
v___x_272_ = lean_array_push(v_vs_265_, v_x_263_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_272_);
lean_ctor_set(v___x_267_, 0, v___x_271_);
v___x_274_ = v___x_267_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_object* v_k_x27_276_; uint8_t v___x_277_; 
v_k_x27_276_ = lean_array_fget_borrowed(v_ks_264_, v_x_261_);
v___x_277_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_262_, v_k_x27_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_279_; 
if (v_isShared_268_ == 0)
{
v___x_279_ = v___x_267_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_ks_264_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_vs_265_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_x_261_, v___x_280_);
lean_dec(v_x_261_);
v_x_260_ = v___x_279_;
v_x_261_ = v___x_281_;
goto _start;
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_284_ = lean_array_fset(v_ks_264_, v_x_261_, v_x_262_);
v___x_285_ = lean_array_fset(v_vs_265_, v_x_261_, v_x_263_);
lean_dec(v_x_261_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_285_);
lean_ctor_set(v___x_267_, 0, v___x_284_);
v___x_287_ = v___x_267_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_290_, lean_object* v_k_291_, lean_object* v_v_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_290_, v___x_293_, v_k_291_, v_v_292_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_296_, size_t v_x_297_, size_t v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
lean_object* v_es_301_; size_t v___x_302_; size_t v___x_303_; lean_object* v_j_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_es_301_ = lean_ctor_get(v_x_296_, 0);
v___x_302_ = ((size_t)31ULL);
v___x_303_ = lean_usize_land(v_x_297_, v___x_302_);
v_j_304_ = lean_usize_to_nat(v___x_303_);
v___x_305_ = lean_array_get_size(v_es_301_);
v___x_306_ = lean_nat_dec_lt(v_j_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v_j_304_);
lean_dec(v_x_300_);
lean_dec_ref(v_x_299_);
return v_x_296_;
}
else
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_345_; 
lean_inc_ref(v_es_301_);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_296_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_x_296_, 0);
lean_dec(v_unused_346_);
v___x_308_ = v_x_296_;
v_isShared_309_ = v_isSharedCheck_345_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_x_296_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_345_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_v_310_; lean_object* v___x_311_; lean_object* v_xs_x27_312_; lean_object* v___y_314_; 
v_v_310_ = lean_array_fget(v_es_301_, v_j_304_);
v___x_311_ = lean_box(0);
v_xs_x27_312_ = lean_array_fset(v_es_301_, v_j_304_, v___x_311_);
switch(lean_obj_tag(v_v_310_))
{
case 0:
{
lean_object* v_key_319_; lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_330_; 
v_key_319_ = lean_ctor_get(v_v_310_, 0);
v_val_320_ = lean_ctor_get(v_v_310_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_v_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_322_ = v_v_310_;
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_inc(v_key_319_);
lean_dec(v_v_310_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
uint8_t v___x_324_; 
v___x_324_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_299_, v_key_319_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_del_object(v___x_322_);
v___x_325_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_319_, v_val_320_, v_x_299_, v_x_300_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
else
{
lean_object* v___x_328_; 
lean_dec(v_val_320_);
lean_dec(v_key_319_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v_x_300_);
lean_ctor_set(v___x_322_, 0, v_x_299_);
v___x_328_ = v___x_322_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_x_299_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_x_300_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v___y_314_ = v___x_328_;
goto v___jp_313_;
}
}
}
}
case 1:
{
lean_object* v_node_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_343_; 
v_node_331_ = lean_ctor_get(v_v_310_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_v_310_);
if (v_isSharedCheck_343_ == 0)
{
v___x_333_ = v_v_310_;
v_isShared_334_ = v_isSharedCheck_343_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_node_331_);
lean_dec(v_v_310_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_343_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_335_ = ((size_t)5ULL);
v___x_336_ = lean_usize_shift_right(v_x_297_, v___x_335_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_x_298_, v___x_337_);
v___x_339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_331_, v___x_336_, v___x_338_, v_x_299_, v_x_300_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_339_);
v___x_341_ = v___x_333_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
v___y_314_ = v___x_341_;
goto v___jp_313_;
}
}
}
default: 
{
lean_object* v___x_344_; 
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_x_299_);
lean_ctor_set(v___x_344_, 1, v_x_300_);
v___y_314_ = v___x_344_;
goto v___jp_313_;
}
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_array_fset(v_xs_x27_312_, v_j_304_, v___y_314_);
lean_dec(v_j_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_315_);
v___x_317_ = v___x_308_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v_ks_347_; lean_object* v_vs_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_366_; 
v_ks_347_ = lean_ctor_get(v_x_296_, 0);
v_vs_348_ = lean_ctor_get(v_x_296_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_296_);
if (v_isSharedCheck_366_ == 0)
{
v___x_350_ = v_x_296_;
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_vs_348_);
lean_inc(v_ks_347_);
lean_dec(v_x_296_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_ks_347_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_vs_348_);
v___x_353_ = v_reuseFailAlloc_365_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v_newNode_354_; size_t v___x_355_; uint8_t v___x_356_; 
v_newNode_354_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_353_, v_x_299_, v_x_300_);
v___x_355_ = ((size_t)7ULL);
v___x_356_ = lean_usize_dec_le(v___x_355_, v_x_298_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_357_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_354_);
v___x_358_ = lean_unsigned_to_nat(4u);
v___x_359_ = lean_nat_dec_lt(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
if (v___x_359_ == 0)
{
lean_object* v_ks_360_; lean_object* v_vs_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_ks_360_ = lean_ctor_get(v_newNode_354_, 0);
lean_inc_ref(v_ks_360_);
v_vs_361_ = lean_ctor_get(v_newNode_354_, 1);
lean_inc_ref(v_vs_361_);
lean_dec_ref(v_newNode_354_);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_298_, v_ks_360_, v_vs_361_, v___x_362_, v___x_363_);
lean_dec_ref(v_vs_361_);
lean_dec_ref(v_ks_360_);
return v___x_364_;
}
else
{
return v_newNode_354_;
}
}
else
{
return v_newNode_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_i_370_, lean_object* v_entries_371_){
_start:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_array_get_size(v_keys_368_);
v___x_373_ = lean_nat_dec_lt(v_i_370_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec(v_i_370_);
return v_entries_371_;
}
else
{
lean_object* v_k_374_; lean_object* v_v_375_; uint64_t v___x_376_; size_t v_h_377_; size_t v___x_378_; lean_object* v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v_h_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_k_374_ = lean_array_fget_borrowed(v_keys_368_, v_i_370_);
v_v_375_ = lean_array_fget_borrowed(v_vals_369_, v_i_370_);
v___x_376_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_374_);
v_h_377_ = lean_uint64_to_usize(v___x_376_);
v___x_378_ = ((size_t)5ULL);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v_depth_367_, v___x_380_);
v___x_382_ = lean_usize_mul(v___x_378_, v___x_381_);
v_h_383_ = lean_usize_shift_right(v_h_377_, v___x_382_);
v___x_384_ = lean_nat_add(v_i_370_, v___x_379_);
lean_dec(v_i_370_);
lean_inc(v_v_375_);
lean_inc(v_k_374_);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_371_, v_h_383_, v_depth_367_, v_k_374_, v_v_375_);
v_i_370_ = v___x_384_;
v_entries_371_ = v___x_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_i_390_, lean_object* v_entries_391_){
_start:
{
size_t v_depth_boxed_392_; lean_object* v_res_393_; 
v_depth_boxed_392_ = lean_unbox_usize(v_depth_387_);
lean_dec(v_depth_387_);
v_res_393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_392_, v_keys_388_, v_vals_389_, v_i_390_, v_entries_391_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
size_t v_x_2066__boxed_399_; size_t v_x_2067__boxed_400_; lean_object* v_res_401_; 
v_x_2066__boxed_399_ = lean_unbox_usize(v_x_395_);
lean_dec(v_x_395_);
v_x_2067__boxed_400_ = lean_unbox_usize(v_x_396_);
lean_dec(v_x_396_);
v_res_401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_394_, v_x_2066__boxed_399_, v_x_2067__boxed_400_, v_x_397_, v_x_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_405_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_403_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_402_, v___x_406_, v___x_407_, v_x_403_, v_x_404_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_409_, lean_object* v_b_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_dec(v_b_410_);
lean_dec_ref(v_a_409_);
return v_x_411_;
}
else
{
lean_object* v_key_412_; lean_object* v_value_413_; lean_object* v_tail_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_428_; 
v_key_412_ = lean_ctor_get(v_x_411_, 0);
v_value_413_ = lean_ctor_get(v_x_411_, 1);
v_tail_414_ = lean_ctor_get(v_x_411_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_411_);
if (v_isSharedCheck_428_ == 0)
{
v___x_416_ = v_x_411_;
v_isShared_417_ = v_isSharedCheck_428_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_tail_414_);
lean_inc(v_value_413_);
lean_inc(v_key_412_);
lean_dec(v_x_411_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_428_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
size_t v___x_418_; size_t v___x_419_; uint8_t v___x_420_; 
v___x_418_ = lean_ptr_addr(v_key_412_);
v___x_419_ = lean_ptr_addr(v_a_409_);
v___x_420_ = lean_usize_dec_eq(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_409_, v_b_410_, v_tail_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 2, v___x_421_);
v___x_423_ = v___x_416_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_key_412_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_value_413_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_object* v___x_426_; 
lean_dec(v_value_413_);
lean_dec(v_key_412_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_b_410_);
lean_ctor_set(v___x_416_, 0, v_a_409_);
v___x_426_ = v___x_416_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_409_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_b_410_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_tail_414_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
return v_x_429_;
}
else
{
lean_object* v_key_431_; lean_object* v_value_432_; lean_object* v_tail_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_459_; 
v_key_431_ = lean_ctor_get(v_x_430_, 0);
v_value_432_ = lean_ctor_get(v_x_430_, 1);
v_tail_433_ = lean_ctor_get(v_x_430_, 2);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_459_ == 0)
{
v___x_435_ = v_x_430_;
v_isShared_436_ = v_isSharedCheck_459_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_tail_433_);
lean_inc(v_value_432_);
lean_inc(v_key_431_);
lean_dec(v_x_430_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_459_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; uint64_t v_fold_444_; uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_437_ = lean_array_get_size(v_x_429_);
v___x_438_ = lean_ptr_addr(v_key_431_);
v___x_439_ = ((size_t)3ULL);
v___x_440_ = lean_usize_shift_right(v___x_438_, v___x_439_);
v___x_441_ = lean_usize_to_uint64(v___x_440_);
v___x_442_ = 32ULL;
v___x_443_ = lean_uint64_shift_right(v___x_441_, v___x_442_);
v_fold_444_ = lean_uint64_xor(v___x_441_, v___x_443_);
v___x_445_ = 16ULL;
v___x_446_ = lean_uint64_shift_right(v_fold_444_, v___x_445_);
v___x_447_ = lean_uint64_xor(v_fold_444_, v___x_446_);
v___x_448_ = lean_uint64_to_usize(v___x_447_);
v___x_449_ = lean_usize_of_nat(v___x_437_);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_sub(v___x_449_, v___x_450_);
v___x_452_ = lean_usize_land(v___x_448_, v___x_451_);
v___x_453_ = lean_array_uget_borrowed(v_x_429_, v___x_452_);
lean_inc(v___x_453_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 2, v___x_453_);
v___x_455_ = v___x_435_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_key_431_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_value_432_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v___x_453_);
v___x_455_ = v_reuseFailAlloc_458_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; 
v___x_456_ = lean_array_uset(v_x_429_, v___x_452_, v___x_455_);
v_x_429_ = v___x_456_;
v_x_430_ = v_tail_433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_460_, lean_object* v_source_461_, lean_object* v_target_462_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_array_get_size(v_source_461_);
v___x_464_ = lean_nat_dec_lt(v_i_460_, v___x_463_);
if (v___x_464_ == 0)
{
lean_dec_ref(v_source_461_);
lean_dec(v_i_460_);
return v_target_462_;
}
else
{
lean_object* v_es_465_; lean_object* v___x_466_; lean_object* v_source_467_; lean_object* v_target_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_es_465_ = lean_array_fget(v_source_461_, v_i_460_);
v___x_466_ = lean_box(0);
v_source_467_ = lean_array_fset(v_source_461_, v_i_460_, v___x_466_);
v_target_468_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_462_, v_es_465_);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_i_460_, v___x_469_);
lean_dec(v_i_460_);
v_i_460_ = v___x_470_;
v_source_461_ = v_source_467_;
v_target_462_ = v_target_468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_nbuckets_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_473_ = lean_array_get_size(v_data_472_);
v___x_474_ = lean_unsigned_to_nat(2u);
v_nbuckets_475_ = lean_nat_mul(v___x_473_, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_box(0);
v___x_478_ = lean_mk_array(v_nbuckets_475_, v___x_477_);
v___x_479_ = lean_array_propagate_mark(v_data_472_, v___x_478_);
v___x_480_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_476_, v_data_472_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
else
{
lean_object* v_key_484_; lean_object* v_tail_485_; size_t v___x_486_; size_t v___x_487_; uint8_t v___x_488_; 
v_key_484_ = lean_ctor_get(v_x_482_, 0);
v_tail_485_ = lean_ctor_get(v_x_482_, 2);
v___x_486_ = lean_ptr_addr(v_key_484_);
v___x_487_ = lean_ptr_addr(v_a_481_);
v___x_488_ = lean_usize_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
v_x_482_ = v_tail_485_;
goto _start;
}
else
{
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_490_, lean_object* v_x_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_490_, v_x_491_);
lean_dec(v_x_491_);
lean_dec_ref(v_a_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_494_, lean_object* v_a_495_, lean_object* v_b_496_){
_start:
{
lean_object* v_size_497_; lean_object* v_buckets_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_544_; 
v_size_497_ = lean_ctor_get(v_m_494_, 0);
v_buckets_498_ = lean_ctor_get(v_m_494_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_m_494_);
if (v_isSharedCheck_544_ == 0)
{
v___x_500_ = v_m_494_;
v_isShared_501_ = v_isSharedCheck_544_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_buckets_498_);
lean_inc(v_size_497_);
lean_dec(v_m_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_544_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; uint64_t v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v_fold_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v_bkt_518_; uint8_t v___x_519_; 
v___x_502_ = lean_array_get_size(v_buckets_498_);
v___x_503_ = lean_ptr_addr(v_a_495_);
v___x_504_ = ((size_t)3ULL);
v___x_505_ = lean_usize_shift_right(v___x_503_, v___x_504_);
v___x_506_ = lean_usize_to_uint64(v___x_505_);
v___x_507_ = 32ULL;
v___x_508_ = lean_uint64_shift_right(v___x_506_, v___x_507_);
v_fold_509_ = lean_uint64_xor(v___x_506_, v___x_508_);
v___x_510_ = 16ULL;
v___x_511_ = lean_uint64_shift_right(v_fold_509_, v___x_510_);
v___x_512_ = lean_uint64_xor(v_fold_509_, v___x_511_);
v___x_513_ = lean_uint64_to_usize(v___x_512_);
v___x_514_ = lean_usize_of_nat(v___x_502_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_sub(v___x_514_, v___x_515_);
v___x_517_ = lean_usize_land(v___x_513_, v___x_516_);
v_bkt_518_ = lean_array_uget_borrowed(v_buckets_498_, v___x_517_);
v___x_519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_495_, v_bkt_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v_size_x27_521_; lean_object* v___x_522_; lean_object* v_buckets_x27_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v_size_x27_521_ = lean_nat_add(v_size_497_, v___x_520_);
lean_dec(v_size_497_);
lean_inc(v_bkt_518_);
v___x_522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_522_, 0, v_a_495_);
lean_ctor_set(v___x_522_, 1, v_b_496_);
lean_ctor_set(v___x_522_, 2, v_bkt_518_);
v_buckets_x27_523_ = lean_array_uset(v_buckets_498_, v___x_517_, v___x_522_);
v___x_524_ = lean_unsigned_to_nat(4u);
v___x_525_ = lean_nat_mul(v_size_x27_521_, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(3u);
v___x_527_ = lean_nat_div(v___x_525_, v___x_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_array_get_size(v_buckets_x27_523_);
v___x_529_ = lean_nat_dec_le(v___x_527_, v___x_528_);
lean_dec(v___x_527_);
if (v___x_529_ == 0)
{
lean_object* v_val_530_; lean_object* v___x_532_; 
v_val_530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_523_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v_val_530_);
lean_ctor_set(v___x_500_, 0, v_size_x27_521_);
v___x_532_ = v___x_500_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_size_x27_521_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_val_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v___x_535_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v_buckets_x27_523_);
lean_ctor_set(v___x_500_, 0, v_size_x27_521_);
v___x_535_ = v___x_500_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_size_x27_521_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_buckets_x27_523_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v___x_537_; lean_object* v_buckets_x27_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_inc(v_bkt_518_);
v___x_537_ = lean_box(0);
v_buckets_x27_538_ = lean_array_uset(v_buckets_498_, v___x_517_, v___x_537_);
v___x_539_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_495_, v_b_496_, v_bkt_518_);
v___x_540_ = lean_array_uset(v_buckets_x27_538_, v___x_517_, v___x_539_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_540_);
v___x_542_ = v___x_500_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_size_497_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_545_; size_t v___x_546_; 
v___x_545_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_546_ = lean_ptr_addr(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_547_, lean_object* v_r_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_map_550_; lean_object* v_set_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_575_; 
v_map_550_ = lean_ctor_get(v_a_549_, 0);
v_set_551_ = lean_ctor_get(v_a_549_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_575_ == 0)
{
v___x_553_ = v_a_549_;
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_set_551_);
lean_inc(v_map_550_);
lean_dec(v_a_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; uint64_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; size_t v___x_559_; size_t v___x_560_; uint8_t v___x_561_; 
v___x_555_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_556_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_548_);
v___x_557_ = lean_uint64_to_usize(v___x_556_);
v___x_558_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_551_, v___x_557_, v_r_548_, v___x_555_);
v___x_559_ = lean_ptr_addr(v___x_558_);
v___x_560_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_561_ = lean_usize_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec_ref(v_r_548_);
lean_inc_ref(v___x_558_);
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_550_, v_e_547_, v___x_558_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_562_);
v___x_564_ = v___x_553_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_set_551_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_558_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_dec_ref(v___x_558_);
lean_inc_ref_n(v_r_548_, 4);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_550_, v_e_547_, v_r_548_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_567_, v_r_548_, v_r_548_);
v___x_569_ = lean_box(0);
v___x_570_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_551_, v_r_548_, v___x_569_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_570_);
lean_ctor_set(v___x_553_, 0, v___x_568_);
v___x_572_ = v___x_553_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_574_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; 
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_r_548_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_576_, lean_object* v_r_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_576_, v_r_577_, v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_581_, lean_object* v_r_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_581_, v_r_582_, v_a_583_, v_a_584_);
lean_dec_ref(v_a_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_586_, lean_object* v_x_587_, size_t v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_587_, v_x_588_, v_x_589_, v_x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_592_, lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
size_t v_x_2519__boxed_597_; lean_object* v_res_598_; 
v_x_2519__boxed_597_ = lean_unbox_usize(v_x_594_);
lean_dec(v_x_594_);
v_res_598_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_592_, v_x_593_, v_x_2519__boxed_597_, v_x_595_, v_x_596_);
lean_dec_ref(v_x_596_);
lean_dec_ref(v_x_595_);
lean_dec_ref(v_x_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_599_, lean_object* v_m_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_600_, v_a_601_, v_b_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_605_, v_x_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_609_, lean_object* v_keys_610_, lean_object* v_vals_611_, lean_object* v_heq_612_, lean_object* v_i_613_, lean_object* v_k_614_, lean_object* v_k_u2080_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_610_, v_i_613_, v_k_614_, v_k_u2080_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_heq_620_, lean_object* v_i_621_, lean_object* v_k_622_, lean_object* v_k_u2080_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_617_, v_keys_618_, v_vals_619_, v_heq_620_, v_i_621_, v_k_622_, v_k_u2080_623_);
lean_dec_ref(v_k_u2080_623_);
lean_dec_ref(v_k_622_);
lean_dec_ref(v_vals_619_);
lean_dec_ref(v_keys_618_);
return v_res_624_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_625_, lean_object* v_a_626_, lean_object* v_x_627_){
_start:
{
uint8_t v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_629_, lean_object* v_a_630_, lean_object* v_x_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_629_, v_a_630_, v_x_631_);
lean_dec(v_x_631_);
lean_dec_ref(v_a_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_634_, lean_object* v_data_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_637_, lean_object* v_a_638_, lean_object* v_b_639_, lean_object* v_x_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_638_, v_b_639_, v_x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_642_, lean_object* v_x_643_, size_t v_x_644_, size_t v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_643_, v_x_644_, v_x_645_, v_x_646_, v_x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
size_t v_x_2556__boxed_655_; size_t v_x_2557__boxed_656_; lean_object* v_res_657_; 
v_x_2556__boxed_655_ = lean_unbox_usize(v_x_651_);
lean_dec(v_x_651_);
v_x_2557__boxed_656_ = lean_unbox_usize(v_x_652_);
lean_dec(v_x_652_);
v_res_657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_649_, v_x_650_, v_x_2556__boxed_655_, v_x_2557__boxed_656_, v_x_653_, v_x_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_658_, lean_object* v_i_659_, lean_object* v_source_660_, lean_object* v_target_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_659_, v_source_660_, v_target_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_663_, lean_object* v_n_664_, lean_object* v_k_665_, lean_object* v_v_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_664_, v_k_665_, v_v_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_668_, size_t v_depth_669_, lean_object* v_keys_670_, lean_object* v_vals_671_, lean_object* v_heq_672_, lean_object* v_i_673_, lean_object* v_entries_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_669_, v_keys_670_, v_vals_671_, v_i_673_, v_entries_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_676_, lean_object* v_depth_677_, lean_object* v_keys_678_, lean_object* v_vals_679_, lean_object* v_heq_680_, lean_object* v_i_681_, lean_object* v_entries_682_){
_start:
{
size_t v_depth_boxed_683_; lean_object* v_res_684_; 
v_depth_boxed_683_ = lean_unbox_usize(v_depth_677_);
lean_dec(v_depth_677_);
v_res_684_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_676_, v_depth_boxed_683_, v_keys_678_, v_vals_679_, v_heq_680_, v_i_681_, v_entries_682_);
lean_dec_ref(v_vals_679_);
lean_dec_ref(v_keys_678_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_690_, v_x_691_, v_x_692_, v_x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_697_, lean_object* v_k_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_map_701_; lean_object* v_set_702_; lean_object* v___f_703_; lean_object* v___f_704_; lean_object* v___x_705_; 
v_map_701_ = lean_ctor_get(v_a_700_, 0);
v_set_702_ = lean_ctor_get(v_a_700_, 1);
v___f_703_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_704_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_697_);
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_703_, v___f_704_, v_map_701_, v_e_697_);
if (lean_obj_tag(v___x_705_) == 1)
{
lean_object* v_val_706_; lean_object* v___x_707_; 
lean_dec_ref(v_k_698_);
lean_dec_ref(v_e_697_);
v_val_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_val_706_);
lean_ctor_set(v___x_707_, 1, v_a_700_);
return v___x_707_;
}
else
{
lean_object* v___f_708_; lean_object* v___x_709_; uint64_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; size_t v___x_713_; size_t v___x_714_; uint8_t v___x_715_; 
lean_dec(v___x_705_);
v___f_708_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_709_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_710_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_697_);
v___x_711_ = lean_uint64_to_usize(v___x_710_);
lean_inc_ref(v_e_697_);
lean_inc_ref(v_set_702_);
v___x_712_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_708_, v_set_702_, v___x_711_, v_e_697_, v___x_709_);
v___x_713_ = lean_ptr_addr(v___x_712_);
v___x_714_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_715_ = lean_usize_dec_eq(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_k_698_);
lean_dec_ref(v_e_697_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_712_);
lean_ctor_set(v___x_716_, 1, v_a_700_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; 
lean_dec(v___x_712_);
lean_inc_ref(v_a_699_);
v___x_717_ = lean_apply_2(v_k_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
v_a_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_717_, 2);
v___x_720_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_697_, v_a_718_, v_a_719_);
return v___x_720_;
}
else
{
lean_dec_ref(v_e_697_);
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_721_, lean_object* v_k_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_721_, v_k_722_, v_a_723_, v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
lean_object* v___x_728_; 
v___x_728_ = lean_box(0);
return v___x_728_;
}
else
{
lean_object* v_key_729_; lean_object* v_value_730_; lean_object* v_tail_731_; size_t v___x_732_; size_t v___x_733_; uint8_t v___x_734_; 
v_key_729_ = lean_ctor_get(v_x_727_, 0);
v_value_730_ = lean_ctor_get(v_x_727_, 1);
v_tail_731_ = lean_ctor_get(v_x_727_, 2);
v___x_732_ = lean_ptr_addr(v_key_729_);
v___x_733_ = lean_ptr_addr(v_a_726_);
v___x_734_ = lean_usize_dec_eq(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
v_x_727_ = v_tail_731_;
goto _start;
}
else
{
lean_object* v___x_736_; 
lean_inc(v_value_730_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_value_730_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_737_, lean_object* v_x_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_737_, v_x_738_);
lean_dec(v_x_738_);
lean_dec_ref(v_a_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_buckets_742_; lean_object* v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; uint64_t v___x_747_; uint64_t v___x_748_; uint64_t v___x_749_; uint64_t v_fold_750_; uint64_t v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; size_t v___x_754_; size_t v___x_755_; size_t v___x_756_; size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_buckets_742_ = lean_ctor_get(v_m_740_, 1);
v___x_743_ = lean_array_get_size(v_buckets_742_);
v___x_744_ = lean_ptr_addr(v_a_741_);
v___x_745_ = ((size_t)3ULL);
v___x_746_ = lean_usize_shift_right(v___x_744_, v___x_745_);
v___x_747_ = lean_usize_to_uint64(v___x_746_);
v___x_748_ = 32ULL;
v___x_749_ = lean_uint64_shift_right(v___x_747_, v___x_748_);
v_fold_750_ = lean_uint64_xor(v___x_747_, v___x_749_);
v___x_751_ = 16ULL;
v___x_752_ = lean_uint64_shift_right(v_fold_750_, v___x_751_);
v___x_753_ = lean_uint64_xor(v_fold_750_, v___x_752_);
v___x_754_ = lean_uint64_to_usize(v___x_753_);
v___x_755_ = lean_usize_of_nat(v___x_743_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_sub(v___x_755_, v___x_756_);
v___x_758_ = lean_usize_land(v___x_754_, v___x_757_);
v___x_759_ = lean_array_uget_borrowed(v_buckets_742_, v___x_758_);
v___x_760_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_741_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_761_, v_a_762_);
lean_dec_ref(v_a_762_);
lean_dec_ref(v_m_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_764_, lean_object* v_vals_765_, lean_object* v_i_766_, lean_object* v_k_767_){
_start:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_array_get_size(v_keys_764_);
v___x_769_ = lean_nat_dec_lt(v_i_766_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_i_766_);
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v_k_x27_771_; uint8_t v___x_772_; 
v_k_x27_771_ = lean_array_fget_borrowed(v_keys_764_, v_i_766_);
v___x_772_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_767_, v_k_x27_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_i_766_, v___x_773_);
lean_dec(v_i_766_);
v_i_766_ = v___x_774_;
goto _start;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_array_fget_borrowed(v_vals_765_, v_i_766_);
lean_dec(v_i_766_);
lean_inc(v___x_776_);
lean_inc(v_k_x27_771_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_k_x27_771_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_779_, lean_object* v_vals_780_, lean_object* v_i_781_, lean_object* v_k_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_779_, v_vals_780_, v_i_781_, v_k_782_);
lean_dec_ref(v_k_782_);
lean_dec_ref(v_vals_780_);
lean_dec_ref(v_keys_779_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_784_, size_t v_x_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_es_787_; lean_object* v___x_788_; size_t v___x_789_; size_t v___x_790_; lean_object* v_j_791_; lean_object* v___x_792_; 
v_es_787_ = lean_ctor_get(v_x_784_, 0);
v___x_788_ = lean_box(2);
v___x_789_ = ((size_t)31ULL);
v___x_790_ = lean_usize_land(v_x_785_, v___x_789_);
v_j_791_ = lean_usize_to_nat(v___x_790_);
v___x_792_ = lean_array_get_borrowed(v___x_788_, v_es_787_, v_j_791_);
lean_dec(v_j_791_);
switch(lean_obj_tag(v___x_792_))
{
case 0:
{
lean_object* v_key_793_; lean_object* v_val_794_; uint8_t v___x_795_; 
v_key_793_ = lean_ctor_get(v___x_792_, 0);
v_val_794_ = lean_ctor_get(v___x_792_, 1);
v___x_795_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_786_, v_key_793_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_box(0);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc(v_val_794_);
lean_inc(v_key_793_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_key_793_);
lean_ctor_set(v___x_797_, 1, v_val_794_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
case 1:
{
lean_object* v_node_799_; size_t v___x_800_; size_t v___x_801_; 
v_node_799_ = lean_ctor_get(v___x_792_, 0);
v___x_800_ = ((size_t)5ULL);
v___x_801_ = lean_usize_shift_right(v_x_785_, v___x_800_);
v_x_784_ = v_node_799_;
v_x_785_ = v___x_801_;
goto _start;
}
default: 
{
lean_object* v___x_803_; 
v___x_803_ = lean_box(0);
return v___x_803_;
}
}
}
else
{
lean_object* v_ks_804_; lean_object* v_vs_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_ks_804_ = lean_ctor_get(v_x_784_, 0);
v_vs_805_ = lean_ctor_get(v_x_784_, 1);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_804_, v_vs_805_, v___x_806_, v_x_786_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
size_t v_x_10839__boxed_811_; lean_object* v_res_812_; 
v_x_10839__boxed_811_ = lean_unbox_usize(v_x_809_);
lean_dec(v_x_809_);
v_res_812_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_808_, v_x_10839__boxed_811_, v_x_810_);
lean_dec_ref(v_x_810_);
lean_dec_ref(v_x_808_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
uint64_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; 
v___x_815_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_814_);
v___x_816_ = lean_uint64_to_usize(v___x_815_);
v___x_817_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_813_, v___x_816_, v_x_814_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_818_, v_x_819_);
lean_dec_ref(v_x_819_);
lean_dec_ref(v_x_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
switch(lean_obj_tag(v_e_821_))
{
case 4:
{
lean_object* v_declName_824_; lean_object* v_map_825_; lean_object* v_set_826_; lean_object* v___x_827_; 
v_declName_824_ = lean_ctor_get(v_e_821_, 0);
v_map_825_ = lean_ctor_get(v_a_823_, 0);
v_set_826_ = lean_ctor_get(v_a_823_, 1);
v___x_827_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_826_, v_e_821_);
if (lean_obj_tag(v___x_827_) == 0)
{
uint8_t v___x_828_; 
lean_inc(v_declName_824_);
lean_inc_ref(v_a_822_);
v___x_828_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_822_, v_declName_824_);
if (v___x_828_ == 0)
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_838_; 
lean_inc_ref(v_set_826_);
lean_inc_ref(v_map_825_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_a_823_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_839_ = lean_ctor_get(v_a_823_, 1);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_a_823_, 0);
lean_dec(v_unused_840_);
v___x_830_ = v_a_823_;
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
else
{
lean_dec(v_a_823_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = lean_box(0);
lean_inc_ref(v_e_821_);
v___x_833_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_826_, v_e_821_, v___x_832_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_833_);
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_map_825_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_837_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_e_821_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
return v___x_836_;
}
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref_known(v_e_821_, 2);
v___x_841_ = lean_box(0);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_a_823_);
return v___x_842_;
}
}
else
{
lean_object* v_val_843_; lean_object* v_fst_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref_known(v_e_821_, 2);
v_val_843_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_827_, 1);
v_fst_844_ = lean_ctor_get(v_val_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_val_843_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v_val_843_, 1);
lean_dec(v_unused_852_);
v___x_846_ = v_val_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_fst_844_);
lean_dec(v_val_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_a_823_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_844_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_a_823_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
case 5:
{
lean_object* v_fn_853_; lean_object* v_arg_854_; lean_object* v_map_855_; lean_object* v_set_856_; lean_object* v___x_857_; 
v_fn_853_ = lean_ctor_get(v_e_821_, 0);
v_arg_854_ = lean_ctor_get(v_e_821_, 1);
v_map_855_ = lean_ctor_get(v_a_823_, 0);
v_set_856_ = lean_ctor_get(v_a_823_, 1);
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_855_, v_e_821_);
if (lean_obj_tag(v___x_857_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_859_; 
lean_dec_ref_known(v_e_821_, 2);
v_val_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_val_858_);
lean_ctor_set(v___x_859_, 1, v_a_823_);
return v___x_859_;
}
else
{
lean_object* v___x_860_; uint64_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; size_t v___x_864_; size_t v___x_865_; uint8_t v___x_866_; 
lean_dec(v___x_857_);
v___x_860_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_861_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_821_);
v___x_862_ = lean_uint64_to_usize(v___x_861_);
v___x_863_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_856_, v___x_862_, v_e_821_, v___x_860_);
v___x_864_ = lean_ptr_addr(v___x_863_);
v___x_865_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_866_ = lean_usize_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_dec_ref_known(v_e_821_, 2);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_863_);
lean_ctor_set(v___x_867_, 1, v_a_823_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; 
lean_dec_ref(v___x_863_);
lean_inc_ref(v_fn_853_);
v___x_868_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_853_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
v_a_870_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_868_, 2);
lean_inc_ref(v_arg_854_);
v___x_871_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_854_, v_a_822_, v_a_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v_a_873_; size_t v___x_874_; size_t v___x_875_; uint8_t v___x_876_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
v_a_873_ = lean_ctor_get(v___x_871_, 1);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_871_, 2);
v___x_874_ = lean_ptr_addr(v_fn_853_);
v___x_875_ = lean_ptr_addr(v_a_869_);
v___x_876_ = lean_usize_dec_eq(v___x_874_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = l_Lean_Expr_app___override(v_a_869_, v_a_872_);
v___x_878_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_877_, v_a_873_);
return v___x_878_;
}
else
{
size_t v___x_879_; size_t v___x_880_; uint8_t v___x_881_; 
v___x_879_ = lean_ptr_addr(v_arg_854_);
v___x_880_ = lean_ptr_addr(v_a_872_);
v___x_881_ = lean_usize_dec_eq(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = l_Lean_Expr_app___override(v_a_869_, v_a_872_);
v___x_883_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_882_, v_a_873_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; 
lean_dec(v_a_872_);
lean_dec(v_a_869_);
lean_inc_ref(v_e_821_);
v___x_884_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v_e_821_, v_a_873_);
return v___x_884_;
}
}
}
else
{
lean_dec(v_a_869_);
lean_dec_ref_known(v_e_821_, 2);
return v___x_871_;
}
}
else
{
lean_dec_ref_known(v_e_821_, 2);
return v___x_868_;
}
}
}
}
case 6:
{
lean_object* v_binderName_885_; lean_object* v_binderType_886_; lean_object* v_body_887_; uint8_t v_binderInfo_888_; lean_object* v_map_889_; lean_object* v_set_890_; lean_object* v___x_891_; 
v_binderName_885_ = lean_ctor_get(v_e_821_, 0);
v_binderType_886_ = lean_ctor_get(v_e_821_, 1);
v_body_887_ = lean_ctor_get(v_e_821_, 2);
v_binderInfo_888_ = lean_ctor_get_uint8(v_e_821_, sizeof(void*)*3 + 8);
v_map_889_ = lean_ctor_get(v_a_823_, 0);
v_set_890_ = lean_ctor_get(v_a_823_, 1);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_889_, v_e_821_);
if (lean_obj_tag(v___x_891_) == 1)
{
lean_object* v_val_892_; lean_object* v___x_893_; 
lean_dec_ref_known(v_e_821_, 3);
v_val_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_val_892_);
lean_ctor_set(v___x_893_, 1, v_a_823_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; uint64_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; size_t v___x_898_; size_t v___x_899_; uint8_t v___x_900_; 
lean_dec(v___x_891_);
v___x_894_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_895_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_821_);
v___x_896_ = lean_uint64_to_usize(v___x_895_);
v___x_897_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_890_, v___x_896_, v_e_821_, v___x_894_);
v___x_898_ = lean_ptr_addr(v___x_897_);
v___x_899_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_900_ = lean_usize_dec_eq(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec_ref_known(v_e_821_, 3);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_897_);
lean_ctor_set(v___x_901_, 1, v_a_823_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; 
lean_dec_ref(v___x_897_);
lean_inc_ref(v_binderType_886_);
v___x_902_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_886_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_a_904_; lean_object* v___x_905_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
v_a_904_ = lean_ctor_get(v___x_902_, 1);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_902_, 2);
lean_inc_ref(v_body_887_);
v___x_905_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_887_, v_a_822_, v_a_904_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v_a_907_; size_t v___x_908_; size_t v___x_909_; uint8_t v___x_910_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
v_a_907_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_905_, 2);
v___x_908_ = lean_ptr_addr(v_binderType_886_);
v___x_909_ = lean_ptr_addr(v_a_903_);
v___x_910_ = lean_usize_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_inc(v_binderName_885_);
v___x_911_ = l_Lean_Expr_lam___override(v_binderName_885_, v_a_903_, v_a_906_, v_binderInfo_888_);
v___x_912_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_911_, v_a_907_);
return v___x_912_;
}
else
{
size_t v___x_913_; size_t v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_ptr_addr(v_body_887_);
v___x_914_ = lean_ptr_addr(v_a_906_);
v___x_915_ = lean_usize_dec_eq(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_inc(v_binderName_885_);
v___x_916_ = l_Lean_Expr_lam___override(v_binderName_885_, v_a_903_, v_a_906_, v_binderInfo_888_);
v___x_917_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_916_, v_a_907_);
return v___x_917_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_888_, v_binderInfo_888_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_inc(v_binderName_885_);
v___x_919_ = l_Lean_Expr_lam___override(v_binderName_885_, v_a_903_, v_a_906_, v_binderInfo_888_);
v___x_920_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_919_, v_a_907_);
return v___x_920_;
}
else
{
lean_object* v___x_921_; 
lean_dec(v_a_906_);
lean_dec(v_a_903_);
lean_inc_ref(v_e_821_);
v___x_921_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v_e_821_, v_a_907_);
return v___x_921_;
}
}
}
}
else
{
lean_dec(v_a_903_);
lean_dec_ref_known(v_e_821_, 3);
return v___x_905_;
}
}
else
{
lean_dec_ref_known(v_e_821_, 3);
return v___x_902_;
}
}
}
}
case 7:
{
lean_object* v_binderName_922_; lean_object* v_binderType_923_; lean_object* v_body_924_; uint8_t v_binderInfo_925_; lean_object* v_map_926_; lean_object* v_set_927_; lean_object* v___x_928_; 
v_binderName_922_ = lean_ctor_get(v_e_821_, 0);
v_binderType_923_ = lean_ctor_get(v_e_821_, 1);
v_body_924_ = lean_ctor_get(v_e_821_, 2);
v_binderInfo_925_ = lean_ctor_get_uint8(v_e_821_, sizeof(void*)*3 + 8);
v_map_926_ = lean_ctor_get(v_a_823_, 0);
v_set_927_ = lean_ctor_get(v_a_823_, 1);
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_926_, v_e_821_);
if (lean_obj_tag(v___x_928_) == 1)
{
lean_object* v_val_929_; lean_object* v___x_930_; 
lean_dec_ref_known(v_e_821_, 3);
v_val_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_val_929_);
lean_ctor_set(v___x_930_, 1, v_a_823_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; uint64_t v___x_932_; size_t v___x_933_; lean_object* v___x_934_; size_t v___x_935_; size_t v___x_936_; uint8_t v___x_937_; 
lean_dec(v___x_928_);
v___x_931_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_932_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_821_);
v___x_933_ = lean_uint64_to_usize(v___x_932_);
v___x_934_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_927_, v___x_933_, v_e_821_, v___x_931_);
v___x_935_ = lean_ptr_addr(v___x_934_);
v___x_936_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_937_ = lean_usize_dec_eq(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_dec_ref_known(v_e_821_, 3);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_934_);
lean_ctor_set(v___x_938_, 1, v_a_823_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; 
lean_dec_ref(v___x_934_);
lean_inc_ref(v_binderType_923_);
v___x_939_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_923_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v___x_942_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
v_a_941_ = lean_ctor_get(v___x_939_, 1);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_939_, 2);
lean_inc_ref(v_body_924_);
v___x_942_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_924_, v_a_822_, v_a_941_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v_a_944_; size_t v___x_945_; size_t v___x_946_; uint8_t v___x_947_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
v_a_944_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_942_, 2);
v___x_945_ = lean_ptr_addr(v_binderType_923_);
v___x_946_ = lean_ptr_addr(v_a_940_);
v___x_947_ = lean_usize_dec_eq(v___x_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_inc(v_binderName_922_);
v___x_948_ = l_Lean_Expr_forallE___override(v_binderName_922_, v_a_940_, v_a_943_, v_binderInfo_925_);
v___x_949_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_948_, v_a_944_);
return v___x_949_;
}
else
{
size_t v___x_950_; size_t v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_ptr_addr(v_body_924_);
v___x_951_ = lean_ptr_addr(v_a_943_);
v___x_952_ = lean_usize_dec_eq(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_inc(v_binderName_922_);
v___x_953_ = l_Lean_Expr_forallE___override(v_binderName_922_, v_a_940_, v_a_943_, v_binderInfo_925_);
v___x_954_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_953_, v_a_944_);
return v___x_954_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_925_, v_binderInfo_925_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_inc(v_binderName_922_);
v___x_956_ = l_Lean_Expr_forallE___override(v_binderName_922_, v_a_940_, v_a_943_, v_binderInfo_925_);
v___x_957_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_956_, v_a_944_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; 
lean_dec(v_a_943_);
lean_dec(v_a_940_);
lean_inc_ref(v_e_821_);
v___x_958_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v_e_821_, v_a_944_);
return v___x_958_;
}
}
}
}
else
{
lean_dec(v_a_940_);
lean_dec_ref_known(v_e_821_, 3);
return v___x_942_;
}
}
else
{
lean_dec_ref_known(v_e_821_, 3);
return v___x_939_;
}
}
}
}
case 8:
{
lean_object* v_declName_959_; lean_object* v_type_960_; lean_object* v_value_961_; lean_object* v_body_962_; uint8_t v_nondep_963_; lean_object* v_map_964_; lean_object* v_set_965_; lean_object* v___x_966_; 
v_declName_959_ = lean_ctor_get(v_e_821_, 0);
v_type_960_ = lean_ctor_get(v_e_821_, 1);
v_value_961_ = lean_ctor_get(v_e_821_, 2);
v_body_962_ = lean_ctor_get(v_e_821_, 3);
v_nondep_963_ = lean_ctor_get_uint8(v_e_821_, sizeof(void*)*4 + 8);
v_map_964_ = lean_ctor_get(v_a_823_, 0);
v_set_965_ = lean_ctor_get(v_a_823_, 1);
v___x_966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_964_, v_e_821_);
if (lean_obj_tag(v___x_966_) == 1)
{
lean_object* v_val_967_; lean_object* v___x_968_; 
lean_dec_ref_known(v_e_821_, 4);
v_val_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_val_967_);
lean_ctor_set(v___x_968_, 1, v_a_823_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; uint64_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; size_t v___x_973_; size_t v___x_974_; uint8_t v___x_975_; 
lean_dec(v___x_966_);
v___x_969_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_970_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_821_);
v___x_971_ = lean_uint64_to_usize(v___x_970_);
v___x_972_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_965_, v___x_971_, v_e_821_, v___x_969_);
v___x_973_ = lean_ptr_addr(v___x_972_);
v___x_974_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_975_ = lean_usize_dec_eq(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_dec_ref_known(v_e_821_, 4);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_972_);
lean_ctor_set(v___x_976_, 1, v_a_823_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; 
lean_dec_ref(v___x_972_);
lean_inc_ref(v_type_960_);
v___x_977_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_960_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
v_a_979_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_977_, 2);
lean_inc_ref(v_value_961_);
v___x_980_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_961_, v_a_822_, v_a_979_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
v_a_982_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_980_, 2);
lean_inc_ref(v_body_962_);
v___x_983_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_962_, v_a_822_, v_a_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_a_985_; size_t v___x_986_; size_t v___x_987_; uint8_t v___x_988_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
v_a_985_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_983_, 2);
v___x_986_ = lean_ptr_addr(v_type_960_);
v___x_987_ = lean_ptr_addr(v_a_978_);
v___x_988_ = lean_usize_dec_eq(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_inc(v_declName_959_);
v___x_989_ = l_Lean_Expr_letE___override(v_declName_959_, v_a_978_, v_a_981_, v_a_984_, v_nondep_963_);
v___x_990_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_989_, v_a_985_);
return v___x_990_;
}
else
{
size_t v___x_991_; size_t v___x_992_; uint8_t v___x_993_; 
v___x_991_ = lean_ptr_addr(v_value_961_);
v___x_992_ = lean_ptr_addr(v_a_981_);
v___x_993_ = lean_usize_dec_eq(v___x_991_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_inc(v_declName_959_);
v___x_994_ = l_Lean_Expr_letE___override(v_declName_959_, v_a_978_, v_a_981_, v_a_984_, v_nondep_963_);
v___x_995_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_994_, v_a_985_);
return v___x_995_;
}
else
{
size_t v___x_996_; size_t v___x_997_; uint8_t v___x_998_; 
v___x_996_ = lean_ptr_addr(v_body_962_);
v___x_997_ = lean_ptr_addr(v_a_984_);
v___x_998_ = lean_usize_dec_eq(v___x_996_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_inc(v_declName_959_);
v___x_999_ = l_Lean_Expr_letE___override(v_declName_959_, v_a_978_, v_a_981_, v_a_984_, v_nondep_963_);
v___x_1000_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_999_, v_a_985_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; 
lean_dec(v_a_984_);
lean_dec(v_a_981_);
lean_dec(v_a_978_);
lean_inc_ref(v_e_821_);
v___x_1001_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v_e_821_, v_a_985_);
return v___x_1001_;
}
}
}
}
else
{
lean_dec(v_a_981_);
lean_dec(v_a_978_);
lean_dec_ref_known(v_e_821_, 4);
return v___x_983_;
}
}
else
{
lean_dec(v_a_978_);
lean_dec_ref_known(v_e_821_, 4);
return v___x_980_;
}
}
else
{
lean_dec_ref_known(v_e_821_, 4);
return v___x_977_;
}
}
}
}
case 10:
{
lean_object* v_data_1002_; lean_object* v_expr_1003_; lean_object* v_map_1004_; lean_object* v_set_1005_; lean_object* v___x_1006_; 
v_data_1002_ = lean_ctor_get(v_e_821_, 0);
v_expr_1003_ = lean_ctor_get(v_e_821_, 1);
v_map_1004_ = lean_ctor_get(v_a_823_, 0);
v_set_1005_ = lean_ctor_get(v_a_823_, 1);
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1004_, v_e_821_);
if (lean_obj_tag(v___x_1006_) == 1)
{
lean_object* v_val_1007_; lean_object* v___x_1008_; 
lean_dec_ref_known(v_e_821_, 2);
v_val_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_val_1007_);
lean_ctor_set(v___x_1008_, 1, v_a_823_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; uint64_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; uint8_t v___x_1015_; 
lean_dec(v___x_1006_);
v___x_1009_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1010_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_821_);
v___x_1011_ = lean_uint64_to_usize(v___x_1010_);
v___x_1012_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1005_, v___x_1011_, v_e_821_, v___x_1009_);
v___x_1013_ = lean_ptr_addr(v___x_1012_);
v___x_1014_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1015_ = lean_usize_dec_eq(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_dec_ref_known(v_e_821_, 2);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1012_);
lean_ctor_set(v___x_1016_, 1, v_a_823_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; 
lean_dec_ref(v___x_1012_);
lean_inc_ref(v_expr_1003_);
v___x_1017_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1003_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v_a_1019_; size_t v___x_1020_; size_t v___x_1021_; uint8_t v___x_1022_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
v_a_1019_ = lean_ctor_get(v___x_1017_, 1);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1017_, 2);
v___x_1020_ = lean_ptr_addr(v_expr_1003_);
v___x_1021_ = lean_ptr_addr(v_a_1018_);
v___x_1022_ = lean_usize_dec_eq(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_inc(v_data_1002_);
v___x_1023_ = l_Lean_Expr_mdata___override(v_data_1002_, v_a_1018_);
v___x_1024_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_1023_, v_a_1019_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; 
lean_dec(v_a_1018_);
lean_inc_ref(v_e_821_);
v___x_1025_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v_e_821_, v_a_1019_);
return v___x_1025_;
}
}
else
{
lean_dec_ref_known(v_e_821_, 2);
return v___x_1017_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1026_; lean_object* v_idx_1027_; lean_object* v_struct_1028_; lean_object* v_map_1029_; lean_object* v_set_1030_; lean_object* v___x_1031_; 
v_typeName_1026_ = lean_ctor_get(v_e_821_, 0);
v_idx_1027_ = lean_ctor_get(v_e_821_, 1);
v_struct_1028_ = lean_ctor_get(v_e_821_, 2);
v_map_1029_ = lean_ctor_get(v_a_823_, 0);
v_set_1030_ = lean_ctor_get(v_a_823_, 1);
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1029_, v_e_821_);
if (lean_obj_tag(v___x_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1033_; 
lean_dec_ref_known(v_e_821_, 3);
v_val_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_val_1032_);
lean_ctor_set(v___x_1033_, 1, v_a_823_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; uint8_t v___x_1040_; 
lean_dec(v___x_1031_);
v___x_1034_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1035_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_821_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1030_, v___x_1036_, v_e_821_, v___x_1034_);
v___x_1038_ = lean_ptr_addr(v___x_1037_);
v___x_1039_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1040_ = lean_usize_dec_eq(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref_known(v_e_821_, 3);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1037_);
lean_ctor_set(v___x_1041_, 1, v_a_823_);
return v___x_1041_;
}
else
{
uint8_t v_checkProj_1042_; 
lean_dec_ref(v___x_1037_);
v_checkProj_1042_ = lean_ctor_get_uint8(v_a_822_, sizeof(void*)*1 + 1);
if (v_checkProj_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_inc_ref(v_struct_1028_);
v___x_1043_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1028_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v_a_1045_; size_t v___x_1046_; size_t v___x_1047_; uint8_t v___x_1048_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
v_a_1045_ = lean_ctor_get(v___x_1043_, 1);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1043_, 2);
v___x_1046_ = lean_ptr_addr(v_struct_1028_);
v___x_1047_ = lean_ptr_addr(v_a_1044_);
v___x_1048_ = lean_usize_dec_eq(v___x_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_inc(v_idx_1027_);
lean_inc(v_typeName_1026_);
v___x_1049_ = l_Lean_Expr_proj___override(v_typeName_1026_, v_idx_1027_, v_a_1044_);
v___x_1050_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v___x_1049_, v_a_1045_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; 
lean_dec(v_a_1044_);
lean_inc_ref(v_e_821_);
v___x_1051_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_821_, v_e_821_, v_a_1045_);
return v___x_1051_;
}
}
else
{
lean_dec_ref_known(v_e_821_, 3);
return v___x_1043_;
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref_known(v_e_821_, 3);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_a_823_);
return v___x_1053_;
}
}
}
}
default: 
{
lean_object* v_map_1054_; lean_object* v_set_1055_; lean_object* v___x_1056_; 
v_map_1054_ = lean_ctor_get(v_a_823_, 0);
v_set_1055_ = lean_ctor_get(v_a_823_, 1);
v___x_1056_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1055_, v_e_821_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1066_; 
lean_inc_ref(v_set_1055_);
lean_inc_ref(v_map_1054_);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_a_823_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; lean_object* v_unused_1068_; 
v_unused_1067_ = lean_ctor_get(v_a_823_, 1);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_a_823_, 0);
lean_dec(v_unused_1068_);
v___x_1058_ = v_a_823_;
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v_a_823_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1060_ = lean_box(0);
lean_inc_ref(v_e_821_);
v___x_1061_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1055_, v_e_821_, v___x_1060_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1061_);
v___x_1063_ = v___x_1058_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_map_1054_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_e_821_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
return v___x_1064_;
}
}
}
else
{
lean_object* v_val_1069_; lean_object* v_fst_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v_e_821_);
v_val_1069_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v___x_1056_, 1);
v_fst_1070_ = lean_ctor_get(v_val_1069_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_val_1069_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_val_1069_, 1);
lean_dec(v_unused_1078_);
v___x_1072_ = v_val_1069_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_fst_1070_);
lean_dec(v_val_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v_a_823_);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_fst_1070_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_a_823_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1079_, v_a_1080_, v_a_1081_);
lean_dec_ref(v_a_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1087_, v_x_1088_, v_x_1089_);
lean_dec_ref(v_x_1089_);
lean_dec_ref(v_x_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1091_, lean_object* v_m_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1092_, v_a_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1095_, lean_object* v_m_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1095_, v_m_1096_, v_a_1097_);
lean_dec_ref(v_a_1097_);
lean_dec_ref(v_m_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1099_, lean_object* v_x_1100_, size_t v_x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1100_, v_x_1101_, v_x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
size_t v_x_11425__boxed_1108_; lean_object* v_res_1109_; 
v_x_11425__boxed_1108_ = lean_unbox_usize(v_x_1106_);
lean_dec(v_x_1106_);
v_res_1109_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1104_, v_x_1105_, v_x_11425__boxed_1108_, v_x_1107_);
lean_dec_ref(v_x_1107_);
lean_dec_ref(v_x_1105_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1114_, v_a_1115_, v_x_1116_);
lean_dec(v_x_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1118_, lean_object* v_keys_1119_, lean_object* v_vals_1120_, lean_object* v_heq_1121_, lean_object* v_i_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1119_, v_vals_1120_, v_i_1122_, v_k_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1125_, lean_object* v_keys_1126_, lean_object* v_vals_1127_, lean_object* v_heq_1128_, lean_object* v_i_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1125_, v_keys_1126_, v_vals_1127_, v_heq_1128_, v_i_1129_, v_k_1130_);
lean_dec_ref(v_k_1130_);
lean_dec_ref(v_vals_1127_);
lean_dec_ref(v_keys_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1132_, lean_object* v_cache_1133_, lean_object* v_ctx_1134_, lean_object* v_s_1135_){
_start:
{
lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; 
v___f_1136_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1137_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1132_);
v___x_1138_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1136_, v___f_1137_, v_s_1135_, v_e_1132_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_cache_1133_);
lean_ctor_set(v___x_1139_, 1, v_s_1135_);
v___x_1140_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1132_, v_ctx_1134_, v___x_1139_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 1);
v_a_1142_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1144_ = v___x_1140_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1141_);
lean_inc(v_a_1142_);
lean_dec(v___x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_set_1146_; lean_object* v___x_1148_; 
v_set_1146_ = lean_ctor_get(v_a_1141_, 1);
lean_inc_ref(v_set_1146_);
lean_dec(v_a_1141_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_set_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_set_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1160_; 
v_a_1151_ = lean_ctor_get(v___x_1140_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1140_, 0);
lean_dec(v_unused_1161_);
v___x_1153_ = v___x_1140_;
v_isShared_1154_ = v_isSharedCheck_1160_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1140_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1160_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_map_1155_; lean_object* v_set_1156_; lean_object* v___x_1158_; 
v_map_1155_ = lean_ctor_get(v_a_1151_, 0);
lean_inc_ref(v_map_1155_);
v_set_1156_ = lean_ctor_get(v_a_1151_, 1);
lean_inc_ref(v_set_1156_);
lean_dec(v_a_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_set_1156_);
lean_ctor_set(v___x_1153_, 0, v_map_1155_);
v___x_1158_ = v___x_1153_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_map_1155_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_set_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v_val_1162_; lean_object* v_fst_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_cache_1133_);
lean_dec_ref(v_e_1132_);
v_val_1162_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v___x_1138_, 1);
v_fst_1163_ = lean_ctor_get(v_val_1162_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_val_1162_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v_val_1162_, 1);
lean_dec(v_unused_1171_);
v___x_1165_ = v_val_1162_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_fst_1163_);
lean_dec(v_val_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v_s_1135_);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_fst_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_s_1135_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1172_, lean_object* v_cache_1173_, lean_object* v_ctx_1174_, lean_object* v_s_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1172_, v_cache_1173_, v_ctx_1174_, v_s_1175_);
lean_dec_ref(v_ctx_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1179_; uint64_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1179_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1180_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1177_);
v___x_1181_ = lean_uint64_to_usize(v___x_1180_);
v___x_1182_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1178_, v___x_1181_, v_e_1177_, v___x_1179_);
v___x_1183_ = lean_ptr_addr(v___x_1182_);
v___x_1184_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1185_ = lean_usize_dec_eq(v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v_e_1177_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1182_);
lean_ctor_set(v___x_1186_, 1, v_a_1178_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v___x_1182_);
v___x_1187_ = lean_box(0);
lean_inc_ref(v_e_1177_);
v___x_1188_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1178_, v_e_1177_, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v_e_1177_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1190_, v_a_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1194_, v_a_1195_, v_a_1196_);
lean_dec_ref(v_a_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1198_, lean_object* v_k_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___f_1202_; lean_object* v___x_1203_; uint64_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; uint8_t v___x_1209_; 
v___f_1202_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1203_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1204_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1198_);
v___x_1205_ = lean_uint64_to_usize(v___x_1204_);
lean_inc_ref(v_a_1201_);
v___x_1206_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1202_, v_a_1201_, v___x_1205_, v_e_1198_, v___x_1203_);
v___x_1207_ = lean_ptr_addr(v___x_1206_);
v___x_1208_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1209_ = lean_usize_dec_eq(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v_k_1199_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1206_);
lean_ctor_set(v___x_1210_, 1, v_a_1201_);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; 
lean_dec(v___x_1206_);
lean_inc_ref(v_a_1200_);
v___x_1211_ = lean_apply_2(v_k_1199_, v_a_1200_, v_a_1201_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
v_a_1213_ = lean_ctor_get(v___x_1211_, 1);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1211_, 2);
v___x_1214_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1212_, v_a_1213_);
return v___x_1214_;
}
else
{
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1215_, lean_object* v_k_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1215_, v_k_1216_, v_a_1217_, v_a_1218_);
lean_dec_ref(v_a_1217_);
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_unsigned_to_nat(16u);
v___x_1222_ = lean_mk_array(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
switch(lean_obj_tag(v_e_1226_))
{
case 4:
{
lean_object* v_declName_1229_; lean_object* v___x_1230_; uint64_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; uint8_t v___x_1236_; 
v_declName_1229_ = lean_ctor_get(v_e_1226_, 0);
v___x_1230_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1231_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1226_);
v___x_1232_ = lean_uint64_to_usize(v___x_1231_);
v___x_1233_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1228_, v___x_1232_, v_e_1226_, v___x_1230_);
v___x_1234_ = lean_ptr_addr(v___x_1233_);
v___x_1235_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1236_ = lean_usize_dec_eq(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1233_);
lean_ctor_set(v___x_1237_, 1, v_a_1228_);
return v___x_1237_;
}
else
{
uint8_t v___x_1238_; 
lean_dec_ref(v___x_1233_);
lean_inc(v_declName_1229_);
lean_inc_ref(v_a_1227_);
v___x_1238_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1227_, v_declName_1229_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_box(0);
lean_inc_ref(v_e_1226_);
v___x_1240_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1228_, v_e_1226_, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_e_1226_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_1228_);
return v___x_1243_;
}
}
}
case 5:
{
lean_object* v_fn_1244_; lean_object* v_arg_1245_; lean_object* v___x_1246_; uint64_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; uint8_t v___x_1252_; 
v_fn_1244_ = lean_ctor_get(v_e_1226_, 0);
v_arg_1245_ = lean_ctor_get(v_e_1226_, 1);
v___x_1246_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1247_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1226_);
v___x_1248_ = lean_uint64_to_usize(v___x_1247_);
v___x_1249_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1228_, v___x_1248_, v_e_1226_, v___x_1246_);
v___x_1250_ = lean_ptr_addr(v___x_1249_);
v___x_1251_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1252_ = lean_usize_dec_eq(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1249_);
lean_ctor_set(v___x_1253_, 1, v_a_1228_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; 
lean_dec_ref(v___x_1249_);
lean_inc_ref(v_fn_1244_);
v___x_1254_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1244_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_a_1256_; lean_object* v___x_1257_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
v_a_1256_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1254_, 2);
lean_inc_ref(v_arg_1245_);
v___x_1257_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1245_, v_a_1227_, v_a_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_a_1259_; size_t v___x_1260_; size_t v___x_1261_; uint8_t v___x_1262_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
v_a_1259_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1257_, 2);
v___x_1260_ = lean_ptr_addr(v_fn_1244_);
v___x_1261_ = lean_ptr_addr(v_a_1255_);
v___x_1262_ = lean_usize_dec_eq(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1263_ = l_Lean_Expr_app___override(v_a_1255_, v_a_1258_);
v___x_1264_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1263_, v_a_1259_);
return v___x_1264_;
}
else
{
size_t v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_ptr_addr(v_arg_1245_);
v___x_1266_ = lean_ptr_addr(v_a_1258_);
v___x_1267_ = lean_usize_dec_eq(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1268_ = l_Lean_Expr_app___override(v_a_1255_, v_a_1258_);
v___x_1269_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1268_, v_a_1259_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_a_1258_);
lean_dec(v_a_1255_);
v___x_1270_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1226_, v_a_1259_);
return v___x_1270_;
}
}
}
else
{
lean_dec(v_a_1255_);
lean_dec_ref_known(v_e_1226_, 2);
return v___x_1257_;
}
}
else
{
lean_dec_ref_known(v_e_1226_, 2);
return v___x_1254_;
}
}
}
case 6:
{
lean_object* v_binderName_1271_; lean_object* v_binderType_1272_; lean_object* v_body_1273_; uint8_t v_binderInfo_1274_; lean_object* v___x_1275_; uint64_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; uint8_t v___x_1281_; 
v_binderName_1271_ = lean_ctor_get(v_e_1226_, 0);
v_binderType_1272_ = lean_ctor_get(v_e_1226_, 1);
v_body_1273_ = lean_ctor_get(v_e_1226_, 2);
v_binderInfo_1274_ = lean_ctor_get_uint8(v_e_1226_, sizeof(void*)*3 + 8);
v___x_1275_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1276_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1226_);
v___x_1277_ = lean_uint64_to_usize(v___x_1276_);
v___x_1278_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1228_, v___x_1277_, v_e_1226_, v___x_1275_);
v___x_1279_ = lean_ptr_addr(v___x_1278_);
v___x_1280_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1281_ = lean_usize_dec_eq(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref_known(v_e_1226_, 3);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1278_);
lean_ctor_set(v___x_1282_, 1, v_a_1228_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; 
lean_dec_ref(v___x_1278_);
lean_inc_ref(v_binderType_1272_);
v___x_1283_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1272_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
v_a_1285_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1283_, 2);
lean_inc_ref(v_body_1273_);
v___x_1286_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1273_, v_a_1227_, v_a_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_a_1288_; size_t v___x_1289_; size_t v___x_1290_; uint8_t v___x_1291_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
v_a_1288_ = lean_ctor_get(v___x_1286_, 1);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1286_, 2);
v___x_1289_ = lean_ptr_addr(v_binderType_1272_);
v___x_1290_ = lean_ptr_addr(v_a_1284_);
v___x_1291_ = lean_usize_dec_eq(v___x_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_inc(v_binderName_1271_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1292_ = l_Lean_Expr_lam___override(v_binderName_1271_, v_a_1284_, v_a_1287_, v_binderInfo_1274_);
v___x_1293_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1292_, v_a_1288_);
return v___x_1293_;
}
else
{
size_t v___x_1294_; size_t v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_ptr_addr(v_body_1273_);
v___x_1295_ = lean_ptr_addr(v_a_1287_);
v___x_1296_ = lean_usize_dec_eq(v___x_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_inc(v_binderName_1271_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1297_ = l_Lean_Expr_lam___override(v_binderName_1271_, v_a_1284_, v_a_1287_, v_binderInfo_1274_);
v___x_1298_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1297_, v_a_1288_);
return v___x_1298_;
}
else
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1274_, v_binderInfo_1274_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc(v_binderName_1271_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1300_ = l_Lean_Expr_lam___override(v_binderName_1271_, v_a_1284_, v_a_1287_, v_binderInfo_1274_);
v___x_1301_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1300_, v_a_1288_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; 
lean_dec(v_a_1287_);
lean_dec(v_a_1284_);
v___x_1302_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1226_, v_a_1288_);
return v___x_1302_;
}
}
}
}
else
{
lean_dec(v_a_1284_);
lean_dec_ref_known(v_e_1226_, 3);
return v___x_1286_;
}
}
else
{
lean_dec_ref_known(v_e_1226_, 3);
return v___x_1283_;
}
}
}
case 7:
{
lean_object* v_binderName_1303_; lean_object* v_binderType_1304_; lean_object* v_body_1305_; uint8_t v_binderInfo_1306_; lean_object* v___x_1307_; uint64_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; uint8_t v___x_1313_; 
v_binderName_1303_ = lean_ctor_get(v_e_1226_, 0);
v_binderType_1304_ = lean_ctor_get(v_e_1226_, 1);
v_body_1305_ = lean_ctor_get(v_e_1226_, 2);
v_binderInfo_1306_ = lean_ctor_get_uint8(v_e_1226_, sizeof(void*)*3 + 8);
v___x_1307_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1308_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1226_);
v___x_1309_ = lean_uint64_to_usize(v___x_1308_);
v___x_1310_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1228_, v___x_1309_, v_e_1226_, v___x_1307_);
v___x_1311_ = lean_ptr_addr(v___x_1310_);
v___x_1312_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1313_ = lean_usize_dec_eq(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref_known(v_e_1226_, 3);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1310_);
lean_ctor_set(v___x_1314_, 1, v_a_1228_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; 
lean_dec_ref(v___x_1310_);
lean_inc_ref(v_binderType_1304_);
v___x_1315_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1304_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v_a_1317_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
v_a_1317_ = lean_ctor_get(v___x_1315_, 1);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1315_, 2);
lean_inc_ref(v_body_1305_);
v___x_1318_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1305_, v_a_1227_, v_a_1317_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_a_1320_; size_t v___x_1321_; size_t v___x_1322_; uint8_t v___x_1323_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
v_a_1320_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1318_, 2);
v___x_1321_ = lean_ptr_addr(v_binderType_1304_);
v___x_1322_ = lean_ptr_addr(v_a_1316_);
v___x_1323_ = lean_usize_dec_eq(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_inc(v_binderName_1303_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1324_ = l_Lean_Expr_forallE___override(v_binderName_1303_, v_a_1316_, v_a_1319_, v_binderInfo_1306_);
v___x_1325_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1324_, v_a_1320_);
return v___x_1325_;
}
else
{
size_t v___x_1326_; size_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = lean_ptr_addr(v_body_1305_);
v___x_1327_ = lean_ptr_addr(v_a_1319_);
v___x_1328_ = lean_usize_dec_eq(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_inc(v_binderName_1303_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1329_ = l_Lean_Expr_forallE___override(v_binderName_1303_, v_a_1316_, v_a_1319_, v_binderInfo_1306_);
v___x_1330_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1329_, v_a_1320_);
return v___x_1330_;
}
else
{
uint8_t v___x_1331_; 
v___x_1331_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1306_, v_binderInfo_1306_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_inc(v_binderName_1303_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1332_ = l_Lean_Expr_forallE___override(v_binderName_1303_, v_a_1316_, v_a_1319_, v_binderInfo_1306_);
v___x_1333_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1332_, v_a_1320_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; 
lean_dec(v_a_1319_);
lean_dec(v_a_1316_);
v___x_1334_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1226_, v_a_1320_);
return v___x_1334_;
}
}
}
}
else
{
lean_dec(v_a_1316_);
lean_dec_ref_known(v_e_1226_, 3);
return v___x_1318_;
}
}
else
{
lean_dec_ref_known(v_e_1226_, 3);
return v___x_1315_;
}
}
}
case 8:
{
lean_object* v_declName_1335_; lean_object* v_type_1336_; lean_object* v_value_1337_; lean_object* v_body_1338_; uint8_t v_nondep_1339_; lean_object* v___x_1340_; uint64_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; uint8_t v___x_1346_; 
v_declName_1335_ = lean_ctor_get(v_e_1226_, 0);
v_type_1336_ = lean_ctor_get(v_e_1226_, 1);
v_value_1337_ = lean_ctor_get(v_e_1226_, 2);
v_body_1338_ = lean_ctor_get(v_e_1226_, 3);
v_nondep_1339_ = lean_ctor_get_uint8(v_e_1226_, sizeof(void*)*4 + 8);
v___x_1340_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1341_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1226_);
v___x_1342_ = lean_uint64_to_usize(v___x_1341_);
v___x_1343_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1228_, v___x_1342_, v_e_1226_, v___x_1340_);
v___x_1344_ = lean_ptr_addr(v___x_1343_);
v___x_1345_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1346_ = lean_usize_dec_eq(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref_known(v_e_1226_, 4);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1343_);
lean_ctor_set(v___x_1347_, 1, v_a_1228_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v___x_1343_);
lean_inc_ref(v_type_1336_);
v___x_1348_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1336_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
v_a_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1348_, 2);
lean_inc_ref(v_value_1337_);
v___x_1351_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1337_, v_a_1227_, v_a_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
v_a_1353_ = lean_ctor_get(v___x_1351_, 1);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1351_, 2);
lean_inc_ref(v_body_1338_);
v___x_1354_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1338_, v_a_1227_, v_a_1353_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_a_1356_; size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
v_a_1356_ = lean_ctor_get(v___x_1354_, 1);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1354_, 2);
v___x_1357_ = lean_ptr_addr(v_type_1336_);
v___x_1358_ = lean_ptr_addr(v_a_1349_);
v___x_1359_ = lean_usize_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_inc(v_declName_1335_);
lean_dec_ref_known(v_e_1226_, 4);
v___x_1360_ = l_Lean_Expr_letE___override(v_declName_1335_, v_a_1349_, v_a_1352_, v_a_1355_, v_nondep_1339_);
v___x_1361_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1360_, v_a_1356_);
return v___x_1361_;
}
else
{
size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_ptr_addr(v_value_1337_);
v___x_1363_ = lean_ptr_addr(v_a_1352_);
v___x_1364_ = lean_usize_dec_eq(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc(v_declName_1335_);
lean_dec_ref_known(v_e_1226_, 4);
v___x_1365_ = l_Lean_Expr_letE___override(v_declName_1335_, v_a_1349_, v_a_1352_, v_a_1355_, v_nondep_1339_);
v___x_1366_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1365_, v_a_1356_);
return v___x_1366_;
}
else
{
size_t v___x_1367_; size_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_ptr_addr(v_body_1338_);
v___x_1368_ = lean_ptr_addr(v_a_1355_);
v___x_1369_ = lean_usize_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_inc(v_declName_1335_);
lean_dec_ref_known(v_e_1226_, 4);
v___x_1370_ = l_Lean_Expr_letE___override(v_declName_1335_, v_a_1349_, v_a_1352_, v_a_1355_, v_nondep_1339_);
v___x_1371_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1370_, v_a_1356_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; 
lean_dec(v_a_1355_);
lean_dec(v_a_1352_);
lean_dec(v_a_1349_);
v___x_1372_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1226_, v_a_1356_);
return v___x_1372_;
}
}
}
}
else
{
lean_dec(v_a_1352_);
lean_dec(v_a_1349_);
lean_dec_ref_known(v_e_1226_, 4);
return v___x_1354_;
}
}
else
{
lean_dec(v_a_1349_);
lean_dec_ref_known(v_e_1226_, 4);
return v___x_1351_;
}
}
else
{
lean_dec_ref_known(v_e_1226_, 4);
return v___x_1348_;
}
}
}
case 10:
{
lean_object* v_data_1373_; lean_object* v_expr_1374_; lean_object* v___x_1375_; uint64_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; uint8_t v___x_1381_; 
v_data_1373_ = lean_ctor_get(v_e_1226_, 0);
v_expr_1374_ = lean_ctor_get(v_e_1226_, 1);
v___x_1375_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1376_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1226_);
v___x_1377_ = lean_uint64_to_usize(v___x_1376_);
v___x_1378_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1228_, v___x_1377_, v_e_1226_, v___x_1375_);
v___x_1379_ = lean_ptr_addr(v___x_1378_);
v___x_1380_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1381_ = lean_usize_dec_eq(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref_known(v_e_1226_, 2);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1378_);
lean_ctor_set(v___x_1382_, 1, v_a_1228_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v___x_1378_);
lean_inc_ref(v_expr_1374_);
v___x_1383_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1374_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_a_1385_; size_t v___x_1386_; size_t v___x_1387_; uint8_t v___x_1388_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
v_a_1385_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1383_, 2);
v___x_1386_ = lean_ptr_addr(v_expr_1374_);
v___x_1387_ = lean_ptr_addr(v_a_1384_);
v___x_1388_ = lean_usize_dec_eq(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc(v_data_1373_);
lean_dec_ref_known(v_e_1226_, 2);
v___x_1389_ = l_Lean_Expr_mdata___override(v_data_1373_, v_a_1384_);
v___x_1390_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1389_, v_a_1385_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; 
lean_dec(v_a_1384_);
v___x_1391_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1226_, v_a_1385_);
return v___x_1391_;
}
}
else
{
lean_dec_ref_known(v_e_1226_, 2);
return v___x_1383_;
}
}
}
case 11:
{
lean_object* v_typeName_1392_; lean_object* v_idx_1393_; lean_object* v_struct_1394_; lean_object* v___x_1395_; uint64_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; uint8_t v___x_1401_; 
v_typeName_1392_ = lean_ctor_get(v_e_1226_, 0);
v_idx_1393_ = lean_ctor_get(v_e_1226_, 1);
v_struct_1394_ = lean_ctor_get(v_e_1226_, 2);
v___x_1395_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1396_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1226_);
v___x_1397_ = lean_uint64_to_usize(v___x_1396_);
v___x_1398_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1228_, v___x_1397_, v_e_1226_, v___x_1395_);
v___x_1399_ = lean_ptr_addr(v___x_1398_);
v___x_1400_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1401_ = lean_usize_dec_eq(v___x_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
lean_dec_ref_known(v_e_1226_, 3);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1398_);
lean_ctor_set(v___x_1402_, 1, v_a_1228_);
return v___x_1402_;
}
else
{
uint8_t v_checkProj_1403_; 
lean_dec_ref(v___x_1398_);
v_checkProj_1403_ = lean_ctor_get_uint8(v_a_1227_, sizeof(void*)*1 + 1);
if (v_checkProj_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_inc_ref(v_struct_1394_);
v___x_1404_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1394_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_a_1406_; size_t v___x_1407_; size_t v___x_1408_; uint8_t v___x_1409_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
v_a_1406_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1404_, 2);
v___x_1407_ = lean_ptr_addr(v_struct_1394_);
v___x_1408_ = lean_ptr_addr(v_a_1405_);
v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_inc(v_idx_1393_);
lean_inc(v_typeName_1392_);
lean_dec_ref_known(v_e_1226_, 3);
v___x_1410_ = l_Lean_Expr_proj___override(v_typeName_1392_, v_idx_1393_, v_a_1405_);
v___x_1411_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1410_, v_a_1406_);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; 
lean_dec(v_a_1405_);
v___x_1412_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1226_, v_a_1406_);
return v___x_1412_;
}
}
else
{
lean_dec_ref_known(v_e_1226_, 3);
return v___x_1404_;
}
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec_ref_known(v_e_1226_, 3);
v___x_1413_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_a_1228_);
return v___x_1414_;
}
}
}
default: 
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1226_, v_a_1228_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1416_, v_a_1417_, v_a_1418_);
lean_dec_ref(v_a_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1420_, v_a_1421_, v_a_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1424_, v_a_1425_, v_a_1426_);
lean_dec_ref(v_a_1425_);
return v_res_1427_;
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

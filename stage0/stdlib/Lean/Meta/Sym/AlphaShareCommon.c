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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_1948__boxed_262_; lean_object* v_res_263_; 
v_x_1948__boxed_262_ = lean_unbox_usize(v_x_259_);
lean_dec(v_x_259_);
v_res_263_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_258_, v_x_1948__boxed_262_, v_x_260_, v_x_261_);
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
v___x_299_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_2066__boxed_403_; size_t v_x_2067__boxed_404_; lean_object* v_res_405_; 
v_x_2066__boxed_403_ = lean_unbox_usize(v_x_399_);
lean_dec(v_x_399_);
v_x_2067__boxed_404_ = lean_unbox_usize(v_x_400_);
lean_dec(v_x_400_);
v_res_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_398_, v_x_2066__boxed_403_, v_x_2067__boxed_404_, v_x_401_, v_x_402_);
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
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_nbuckets_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_477_ = lean_array_get_size(v_data_476_);
v___x_478_ = lean_unsigned_to_nat(2u);
v_nbuckets_479_ = lean_nat_mul(v___x_477_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_box(0);
v___x_482_ = lean_mk_array(v_nbuckets_479_, v___x_481_);
v___x_483_ = lean_array_propagate_mark(v_data_476_, v___x_482_);
v___x_484_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_480_, v_data_476_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
uint8_t v___x_487_; 
v___x_487_ = 0;
return v___x_487_;
}
else
{
lean_object* v_key_488_; lean_object* v_tail_489_; size_t v___x_490_; size_t v___x_491_; uint8_t v___x_492_; 
v_key_488_ = lean_ctor_get(v_x_486_, 0);
v_tail_489_ = lean_ctor_get(v_x_486_, 2);
v___x_490_ = lean_ptr_addr(v_key_488_);
v___x_491_ = lean_ptr_addr(v_a_485_);
v___x_492_ = lean_usize_dec_eq(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
v_x_486_ = v_tail_489_;
goto _start;
}
else
{
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_494_, v_x_495_);
lean_dec(v_x_495_);
lean_dec_ref(v_a_494_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_498_, lean_object* v_a_499_, lean_object* v_b_500_){
_start:
{
lean_object* v_size_501_; lean_object* v_buckets_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_548_; 
v_size_501_ = lean_ctor_get(v_m_498_, 0);
v_buckets_502_ = lean_ctor_get(v_m_498_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_m_498_);
if (v_isSharedCheck_548_ == 0)
{
v___x_504_ = v_m_498_;
v_isShared_505_ = v_isSharedCheck_548_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_buckets_502_);
lean_inc(v_size_501_);
lean_dec(v_m_498_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_548_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v_fold_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; lean_object* v_bkt_522_; uint8_t v___x_523_; 
v___x_506_ = lean_array_get_size(v_buckets_502_);
v___x_507_ = lean_ptr_addr(v_a_499_);
v___x_508_ = ((size_t)3ULL);
v___x_509_ = lean_usize_shift_right(v___x_507_, v___x_508_);
v___x_510_ = lean_usize_to_uint64(v___x_509_);
v___x_511_ = 32ULL;
v___x_512_ = lean_uint64_shift_right(v___x_510_, v___x_511_);
v_fold_513_ = lean_uint64_xor(v___x_510_, v___x_512_);
v___x_514_ = 16ULL;
v___x_515_ = lean_uint64_shift_right(v_fold_513_, v___x_514_);
v___x_516_ = lean_uint64_xor(v_fold_513_, v___x_515_);
v___x_517_ = lean_uint64_to_usize(v___x_516_);
v___x_518_ = lean_usize_of_nat(v___x_506_);
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_sub(v___x_518_, v___x_519_);
v___x_521_ = lean_usize_land(v___x_517_, v___x_520_);
v_bkt_522_ = lean_array_uget_borrowed(v_buckets_502_, v___x_521_);
v___x_523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_499_, v_bkt_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v_size_x27_525_; lean_object* v___x_526_; lean_object* v_buckets_x27_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_524_ = lean_unsigned_to_nat(1u);
v_size_x27_525_ = lean_nat_add(v_size_501_, v___x_524_);
lean_dec(v_size_501_);
lean_inc(v_bkt_522_);
v___x_526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_526_, 0, v_a_499_);
lean_ctor_set(v___x_526_, 1, v_b_500_);
lean_ctor_set(v___x_526_, 2, v_bkt_522_);
v_buckets_x27_527_ = lean_array_uset(v_buckets_502_, v___x_521_, v___x_526_);
v___x_528_ = lean_unsigned_to_nat(4u);
v___x_529_ = lean_nat_mul(v_size_x27_525_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(3u);
v___x_531_ = lean_nat_div(v___x_529_, v___x_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_array_get_size(v_buckets_x27_527_);
v___x_533_ = lean_nat_dec_le(v___x_531_, v___x_532_);
lean_dec(v___x_531_);
if (v___x_533_ == 0)
{
lean_object* v_val_534_; lean_object* v___x_536_; 
v_val_534_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_527_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_val_534_);
lean_ctor_set(v___x_504_, 0, v_size_x27_525_);
v___x_536_ = v___x_504_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_size_x27_525_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_val_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
else
{
lean_object* v___x_539_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_buckets_x27_527_);
lean_ctor_set(v___x_504_, 0, v_size_x27_525_);
v___x_539_ = v___x_504_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_size_x27_525_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_buckets_x27_527_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
lean_object* v___x_541_; lean_object* v_buckets_x27_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
lean_inc(v_bkt_522_);
v___x_541_ = lean_box(0);
v_buckets_x27_542_ = lean_array_uset(v_buckets_502_, v___x_521_, v___x_541_);
v___x_543_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_499_, v_b_500_, v_bkt_522_);
v___x_544_ = lean_array_uset(v_buckets_x27_542_, v___x_521_, v___x_543_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_544_);
v___x_546_ = v___x_504_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_size_501_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
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
lean_object* v_map_554_; lean_object* v_set_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_579_; 
v_map_554_ = lean_ctor_get(v_a_553_, 0);
v_set_555_ = lean_ctor_get(v_a_553_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_553_);
if (v_isSharedCheck_579_ == 0)
{
v___x_557_ = v_a_553_;
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_set_555_);
lean_inc(v_map_554_);
lean_dec(v_a_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; uint64_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; size_t v___x_563_; size_t v___x_564_; uint8_t v___x_565_; 
v___x_559_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_560_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_552_);
v___x_561_ = lean_uint64_to_usize(v___x_560_);
v___x_562_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_555_, v___x_561_, v_r_552_, v___x_559_);
v___x_563_ = lean_ptr_addr(v___x_562_);
v___x_564_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_565_ = lean_usize_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec_ref(v_r_552_);
lean_inc_ref(v___x_562_);
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_554_, v_e_551_, v___x_562_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_566_);
v___x_568_ = v___x_557_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_set_555_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_562_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
return v___x_569_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
lean_dec_ref(v___x_562_);
lean_inc_ref_n(v_r_552_, 4);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_554_, v_e_551_, v_r_552_);
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_571_, v_r_552_, v_r_552_);
v___x_573_ = lean_box(0);
v___x_574_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_555_, v_r_552_, v___x_573_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_574_);
lean_ctor_set(v___x_557_, 0, v___x_572_);
v___x_576_ = v___x_557_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_r_552_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_580_, lean_object* v_r_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_580_, v_r_581_, v_a_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_585_, lean_object* v_r_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_585_, v_r_586_, v_a_587_, v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_590_, lean_object* v_x_591_, size_t v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_591_, v_x_592_, v_x_593_, v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
size_t v_x_2519__boxed_601_; lean_object* v_res_602_; 
v_x_2519__boxed_601_ = lean_unbox_usize(v_x_598_);
lean_dec(v_x_598_);
v_res_602_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_596_, v_x_597_, v_x_2519__boxed_601_, v_x_599_, v_x_600_);
lean_dec_ref(v_x_600_);
lean_dec_ref(v_x_599_);
lean_dec_ref(v_x_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_603_, lean_object* v_m_604_, lean_object* v_a_605_, lean_object* v_b_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_604_, v_a_605_, v_b_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_609_, v_x_610_, v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_613_, lean_object* v_keys_614_, lean_object* v_vals_615_, lean_object* v_heq_616_, lean_object* v_i_617_, lean_object* v_k_618_, lean_object* v_k_u2080_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_614_, v_i_617_, v_k_618_, v_k_u2080_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_621_, lean_object* v_keys_622_, lean_object* v_vals_623_, lean_object* v_heq_624_, lean_object* v_i_625_, lean_object* v_k_626_, lean_object* v_k_u2080_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_621_, v_keys_622_, v_vals_623_, v_heq_624_, v_i_625_, v_k_626_, v_k_u2080_627_);
lean_dec_ref(v_k_u2080_627_);
lean_dec_ref(v_k_626_);
lean_dec_ref(v_vals_623_);
lean_dec_ref(v_keys_622_);
return v_res_628_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_629_, lean_object* v_a_630_, lean_object* v_x_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_630_, v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_633_, v_a_634_, v_x_635_);
lean_dec(v_x_635_);
lean_dec_ref(v_a_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_638_, lean_object* v_data_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_641_, lean_object* v_a_642_, lean_object* v_b_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_642_, v_b_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_646_, lean_object* v_x_647_, size_t v_x_648_, size_t v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_647_, v_x_648_, v_x_649_, v_x_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
size_t v_x_2556__boxed_659_; size_t v_x_2557__boxed_660_; lean_object* v_res_661_; 
v_x_2556__boxed_659_ = lean_unbox_usize(v_x_655_);
lean_dec(v_x_655_);
v_x_2557__boxed_660_ = lean_unbox_usize(v_x_656_);
lean_dec(v_x_656_);
v_res_661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_653_, v_x_654_, v_x_2556__boxed_659_, v_x_2557__boxed_660_, v_x_657_, v_x_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_662_, lean_object* v_i_663_, lean_object* v_source_664_, lean_object* v_target_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_663_, v_source_664_, v_target_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_667_, lean_object* v_n_668_, lean_object* v_k_669_, lean_object* v_v_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_668_, v_k_669_, v_v_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_672_, size_t v_depth_673_, lean_object* v_keys_674_, lean_object* v_vals_675_, lean_object* v_heq_676_, lean_object* v_i_677_, lean_object* v_entries_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_673_, v_keys_674_, v_vals_675_, v_i_677_, v_entries_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_680_, lean_object* v_depth_681_, lean_object* v_keys_682_, lean_object* v_vals_683_, lean_object* v_heq_684_, lean_object* v_i_685_, lean_object* v_entries_686_){
_start:
{
size_t v_depth_boxed_687_; lean_object* v_res_688_; 
v_depth_boxed_687_ = lean_unbox_usize(v_depth_681_);
lean_dec(v_depth_681_);
v_res_688_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_680_, v_depth_boxed_687_, v_keys_682_, v_vals_683_, v_heq_684_, v_i_685_, v_entries_686_);
lean_dec_ref(v_vals_683_);
lean_dec_ref(v_keys_682_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_690_, v_x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_694_, v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_701_, lean_object* v_k_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_map_705_; lean_object* v_set_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___x_709_; 
v_map_705_ = lean_ctor_get(v_a_704_, 0);
v_set_706_ = lean_ctor_get(v_a_704_, 1);
v___f_707_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_708_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_701_);
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_707_, v___f_708_, v_map_705_, v_e_701_);
if (lean_obj_tag(v___x_709_) == 1)
{
lean_object* v_val_710_; lean_object* v___x_711_; 
lean_dec_ref(v_k_702_);
lean_dec_ref(v_e_701_);
v_val_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_val_710_);
lean_ctor_set(v___x_711_, 1, v_a_704_);
return v___x_711_;
}
else
{
lean_object* v___f_712_; lean_object* v___x_713_; uint64_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; size_t v___x_717_; size_t v___x_718_; uint8_t v___x_719_; 
lean_dec(v___x_709_);
v___f_712_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_713_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_714_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_701_);
v___x_715_ = lean_uint64_to_usize(v___x_714_);
lean_inc_ref(v_e_701_);
lean_inc_ref(v_set_706_);
v___x_716_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_712_, v_set_706_, v___x_715_, v_e_701_, v___x_713_);
v___x_717_ = lean_ptr_addr(v___x_716_);
v___x_718_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_719_ = lean_usize_dec_eq(v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec_ref(v_k_702_);
lean_dec_ref(v_e_701_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_716_);
lean_ctor_set(v___x_720_, 1, v_a_704_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; 
lean_dec(v___x_716_);
lean_inc_ref(v_a_703_);
v___x_721_ = lean_apply_2(v_k_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v_a_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
v_a_723_ = lean_ctor_get(v___x_721_, 1);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_721_, 2);
v___x_724_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_701_, v_a_722_, v_a_723_);
return v___x_724_;
}
else
{
lean_dec_ref(v_e_701_);
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_725_, lean_object* v_k_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_725_, v_k_726_, v_a_727_, v_a_728_);
lean_dec_ref(v_a_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
else
{
lean_object* v_key_733_; lean_object* v_value_734_; lean_object* v_tail_735_; size_t v___x_736_; size_t v___x_737_; uint8_t v___x_738_; 
v_key_733_ = lean_ctor_get(v_x_731_, 0);
v_value_734_ = lean_ctor_get(v_x_731_, 1);
v_tail_735_ = lean_ctor_get(v_x_731_, 2);
v___x_736_ = lean_ptr_addr(v_key_733_);
v___x_737_ = lean_ptr_addr(v_a_730_);
v___x_738_ = lean_usize_dec_eq(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
v_x_731_ = v_tail_735_;
goto _start;
}
else
{
lean_object* v___x_740_; 
lean_inc(v_value_734_);
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v_value_734_);
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_741_, lean_object* v_x_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_741_, v_x_742_);
lean_dec(v_x_742_);
lean_dec_ref(v_a_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_buckets_746_; lean_object* v___x_747_; size_t v___x_748_; size_t v___x_749_; size_t v___x_750_; uint64_t v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; uint64_t v_fold_754_; uint64_t v___x_755_; uint64_t v___x_756_; uint64_t v___x_757_; size_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_buckets_746_ = lean_ctor_get(v_m_744_, 1);
v___x_747_ = lean_array_get_size(v_buckets_746_);
v___x_748_ = lean_ptr_addr(v_a_745_);
v___x_749_ = ((size_t)3ULL);
v___x_750_ = lean_usize_shift_right(v___x_748_, v___x_749_);
v___x_751_ = lean_usize_to_uint64(v___x_750_);
v___x_752_ = 32ULL;
v___x_753_ = lean_uint64_shift_right(v___x_751_, v___x_752_);
v_fold_754_ = lean_uint64_xor(v___x_751_, v___x_753_);
v___x_755_ = 16ULL;
v___x_756_ = lean_uint64_shift_right(v_fold_754_, v___x_755_);
v___x_757_ = lean_uint64_xor(v_fold_754_, v___x_756_);
v___x_758_ = lean_uint64_to_usize(v___x_757_);
v___x_759_ = lean_usize_of_nat(v___x_747_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_sub(v___x_759_, v___x_760_);
v___x_762_ = lean_usize_land(v___x_758_, v___x_761_);
v___x_763_ = lean_array_uget_borrowed(v_buckets_746_, v___x_762_);
v___x_764_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_745_, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_765_, v_a_766_);
lean_dec_ref(v_a_766_);
lean_dec_ref(v_m_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_768_, lean_object* v_vals_769_, lean_object* v_i_770_, lean_object* v_k_771_){
_start:
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = lean_array_get_size(v_keys_768_);
v___x_773_ = lean_nat_dec_lt(v_i_770_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec(v_i_770_);
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v_k_x27_775_; uint8_t v___x_776_; 
v_k_x27_775_ = lean_array_fget_borrowed(v_keys_768_, v_i_770_);
v___x_776_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_771_, v_k_x27_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_add(v_i_770_, v___x_777_);
lean_dec(v_i_770_);
v_i_770_ = v___x_778_;
goto _start;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_array_fget_borrowed(v_vals_769_, v_i_770_);
lean_dec(v_i_770_);
lean_inc(v___x_780_);
lean_inc(v_k_x27_775_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_k_x27_775_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_783_, lean_object* v_vals_784_, lean_object* v_i_785_, lean_object* v_k_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_783_, v_vals_784_, v_i_785_, v_k_786_);
lean_dec_ref(v_k_786_);
lean_dec_ref(v_vals_784_);
lean_dec_ref(v_keys_783_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_788_, size_t v_x_789_, lean_object* v_x_790_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v_es_791_; lean_object* v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v_j_795_; lean_object* v___x_796_; 
v_es_791_ = lean_ctor_get(v_x_788_, 0);
v___x_792_ = lean_box(2);
v___x_793_ = ((size_t)31ULL);
v___x_794_ = lean_usize_land(v_x_789_, v___x_793_);
v_j_795_ = lean_usize_to_nat(v___x_794_);
v___x_796_ = lean_array_get_borrowed(v___x_792_, v_es_791_, v_j_795_);
lean_dec(v_j_795_);
switch(lean_obj_tag(v___x_796_))
{
case 0:
{
lean_object* v_key_797_; lean_object* v_val_798_; uint8_t v___x_799_; 
v_key_797_ = lean_ctor_get(v___x_796_, 0);
v_val_798_ = lean_ctor_get(v___x_796_, 1);
v___x_799_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_790_, v_key_797_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_inc(v_val_798_);
lean_inc(v_key_797_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_key_797_);
lean_ctor_set(v___x_801_, 1, v_val_798_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
case 1:
{
lean_object* v_node_803_; size_t v___x_804_; size_t v___x_805_; 
v_node_803_ = lean_ctor_get(v___x_796_, 0);
v___x_804_ = ((size_t)5ULL);
v___x_805_ = lean_usize_shift_right(v_x_789_, v___x_804_);
v_x_788_ = v_node_803_;
v_x_789_ = v___x_805_;
goto _start;
}
default: 
{
lean_object* v___x_807_; 
v___x_807_ = lean_box(0);
return v___x_807_;
}
}
}
else
{
lean_object* v_ks_808_; lean_object* v_vs_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_ks_808_ = lean_ctor_get(v_x_788_, 0);
v_vs_809_ = lean_ctor_get(v_x_788_, 1);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_808_, v_vs_809_, v___x_810_, v_x_790_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
size_t v_x_11088__boxed_815_; lean_object* v_res_816_; 
v_x_11088__boxed_815_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_res_816_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_812_, v_x_11088__boxed_815_, v_x_814_);
lean_dec_ref(v_x_814_);
lean_dec_ref(v_x_812_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
uint64_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_819_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_818_);
v___x_820_ = lean_uint64_to_usize(v___x_819_);
v___x_821_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_817_, v___x_820_, v_x_818_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_822_, v_x_823_);
lean_dec_ref(v_x_823_);
lean_dec_ref(v_x_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___y_829_; lean_object* v___y_834_; lean_object* v___y_839_; lean_object* v___y_844_; 
switch(lean_obj_tag(v_e_825_))
{
case 4:
{
lean_object* v_declName_848_; lean_object* v_map_849_; lean_object* v_set_850_; lean_object* v___x_851_; 
v_declName_848_ = lean_ctor_get(v_e_825_, 0);
v_map_849_ = lean_ctor_get(v_a_827_, 0);
v_set_850_ = lean_ctor_get(v_a_827_, 1);
v___x_851_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_850_, v_e_825_);
if (lean_obj_tag(v___x_851_) == 0)
{
uint8_t v___x_852_; 
lean_inc(v_declName_848_);
lean_inc_ref(v_a_826_);
v___x_852_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_826_, v_declName_848_);
if (v___x_852_ == 0)
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
lean_inc_ref(v_set_850_);
lean_inc_ref(v_map_849_);
v_isSharedCheck_862_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; lean_object* v_unused_864_; 
v_unused_863_ = lean_ctor_get(v_a_827_, 1);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_a_827_, 0);
lean_dec(v_unused_864_);
v___x_854_ = v_a_827_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_dec(v_a_827_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
lean_inc_ref(v_e_825_);
v___x_857_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_850_, v_e_825_, v___x_856_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_map_849_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_861_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_e_825_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
return v___x_860_;
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref_known(v_e_825_, 2);
v___x_865_ = lean_box(0);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v_a_827_);
return v___x_866_;
}
}
else
{
lean_object* v_val_867_; lean_object* v_fst_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref_known(v_e_825_, 2);
v_val_867_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v___x_851_, 1);
v_fst_868_ = lean_ctor_get(v_val_867_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_val_867_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v_val_867_, 1);
lean_dec(v_unused_876_);
v___x_870_ = v_val_867_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_fst_868_);
lean_dec(v_val_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v_a_827_);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_fst_868_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_827_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
case 5:
{
lean_object* v_fn_877_; lean_object* v_arg_878_; lean_object* v_map_879_; lean_object* v_set_880_; lean_object* v___x_881_; 
v_fn_877_ = lean_ctor_get(v_e_825_, 0);
v_arg_878_ = lean_ctor_get(v_e_825_, 1);
v_map_879_ = lean_ctor_get(v_a_827_, 0);
v_set_880_ = lean_ctor_get(v_a_827_, 1);
v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_879_, v_e_825_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_883_; 
lean_dec_ref_known(v_e_825_, 2);
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v_val_882_);
lean_ctor_set(v___x_883_, 1, v_a_827_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; uint64_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; uint8_t v___x_890_; 
lean_dec(v___x_881_);
v___x_884_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_885_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_825_);
v___x_886_ = lean_uint64_to_usize(v___x_885_);
v___x_887_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_880_, v___x_886_, v_e_825_, v___x_884_);
v___x_888_ = lean_ptr_addr(v___x_887_);
v___x_889_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_890_ = lean_usize_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec_ref_known(v_e_825_, 2);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_887_);
lean_ctor_set(v___x_891_, 1, v_a_827_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; 
lean_dec_ref(v___x_887_);
lean_inc_ref(v_fn_877_);
v___x_892_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_877_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v_a_894_; lean_object* v___x_895_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
v_a_894_ = lean_ctor_get(v___x_892_, 1);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_892_, 2);
lean_inc_ref(v_arg_878_);
v___x_895_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_878_, v_a_826_, v_a_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v_a_897_; size_t v___x_898_; size_t v___x_899_; uint8_t v___x_900_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
v_a_897_ = lean_ctor_get(v___x_895_, 1);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_895_, 2);
v___x_898_ = lean_ptr_addr(v_fn_877_);
v___x_899_ = lean_ptr_addr(v_a_893_);
v___x_900_ = lean_usize_dec_eq(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = l_Lean_Expr_app___override(v_a_893_, v_a_896_);
v___x_902_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_901_, v_a_897_);
return v___x_902_;
}
else
{
size_t v___x_903_; size_t v___x_904_; uint8_t v___x_905_; 
v___x_903_ = lean_ptr_addr(v_arg_878_);
v___x_904_ = lean_ptr_addr(v_a_896_);
v___x_905_ = lean_usize_dec_eq(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = l_Lean_Expr_app___override(v_a_893_, v_a_896_);
v___x_907_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_906_, v_a_897_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; 
lean_dec(v_a_896_);
lean_dec(v_a_893_);
lean_inc_ref(v_e_825_);
v___x_908_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_e_825_, v_a_897_);
return v___x_908_;
}
}
}
else
{
lean_dec(v_a_893_);
v___y_829_ = v___x_895_;
goto v___jp_828_;
}
}
else
{
v___y_829_ = v___x_892_;
goto v___jp_828_;
}
}
}
}
case 6:
{
lean_object* v_binderName_909_; lean_object* v_binderType_910_; lean_object* v_body_911_; uint8_t v_binderInfo_912_; lean_object* v_map_913_; lean_object* v_set_914_; lean_object* v___x_915_; 
v_binderName_909_ = lean_ctor_get(v_e_825_, 0);
v_binderType_910_ = lean_ctor_get(v_e_825_, 1);
v_body_911_ = lean_ctor_get(v_e_825_, 2);
v_binderInfo_912_ = lean_ctor_get_uint8(v_e_825_, sizeof(void*)*3 + 8);
v_map_913_ = lean_ctor_get(v_a_827_, 0);
v_set_914_ = lean_ctor_get(v_a_827_, 1);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_913_, v_e_825_);
if (lean_obj_tag(v___x_915_) == 1)
{
lean_object* v_val_916_; lean_object* v___x_917_; 
lean_dec_ref_known(v_e_825_, 3);
v_val_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_val_916_);
lean_ctor_set(v___x_917_, 1, v_a_827_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; uint64_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; size_t v___x_922_; size_t v___x_923_; uint8_t v___x_924_; 
lean_dec(v___x_915_);
v___x_918_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_919_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_825_);
v___x_920_ = lean_uint64_to_usize(v___x_919_);
v___x_921_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_914_, v___x_920_, v_e_825_, v___x_918_);
v___x_922_ = lean_ptr_addr(v___x_921_);
v___x_923_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_924_ = lean_usize_dec_eq(v___x_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
lean_dec_ref_known(v_e_825_, 3);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_921_);
lean_ctor_set(v___x_925_, 1, v_a_827_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; 
lean_dec_ref(v___x_921_);
lean_inc_ref(v_binderType_910_);
v___x_926_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_910_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v_a_928_; lean_object* v___x_929_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
v_a_928_ = lean_ctor_get(v___x_926_, 1);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_926_, 2);
lean_inc_ref(v_body_911_);
v___x_929_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_911_, v_a_826_, v_a_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v_a_931_; size_t v___x_932_; size_t v___x_933_; uint8_t v___x_934_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
v_a_931_ = lean_ctor_get(v___x_929_, 1);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_929_, 2);
v___x_932_ = lean_ptr_addr(v_binderType_910_);
v___x_933_ = lean_ptr_addr(v_a_927_);
v___x_934_ = lean_usize_dec_eq(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_inc(v_binderName_909_);
v___x_935_ = l_Lean_Expr_lam___override(v_binderName_909_, v_a_927_, v_a_930_, v_binderInfo_912_);
v___x_936_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_935_, v_a_931_);
return v___x_936_;
}
else
{
size_t v___x_937_; size_t v___x_938_; uint8_t v___x_939_; 
v___x_937_ = lean_ptr_addr(v_body_911_);
v___x_938_ = lean_ptr_addr(v_a_930_);
v___x_939_ = lean_usize_dec_eq(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; 
lean_inc(v_binderName_909_);
v___x_940_ = l_Lean_Expr_lam___override(v_binderName_909_, v_a_927_, v_a_930_, v_binderInfo_912_);
v___x_941_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_940_, v_a_931_);
return v___x_941_;
}
else
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_912_, v_binderInfo_912_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_inc(v_binderName_909_);
v___x_943_ = l_Lean_Expr_lam___override(v_binderName_909_, v_a_927_, v_a_930_, v_binderInfo_912_);
v___x_944_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_943_, v_a_931_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
lean_dec(v_a_930_);
lean_dec(v_a_927_);
lean_inc_ref(v_e_825_);
v___x_945_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_e_825_, v_a_931_);
return v___x_945_;
}
}
}
}
else
{
lean_dec(v_a_927_);
v___y_834_ = v___x_929_;
goto v___jp_833_;
}
}
else
{
v___y_834_ = v___x_926_;
goto v___jp_833_;
}
}
}
}
case 7:
{
lean_object* v_binderName_946_; lean_object* v_binderType_947_; lean_object* v_body_948_; uint8_t v_binderInfo_949_; lean_object* v_map_950_; lean_object* v_set_951_; lean_object* v___x_952_; 
v_binderName_946_ = lean_ctor_get(v_e_825_, 0);
v_binderType_947_ = lean_ctor_get(v_e_825_, 1);
v_body_948_ = lean_ctor_get(v_e_825_, 2);
v_binderInfo_949_ = lean_ctor_get_uint8(v_e_825_, sizeof(void*)*3 + 8);
v_map_950_ = lean_ctor_get(v_a_827_, 0);
v_set_951_ = lean_ctor_get(v_a_827_, 1);
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_950_, v_e_825_);
if (lean_obj_tag(v___x_952_) == 1)
{
lean_object* v_val_953_; lean_object* v___x_954_; 
lean_dec_ref_known(v_e_825_, 3);
v_val_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_val_953_);
lean_ctor_set(v___x_954_, 1, v_a_827_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; uint64_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; size_t v___x_959_; size_t v___x_960_; uint8_t v___x_961_; 
lean_dec(v___x_952_);
v___x_955_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_956_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_825_);
v___x_957_ = lean_uint64_to_usize(v___x_956_);
v___x_958_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_951_, v___x_957_, v_e_825_, v___x_955_);
v___x_959_ = lean_ptr_addr(v___x_958_);
v___x_960_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_961_ = lean_usize_dec_eq(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec_ref_known(v_e_825_, 3);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_958_);
lean_ctor_set(v___x_962_, 1, v_a_827_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
lean_dec_ref(v___x_958_);
lean_inc_ref(v_binderType_947_);
v___x_963_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_947_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
v_a_965_ = lean_ctor_get(v___x_963_, 1);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_963_, 2);
lean_inc_ref(v_body_948_);
v___x_966_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_948_, v_a_826_, v_a_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v_a_968_; size_t v___x_969_; size_t v___x_970_; uint8_t v___x_971_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
v_a_968_ = lean_ctor_get(v___x_966_, 1);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_966_, 2);
v___x_969_ = lean_ptr_addr(v_binderType_947_);
v___x_970_ = lean_ptr_addr(v_a_964_);
v___x_971_ = lean_usize_dec_eq(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc(v_binderName_946_);
v___x_972_ = l_Lean_Expr_forallE___override(v_binderName_946_, v_a_964_, v_a_967_, v_binderInfo_949_);
v___x_973_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_972_, v_a_968_);
return v___x_973_;
}
else
{
size_t v___x_974_; size_t v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_ptr_addr(v_body_948_);
v___x_975_ = lean_ptr_addr(v_a_967_);
v___x_976_ = lean_usize_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc(v_binderName_946_);
v___x_977_ = l_Lean_Expr_forallE___override(v_binderName_946_, v_a_964_, v_a_967_, v_binderInfo_949_);
v___x_978_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_977_, v_a_968_);
return v___x_978_;
}
else
{
uint8_t v___x_979_; 
v___x_979_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_949_, v_binderInfo_949_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_inc(v_binderName_946_);
v___x_980_ = l_Lean_Expr_forallE___override(v_binderName_946_, v_a_964_, v_a_967_, v_binderInfo_949_);
v___x_981_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_980_, v_a_968_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; 
lean_dec(v_a_967_);
lean_dec(v_a_964_);
lean_inc_ref(v_e_825_);
v___x_982_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_e_825_, v_a_968_);
return v___x_982_;
}
}
}
}
else
{
lean_dec(v_a_964_);
v___y_839_ = v___x_966_;
goto v___jp_838_;
}
}
else
{
v___y_839_ = v___x_963_;
goto v___jp_838_;
}
}
}
}
case 8:
{
lean_object* v_declName_983_; lean_object* v_type_984_; lean_object* v_value_985_; lean_object* v_body_986_; uint8_t v_nondep_987_; lean_object* v_map_988_; lean_object* v_set_989_; lean_object* v___x_990_; 
v_declName_983_ = lean_ctor_get(v_e_825_, 0);
v_type_984_ = lean_ctor_get(v_e_825_, 1);
v_value_985_ = lean_ctor_get(v_e_825_, 2);
v_body_986_ = lean_ctor_get(v_e_825_, 3);
v_nondep_987_ = lean_ctor_get_uint8(v_e_825_, sizeof(void*)*4 + 8);
v_map_988_ = lean_ctor_get(v_a_827_, 0);
v_set_989_ = lean_ctor_get(v_a_827_, 1);
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_988_, v_e_825_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_val_991_; lean_object* v___x_992_; 
lean_dec_ref_known(v_e_825_, 4);
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_val_991_);
lean_ctor_set(v___x_992_, 1, v_a_827_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; uint64_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; size_t v___x_997_; size_t v___x_998_; uint8_t v___x_999_; 
lean_dec(v___x_990_);
v___x_993_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_994_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_825_);
v___x_995_ = lean_uint64_to_usize(v___x_994_);
v___x_996_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_989_, v___x_995_, v_e_825_, v___x_993_);
v___x_997_ = lean_ptr_addr(v___x_996_);
v___x_998_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_999_ = lean_usize_dec_eq(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref_known(v_e_825_, 4);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_996_);
lean_ctor_set(v___x_1000_, 1, v_a_827_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; 
lean_dec_ref(v___x_996_);
lean_inc_ref(v_type_984_);
v___x_1001_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_984_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
v_a_1003_ = lean_ctor_get(v___x_1001_, 1);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1001_, 2);
lean_inc_ref(v_value_985_);
v___x_1004_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_985_, v_a_826_, v_a_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
v_a_1006_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1004_, 2);
lean_inc_ref(v_body_986_);
v___x_1007_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_986_, v_a_826_, v_a_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v_a_1009_; size_t v___x_1010_; size_t v___x_1011_; uint8_t v___x_1012_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
v_a_1009_ = lean_ctor_get(v___x_1007_, 1);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1007_, 2);
v___x_1010_ = lean_ptr_addr(v_type_984_);
v___x_1011_ = lean_ptr_addr(v_a_1002_);
v___x_1012_ = lean_usize_dec_eq(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_inc(v_declName_983_);
v___x_1013_ = l_Lean_Expr_letE___override(v_declName_983_, v_a_1002_, v_a_1005_, v_a_1008_, v_nondep_987_);
v___x_1014_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_1013_, v_a_1009_);
return v___x_1014_;
}
else
{
size_t v___x_1015_; size_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1015_ = lean_ptr_addr(v_value_985_);
v___x_1016_ = lean_ptr_addr(v_a_1005_);
v___x_1017_ = lean_usize_dec_eq(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_inc(v_declName_983_);
v___x_1018_ = l_Lean_Expr_letE___override(v_declName_983_, v_a_1002_, v_a_1005_, v_a_1008_, v_nondep_987_);
v___x_1019_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_1018_, v_a_1009_);
return v___x_1019_;
}
else
{
size_t v___x_1020_; size_t v___x_1021_; uint8_t v___x_1022_; 
v___x_1020_ = lean_ptr_addr(v_body_986_);
v___x_1021_ = lean_ptr_addr(v_a_1008_);
v___x_1022_ = lean_usize_dec_eq(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_inc(v_declName_983_);
v___x_1023_ = l_Lean_Expr_letE___override(v_declName_983_, v_a_1002_, v_a_1005_, v_a_1008_, v_nondep_987_);
v___x_1024_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_1023_, v_a_1009_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; 
lean_dec(v_a_1008_);
lean_dec(v_a_1005_);
lean_dec(v_a_1002_);
lean_inc_ref(v_e_825_);
v___x_1025_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_e_825_, v_a_1009_);
return v___x_1025_;
}
}
}
}
else
{
lean_dec(v_a_1005_);
lean_dec(v_a_1002_);
v___y_844_ = v___x_1007_;
goto v___jp_843_;
}
}
else
{
lean_dec(v_a_1002_);
v___y_844_ = v___x_1004_;
goto v___jp_843_;
}
}
else
{
v___y_844_ = v___x_1001_;
goto v___jp_843_;
}
}
}
}
case 10:
{
lean_object* v_data_1026_; lean_object* v_expr_1027_; lean_object* v_map_1028_; lean_object* v_set_1029_; lean_object* v___x_1030_; 
v_data_1026_ = lean_ctor_get(v_e_825_, 0);
v_expr_1027_ = lean_ctor_get(v_e_825_, 1);
v_map_1028_ = lean_ctor_get(v_a_827_, 0);
v_set_1029_ = lean_ctor_get(v_a_827_, 1);
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1028_, v_e_825_);
if (lean_obj_tag(v___x_1030_) == 1)
{
lean_object* v_val_1031_; lean_object* v___x_1032_; 
lean_dec_ref_known(v_e_825_, 2);
v_val_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_val_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_val_1031_);
lean_ctor_set(v___x_1032_, 1, v_a_827_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; uint64_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; uint8_t v___x_1039_; 
lean_dec(v___x_1030_);
v___x_1033_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1034_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_825_);
v___x_1035_ = lean_uint64_to_usize(v___x_1034_);
v___x_1036_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1029_, v___x_1035_, v_e_825_, v___x_1033_);
v___x_1037_ = lean_ptr_addr(v___x_1036_);
v___x_1038_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1039_ = lean_usize_dec_eq(v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref_known(v_e_825_, 2);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1036_);
lean_ctor_set(v___x_1040_, 1, v_a_827_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; 
lean_dec_ref(v___x_1036_);
lean_inc_ref(v_expr_1027_);
v___x_1041_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1027_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v_a_1043_; size_t v___x_1044_; size_t v___x_1045_; uint8_t v___x_1046_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
v_a_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1041_, 2);
v___x_1044_ = lean_ptr_addr(v_expr_1027_);
v___x_1045_ = lean_ptr_addr(v_a_1042_);
v___x_1046_ = lean_usize_dec_eq(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_inc(v_data_1026_);
v___x_1047_ = l_Lean_Expr_mdata___override(v_data_1026_, v_a_1042_);
v___x_1048_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_1047_, v_a_1043_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; 
lean_dec(v_a_1042_);
lean_inc_ref(v_e_825_);
v___x_1049_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_e_825_, v_a_1043_);
return v___x_1049_;
}
}
else
{
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1050_; lean_object* v_a_1051_; lean_object* v___x_1052_; 
v_a_1050_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1050_);
v_a_1051_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1041_, 2);
v___x_1052_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_a_1050_, v_a_1051_);
return v___x_1052_;
}
else
{
lean_dec_ref_known(v_e_825_, 2);
return v___x_1041_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1053_; lean_object* v_idx_1054_; lean_object* v_struct_1055_; lean_object* v_map_1056_; lean_object* v_set_1057_; lean_object* v___x_1058_; 
v_typeName_1053_ = lean_ctor_get(v_e_825_, 0);
v_idx_1054_ = lean_ctor_get(v_e_825_, 1);
v_struct_1055_ = lean_ctor_get(v_e_825_, 2);
v_map_1056_ = lean_ctor_get(v_a_827_, 0);
v_set_1057_ = lean_ctor_get(v_a_827_, 1);
v___x_1058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1056_, v_e_825_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1060_; 
lean_dec_ref_known(v_e_825_, 3);
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_val_1059_);
lean_ctor_set(v___x_1060_, 1, v_a_827_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; uint64_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; uint8_t v___x_1067_; 
lean_dec(v___x_1058_);
v___x_1061_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1062_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_825_);
v___x_1063_ = lean_uint64_to_usize(v___x_1062_);
v___x_1064_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1057_, v___x_1063_, v_e_825_, v___x_1061_);
v___x_1065_ = lean_ptr_addr(v___x_1064_);
v___x_1066_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1067_ = lean_usize_dec_eq(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_dec_ref_known(v_e_825_, 3);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1064_);
lean_ctor_set(v___x_1068_, 1, v_a_827_);
return v___x_1068_;
}
else
{
uint8_t v_checkProj_1069_; 
lean_dec_ref(v___x_1064_);
v_checkProj_1069_ = lean_ctor_get_uint8(v_a_826_, sizeof(void*)*1 + 1);
if (v_checkProj_1069_ == 0)
{
lean_object* v___x_1070_; 
lean_inc_ref(v_struct_1055_);
v___x_1070_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1055_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v_a_1072_; size_t v___x_1073_; size_t v___x_1074_; uint8_t v___x_1075_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
v_a_1072_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1070_, 2);
v___x_1073_ = lean_ptr_addr(v_struct_1055_);
v___x_1074_ = lean_ptr_addr(v_a_1071_);
v___x_1075_ = lean_usize_dec_eq(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_inc(v_idx_1054_);
lean_inc(v_typeName_1053_);
v___x_1076_ = l_Lean_Expr_proj___override(v_typeName_1053_, v_idx_1054_, v_a_1071_);
v___x_1077_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v___x_1076_, v_a_1072_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; 
lean_dec(v_a_1071_);
lean_inc_ref(v_e_825_);
v___x_1078_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_e_825_, v_a_1072_);
return v___x_1078_;
}
}
else
{
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; 
v_a_1079_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1079_);
v_a_1080_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1070_, 2);
v___x_1081_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_a_1079_, v_a_1080_);
return v___x_1081_;
}
else
{
lean_dec_ref_known(v_e_825_, 3);
return v___x_1070_;
}
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec_ref_known(v_e_825_, 3);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_a_827_);
return v___x_1083_;
}
}
}
}
default: 
{
lean_object* v_map_1084_; lean_object* v_set_1085_; lean_object* v___x_1086_; 
v_map_1084_ = lean_ctor_get(v_a_827_, 0);
v_set_1085_ = lean_ctor_get(v_a_827_, 1);
v___x_1086_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1085_, v_e_825_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1096_; 
lean_inc_ref(v_set_1085_);
lean_inc_ref(v_map_1084_);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1097_ = lean_ctor_get(v_a_827_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_a_827_, 0);
lean_dec(v_unused_1098_);
v___x_1088_ = v_a_827_;
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v_a_827_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1090_ = lean_box(0);
lean_inc_ref(v_e_825_);
v___x_1091_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1085_, v_e_825_, v___x_1090_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_map_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_e_825_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
return v___x_1094_;
}
}
}
else
{
lean_object* v_val_1099_; lean_object* v_fst_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v_e_825_);
v_val_1099_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v___x_1086_, 1);
v_fst_1100_ = lean_ctor_get(v_val_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_val_1099_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; 
v_unused_1108_ = lean_ctor_get(v_val_1099_, 1);
lean_dec(v_unused_1108_);
v___x_1102_ = v_val_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_fst_1100_);
lean_dec(v_val_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v_a_827_);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_fst_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_a_827_);
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
}
v___jp_828_:
{
if (lean_obj_tag(v___y_829_) == 0)
{
lean_object* v_a_830_; lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_830_ = lean_ctor_get(v___y_829_, 0);
lean_inc(v_a_830_);
v_a_831_ = lean_ctor_get(v___y_829_, 1);
lean_inc(v_a_831_);
lean_dec_ref_known(v___y_829_, 2);
v___x_832_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_a_830_, v_a_831_);
return v___x_832_;
}
else
{
lean_dec_ref(v_e_825_);
return v___y_829_;
}
}
v___jp_833_:
{
if (lean_obj_tag(v___y_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_835_ = lean_ctor_get(v___y_834_, 0);
lean_inc(v_a_835_);
v_a_836_ = lean_ctor_get(v___y_834_, 1);
lean_inc(v_a_836_);
lean_dec_ref_known(v___y_834_, 2);
v___x_837_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_a_835_, v_a_836_);
return v___x_837_;
}
else
{
lean_dec_ref(v_e_825_);
return v___y_834_;
}
}
v___jp_838_:
{
if (lean_obj_tag(v___y_839_) == 0)
{
lean_object* v_a_840_; lean_object* v_a_841_; lean_object* v___x_842_; 
v_a_840_ = lean_ctor_get(v___y_839_, 0);
lean_inc(v_a_840_);
v_a_841_ = lean_ctor_get(v___y_839_, 1);
lean_inc(v_a_841_);
lean_dec_ref_known(v___y_839_, 2);
v___x_842_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_a_840_, v_a_841_);
return v___x_842_;
}
else
{
lean_dec_ref(v_e_825_);
return v___y_839_;
}
}
v___jp_843_:
{
if (lean_obj_tag(v___y_844_) == 0)
{
lean_object* v_a_845_; lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_845_ = lean_ctor_get(v___y_844_, 0);
lean_inc(v_a_845_);
v_a_846_ = lean_ctor_get(v___y_844_, 1);
lean_inc(v_a_846_);
lean_dec_ref_known(v___y_844_, 2);
v___x_847_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_825_, v_a_845_, v_a_846_);
return v___x_847_;
}
else
{
lean_dec_ref(v_e_825_);
return v___y_844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1109_, v_a_1110_, v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1117_, v_x_1118_, v_x_1119_);
lean_dec_ref(v_x_1119_);
lean_dec_ref(v_x_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1121_, lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1122_, v_a_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1125_, lean_object* v_m_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1125_, v_m_1126_, v_a_1127_);
lean_dec_ref(v_a_1127_);
lean_dec_ref(v_m_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1129_, lean_object* v_x_1130_, size_t v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1130_, v_x_1131_, v_x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
size_t v_x_11734__boxed_1138_; lean_object* v_res_1139_; 
v_x_11734__boxed_1138_ = lean_unbox_usize(v_x_1136_);
lean_dec(v_x_1136_);
v_res_1139_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1134_, v_x_1135_, v_x_11734__boxed_1138_, v_x_1137_);
lean_dec_ref(v_x_1137_);
lean_dec_ref(v_x_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1140_, lean_object* v_a_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1141_, v_x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1144_, lean_object* v_a_1145_, lean_object* v_x_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1144_, v_a_1145_, v_x_1146_);
lean_dec(v_x_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1148_, lean_object* v_keys_1149_, lean_object* v_vals_1150_, lean_object* v_heq_1151_, lean_object* v_i_1152_, lean_object* v_k_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1149_, v_vals_1150_, v_i_1152_, v_k_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1155_, lean_object* v_keys_1156_, lean_object* v_vals_1157_, lean_object* v_heq_1158_, lean_object* v_i_1159_, lean_object* v_k_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1155_, v_keys_1156_, v_vals_1157_, v_heq_1158_, v_i_1159_, v_k_1160_);
lean_dec_ref(v_k_1160_);
lean_dec_ref(v_vals_1157_);
lean_dec_ref(v_keys_1156_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1162_, lean_object* v_cache_1163_, lean_object* v_ctx_1164_, lean_object* v_s_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; 
v___f_1166_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1167_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1162_);
v___x_1168_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1166_, v___f_1167_, v_s_1165_, v_e_1162_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_cache_1163_);
lean_ctor_set(v___x_1169_, 1, v_s_1165_);
v___x_1170_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1162_, v_ctx_1164_, v___x_1169_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 1);
v_a_1172_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v___x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1171_);
lean_inc(v_a_1172_);
lean_dec(v___x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_set_1176_; lean_object* v___x_1178_; 
v_set_1176_ = lean_ctor_get(v_a_1171_, 1);
lean_inc_ref(v_set_1176_);
lean_dec(v_a_1171_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_set_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1172_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_set_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1190_; 
v_a_1181_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v___x_1170_, 0);
lean_dec(v_unused_1191_);
v___x_1183_ = v___x_1170_;
v_isShared_1184_ = v_isSharedCheck_1190_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1170_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1190_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_map_1185_; lean_object* v_set_1186_; lean_object* v___x_1188_; 
v_map_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_ref(v_map_1185_);
v_set_1186_ = lean_ctor_get(v_a_1181_, 1);
lean_inc_ref(v_set_1186_);
lean_dec(v_a_1181_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_set_1186_);
lean_ctor_set(v___x_1183_, 0, v_map_1185_);
v___x_1188_ = v___x_1183_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_map_1185_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_set_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_val_1192_; lean_object* v_fst_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_cache_1163_);
lean_dec_ref(v_e_1162_);
v_val_1192_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v___x_1168_, 1);
v_fst_1193_ = lean_ctor_get(v_val_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_val_1192_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_val_1192_, 1);
lean_dec(v_unused_1201_);
v___x_1195_ = v_val_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_fst_1193_);
lean_dec(v_val_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_s_1165_);
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_fst_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_s_1165_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1202_, lean_object* v_cache_1203_, lean_object* v_ctx_1204_, lean_object* v_s_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1202_, v_cache_1203_, v_ctx_1204_, v_s_1205_);
lean_dec_ref(v_ctx_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v___x_1209_; uint64_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1209_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1210_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1207_);
v___x_1211_ = lean_uint64_to_usize(v___x_1210_);
v___x_1212_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1208_, v___x_1211_, v_e_1207_, v___x_1209_);
v___x_1213_ = lean_ptr_addr(v___x_1212_);
v___x_1214_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec_ref(v_e_1207_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1212_);
lean_ctor_set(v___x_1216_, 1, v_a_1208_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec_ref(v___x_1212_);
v___x_1217_ = lean_box(0);
lean_inc_ref(v_e_1207_);
v___x_1218_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1208_, v_e_1207_, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_e_1207_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1220_, v_a_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1224_, v_a_1225_, v_a_1226_);
lean_dec_ref(v_a_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1228_, lean_object* v_k_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___f_1232_; lean_object* v___x_1233_; uint64_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; uint8_t v___x_1239_; 
v___f_1232_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1233_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1234_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1228_);
v___x_1235_ = lean_uint64_to_usize(v___x_1234_);
lean_inc_ref(v_a_1231_);
v___x_1236_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1232_, v_a_1231_, v___x_1235_, v_e_1228_, v___x_1233_);
v___x_1237_ = lean_ptr_addr(v___x_1236_);
v___x_1238_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1239_ = lean_usize_dec_eq(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_k_1229_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1236_);
lean_ctor_set(v___x_1240_, 1, v_a_1231_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; 
lean_dec(v___x_1236_);
lean_inc_ref(v_a_1230_);
v___x_1241_ = lean_apply_2(v_k_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
v_a_1243_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1241_, 2);
v___x_1244_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1242_, v_a_1243_);
return v___x_1244_;
}
else
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1245_, lean_object* v_k_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1245_, v_k_1246_, v_a_1247_, v_a_1248_);
lean_dec_ref(v_a_1247_);
return v_res_1249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_unsigned_to_nat(16u);
v___x_1252_ = lean_mk_array(v___x_1251_, v___x_1250_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___y_1260_; lean_object* v___y_1265_; lean_object* v___y_1270_; lean_object* v___y_1275_; 
switch(lean_obj_tag(v_e_1256_))
{
case 4:
{
lean_object* v_declName_1279_; lean_object* v___x_1280_; uint64_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; uint8_t v___x_1286_; 
v_declName_1279_ = lean_ctor_get(v_e_1256_, 0);
v___x_1280_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1281_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1256_);
v___x_1282_ = lean_uint64_to_usize(v___x_1281_);
v___x_1283_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1258_, v___x_1282_, v_e_1256_, v___x_1280_);
v___x_1284_ = lean_ptr_addr(v___x_1283_);
v___x_1285_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1286_ = lean_usize_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec_ref_known(v_e_1256_, 2);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1283_);
lean_ctor_set(v___x_1287_, 1, v_a_1258_);
return v___x_1287_;
}
else
{
uint8_t v___x_1288_; 
lean_dec_ref(v___x_1283_);
lean_inc(v_declName_1279_);
lean_inc_ref(v_a_1257_);
v___x_1288_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1257_, v_declName_1279_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_box(0);
lean_inc_ref(v_e_1256_);
v___x_1290_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1258_, v_e_1256_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_e_1256_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref_known(v_e_1256_, 2);
v___x_1292_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v_a_1258_);
return v___x_1293_;
}
}
}
case 5:
{
lean_object* v_fn_1294_; lean_object* v_arg_1295_; lean_object* v___x_1296_; uint64_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; uint8_t v___x_1302_; 
v_fn_1294_ = lean_ctor_get(v_e_1256_, 0);
v_arg_1295_ = lean_ctor_get(v_e_1256_, 1);
v___x_1296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1297_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1256_);
v___x_1298_ = lean_uint64_to_usize(v___x_1297_);
v___x_1299_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1258_, v___x_1298_, v_e_1256_, v___x_1296_);
v___x_1300_ = lean_ptr_addr(v___x_1299_);
v___x_1301_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1302_ = lean_usize_dec_eq(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec_ref_known(v_e_1256_, 2);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1299_);
lean_ctor_set(v___x_1303_, 1, v_a_1258_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; 
lean_dec_ref(v___x_1299_);
lean_inc_ref(v_fn_1294_);
v___x_1304_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1294_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v_a_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
v_a_1306_ = lean_ctor_get(v___x_1304_, 1);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1304_, 2);
lean_inc_ref(v_arg_1295_);
v___x_1307_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1295_, v_a_1257_, v_a_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v_a_1309_; size_t v___x_1310_; size_t v___x_1311_; uint8_t v___x_1312_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
v_a_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1307_, 2);
v___x_1310_ = lean_ptr_addr(v_fn_1294_);
v___x_1311_ = lean_ptr_addr(v_a_1305_);
v___x_1312_ = lean_usize_dec_eq(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec_ref_known(v_e_1256_, 2);
v___x_1313_ = l_Lean_Expr_app___override(v_a_1305_, v_a_1308_);
v___x_1314_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1313_, v_a_1309_);
return v___x_1314_;
}
else
{
size_t v___x_1315_; size_t v___x_1316_; uint8_t v___x_1317_; 
v___x_1315_ = lean_ptr_addr(v_arg_1295_);
v___x_1316_ = lean_ptr_addr(v_a_1308_);
v___x_1317_ = lean_usize_dec_eq(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref_known(v_e_1256_, 2);
v___x_1318_ = l_Lean_Expr_app___override(v_a_1305_, v_a_1308_);
v___x_1319_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1318_, v_a_1309_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
lean_dec(v_a_1308_);
lean_dec(v_a_1305_);
v___x_1320_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1256_, v_a_1309_);
return v___x_1320_;
}
}
}
else
{
lean_dec(v_a_1305_);
lean_dec_ref_known(v_e_1256_, 2);
v___y_1260_ = v___x_1307_;
goto v___jp_1259_;
}
}
else
{
lean_dec_ref_known(v_e_1256_, 2);
v___y_1260_ = v___x_1304_;
goto v___jp_1259_;
}
}
}
case 6:
{
lean_object* v_binderName_1321_; lean_object* v_binderType_1322_; lean_object* v_body_1323_; uint8_t v_binderInfo_1324_; lean_object* v___x_1325_; uint64_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; uint8_t v___x_1331_; 
v_binderName_1321_ = lean_ctor_get(v_e_1256_, 0);
v_binderType_1322_ = lean_ctor_get(v_e_1256_, 1);
v_body_1323_ = lean_ctor_get(v_e_1256_, 2);
v_binderInfo_1324_ = lean_ctor_get_uint8(v_e_1256_, sizeof(void*)*3 + 8);
v___x_1325_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1326_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1256_);
v___x_1327_ = lean_uint64_to_usize(v___x_1326_);
v___x_1328_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1258_, v___x_1327_, v_e_1256_, v___x_1325_);
v___x_1329_ = lean_ptr_addr(v___x_1328_);
v___x_1330_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1331_ = lean_usize_dec_eq(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec_ref_known(v_e_1256_, 3);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1328_);
lean_ctor_set(v___x_1332_, 1, v_a_1258_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; 
lean_dec_ref(v___x_1328_);
lean_inc_ref(v_binderType_1322_);
v___x_1333_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1322_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_a_1335_; lean_object* v___x_1336_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
v_a_1335_ = lean_ctor_get(v___x_1333_, 1);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1333_, 2);
lean_inc_ref(v_body_1323_);
v___x_1336_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1323_, v_a_1257_, v_a_1335_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v_a_1338_; size_t v___x_1339_; size_t v___x_1340_; uint8_t v___x_1341_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
v_a_1338_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1336_, 2);
v___x_1339_ = lean_ptr_addr(v_binderType_1322_);
v___x_1340_ = lean_ptr_addr(v_a_1334_);
v___x_1341_ = lean_usize_dec_eq(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_inc(v_binderName_1321_);
lean_dec_ref_known(v_e_1256_, 3);
v___x_1342_ = l_Lean_Expr_lam___override(v_binderName_1321_, v_a_1334_, v_a_1337_, v_binderInfo_1324_);
v___x_1343_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1342_, v_a_1338_);
return v___x_1343_;
}
else
{
size_t v___x_1344_; size_t v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = lean_ptr_addr(v_body_1323_);
v___x_1345_ = lean_ptr_addr(v_a_1337_);
v___x_1346_ = lean_usize_dec_eq(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_inc(v_binderName_1321_);
lean_dec_ref_known(v_e_1256_, 3);
v___x_1347_ = l_Lean_Expr_lam___override(v_binderName_1321_, v_a_1334_, v_a_1337_, v_binderInfo_1324_);
v___x_1348_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1347_, v_a_1338_);
return v___x_1348_;
}
else
{
uint8_t v___x_1349_; 
v___x_1349_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1324_, v_binderInfo_1324_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_inc(v_binderName_1321_);
lean_dec_ref_known(v_e_1256_, 3);
v___x_1350_ = l_Lean_Expr_lam___override(v_binderName_1321_, v_a_1334_, v_a_1337_, v_binderInfo_1324_);
v___x_1351_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1350_, v_a_1338_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; 
lean_dec(v_a_1337_);
lean_dec(v_a_1334_);
v___x_1352_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1256_, v_a_1338_);
return v___x_1352_;
}
}
}
}
else
{
lean_dec(v_a_1334_);
lean_dec_ref_known(v_e_1256_, 3);
v___y_1265_ = v___x_1336_;
goto v___jp_1264_;
}
}
else
{
lean_dec_ref_known(v_e_1256_, 3);
v___y_1265_ = v___x_1333_;
goto v___jp_1264_;
}
}
}
case 7:
{
lean_object* v_binderName_1353_; lean_object* v_binderType_1354_; lean_object* v_body_1355_; uint8_t v_binderInfo_1356_; lean_object* v___x_1357_; uint64_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; uint8_t v___x_1363_; 
v_binderName_1353_ = lean_ctor_get(v_e_1256_, 0);
v_binderType_1354_ = lean_ctor_get(v_e_1256_, 1);
v_body_1355_ = lean_ctor_get(v_e_1256_, 2);
v_binderInfo_1356_ = lean_ctor_get_uint8(v_e_1256_, sizeof(void*)*3 + 8);
v___x_1357_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1358_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1256_);
v___x_1359_ = lean_uint64_to_usize(v___x_1358_);
v___x_1360_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1258_, v___x_1359_, v_e_1256_, v___x_1357_);
v___x_1361_ = lean_ptr_addr(v___x_1360_);
v___x_1362_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1363_ = lean_usize_dec_eq(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_dec_ref_known(v_e_1256_, 3);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1360_);
lean_ctor_set(v___x_1364_, 1, v_a_1258_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; 
lean_dec_ref(v___x_1360_);
lean_inc_ref(v_binderType_1354_);
v___x_1365_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1354_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
v_a_1367_ = lean_ctor_get(v___x_1365_, 1);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1365_, 2);
lean_inc_ref(v_body_1355_);
v___x_1368_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1355_, v_a_1257_, v_a_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_a_1370_; size_t v___x_1371_; size_t v___x_1372_; uint8_t v___x_1373_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
v_a_1370_ = lean_ctor_get(v___x_1368_, 1);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1368_, 2);
v___x_1371_ = lean_ptr_addr(v_binderType_1354_);
v___x_1372_ = lean_ptr_addr(v_a_1366_);
v___x_1373_ = lean_usize_dec_eq(v___x_1371_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc(v_binderName_1353_);
lean_dec_ref_known(v_e_1256_, 3);
v___x_1374_ = l_Lean_Expr_forallE___override(v_binderName_1353_, v_a_1366_, v_a_1369_, v_binderInfo_1356_);
v___x_1375_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1374_, v_a_1370_);
return v___x_1375_;
}
else
{
size_t v___x_1376_; size_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = lean_ptr_addr(v_body_1355_);
v___x_1377_ = lean_ptr_addr(v_a_1369_);
v___x_1378_ = lean_usize_dec_eq(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_inc(v_binderName_1353_);
lean_dec_ref_known(v_e_1256_, 3);
v___x_1379_ = l_Lean_Expr_forallE___override(v_binderName_1353_, v_a_1366_, v_a_1369_, v_binderInfo_1356_);
v___x_1380_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1379_, v_a_1370_);
return v___x_1380_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1356_, v_binderInfo_1356_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_inc(v_binderName_1353_);
lean_dec_ref_known(v_e_1256_, 3);
v___x_1382_ = l_Lean_Expr_forallE___override(v_binderName_1353_, v_a_1366_, v_a_1369_, v_binderInfo_1356_);
v___x_1383_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1382_, v_a_1370_);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; 
lean_dec(v_a_1369_);
lean_dec(v_a_1366_);
v___x_1384_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1256_, v_a_1370_);
return v___x_1384_;
}
}
}
}
else
{
lean_dec(v_a_1366_);
lean_dec_ref_known(v_e_1256_, 3);
v___y_1270_ = v___x_1368_;
goto v___jp_1269_;
}
}
else
{
lean_dec_ref_known(v_e_1256_, 3);
v___y_1270_ = v___x_1365_;
goto v___jp_1269_;
}
}
}
case 8:
{
lean_object* v_declName_1385_; lean_object* v_type_1386_; lean_object* v_value_1387_; lean_object* v_body_1388_; uint8_t v_nondep_1389_; lean_object* v___x_1390_; uint64_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v_declName_1385_ = lean_ctor_get(v_e_1256_, 0);
v_type_1386_ = lean_ctor_get(v_e_1256_, 1);
v_value_1387_ = lean_ctor_get(v_e_1256_, 2);
v_body_1388_ = lean_ctor_get(v_e_1256_, 3);
v_nondep_1389_ = lean_ctor_get_uint8(v_e_1256_, sizeof(void*)*4 + 8);
v___x_1390_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1391_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1256_);
v___x_1392_ = lean_uint64_to_usize(v___x_1391_);
v___x_1393_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1258_, v___x_1392_, v_e_1256_, v___x_1390_);
v___x_1394_ = lean_ptr_addr(v___x_1393_);
v___x_1395_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref_known(v_e_1256_, 4);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1393_);
lean_ctor_set(v___x_1397_, 1, v_a_1258_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
lean_dec_ref(v___x_1393_);
lean_inc_ref(v_type_1386_);
v___x_1398_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1386_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_a_1400_; lean_object* v___x_1401_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
v_a_1400_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1398_, 2);
lean_inc_ref(v_value_1387_);
v___x_1401_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1387_, v_a_1257_, v_a_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v_a_1403_; lean_object* v___x_1404_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
v_a_1403_ = lean_ctor_get(v___x_1401_, 1);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1401_, 2);
lean_inc_ref(v_body_1388_);
v___x_1404_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1388_, v_a_1257_, v_a_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_a_1406_; size_t v___x_1407_; size_t v___x_1408_; uint8_t v___x_1409_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
v_a_1406_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1404_, 2);
v___x_1407_ = lean_ptr_addr(v_type_1386_);
v___x_1408_ = lean_ptr_addr(v_a_1399_);
v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_inc(v_declName_1385_);
lean_dec_ref_known(v_e_1256_, 4);
v___x_1410_ = l_Lean_Expr_letE___override(v_declName_1385_, v_a_1399_, v_a_1402_, v_a_1405_, v_nondep_1389_);
v___x_1411_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1410_, v_a_1406_);
return v___x_1411_;
}
else
{
size_t v___x_1412_; size_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = lean_ptr_addr(v_value_1387_);
v___x_1413_ = lean_ptr_addr(v_a_1402_);
v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_inc(v_declName_1385_);
lean_dec_ref_known(v_e_1256_, 4);
v___x_1415_ = l_Lean_Expr_letE___override(v_declName_1385_, v_a_1399_, v_a_1402_, v_a_1405_, v_nondep_1389_);
v___x_1416_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1415_, v_a_1406_);
return v___x_1416_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = lean_ptr_addr(v_body_1388_);
v___x_1418_ = lean_ptr_addr(v_a_1405_);
v___x_1419_ = lean_usize_dec_eq(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_inc(v_declName_1385_);
lean_dec_ref_known(v_e_1256_, 4);
v___x_1420_ = l_Lean_Expr_letE___override(v_declName_1385_, v_a_1399_, v_a_1402_, v_a_1405_, v_nondep_1389_);
v___x_1421_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1420_, v_a_1406_);
return v___x_1421_;
}
else
{
lean_object* v___x_1422_; 
lean_dec(v_a_1405_);
lean_dec(v_a_1402_);
lean_dec(v_a_1399_);
v___x_1422_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1256_, v_a_1406_);
return v___x_1422_;
}
}
}
}
else
{
lean_dec(v_a_1402_);
lean_dec(v_a_1399_);
lean_dec_ref_known(v_e_1256_, 4);
v___y_1275_ = v___x_1404_;
goto v___jp_1274_;
}
}
else
{
lean_dec(v_a_1399_);
lean_dec_ref_known(v_e_1256_, 4);
v___y_1275_ = v___x_1401_;
goto v___jp_1274_;
}
}
else
{
lean_dec_ref_known(v_e_1256_, 4);
v___y_1275_ = v___x_1398_;
goto v___jp_1274_;
}
}
}
case 10:
{
lean_object* v_data_1423_; lean_object* v_expr_1424_; lean_object* v___x_1425_; uint64_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; uint8_t v___x_1431_; 
v_data_1423_ = lean_ctor_get(v_e_1256_, 0);
v_expr_1424_ = lean_ctor_get(v_e_1256_, 1);
v___x_1425_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1426_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1256_);
v___x_1427_ = lean_uint64_to_usize(v___x_1426_);
v___x_1428_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1258_, v___x_1427_, v_e_1256_, v___x_1425_);
v___x_1429_ = lean_ptr_addr(v___x_1428_);
v___x_1430_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1431_ = lean_usize_dec_eq(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec_ref_known(v_e_1256_, 2);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1428_);
lean_ctor_set(v___x_1432_, 1, v_a_1258_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_dec_ref(v___x_1428_);
lean_inc_ref(v_expr_1424_);
v___x_1433_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1424_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v_a_1435_; size_t v___x_1436_; size_t v___x_1437_; uint8_t v___x_1438_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
v_a_1435_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1433_, 2);
v___x_1436_ = lean_ptr_addr(v_expr_1424_);
v___x_1437_ = lean_ptr_addr(v_a_1434_);
v___x_1438_ = lean_usize_dec_eq(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_inc(v_data_1423_);
lean_dec_ref_known(v_e_1256_, 2);
v___x_1439_ = l_Lean_Expr_mdata___override(v_data_1423_, v_a_1434_);
v___x_1440_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1439_, v_a_1435_);
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; 
lean_dec(v_a_1434_);
v___x_1441_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1256_, v_a_1435_);
return v___x_1441_;
}
}
else
{
lean_dec_ref_known(v_e_1256_, 2);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1442_; lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1442_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1442_);
v_a_1443_ = lean_ctor_get(v___x_1433_, 1);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1433_, 2);
v___x_1444_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1442_, v_a_1443_);
return v___x_1444_;
}
else
{
return v___x_1433_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1445_; lean_object* v_idx_1446_; lean_object* v_struct_1447_; lean_object* v___x_1448_; uint64_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; uint8_t v___x_1454_; 
v_typeName_1445_ = lean_ctor_get(v_e_1256_, 0);
v_idx_1446_ = lean_ctor_get(v_e_1256_, 1);
v_struct_1447_ = lean_ctor_get(v_e_1256_, 2);
v___x_1448_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1449_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1256_);
v___x_1450_ = lean_uint64_to_usize(v___x_1449_);
v___x_1451_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1258_, v___x_1450_, v_e_1256_, v___x_1448_);
v___x_1452_ = lean_ptr_addr(v___x_1451_);
v___x_1453_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1454_ = lean_usize_dec_eq(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref_known(v_e_1256_, 3);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1451_);
lean_ctor_set(v___x_1455_, 1, v_a_1258_);
return v___x_1455_;
}
else
{
uint8_t v_checkProj_1456_; 
lean_dec_ref(v___x_1451_);
v_checkProj_1456_ = lean_ctor_get_uint8(v_a_1257_, sizeof(void*)*1 + 1);
if (v_checkProj_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_inc_ref(v_struct_1447_);
v___x_1457_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1447_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v_a_1459_; size_t v___x_1460_; size_t v___x_1461_; uint8_t v___x_1462_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
v_a_1459_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1457_, 2);
v___x_1460_ = lean_ptr_addr(v_struct_1447_);
v___x_1461_ = lean_ptr_addr(v_a_1458_);
v___x_1462_ = lean_usize_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_inc(v_idx_1446_);
lean_inc(v_typeName_1445_);
lean_dec_ref_known(v_e_1256_, 3);
v___x_1463_ = l_Lean_Expr_proj___override(v_typeName_1445_, v_idx_1446_, v_a_1458_);
v___x_1464_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1463_, v_a_1459_);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; 
lean_dec(v_a_1458_);
v___x_1465_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1256_, v_a_1459_);
return v___x_1465_;
}
}
else
{
lean_dec_ref_known(v_e_1256_, 3);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1466_; lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1466_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1466_);
v_a_1467_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1457_, 2);
v___x_1468_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1466_, v_a_1467_);
return v___x_1468_;
}
else
{
return v___x_1457_;
}
}
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref_known(v_e_1256_, 3);
v___x_1469_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v_a_1258_);
return v___x_1470_;
}
}
}
default: 
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1256_, v_a_1258_);
return v___x_1471_;
}
}
v___jp_1259_:
{
if (lean_obj_tag(v___y_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1261_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_a_1261_);
v_a_1262_ = lean_ctor_get(v___y_1260_, 1);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___y_1260_, 2);
v___x_1263_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1261_, v_a_1262_);
return v___x_1263_;
}
else
{
return v___y_1260_;
}
}
v___jp_1264_:
{
if (lean_obj_tag(v___y_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v___x_1268_; 
v_a_1266_ = lean_ctor_get(v___y_1265_, 0);
lean_inc(v_a_1266_);
v_a_1267_ = lean_ctor_get(v___y_1265_, 1);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___y_1265_, 2);
v___x_1268_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1266_, v_a_1267_);
return v___x_1268_;
}
else
{
return v___y_1265_;
}
}
v___jp_1269_:
{
if (lean_obj_tag(v___y_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1271_ = lean_ctor_get(v___y_1270_, 0);
lean_inc(v_a_1271_);
v_a_1272_ = lean_ctor_get(v___y_1270_, 1);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___y_1270_, 2);
v___x_1273_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1271_, v_a_1272_);
return v___x_1273_;
}
else
{
return v___y_1270_;
}
}
v___jp_1274_:
{
if (lean_obj_tag(v___y_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1276_ = lean_ctor_get(v___y_1275_, 0);
lean_inc(v_a_1276_);
v_a_1277_ = lean_ctor_get(v___y_1275_, 1);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___y_1275_, 2);
v___x_1278_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1276_, v_a_1277_);
return v___x_1278_;
}
else
{
return v___y_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1472_, v_a_1473_, v_a_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1476_, v_a_1477_, v_a_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1480_, v_a_1481_, v_a_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1483_;
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

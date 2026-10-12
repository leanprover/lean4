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
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(lean_object* v_e_1_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
uint64_t v_res_24_;
v_res_24_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_e_1_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild___boxed(lean_object* v_e_25_){
_start:
{
uint64_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_e_25_);
lean_dec_ref(v_e_25_);
v_r_27_ = lean_box_uint64(v_res_26_);
return v_r_27_;
}
}
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object* v_e_28_){
_start:
{
lean_object* v_d_30_; lean_object* v_b_31_; 
switch(lean_obj_tag(v_e_28_))
{
case 5:
{
lean_object* v_fn_35_; lean_object* v_arg_36_; uint64_t v___x_37_; uint64_t v___x_38_; uint64_t v___x_39_; 
v_fn_35_ = lean_ctor_get(v_e_28_, 0);
v_arg_36_ = lean_ctor_get(v_e_28_, 1);
v___x_37_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_fn_35_);
v___x_38_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_arg_36_);
v___x_39_ = lean_uint64_mix_hash(v___x_37_, v___x_38_);
return v___x_39_;
}
case 6:
{
lean_object* v_binderType_40_; lean_object* v_body_41_; 
v_binderType_40_ = lean_ctor_get(v_e_28_, 1);
v_body_41_ = lean_ctor_get(v_e_28_, 2);
v_d_30_ = v_binderType_40_;
v_b_31_ = v_body_41_;
goto v___jp_29_;
}
case 7:
{
lean_object* v_binderType_42_; lean_object* v_body_43_; 
v_binderType_42_ = lean_ctor_get(v_e_28_, 1);
v_body_43_ = lean_ctor_get(v_e_28_, 2);
v_d_30_ = v_binderType_42_;
v_b_31_ = v_body_43_;
goto v___jp_29_;
}
case 8:
{
lean_object* v_value_44_; lean_object* v_body_45_; uint8_t v_nondep_46_; uint64_t v___y_48_; 
v_value_44_ = lean_ctor_get(v_e_28_, 2);
v_body_45_ = lean_ctor_get(v_e_28_, 3);
v_nondep_46_ = lean_ctor_get_uint8(v_e_28_, sizeof(void*)*4 + 8);
if (v_nondep_46_ == 0)
{
uint64_t v___x_53_; 
v___x_53_ = 19ULL;
v___y_48_ = v___x_53_;
goto v___jp_47_;
}
else
{
uint64_t v___x_54_; 
v___x_54_ = 17ULL;
v___y_48_ = v___x_54_;
goto v___jp_47_;
}
v___jp_47_:
{
uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; 
v___x_49_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_value_44_);
v___x_50_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_body_45_);
v___x_51_ = lean_uint64_mix_hash(v___x_49_, v___x_50_);
v___x_52_ = lean_uint64_mix_hash(v___y_48_, v___x_51_);
return v___x_52_;
}
}
case 10:
{
lean_object* v_expr_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; 
v_expr_55_ = lean_ctor_get(v_e_28_, 1);
v___x_56_ = 13ULL;
v___x_57_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_expr_55_);
v___x_58_ = lean_uint64_mix_hash(v___x_56_, v___x_57_);
return v___x_58_;
}
case 11:
{
lean_object* v_typeName_59_; lean_object* v_idx_60_; lean_object* v_struct_61_; uint64_t v___y_63_; 
v_typeName_59_ = lean_ctor_get(v_e_28_, 0);
v_idx_60_ = lean_ctor_get(v_e_28_, 1);
v_struct_61_ = lean_ctor_get(v_e_28_, 2);
if (lean_obj_tag(v_typeName_59_) == 0)
{
uint64_t v___x_68_; 
v___x_68_ = 1723ULL;
v___y_63_ = v___x_68_;
goto v___jp_62_;
}
else
{
uint64_t v_hash_69_; 
v_hash_69_ = lean_ctor_get_uint64(v_typeName_59_, sizeof(void*)*2);
v___y_63_ = v_hash_69_;
goto v___jp_62_;
}
v___jp_62_:
{
uint64_t v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; 
v___x_64_ = lean_uint64_of_nat(v_idx_60_);
v___x_65_ = lean_uint64_mix_hash(v___y_63_, v___x_64_);
v___x_66_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_struct_61_);
v___x_67_ = lean_uint64_mix_hash(v___x_65_, v___x_66_);
return v___x_67_;
}
}
default: 
{
uint64_t v___x_70_; 
v___x_70_ = l_Lean_Expr_hash(v_e_28_);
return v___x_70_;
}
}
v___jp_29_:
{
uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v___x_34_; 
v___x_32_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_d_30_);
v___x_33_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_b_31_);
v___x_34_ = lean_uint64_mix_hash(v___x_32_, v___x_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_28_ = stack[0].m_obj;
uint64_t v_res_71_;
v_res_71_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_28_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object* v_e_72_){
_start:
{
uint64_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_72_);
lean_dec_ref(v_e_72_);
v_r_74_ = lean_box_uint64(v_res_73_);
return v_r_74_;
}
}
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object* v_e_u2081_75_, lean_object* v_e_u2082_76_){
_start:
{
switch(lean_obj_tag(v_e_u2081_75_))
{
case 5:
{
if (lean_obj_tag(v_e_u2082_76_) == 5)
{
lean_object* v_fn_77_; lean_object* v_arg_78_; lean_object* v_fn_79_; lean_object* v_arg_80_; size_t v___x_81_; size_t v___x_82_; uint8_t v___x_83_; 
v_fn_77_ = lean_ctor_get(v_e_u2081_75_, 0);
v_arg_78_ = lean_ctor_get(v_e_u2081_75_, 1);
v_fn_79_ = lean_ctor_get(v_e_u2082_76_, 0);
v_arg_80_ = lean_ctor_get(v_e_u2082_76_, 1);
v___x_81_ = lean_ptr_addr(v_fn_77_);
v___x_82_ = lean_ptr_addr(v_fn_79_);
v___x_83_ = lean_usize_dec_eq(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
return v___x_83_;
}
else
{
size_t v___x_84_; size_t v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_ptr_addr(v_arg_78_);
v___x_85_ = lean_ptr_addr(v_arg_80_);
v___x_86_ = lean_usize_dec_eq(v___x_84_, v___x_85_);
return v___x_86_;
}
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_76_) == 6)
{
lean_object* v_binderType_88_; lean_object* v_body_89_; lean_object* v_binderType_90_; lean_object* v_body_91_; size_t v___x_92_; size_t v___x_93_; uint8_t v___x_94_; 
v_binderType_88_ = lean_ctor_get(v_e_u2081_75_, 1);
v_body_89_ = lean_ctor_get(v_e_u2081_75_, 2);
v_binderType_90_ = lean_ctor_get(v_e_u2082_76_, 1);
v_body_91_ = lean_ctor_get(v_e_u2082_76_, 2);
v___x_92_ = lean_ptr_addr(v_binderType_88_);
v___x_93_ = lean_ptr_addr(v_binderType_90_);
v___x_94_ = lean_usize_dec_eq(v___x_92_, v___x_93_);
if (v___x_94_ == 0)
{
return v___x_94_;
}
else
{
size_t v___x_95_; size_t v___x_96_; uint8_t v___x_97_; 
v___x_95_ = lean_ptr_addr(v_body_89_);
v___x_96_ = lean_ptr_addr(v_body_91_);
v___x_97_ = lean_usize_dec_eq(v___x_95_, v___x_96_);
return v___x_97_;
}
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_76_) == 7)
{
lean_object* v_binderType_99_; lean_object* v_body_100_; lean_object* v_binderType_101_; lean_object* v_body_102_; size_t v___x_103_; size_t v___x_104_; uint8_t v___x_105_; 
v_binderType_99_ = lean_ctor_get(v_e_u2081_75_, 1);
v_body_100_ = lean_ctor_get(v_e_u2081_75_, 2);
v_binderType_101_ = lean_ctor_get(v_e_u2082_76_, 1);
v_body_102_ = lean_ctor_get(v_e_u2082_76_, 2);
v___x_103_ = lean_ptr_addr(v_binderType_99_);
v___x_104_ = lean_ptr_addr(v_binderType_101_);
v___x_105_ = lean_usize_dec_eq(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
return v___x_105_;
}
else
{
size_t v___x_106_; size_t v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_ptr_addr(v_body_100_);
v___x_107_ = lean_ptr_addr(v_body_102_);
v___x_108_ = lean_usize_dec_eq(v___x_106_, v___x_107_);
return v___x_108_;
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_76_) == 8)
{
lean_object* v_value_110_; lean_object* v_body_111_; uint8_t v_nondep_112_; lean_object* v_value_113_; lean_object* v_body_114_; uint8_t v_nondep_115_; 
v_value_110_ = lean_ctor_get(v_e_u2081_75_, 2);
v_body_111_ = lean_ctor_get(v_e_u2081_75_, 3);
v_nondep_112_ = lean_ctor_get_uint8(v_e_u2081_75_, sizeof(void*)*4 + 8);
v_value_113_ = lean_ctor_get(v_e_u2082_76_, 2);
v_body_114_ = lean_ctor_get(v_e_u2082_76_, 3);
v_nondep_115_ = lean_ctor_get_uint8(v_e_u2082_76_, sizeof(void*)*4 + 8);
if (v_nondep_115_ == 0)
{
if (v_nondep_112_ == 0)
{
goto v___jp_116_;
}
else
{
return v_nondep_115_;
}
}
else
{
if (v_nondep_112_ == 0)
{
return v_nondep_112_;
}
else
{
goto v___jp_116_;
}
}
v___jp_116_:
{
size_t v___x_117_; size_t v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_ptr_addr(v_value_110_);
v___x_118_ = lean_ptr_addr(v_value_113_);
v___x_119_ = lean_usize_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
size_t v___x_120_; size_t v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_ptr_addr(v_body_111_);
v___x_121_ = lean_ptr_addr(v_body_114_);
v___x_122_ = lean_usize_dec_eq(v___x_120_, v___x_121_);
return v___x_122_;
}
}
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_76_) == 10)
{
lean_object* v_data_124_; lean_object* v_expr_125_; lean_object* v_data_126_; lean_object* v_expr_127_; size_t v___x_128_; size_t v___x_129_; uint8_t v___x_130_; 
v_data_124_ = lean_ctor_get(v_e_u2081_75_, 0);
v_expr_125_ = lean_ctor_get(v_e_u2081_75_, 1);
v_data_126_ = lean_ctor_get(v_e_u2082_76_, 0);
v_expr_127_ = lean_ctor_get(v_e_u2082_76_, 1);
v___x_128_ = lean_ptr_addr(v_expr_125_);
v___x_129_ = lean_ptr_addr(v_expr_127_);
v___x_130_ = lean_usize_dec_eq(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_KVMap_eqv(v_data_124_, v_data_126_);
return v___x_131_;
}
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_76_) == 11)
{
lean_object* v_typeName_133_; lean_object* v_idx_134_; lean_object* v_struct_135_; lean_object* v_typeName_136_; lean_object* v_idx_137_; lean_object* v_struct_138_; uint8_t v___y_140_; uint8_t v___x_144_; 
v_typeName_133_ = lean_ctor_get(v_e_u2081_75_, 0);
v_idx_134_ = lean_ctor_get(v_e_u2081_75_, 1);
v_struct_135_ = lean_ctor_get(v_e_u2081_75_, 2);
v_typeName_136_ = lean_ctor_get(v_e_u2082_76_, 0);
v_idx_137_ = lean_ctor_get(v_e_u2082_76_, 1);
v_struct_138_ = lean_ctor_get(v_e_u2082_76_, 2);
v___x_144_ = lean_name_eq(v_typeName_133_, v_typeName_136_);
if (v___x_144_ == 0)
{
v___y_140_ = v___x_144_;
goto v___jp_139_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_eq(v_idx_134_, v_idx_137_);
v___y_140_ = v___x_145_;
goto v___jp_139_;
}
v___jp_139_:
{
if (v___y_140_ == 0)
{
return v___y_140_;
}
else
{
size_t v___x_141_; size_t v___x_142_; uint8_t v___x_143_; 
v___x_141_ = lean_ptr_addr(v_struct_135_);
v___x_142_ = lean_ptr_addr(v_struct_138_);
v___x_143_ = lean_usize_dec_eq(v___x_141_, v___x_142_);
return v___x_143_;
}
}
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
default: 
{
uint8_t v___x_147_; 
v___x_147_ = lean_expr_eqv(v_e_u2081_75_, v_e_u2082_76_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_75_ = stack[0].m_obj;
lean_object* v_e_u2082_76_ = stack[1].m_obj;
uint8_t v_res_148_;
v_res_148_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_e_u2081_75_, v_e_u2082_76_);
stack->m_num = v_res_148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object* v_e_u2081_149_, lean_object* v_e_u2082_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_e_u2081_149_, v_e_u2082_150_);
lean_dec_ref(v_e_u2082_150_);
lean_dec_ref(v_e_u2081_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_170_){
_start:
{
uint8_t v___y_172_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__5));
v___x_176_ = lean_name_eq(v_declName_170_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__7));
v___x_178_ = lean_name_eq(v_declName_170_, v___x_177_);
v___y_172_ = v___x_178_;
goto v___jp_171_;
}
else
{
v___y_172_ = v___x_176_;
goto v___jp_171_;
}
v___jp_171_:
{
if (v___y_172_ == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_174_ = lean_name_eq(v_declName_170_, v___x_173_);
return v___x_174_;
}
else
{
return v___y_172_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isGrindGadget_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_170_ = stack[0].m_obj;
uint8_t v_res_179_;
v_res_179_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_170_);
stack->m_num = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_180_);
lean_dec(v_declName_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object* v_env_183_, lean_object* v_declName_184_){
_start:
{
uint8_t v___x_185_; 
lean_inc(v_declName_184_);
lean_inc_ref(v_env_183_);
v___x_185_ = l_Lean_getReducibilityStatusCore(v_env_183_, v_declName_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_184_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
v___x_187_ = l_Lean_Environment_isProjectionFn(v_env_183_, v_declName_184_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 1;
return v___x_188_;
}
else
{
return v___x_186_;
}
}
else
{
uint8_t v___x_189_; 
lean_dec(v_declName_184_);
lean_dec_ref(v_env_183_);
v___x_189_ = 0;
return v___x_189_;
}
}
else
{
uint8_t v___x_190_; 
lean_dec(v_declName_184_);
lean_dec_ref(v_env_183_);
v___x_190_ = 0;
return v___x_190_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_isUnfoldReducibleCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_183_ = stack[0].m_obj;
lean_object* v_declName_184_ = stack[1].m_obj;
uint8_t v_res_191_;
v_res_191_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_183_, v_declName_184_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object* v_env_192_, lean_object* v_declName_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_192_, v_declName_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_196_){
_start:
{
uint64_t v___x_197_; 
v___x_197_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instHashableAlphaKey___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_196_ = stack[0].m_obj;
uint64_t v_res_198_;
v_res_198_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_196_);
stack->m_num = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_199_){
_start:
{
uint64_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_199_);
lean_dec_ref(v_k_199_);
v_r_201_ = lean_box_uint64(v_res_200_);
return v_r_201_;
}
}
uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_204_, lean_object* v_k_u2082_205_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_204_, v_k_u2082_205_);
return v___x_206_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_instBEqAlphaKey___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_u2081_204_ = stack[0].m_obj;
lean_object* v_k_u2082_205_ = stack[1].m_obj;
uint8_t v_res_207_;
v_res_207_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_204_, v_k_u2082_205_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_208_, lean_object* v_k_u2082_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_208_, v_k_u2082_209_);
lean_dec_ref(v_k_u2082_209_);
lean_dec_ref(v_k_u2081_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object* v_ctx_214_, lean_object* v_declName_215_){
_start:
{
uint8_t v_checkReducible_216_; 
v_checkReducible_216_ = lean_ctor_get_uint8(v_ctx_214_, sizeof(void*)*1);
if (v_checkReducible_216_ == 0)
{
lean_dec(v_declName_215_);
lean_dec_ref(v_ctx_214_);
return v_checkReducible_216_;
}
else
{
lean_object* v_env_217_; uint8_t v___x_218_; 
v_env_217_ = lean_ctor_get(v_ctx_214_, 0);
lean_inc_ref(v_env_217_);
lean_dec_ref(v_ctx_214_);
v___x_218_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_217_, v_declName_215_);
return v___x_218_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_214_ = stack[0].m_obj;
lean_object* v_declName_215_ = stack[1].m_obj;
uint8_t v_res_219_;
v_res_219_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_214_, v_declName_215_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object* v_ctx_220_, lean_object* v_declName_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_220_, v_declName_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_box(0);
v___x_228_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_229_ = l_Lean_mkConst(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_231_, lean_object* v_i_232_, lean_object* v_k_233_, lean_object* v_k_u2080_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_get_size(v_keys_231_);
v___x_236_ = lean_nat_dec_lt(v_i_232_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_i_232_);
lean_inc_ref(v_k_u2080_234_);
return v_k_u2080_234_;
}
else
{
lean_object* v_k_x27_237_; uint8_t v___x_238_; 
v_k_x27_237_ = lean_array_fget_borrowed(v_keys_231_, v_i_232_);
v___x_238_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_233_, v_k_x27_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_i_232_, v___x_239_);
lean_dec(v_i_232_);
v_i_232_ = v___x_240_;
goto _start;
}
else
{
lean_dec(v_i_232_);
lean_inc(v_k_x27_237_);
return v_k_x27_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_242_, lean_object* v_i_243_, lean_object* v_k_244_, lean_object* v_k_u2080_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_242_, v_i_243_, v_k_244_, v_k_u2080_245_);
lean_dec_ref(v_k_u2080_245_);
lean_dec_ref(v_k_244_);
lean_dec_ref(v_keys_242_);
return v_res_246_;
}
}
lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_247_, size_t v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_object* v_es_251_; lean_object* v___x_252_; size_t v___x_253_; size_t v___x_254_; lean_object* v_j_255_; lean_object* v___x_256_; 
v_es_251_ = lean_ctor_get(v_x_247_, 0);
v___x_252_ = lean_box(2);
v___x_253_ = ((size_t)31ULL);
v___x_254_ = lean_usize_land(v_x_248_, v___x_253_);
v_j_255_ = lean_usize_to_nat(v___x_254_);
v___x_256_ = lean_array_get_borrowed(v___x_252_, v_es_251_, v_j_255_);
lean_dec(v_j_255_);
switch(lean_obj_tag(v___x_256_))
{
case 0:
{
lean_object* v_key_257_; uint8_t v___x_258_; 
v_key_257_ = lean_ctor_get(v___x_256_, 0);
v___x_258_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_249_, v_key_257_);
if (v___x_258_ == 0)
{
lean_inc_ref(v_x_250_);
return v_x_250_;
}
else
{
lean_inc(v_key_257_);
return v_key_257_;
}
}
case 1:
{
lean_object* v_node_259_; size_t v___x_260_; size_t v___x_261_; 
v_node_259_ = lean_ctor_get(v___x_256_, 0);
v___x_260_ = ((size_t)5ULL);
v___x_261_ = lean_usize_shift_right(v_x_248_, v___x_260_);
v_x_247_ = v_node_259_;
v_x_248_ = v___x_261_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_250_);
return v_x_250_;
}
}
}
else
{
lean_object* v_ks_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_ks_263_ = lean_ctor_get(v_x_247_, 0);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_263_, v___x_264_, v_x_249_, v_x_250_);
return v___x_265_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_247_ = stack[0].m_obj;
size_t v_x_248_ = stack[1].m_num;
lean_object* v_x_249_ = stack[2].m_obj;
lean_object* v_x_250_ = stack[3].m_obj;
lean_object* v_res_266_;
v_res_266_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_247_, v_x_248_, v_x_249_, v_x_250_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
size_t v_x_1954__boxed_271_; lean_object* v_res_272_; 
v_x_1954__boxed_271_ = lean_unbox_usize(v_x_268_);
lean_dec(v_x_268_);
v_res_272_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_267_, v_x_1954__boxed_271_, v_x_269_, v_x_270_);
lean_dec_ref(v_x_270_);
lean_dec_ref(v_x_269_);
lean_dec_ref(v_x_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
lean_object* v_ks_277_; lean_object* v_vs_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_302_; 
v_ks_277_ = lean_ctor_get(v_x_273_, 0);
v_vs_278_ = lean_ctor_get(v_x_273_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_302_ == 0)
{
v___x_280_ = v_x_273_;
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_vs_278_);
lean_inc(v_ks_277_);
lean_dec(v_x_273_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_array_get_size(v_ks_277_);
v___x_283_ = lean_nat_dec_lt(v_x_274_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_dec(v_x_274_);
v___x_284_ = lean_array_push(v_ks_277_, v_x_275_);
v___x_285_ = lean_array_push(v_vs_278_, v_x_276_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_285_);
lean_ctor_set(v___x_280_, 0, v___x_284_);
v___x_287_ = v___x_280_;
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
else
{
lean_object* v_k_x27_289_; uint8_t v___x_290_; 
v_k_x27_289_ = lean_array_fget_borrowed(v_ks_277_, v_x_274_);
v___x_290_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_275_, v_k_x27_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_292_; 
if (v_isShared_281_ == 0)
{
v___x_292_ = v___x_280_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_ks_277_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_vs_278_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_x_274_, v___x_293_);
lean_dec(v_x_274_);
v_x_273_ = v___x_292_;
v_x_274_ = v___x_294_;
goto _start;
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_297_ = lean_array_fset(v_ks_277_, v_x_274_, v_x_275_);
v___x_298_ = lean_array_fset(v_vs_278_, v_x_274_, v_x_276_);
lean_dec(v_x_274_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_298_);
lean_ctor_set(v___x_280_, 0, v___x_297_);
v___x_300_ = v___x_280_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_303_, lean_object* v_k_304_, lean_object* v_v_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_303_, v___x_306_, v_k_304_, v_v_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_308_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_309_, size_t v_x_310_, size_t v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v_es_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v_j_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_es_314_ = lean_ctor_get(v_x_309_, 0);
v___x_315_ = ((size_t)31ULL);
v___x_316_ = lean_usize_land(v_x_310_, v___x_315_);
v_j_317_ = lean_usize_to_nat(v___x_316_);
v___x_318_ = lean_array_get_size(v_es_314_);
v___x_319_ = lean_nat_dec_lt(v_j_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_dec(v_j_317_);
lean_dec(v_x_313_);
lean_dec_ref(v_x_312_);
return v_x_309_;
}
else
{
lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_358_; 
lean_inc_ref(v_es_314_);
v_isSharedCheck_358_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v_x_309_, 0);
lean_dec(v_unused_359_);
v___x_321_ = v_x_309_;
v_isShared_322_ = v_isSharedCheck_358_;
goto v_resetjp_320_;
}
else
{
lean_dec(v_x_309_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_358_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_v_323_; lean_object* v___x_324_; lean_object* v_xs_x27_325_; lean_object* v___y_327_; 
v_v_323_ = lean_array_fget(v_es_314_, v_j_317_);
v___x_324_ = lean_box(0);
v_xs_x27_325_ = lean_array_fset(v_es_314_, v_j_317_, v___x_324_);
switch(lean_obj_tag(v_v_323_))
{
case 0:
{
lean_object* v_key_332_; lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_343_; 
v_key_332_ = lean_ctor_get(v_v_323_, 0);
v_val_333_ = lean_ctor_get(v_v_323_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_v_323_);
if (v_isSharedCheck_343_ == 0)
{
v___x_335_ = v_v_323_;
v_isShared_336_ = v_isSharedCheck_343_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_inc(v_key_332_);
lean_dec(v_v_323_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_343_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
uint8_t v___x_337_; 
v___x_337_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_312_, v_key_332_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_del_object(v___x_335_);
v___x_338_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_332_, v_val_333_, v_x_312_, v_x_313_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___y_327_ = v___x_339_;
goto v___jp_326_;
}
else
{
lean_object* v___x_341_; 
lean_dec(v_val_333_);
lean_dec(v_key_332_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_x_313_);
lean_ctor_set(v___x_335_, 0, v_x_312_);
v___x_341_ = v___x_335_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_x_312_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_x_313_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
v___y_327_ = v___x_341_;
goto v___jp_326_;
}
}
}
}
case 1:
{
lean_object* v_node_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_356_; 
v_node_344_ = lean_ctor_get(v_v_323_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_v_323_);
if (v_isSharedCheck_356_ == 0)
{
v___x_346_ = v_v_323_;
v_isShared_347_ = v_isSharedCheck_356_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_node_344_);
lean_dec(v_v_323_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_356_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_348_ = ((size_t)5ULL);
v___x_349_ = lean_usize_shift_right(v_x_310_, v___x_348_);
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_add(v_x_311_, v___x_350_);
v___x_352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_344_, v___x_349_, v___x_351_, v_x_312_, v_x_313_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_352_);
v___x_354_ = v___x_346_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
v___y_327_ = v___x_354_;
goto v___jp_326_;
}
}
}
default: 
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_x_312_);
lean_ctor_set(v___x_357_, 1, v_x_313_);
v___y_327_ = v___x_357_;
goto v___jp_326_;
}
}
v___jp_326_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_array_fset(v_xs_x27_325_, v_j_317_, v___y_327_);
lean_dec(v_j_317_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_328_);
v___x_330_ = v___x_321_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
else
{
lean_object* v_ks_360_; lean_object* v_vs_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_379_; 
v_ks_360_ = lean_ctor_get(v_x_309_, 0);
v_vs_361_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_379_ == 0)
{
v___x_363_ = v_x_309_;
v_isShared_364_ = v_isSharedCheck_379_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_vs_361_);
lean_inc(v_ks_360_);
lean_dec(v_x_309_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_379_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_ks_360_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_vs_361_);
v___x_366_ = v_reuseFailAlloc_378_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v_newNode_367_; size_t v___x_368_; uint8_t v___x_369_; 
v_newNode_367_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_366_, v_x_312_, v_x_313_);
v___x_368_ = ((size_t)7ULL);
v___x_369_ = lean_usize_dec_le(v___x_368_, v_x_311_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_367_);
v___x_371_ = lean_unsigned_to_nat(4u);
v___x_372_ = lean_nat_dec_lt(v___x_370_, v___x_371_);
lean_dec(v___x_370_);
if (v___x_372_ == 0)
{
lean_object* v_ks_373_; lean_object* v_vs_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_ks_373_ = lean_ctor_get(v_newNode_367_, 0);
lean_inc_ref(v_ks_373_);
v_vs_374_ = lean_ctor_get(v_newNode_367_, 1);
lean_inc_ref(v_vs_374_);
lean_dec_ref(v_newNode_367_);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_311_, v_ks_373_, v_vs_374_, v___x_375_, v___x_376_);
lean_dec_ref(v_vs_374_);
lean_dec_ref(v_ks_373_);
return v___x_377_;
}
else
{
return v_newNode_367_;
}
}
else
{
return v_newNode_367_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_309_ = stack[0].m_obj;
size_t v_x_310_ = stack[1].m_num;
size_t v_x_311_ = stack[2].m_num;
lean_object* v_x_312_ = stack[3].m_obj;
lean_object* v_x_313_ = stack[4].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_309_, v_x_310_, v_x_311_, v_x_312_, v_x_313_);
stack->m_obj
 = v_res_380_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_381_, lean_object* v_keys_382_, lean_object* v_vals_383_, lean_object* v_i_384_, lean_object* v_entries_385_){
_start:
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = lean_array_get_size(v_keys_382_);
v___x_387_ = lean_nat_dec_lt(v_i_384_, v___x_386_);
if (v___x_387_ == 0)
{
lean_dec(v_i_384_);
return v_entries_385_;
}
else
{
lean_object* v_k_388_; lean_object* v_v_389_; uint64_t v___x_390_; size_t v_h_391_; size_t v___x_392_; lean_object* v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v_h_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_k_388_ = lean_array_fget_borrowed(v_keys_382_, v_i_384_);
v_v_389_ = lean_array_fget_borrowed(v_vals_383_, v_i_384_);
v___x_390_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_388_);
v_h_391_ = lean_uint64_to_usize(v___x_390_);
v___x_392_ = ((size_t)5ULL);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_sub(v_depth_381_, v___x_394_);
v___x_396_ = lean_usize_mul(v___x_392_, v___x_395_);
v_h_397_ = lean_usize_shift_right(v_h_391_, v___x_396_);
v___x_398_ = lean_nat_add(v_i_384_, v___x_393_);
lean_dec(v_i_384_);
lean_inc(v_v_389_);
lean_inc(v_k_388_);
v___x_399_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_385_, v_h_397_, v_depth_381_, v_k_388_, v_v_389_);
v_i_384_ = v___x_398_;
v_entries_385_ = v___x_399_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_381_ = stack[0].m_num;
lean_object* v_keys_382_ = stack[1].m_obj;
lean_object* v_vals_383_ = stack[2].m_obj;
lean_object* v_i_384_ = stack[3].m_obj;
lean_object* v_entries_385_ = stack[4].m_obj;
lean_object* v_res_401_;
v_res_401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_381_, v_keys_382_, v_vals_383_, v_i_384_, v_entries_385_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_402_, lean_object* v_keys_403_, lean_object* v_vals_404_, lean_object* v_i_405_, lean_object* v_entries_406_){
_start:
{
size_t v_depth_boxed_407_; lean_object* v_res_408_; 
v_depth_boxed_407_ = lean_unbox_usize(v_depth_402_);
lean_dec(v_depth_402_);
v_res_408_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_407_, v_keys_403_, v_vals_404_, v_i_405_, v_entries_406_);
lean_dec_ref(v_vals_404_);
lean_dec_ref(v_keys_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
size_t v_x_2125__boxed_414_; size_t v_x_2126__boxed_415_; lean_object* v_res_416_; 
v_x_2125__boxed_414_ = lean_unbox_usize(v_x_410_);
lean_dec(v_x_410_);
v_x_2126__boxed_415_ = lean_unbox_usize(v_x_411_);
lean_dec(v_x_411_);
v_res_416_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_409_, v_x_2125__boxed_414_, v_x_2126__boxed_415_, v_x_412_, v_x_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
uint64_t v___x_420_; size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v___x_420_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_418_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_417_, v___x_421_, v___x_422_, v_x_418_, v_x_419_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_424_, lean_object* v_b_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_dec(v_b_425_);
lean_dec_ref(v_a_424_);
return v_x_426_;
}
else
{
lean_object* v_key_427_; lean_object* v_value_428_; lean_object* v_tail_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_443_; 
v_key_427_ = lean_ctor_get(v_x_426_, 0);
v_value_428_ = lean_ctor_get(v_x_426_, 1);
v_tail_429_ = lean_ctor_get(v_x_426_, 2);
v_isSharedCheck_443_ = !lean_is_exclusive(v_x_426_);
if (v_isSharedCheck_443_ == 0)
{
v___x_431_ = v_x_426_;
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_tail_429_);
lean_inc(v_value_428_);
lean_inc(v_key_427_);
lean_dec(v_x_426_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
size_t v___x_433_; size_t v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_ptr_addr(v_key_427_);
v___x_434_ = lean_ptr_addr(v_a_424_);
v___x_435_ = lean_usize_dec_eq(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_424_, v_b_425_, v_tail_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 2, v___x_436_);
v___x_438_ = v___x_431_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_key_427_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_value_428_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v_value_428_);
lean_dec(v_key_427_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v_b_425_);
lean_ctor_set(v___x_431_, 0, v_a_424_);
v___x_441_ = v___x_431_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_424_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_b_425_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_tail_429_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
return v_x_444_;
}
else
{
lean_object* v_key_446_; lean_object* v_value_447_; lean_object* v_tail_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_474_; 
v_key_446_ = lean_ctor_get(v_x_445_, 0);
v_value_447_ = lean_ctor_get(v_x_445_, 1);
v_tail_448_ = lean_ctor_get(v_x_445_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_474_ == 0)
{
v___x_450_ = v_x_445_;
v_isShared_451_ = v_isSharedCheck_474_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_tail_448_);
lean_inc(v_value_447_);
lean_inc(v_key_446_);
lean_dec(v_x_445_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_474_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v_fold_459_; uint64_t v___x_460_; uint64_t v___x_461_; uint64_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_452_ = lean_array_get_size(v_x_444_);
v___x_453_ = lean_ptr_addr(v_key_446_);
v___x_454_ = ((size_t)3ULL);
v___x_455_ = lean_usize_shift_right(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_to_uint64(v___x_455_);
v___x_457_ = 32ULL;
v___x_458_ = lean_uint64_shift_right(v___x_456_, v___x_457_);
v_fold_459_ = lean_uint64_xor(v___x_456_, v___x_458_);
v___x_460_ = 16ULL;
v___x_461_ = lean_uint64_shift_right(v_fold_459_, v___x_460_);
v___x_462_ = lean_uint64_xor(v_fold_459_, v___x_461_);
v___x_463_ = lean_uint64_to_usize(v___x_462_);
v___x_464_ = lean_usize_of_nat(v___x_452_);
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_sub(v___x_464_, v___x_465_);
v___x_467_ = lean_usize_land(v___x_463_, v___x_466_);
v___x_468_ = lean_array_uget_borrowed(v_x_444_, v___x_467_);
lean_inc(v___x_468_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 2, v___x_468_);
v___x_470_ = v___x_450_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_key_446_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_value_447_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v___x_468_);
v___x_470_ = v_reuseFailAlloc_473_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; 
v___x_471_ = lean_array_uset(v_x_444_, v___x_467_, v___x_470_);
v_x_444_ = v___x_471_;
v_x_445_ = v_tail_448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_475_, lean_object* v_source_476_, lean_object* v_target_477_){
_start:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_array_get_size(v_source_476_);
v___x_479_ = lean_nat_dec_lt(v_i_475_, v___x_478_);
if (v___x_479_ == 0)
{
lean_dec_ref(v_source_476_);
lean_dec(v_i_475_);
return v_target_477_;
}
else
{
lean_object* v_es_480_; lean_object* v___x_481_; lean_object* v_source_482_; lean_object* v_target_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_es_480_ = lean_array_fget(v_source_476_, v_i_475_);
v___x_481_ = lean_box(0);
v_source_482_ = lean_array_fset(v_source_476_, v_i_475_, v___x_481_);
v_target_483_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_477_, v_es_480_);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_i_475_, v___x_484_);
lean_dec(v_i_475_);
v_i_475_ = v___x_485_;
v_source_476_ = v_source_482_;
v_target_477_ = v_target_483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_nbuckets_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_488_ = lean_array_get_size(v_data_487_);
v___x_489_ = lean_unsigned_to_nat(2u);
v_nbuckets_490_ = lean_nat_mul(v___x_488_, v___x_489_);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_box(0);
v___x_493_ = lean_mk_array(v_nbuckets_490_, v___x_492_);
v___x_494_ = lean_array_propagate_mark(v_data_487_, v___x_493_);
v___x_495_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_491_, v_data_487_, v___x_494_);
return v___x_495_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
uint8_t v___x_498_; 
v___x_498_ = 0;
return v___x_498_;
}
else
{
lean_object* v_key_499_; lean_object* v_tail_500_; size_t v___x_501_; size_t v___x_502_; uint8_t v___x_503_; 
v_key_499_ = lean_ctor_get(v_x_497_, 0);
v_tail_500_ = lean_ctor_get(v_x_497_, 2);
v___x_501_ = lean_ptr_addr(v_key_499_);
v___x_502_ = lean_ptr_addr(v_a_496_);
v___x_503_ = lean_usize_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
v_x_497_ = v_tail_500_;
goto _start;
}
else
{
return v___x_503_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_496_ = stack[0].m_obj;
lean_object* v_x_497_ = stack[1].m_obj;
uint8_t v_res_505_;
v_res_505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_496_, v_x_497_);
stack->m_num = v_res_505_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_506_, lean_object* v_x_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_506_, v_x_507_);
lean_dec(v_x_507_);
lean_dec_ref(v_a_506_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_510_, lean_object* v_a_511_, lean_object* v_b_512_){
_start:
{
lean_object* v_size_513_; lean_object* v_buckets_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_560_; 
v_size_513_ = lean_ctor_get(v_m_510_, 0);
v_buckets_514_ = lean_ctor_get(v_m_510_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_m_510_);
if (v_isSharedCheck_560_ == 0)
{
v___x_516_ = v_m_510_;
v_isShared_517_ = v_isSharedCheck_560_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_buckets_514_);
lean_inc(v_size_513_);
lean_dec(v_m_510_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_560_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v_fold_525_; uint64_t v___x_526_; uint64_t v___x_527_; uint64_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v_bkt_534_; uint8_t v___x_535_; 
v___x_518_ = lean_array_get_size(v_buckets_514_);
v___x_519_ = lean_ptr_addr(v_a_511_);
v___x_520_ = ((size_t)3ULL);
v___x_521_ = lean_usize_shift_right(v___x_519_, v___x_520_);
v___x_522_ = lean_usize_to_uint64(v___x_521_);
v___x_523_ = 32ULL;
v___x_524_ = lean_uint64_shift_right(v___x_522_, v___x_523_);
v_fold_525_ = lean_uint64_xor(v___x_522_, v___x_524_);
v___x_526_ = 16ULL;
v___x_527_ = lean_uint64_shift_right(v_fold_525_, v___x_526_);
v___x_528_ = lean_uint64_xor(v_fold_525_, v___x_527_);
v___x_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = lean_usize_of_nat(v___x_518_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_sub(v___x_530_, v___x_531_);
v___x_533_ = lean_usize_land(v___x_529_, v___x_532_);
v_bkt_534_ = lean_array_uget_borrowed(v_buckets_514_, v___x_533_);
v___x_535_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_511_, v_bkt_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v_size_x27_537_; lean_object* v___x_538_; lean_object* v_buckets_x27_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_536_ = lean_unsigned_to_nat(1u);
v_size_x27_537_ = lean_nat_add(v_size_513_, v___x_536_);
lean_dec(v_size_513_);
lean_inc(v_bkt_534_);
v___x_538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_538_, 0, v_a_511_);
lean_ctor_set(v___x_538_, 1, v_b_512_);
lean_ctor_set(v___x_538_, 2, v_bkt_534_);
v_buckets_x27_539_ = lean_array_uset(v_buckets_514_, v___x_533_, v___x_538_);
v___x_540_ = lean_unsigned_to_nat(4u);
v___x_541_ = lean_nat_mul(v_size_x27_537_, v___x_540_);
v___x_542_ = lean_unsigned_to_nat(3u);
v___x_543_ = lean_nat_div(v___x_541_, v___x_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_array_get_size(v_buckets_x27_539_);
v___x_545_ = lean_nat_dec_le(v___x_543_, v___x_544_);
lean_dec(v___x_543_);
if (v___x_545_ == 0)
{
lean_object* v_val_546_; lean_object* v___x_548_; 
v_val_546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_539_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_val_546_);
lean_ctor_set(v___x_516_, 0, v_size_x27_537_);
v___x_548_ = v___x_516_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_size_x27_537_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_val_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_object* v___x_551_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_buckets_x27_539_);
lean_ctor_set(v___x_516_, 0, v_size_x27_537_);
v___x_551_ = v___x_516_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_size_x27_537_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_buckets_x27_539_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
lean_object* v___x_553_; lean_object* v_buckets_x27_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
lean_inc(v_bkt_534_);
v___x_553_ = lean_box(0);
v_buckets_x27_554_ = lean_array_uset(v_buckets_514_, v___x_533_, v___x_553_);
v___x_555_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_511_, v_b_512_, v_bkt_534_);
v___x_556_ = lean_array_uset(v_buckets_x27_554_, v___x_533_, v___x_555_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_556_);
v___x_558_ = v___x_516_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_size_513_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_561_; size_t v___x_562_; 
v___x_561_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_562_ = lean_ptr_addr(v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_563_, lean_object* v_r_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_map_566_; lean_object* v_set_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_591_; 
v_map_566_ = lean_ctor_get(v_a_565_, 0);
v_set_567_ = lean_ctor_get(v_a_565_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_591_ == 0)
{
v___x_569_ = v_a_565_;
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_set_567_);
lean_inc(v_map_566_);
lean_dec(v_a_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; uint64_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; size_t v___x_575_; size_t v___x_576_; uint8_t v___x_577_; 
v___x_571_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_572_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_564_);
v___x_573_ = lean_uint64_to_usize(v___x_572_);
v___x_574_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_567_, v___x_573_, v_r_564_, v___x_571_);
v___x_575_ = lean_ptr_addr(v___x_574_);
v___x_576_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_577_ = lean_usize_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec_ref(v_r_564_);
lean_inc_ref(v___x_574_);
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_566_, v_e_563_, v___x_574_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_578_);
v___x_580_ = v___x_569_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_set_567_);
v___x_580_ = v_reuseFailAlloc_582_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_574_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
return v___x_581_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec_ref(v___x_574_);
lean_inc_ref_n(v_r_564_, 4);
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_566_, v_e_563_, v_r_564_);
v___x_584_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_583_, v_r_564_, v_r_564_);
v___x_585_ = lean_box(0);
v___x_586_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_567_, v_r_564_, v___x_585_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v___x_586_);
lean_ctor_set(v___x_569_, 0, v___x_584_);
v___x_588_ = v___x_569_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_586_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_r_564_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_592_, lean_object* v_r_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_592_, v_r_593_, v_a_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_597_, lean_object* v_r_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_597_, v_r_598_, v_a_599_, v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_601_;
}
}
lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_602_, lean_object* v_x_603_, size_t v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_603_, v_x_604_, v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_603_ = stack[1].m_obj;
size_t v_x_604_ = stack[2].m_num;
lean_object* v_x_605_ = stack[3].m_obj;
lean_object* v_x_606_ = stack[4].m_obj;
lean_object* v_res_608_;
v_res_608_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_box(0), v_x_603_, v_x_604_, v_x_605_, v_x_606_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
size_t v_x_2812__boxed_614_; lean_object* v_res_615_; 
v_x_2812__boxed_614_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_res_615_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_609_, v_x_610_, v_x_2812__boxed_614_, v_x_612_, v_x_613_);
lean_dec_ref(v_x_613_);
lean_dec_ref(v_x_612_);
lean_dec_ref(v_x_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_616_, lean_object* v_m_617_, lean_object* v_a_618_, lean_object* v_b_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_617_, v_a_618_, v_b_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_622_, v_x_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_626_, lean_object* v_keys_627_, lean_object* v_vals_628_, lean_object* v_heq_629_, lean_object* v_i_630_, lean_object* v_k_631_, lean_object* v_k_u2080_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_627_, v_i_630_, v_k_631_, v_k_u2080_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_634_, lean_object* v_keys_635_, lean_object* v_vals_636_, lean_object* v_heq_637_, lean_object* v_i_638_, lean_object* v_k_639_, lean_object* v_k_u2080_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_634_, v_keys_635_, v_vals_636_, v_heq_637_, v_i_638_, v_k_639_, v_k_u2080_640_);
lean_dec_ref(v_k_u2080_640_);
lean_dec_ref(v_k_639_);
lean_dec_ref(v_vals_636_);
lean_dec_ref(v_keys_635_);
return v_res_641_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_642_, lean_object* v_a_643_, lean_object* v_x_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_643_ = stack[1].m_obj;
lean_object* v_x_644_ = stack[2].m_obj;
uint8_t v_res_646_;
v_res_646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_box(0), v_a_643_, v_x_644_);
stack->m_num = v_res_646_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_647_, lean_object* v_a_648_, lean_object* v_x_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_647_, v_a_648_, v_x_649_);
lean_dec(v_x_649_);
lean_dec_ref(v_a_648_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_652_, lean_object* v_data_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_655_, lean_object* v_a_656_, lean_object* v_b_657_, lean_object* v_x_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_656_, v_b_657_, v_x_658_);
return v___x_659_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_660_, lean_object* v_x_661_, size_t v_x_662_, size_t v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_661_, v_x_662_, v_x_663_, v_x_664_, v_x_665_);
return v___x_666_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_661_ = stack[1].m_obj;
size_t v_x_662_ = stack[2].m_num;
size_t v_x_663_ = stack[3].m_num;
lean_object* v_x_664_ = stack[4].m_obj;
lean_object* v_x_665_ = stack[5].m_obj;
lean_object* v_res_667_;
v_res_667_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_box(0), v_x_661_, v_x_662_, v_x_663_, v_x_664_, v_x_665_);
stack->m_obj
 = v_res_667_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
size_t v_x_2870__boxed_674_; size_t v_x_2871__boxed_675_; lean_object* v_res_676_; 
v_x_2870__boxed_674_ = lean_unbox_usize(v_x_670_);
lean_dec(v_x_670_);
v_x_2871__boxed_675_ = lean_unbox_usize(v_x_671_);
lean_dec(v_x_671_);
v_res_676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_668_, v_x_669_, v_x_2870__boxed_674_, v_x_2871__boxed_675_, v_x_672_, v_x_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_677_, lean_object* v_i_678_, lean_object* v_source_679_, lean_object* v_target_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_678_, v_source_679_, v_target_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_682_, lean_object* v_n_683_, lean_object* v_k_684_, lean_object* v_v_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_683_, v_k_684_, v_v_685_);
return v___x_686_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_687_, size_t v_depth_688_, lean_object* v_keys_689_, lean_object* v_vals_690_, lean_object* v_heq_691_, lean_object* v_i_692_, lean_object* v_entries_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_688_, v_keys_689_, v_vals_690_, v_i_692_, v_entries_693_);
return v___x_694_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_688_ = stack[1].m_num;
lean_object* v_keys_689_ = stack[2].m_obj;
lean_object* v_vals_690_ = stack[3].m_obj;
lean_object* v_i_692_ = stack[5].m_obj;
lean_object* v_entries_693_ = stack[6].m_obj;
lean_object* v_res_695_;
v_res_695_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_box(0), v_depth_688_, v_keys_689_, v_vals_690_, lean_box(0), v_i_692_, v_entries_693_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_696_, lean_object* v_depth_697_, lean_object* v_keys_698_, lean_object* v_vals_699_, lean_object* v_heq_700_, lean_object* v_i_701_, lean_object* v_entries_702_){
_start:
{
size_t v_depth_boxed_703_; lean_object* v_res_704_; 
v_depth_boxed_703_ = lean_unbox_usize(v_depth_697_);
lean_dec(v_depth_697_);
v_res_704_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_696_, v_depth_boxed_703_, v_keys_698_, v_vals_699_, v_heq_700_, v_i_701_, v_entries_702_);
lean_dec_ref(v_vals_699_);
lean_dec_ref(v_keys_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_706_, v_x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_710_, v_x_711_, v_x_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_717_, lean_object* v_k_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_map_721_; lean_object* v_set_722_; lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v_map_721_ = lean_ctor_get(v_a_720_, 0);
v_set_722_ = lean_ctor_get(v_a_720_, 1);
v___f_723_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_724_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_717_);
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_723_, v___f_724_, v_map_721_, v_e_717_);
if (lean_obj_tag(v___x_725_) == 1)
{
lean_object* v_val_726_; lean_object* v___x_727_; 
lean_dec_ref(v_k_718_);
lean_dec_ref(v_e_717_);
v_val_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_val_726_);
lean_ctor_set(v___x_727_, 1, v_a_720_);
return v___x_727_;
}
else
{
lean_object* v___f_728_; lean_object* v___x_729_; uint64_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; size_t v___x_733_; size_t v___x_734_; uint8_t v___x_735_; 
lean_dec(v___x_725_);
v___f_728_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_729_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_730_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_717_);
v___x_731_ = lean_uint64_to_usize(v___x_730_);
lean_inc_ref(v_e_717_);
lean_inc_ref(v_set_722_);
v___x_732_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_728_, v_set_722_, v___x_731_, v_e_717_, v___x_729_);
v___x_733_ = lean_ptr_addr(v___x_732_);
v___x_734_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_735_ = lean_usize_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_dec_ref(v_k_718_);
lean_dec_ref(v_e_717_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_732_);
lean_ctor_set(v___x_736_, 1, v_a_720_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
lean_dec(v___x_732_);
lean_inc_ref(v_a_719_);
v___x_737_ = lean_apply_2(v_k_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
v_a_739_ = lean_ctor_get(v___x_737_, 1);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_737_, 2);
v___x_740_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_717_, v_a_738_, v_a_739_);
return v___x_740_;
}
else
{
lean_dec_ref(v_e_717_);
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_741_, lean_object* v_k_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_741_, v_k_742_, v_a_743_, v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_746_, lean_object* v_x_747_){
_start:
{
if (lean_obj_tag(v_x_747_) == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(0);
return v___x_748_;
}
else
{
lean_object* v_key_749_; lean_object* v_value_750_; lean_object* v_tail_751_; size_t v___x_752_; size_t v___x_753_; uint8_t v___x_754_; 
v_key_749_ = lean_ctor_get(v_x_747_, 0);
v_value_750_ = lean_ctor_get(v_x_747_, 1);
v_tail_751_ = lean_ctor_get(v_x_747_, 2);
v___x_752_ = lean_ptr_addr(v_key_749_);
v___x_753_ = lean_ptr_addr(v_a_746_);
v___x_754_ = lean_usize_dec_eq(v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
v_x_747_ = v_tail_751_;
goto _start;
}
else
{
lean_object* v___x_756_; 
lean_inc(v_value_750_);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v_value_750_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_757_, lean_object* v_x_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_757_, v_x_758_);
lean_dec(v_x_758_);
lean_dec_ref(v_a_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_buckets_762_; lean_object* v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v___x_769_; uint64_t v_fold_770_; uint64_t v___x_771_; uint64_t v___x_772_; uint64_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_buckets_762_ = lean_ctor_get(v_m_760_, 1);
v___x_763_ = lean_array_get_size(v_buckets_762_);
v___x_764_ = lean_ptr_addr(v_a_761_);
v___x_765_ = ((size_t)3ULL);
v___x_766_ = lean_usize_shift_right(v___x_764_, v___x_765_);
v___x_767_ = lean_usize_to_uint64(v___x_766_);
v___x_768_ = 32ULL;
v___x_769_ = lean_uint64_shift_right(v___x_767_, v___x_768_);
v_fold_770_ = lean_uint64_xor(v___x_767_, v___x_769_);
v___x_771_ = 16ULL;
v___x_772_ = lean_uint64_shift_right(v_fold_770_, v___x_771_);
v___x_773_ = lean_uint64_xor(v_fold_770_, v___x_772_);
v___x_774_ = lean_uint64_to_usize(v___x_773_);
v___x_775_ = lean_usize_of_nat(v___x_763_);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_sub(v___x_775_, v___x_776_);
v___x_778_ = lean_usize_land(v___x_774_, v___x_777_);
v___x_779_ = lean_array_uget_borrowed(v_buckets_762_, v___x_778_);
v___x_780_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_761_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_781_, v_a_782_);
lean_dec_ref(v_a_782_);
lean_dec_ref(v_m_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_i_786_, lean_object* v_k_787_){
_start:
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_array_get_size(v_keys_784_);
v___x_789_ = lean_nat_dec_lt(v_i_786_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v_i_786_);
v___x_790_ = lean_box(0);
return v___x_790_;
}
else
{
lean_object* v_k_x27_791_; uint8_t v___x_792_; 
v_k_x27_791_ = lean_array_fget_borrowed(v_keys_784_, v_i_786_);
v___x_792_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_787_, v_k_x27_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_i_786_, v___x_793_);
lean_dec(v_i_786_);
v_i_786_ = v___x_794_;
goto _start;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = lean_array_fget_borrowed(v_vals_785_, v_i_786_);
lean_dec(v_i_786_);
lean_inc(v___x_796_);
lean_inc(v_k_x27_791_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_k_x27_791_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_799_, lean_object* v_vals_800_, lean_object* v_i_801_, lean_object* v_k_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_799_, v_vals_800_, v_i_801_, v_k_802_);
lean_dec_ref(v_k_802_);
lean_dec_ref(v_vals_800_);
lean_dec_ref(v_keys_799_);
return v_res_803_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_804_, size_t v_x_805_, lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
lean_object* v_es_807_; lean_object* v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v_j_811_; lean_object* v___x_812_; 
v_es_807_ = lean_ctor_get(v_x_804_, 0);
v___x_808_ = lean_box(2);
v___x_809_ = ((size_t)31ULL);
v___x_810_ = lean_usize_land(v_x_805_, v___x_809_);
v_j_811_ = lean_usize_to_nat(v___x_810_);
v___x_812_ = lean_array_get_borrowed(v___x_808_, v_es_807_, v_j_811_);
lean_dec(v_j_811_);
switch(lean_obj_tag(v___x_812_))
{
case 0:
{
lean_object* v_key_813_; lean_object* v_val_814_; uint8_t v___x_815_; 
v_key_813_ = lean_ctor_get(v___x_812_, 0);
v_val_814_ = lean_ctor_get(v___x_812_, 1);
v___x_815_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_806_, v_key_813_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
v___x_816_ = lean_box(0);
return v___x_816_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; 
lean_inc(v_val_814_);
lean_inc(v_key_813_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_key_813_);
lean_ctor_set(v___x_817_, 1, v_val_814_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
case 1:
{
lean_object* v_node_819_; size_t v___x_820_; size_t v___x_821_; 
v_node_819_ = lean_ctor_get(v___x_812_, 0);
v___x_820_ = ((size_t)5ULL);
v___x_821_ = lean_usize_shift_right(v_x_805_, v___x_820_);
v_x_804_ = v_node_819_;
v_x_805_ = v___x_821_;
goto _start;
}
default: 
{
lean_object* v___x_823_; 
v___x_823_ = lean_box(0);
return v___x_823_;
}
}
}
else
{
lean_object* v_ks_824_; lean_object* v_vs_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_ks_824_ = lean_ctor_get(v_x_804_, 0);
v_vs_825_ = lean_ctor_get(v_x_804_, 1);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_824_, v_vs_825_, v___x_826_, v_x_806_);
return v___x_827_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_804_ = stack[0].m_obj;
size_t v_x_805_ = stack[1].m_num;
lean_object* v_x_806_ = stack[2].m_obj;
lean_object* v_res_828_;
v_res_828_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_804_, v_x_805_, v_x_806_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
size_t v_x_10862__boxed_832_; lean_object* v_res_833_; 
v_x_10862__boxed_832_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_res_833_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_829_, v_x_10862__boxed_832_, v_x_831_);
lean_dec_ref(v_x_831_);
lean_dec_ref(v_x_829_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint64_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_835_);
v___x_837_ = lean_uint64_to_usize(v___x_836_);
v___x_838_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_834_, v___x_837_, v_x_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_839_, v_x_840_);
lean_dec_ref(v_x_840_);
lean_dec_ref(v_x_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___y_846_; lean_object* v___y_851_; lean_object* v___y_856_; lean_object* v___y_861_; 
switch(lean_obj_tag(v_e_842_))
{
case 4:
{
lean_object* v_declName_865_; lean_object* v_map_866_; lean_object* v_set_867_; lean_object* v___x_868_; 
v_declName_865_ = lean_ctor_get(v_e_842_, 0);
v_map_866_ = lean_ctor_get(v_a_844_, 0);
v_set_867_ = lean_ctor_get(v_a_844_, 1);
v___x_868_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_867_, v_e_842_);
if (lean_obj_tag(v___x_868_) == 0)
{
uint8_t v___x_869_; 
lean_inc(v_declName_865_);
lean_inc_ref(v_a_843_);
v___x_869_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_843_, v_declName_865_);
if (v___x_869_ == 0)
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_879_; 
lean_inc_ref(v_set_867_);
lean_inc_ref(v_map_866_);
v_isSharedCheck_879_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; lean_object* v_unused_881_; 
v_unused_880_ = lean_ctor_get(v_a_844_, 1);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_a_844_, 0);
lean_dec(v_unused_881_);
v___x_871_ = v_a_844_;
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
else
{
lean_dec(v_a_844_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_879_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_873_ = lean_box(0);
lean_inc_ref(v_e_842_);
v___x_874_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_867_, v_e_842_, v___x_873_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_map_866_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_e_842_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
return v___x_877_;
}
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec_ref_known(v_e_842_, 2);
v___x_882_ = lean_box(0);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v_a_844_);
return v___x_883_;
}
}
else
{
lean_object* v_val_884_; lean_object* v_fst_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref_known(v_e_842_, 2);
v_val_884_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v___x_868_, 1);
v_fst_885_ = lean_ctor_get(v_val_884_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_val_884_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_val_884_, 1);
lean_dec(v_unused_893_);
v___x_887_ = v_val_884_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_fst_885_);
lean_dec(v_val_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_a_844_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_885_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_a_844_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
case 5:
{
lean_object* v_fn_894_; lean_object* v_arg_895_; lean_object* v_map_896_; lean_object* v_set_897_; lean_object* v___x_898_; 
v_fn_894_ = lean_ctor_get(v_e_842_, 0);
v_arg_895_ = lean_ctor_get(v_e_842_, 1);
v_map_896_ = lean_ctor_get(v_a_844_, 0);
v_set_897_ = lean_ctor_get(v_a_844_, 1);
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_896_, v_e_842_);
if (lean_obj_tag(v___x_898_) == 1)
{
lean_object* v_val_899_; lean_object* v___x_900_; 
lean_dec_ref_known(v_e_842_, 2);
v_val_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_val_899_);
lean_ctor_set(v___x_900_, 1, v_a_844_);
return v___x_900_;
}
else
{
lean_object* v___x_901_; uint64_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; size_t v___x_905_; size_t v___x_906_; uint8_t v___x_907_; 
lean_dec(v___x_898_);
v___x_901_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_902_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_842_);
v___x_903_ = lean_uint64_to_usize(v___x_902_);
v___x_904_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_897_, v___x_903_, v_e_842_, v___x_901_);
v___x_905_ = lean_ptr_addr(v___x_904_);
v___x_906_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_907_ = lean_usize_dec_eq(v___x_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec_ref_known(v_e_842_, 2);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_904_);
lean_ctor_set(v___x_908_, 1, v_a_844_);
return v___x_908_;
}
else
{
lean_object* v___x_909_; 
lean_dec_ref(v___x_904_);
lean_inc_ref(v_fn_894_);
v___x_909_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_894_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
v_a_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_909_, 2);
lean_inc_ref(v_arg_895_);
v___x_912_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_895_, v_a_843_, v_a_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_a_914_; size_t v___x_915_; size_t v___x_916_; uint8_t v___x_917_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
v_a_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_912_, 2);
v___x_915_ = lean_ptr_addr(v_fn_894_);
v___x_916_ = lean_ptr_addr(v_a_910_);
v___x_917_ = lean_usize_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = l_Lean_Expr_app___override(v_a_910_, v_a_913_);
v___x_919_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_918_, v_a_914_);
return v___x_919_;
}
else
{
size_t v___x_920_; size_t v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_ptr_addr(v_arg_895_);
v___x_921_ = lean_ptr_addr(v_a_913_);
v___x_922_ = lean_usize_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = l_Lean_Expr_app___override(v_a_910_, v_a_913_);
v___x_924_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_923_, v_a_914_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; 
lean_dec(v_a_913_);
lean_dec(v_a_910_);
lean_inc_ref(v_e_842_);
v___x_925_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_e_842_, v_a_914_);
return v___x_925_;
}
}
}
else
{
lean_dec(v_a_910_);
v___y_846_ = v___x_912_;
goto v___jp_845_;
}
}
else
{
v___y_846_ = v___x_909_;
goto v___jp_845_;
}
}
}
}
case 6:
{
lean_object* v_binderName_926_; lean_object* v_binderType_927_; lean_object* v_body_928_; uint8_t v_binderInfo_929_; lean_object* v_map_930_; lean_object* v_set_931_; lean_object* v___x_932_; 
v_binderName_926_ = lean_ctor_get(v_e_842_, 0);
v_binderType_927_ = lean_ctor_get(v_e_842_, 1);
v_body_928_ = lean_ctor_get(v_e_842_, 2);
v_binderInfo_929_ = lean_ctor_get_uint8(v_e_842_, sizeof(void*)*3 + 8);
v_map_930_ = lean_ctor_get(v_a_844_, 0);
v_set_931_ = lean_ctor_get(v_a_844_, 1);
v___x_932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_930_, v_e_842_);
if (lean_obj_tag(v___x_932_) == 1)
{
lean_object* v_val_933_; lean_object* v___x_934_; 
lean_dec_ref_known(v_e_842_, 3);
v_val_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_val_933_);
lean_ctor_set(v___x_934_, 1, v_a_844_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; uint64_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; size_t v___x_939_; size_t v___x_940_; uint8_t v___x_941_; 
lean_dec(v___x_932_);
v___x_935_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_936_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_842_);
v___x_937_ = lean_uint64_to_usize(v___x_936_);
v___x_938_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_931_, v___x_937_, v_e_842_, v___x_935_);
v___x_939_ = lean_ptr_addr(v___x_938_);
v___x_940_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_941_ = lean_usize_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec_ref_known(v_e_842_, 3);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_938_);
lean_ctor_set(v___x_942_, 1, v_a_844_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v___x_938_);
lean_inc_ref(v_binderType_927_);
v___x_943_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_927_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_946_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
v_a_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_943_, 2);
lean_inc_ref(v_body_928_);
v___x_946_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_928_, v_a_843_, v_a_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_a_948_; size_t v___x_949_; size_t v___x_950_; uint8_t v___x_951_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
v_a_948_ = lean_ctor_get(v___x_946_, 1);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_946_, 2);
v___x_949_ = lean_ptr_addr(v_binderType_927_);
v___x_950_ = lean_ptr_addr(v_a_944_);
v___x_951_ = lean_usize_dec_eq(v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_inc(v_binderName_926_);
v___x_952_ = l_Lean_Expr_lam___override(v_binderName_926_, v_a_944_, v_a_947_, v_binderInfo_929_);
v___x_953_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_952_, v_a_948_);
return v___x_953_;
}
else
{
size_t v___x_954_; size_t v___x_955_; uint8_t v___x_956_; 
v___x_954_ = lean_ptr_addr(v_body_928_);
v___x_955_ = lean_ptr_addr(v_a_947_);
v___x_956_ = lean_usize_dec_eq(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc(v_binderName_926_);
v___x_957_ = l_Lean_Expr_lam___override(v_binderName_926_, v_a_944_, v_a_947_, v_binderInfo_929_);
v___x_958_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_957_, v_a_948_);
return v___x_958_;
}
else
{
uint8_t v___x_959_; 
v___x_959_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_929_, v_binderInfo_929_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_inc(v_binderName_926_);
v___x_960_ = l_Lean_Expr_lam___override(v_binderName_926_, v_a_944_, v_a_947_, v_binderInfo_929_);
v___x_961_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_960_, v_a_948_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; 
lean_dec(v_a_947_);
lean_dec(v_a_944_);
lean_inc_ref(v_e_842_);
v___x_962_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_e_842_, v_a_948_);
return v___x_962_;
}
}
}
}
else
{
lean_dec(v_a_944_);
v___y_851_ = v___x_946_;
goto v___jp_850_;
}
}
else
{
v___y_851_ = v___x_943_;
goto v___jp_850_;
}
}
}
}
case 7:
{
lean_object* v_binderName_963_; lean_object* v_binderType_964_; lean_object* v_body_965_; uint8_t v_binderInfo_966_; lean_object* v_map_967_; lean_object* v_set_968_; lean_object* v___x_969_; 
v_binderName_963_ = lean_ctor_get(v_e_842_, 0);
v_binderType_964_ = lean_ctor_get(v_e_842_, 1);
v_body_965_ = lean_ctor_get(v_e_842_, 2);
v_binderInfo_966_ = lean_ctor_get_uint8(v_e_842_, sizeof(void*)*3 + 8);
v_map_967_ = lean_ctor_get(v_a_844_, 0);
v_set_968_ = lean_ctor_get(v_a_844_, 1);
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_967_, v_e_842_);
if (lean_obj_tag(v___x_969_) == 1)
{
lean_object* v_val_970_; lean_object* v___x_971_; 
lean_dec_ref_known(v_e_842_, 3);
v_val_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_val_970_);
lean_ctor_set(v___x_971_, 1, v_a_844_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; uint64_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; size_t v___x_976_; size_t v___x_977_; uint8_t v___x_978_; 
lean_dec(v___x_969_);
v___x_972_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_973_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_842_);
v___x_974_ = lean_uint64_to_usize(v___x_973_);
v___x_975_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_968_, v___x_974_, v_e_842_, v___x_972_);
v___x_976_ = lean_ptr_addr(v___x_975_);
v___x_977_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_978_ = lean_usize_dec_eq(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec_ref_known(v_e_842_, 3);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_975_);
lean_ctor_set(v___x_979_, 1, v_a_844_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; 
lean_dec_ref(v___x_975_);
lean_inc_ref(v_binderType_964_);
v___x_980_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_964_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
v_a_982_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_980_, 2);
lean_inc_ref(v_body_965_);
v___x_983_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_965_, v_a_843_, v_a_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_a_985_; size_t v___x_986_; size_t v___x_987_; uint8_t v___x_988_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
v_a_985_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_983_, 2);
v___x_986_ = lean_ptr_addr(v_binderType_964_);
v___x_987_ = lean_ptr_addr(v_a_981_);
v___x_988_ = lean_usize_dec_eq(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_inc(v_binderName_963_);
v___x_989_ = l_Lean_Expr_forallE___override(v_binderName_963_, v_a_981_, v_a_984_, v_binderInfo_966_);
v___x_990_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_989_, v_a_985_);
return v___x_990_;
}
else
{
size_t v___x_991_; size_t v___x_992_; uint8_t v___x_993_; 
v___x_991_ = lean_ptr_addr(v_body_965_);
v___x_992_ = lean_ptr_addr(v_a_984_);
v___x_993_ = lean_usize_dec_eq(v___x_991_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_inc(v_binderName_963_);
v___x_994_ = l_Lean_Expr_forallE___override(v_binderName_963_, v_a_981_, v_a_984_, v_binderInfo_966_);
v___x_995_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_994_, v_a_985_);
return v___x_995_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_966_, v_binderInfo_966_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc(v_binderName_963_);
v___x_997_ = l_Lean_Expr_forallE___override(v_binderName_963_, v_a_981_, v_a_984_, v_binderInfo_966_);
v___x_998_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_997_, v_a_985_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; 
lean_dec(v_a_984_);
lean_dec(v_a_981_);
lean_inc_ref(v_e_842_);
v___x_999_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_e_842_, v_a_985_);
return v___x_999_;
}
}
}
}
else
{
lean_dec(v_a_981_);
v___y_856_ = v___x_983_;
goto v___jp_855_;
}
}
else
{
v___y_856_ = v___x_980_;
goto v___jp_855_;
}
}
}
}
case 8:
{
lean_object* v_declName_1000_; lean_object* v_type_1001_; lean_object* v_value_1002_; lean_object* v_body_1003_; uint8_t v_nondep_1004_; lean_object* v_map_1005_; lean_object* v_set_1006_; lean_object* v___x_1007_; 
v_declName_1000_ = lean_ctor_get(v_e_842_, 0);
v_type_1001_ = lean_ctor_get(v_e_842_, 1);
v_value_1002_ = lean_ctor_get(v_e_842_, 2);
v_body_1003_ = lean_ctor_get(v_e_842_, 3);
v_nondep_1004_ = lean_ctor_get_uint8(v_e_842_, sizeof(void*)*4 + 8);
v_map_1005_ = lean_ctor_get(v_a_844_, 0);
v_set_1006_ = lean_ctor_get(v_a_844_, 1);
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1005_, v_e_842_);
if (lean_obj_tag(v___x_1007_) == 1)
{
lean_object* v_val_1008_; lean_object* v___x_1009_; 
lean_dec_ref_known(v_e_842_, 4);
v_val_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_val_1008_);
lean_ctor_set(v___x_1009_, 1, v_a_844_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; uint64_t v___x_1011_; size_t v___x_1012_; lean_object* v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; uint8_t v___x_1016_; 
lean_dec(v___x_1007_);
v___x_1010_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1011_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_842_);
v___x_1012_ = lean_uint64_to_usize(v___x_1011_);
v___x_1013_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1006_, v___x_1012_, v_e_842_, v___x_1010_);
v___x_1014_ = lean_ptr_addr(v___x_1013_);
v___x_1015_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1016_ = lean_usize_dec_eq(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_dec_ref_known(v_e_842_, 4);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1013_);
lean_ctor_set(v___x_1017_, 1, v_a_844_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; 
lean_dec_ref(v___x_1013_);
lean_inc_ref(v_type_1001_);
v___x_1018_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_1001_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_a_1020_; lean_object* v___x_1021_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
v_a_1020_ = lean_ctor_get(v___x_1018_, 1);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1018_, 2);
lean_inc_ref(v_value_1002_);
v___x_1021_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_1002_, v_a_843_, v_a_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
v_a_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1021_, 2);
lean_inc_ref(v_body_1003_);
v___x_1024_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_1003_, v_a_843_, v_a_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_a_1026_; size_t v___x_1027_; size_t v___x_1028_; uint8_t v___x_1029_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
v_a_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1024_, 2);
v___x_1027_ = lean_ptr_addr(v_type_1001_);
v___x_1028_ = lean_ptr_addr(v_a_1019_);
v___x_1029_ = lean_usize_dec_eq(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_inc(v_declName_1000_);
v___x_1030_ = l_Lean_Expr_letE___override(v_declName_1000_, v_a_1019_, v_a_1022_, v_a_1025_, v_nondep_1004_);
v___x_1031_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_1030_, v_a_1026_);
return v___x_1031_;
}
else
{
size_t v___x_1032_; size_t v___x_1033_; uint8_t v___x_1034_; 
v___x_1032_ = lean_ptr_addr(v_value_1002_);
v___x_1033_ = lean_ptr_addr(v_a_1022_);
v___x_1034_ = lean_usize_dec_eq(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_inc(v_declName_1000_);
v___x_1035_ = l_Lean_Expr_letE___override(v_declName_1000_, v_a_1019_, v_a_1022_, v_a_1025_, v_nondep_1004_);
v___x_1036_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_1035_, v_a_1026_);
return v___x_1036_;
}
else
{
size_t v___x_1037_; size_t v___x_1038_; uint8_t v___x_1039_; 
v___x_1037_ = lean_ptr_addr(v_body_1003_);
v___x_1038_ = lean_ptr_addr(v_a_1025_);
v___x_1039_ = lean_usize_dec_eq(v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_inc(v_declName_1000_);
v___x_1040_ = l_Lean_Expr_letE___override(v_declName_1000_, v_a_1019_, v_a_1022_, v_a_1025_, v_nondep_1004_);
v___x_1041_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_1040_, v_a_1026_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; 
lean_dec(v_a_1025_);
lean_dec(v_a_1022_);
lean_dec(v_a_1019_);
lean_inc_ref(v_e_842_);
v___x_1042_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_e_842_, v_a_1026_);
return v___x_1042_;
}
}
}
}
else
{
lean_dec(v_a_1022_);
lean_dec(v_a_1019_);
v___y_861_ = v___x_1024_;
goto v___jp_860_;
}
}
else
{
lean_dec(v_a_1019_);
v___y_861_ = v___x_1021_;
goto v___jp_860_;
}
}
else
{
v___y_861_ = v___x_1018_;
goto v___jp_860_;
}
}
}
}
case 10:
{
lean_object* v_data_1043_; lean_object* v_expr_1044_; lean_object* v_map_1045_; lean_object* v_set_1046_; lean_object* v___x_1047_; 
v_data_1043_ = lean_ctor_get(v_e_842_, 0);
v_expr_1044_ = lean_ctor_get(v_e_842_, 1);
v_map_1045_ = lean_ctor_get(v_a_844_, 0);
v_set_1046_ = lean_ctor_get(v_a_844_, 1);
v___x_1047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1045_, v_e_842_);
if (lean_obj_tag(v___x_1047_) == 1)
{
lean_object* v_val_1048_; lean_object* v___x_1049_; 
lean_dec_ref_known(v_e_842_, 2);
v_val_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_val_1048_);
lean_ctor_set(v___x_1049_, 1, v_a_844_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; uint64_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; uint8_t v___x_1056_; 
lean_dec(v___x_1047_);
v___x_1050_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1051_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_842_);
v___x_1052_ = lean_uint64_to_usize(v___x_1051_);
v___x_1053_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1046_, v___x_1052_, v_e_842_, v___x_1050_);
v___x_1054_ = lean_ptr_addr(v___x_1053_);
v___x_1055_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1056_ = lean_usize_dec_eq(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref_known(v_e_842_, 2);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1053_);
lean_ctor_set(v___x_1057_, 1, v_a_844_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; 
lean_dec_ref(v___x_1053_);
lean_inc_ref(v_expr_1044_);
v___x_1058_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1044_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v_a_1060_; size_t v___x_1061_; size_t v___x_1062_; uint8_t v___x_1063_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
v_a_1060_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1058_, 2);
v___x_1061_ = lean_ptr_addr(v_expr_1044_);
v___x_1062_ = lean_ptr_addr(v_a_1059_);
v___x_1063_ = lean_usize_dec_eq(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_inc(v_data_1043_);
v___x_1064_ = l_Lean_Expr_mdata___override(v_data_1043_, v_a_1059_);
v___x_1065_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_1064_, v_a_1060_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; 
lean_dec(v_a_1059_);
lean_inc_ref(v_e_842_);
v___x_1066_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_e_842_, v_a_1060_);
return v___x_1066_;
}
}
else
{
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1067_);
v_a_1068_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1058_, 2);
v___x_1069_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_a_1067_, v_a_1068_);
return v___x_1069_;
}
else
{
lean_dec_ref_known(v_e_842_, 2);
return v___x_1058_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1070_; lean_object* v_idx_1071_; lean_object* v_struct_1072_; lean_object* v_map_1073_; lean_object* v_set_1074_; lean_object* v___x_1075_; 
v_typeName_1070_ = lean_ctor_get(v_e_842_, 0);
v_idx_1071_ = lean_ctor_get(v_e_842_, 1);
v_struct_1072_ = lean_ctor_get(v_e_842_, 2);
v_map_1073_ = lean_ctor_get(v_a_844_, 0);
v_set_1074_ = lean_ctor_get(v_a_844_, 1);
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1073_, v_e_842_);
if (lean_obj_tag(v___x_1075_) == 1)
{
lean_object* v_val_1076_; lean_object* v___x_1077_; 
lean_dec_ref_known(v_e_842_, 3);
v_val_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_val_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_val_1076_);
lean_ctor_set(v___x_1077_, 1, v_a_844_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; uint64_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; uint8_t v___x_1084_; 
lean_dec(v___x_1075_);
v___x_1078_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1079_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_842_);
v___x_1080_ = lean_uint64_to_usize(v___x_1079_);
v___x_1081_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1074_, v___x_1080_, v_e_842_, v___x_1078_);
v___x_1082_ = lean_ptr_addr(v___x_1081_);
v___x_1083_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1084_ = lean_usize_dec_eq(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_dec_ref_known(v_e_842_, 3);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1081_);
lean_ctor_set(v___x_1085_, 1, v_a_844_);
return v___x_1085_;
}
else
{
uint8_t v_checkProj_1086_; 
lean_dec_ref(v___x_1081_);
v_checkProj_1086_ = lean_ctor_get_uint8(v_a_843_, sizeof(void*)*1 + 1);
if (v_checkProj_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_inc_ref(v_struct_1072_);
v___x_1087_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1072_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v_a_1089_; size_t v___x_1090_; size_t v___x_1091_; uint8_t v___x_1092_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
v_a_1089_ = lean_ctor_get(v___x_1087_, 1);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1087_, 2);
v___x_1090_ = lean_ptr_addr(v_struct_1072_);
v___x_1091_ = lean_ptr_addr(v_a_1088_);
v___x_1092_ = lean_usize_dec_eq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc(v_idx_1071_);
lean_inc(v_typeName_1070_);
v___x_1093_ = l_Lean_Expr_proj___override(v_typeName_1070_, v_idx_1071_, v_a_1088_);
v___x_1094_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v___x_1093_, v_a_1089_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
lean_dec(v_a_1088_);
lean_inc_ref(v_e_842_);
v___x_1095_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_e_842_, v_a_1089_);
return v___x_1095_;
}
}
else
{
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1096_; lean_object* v_a_1097_; lean_object* v___x_1098_; 
v_a_1096_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1096_);
v_a_1097_ = lean_ctor_get(v___x_1087_, 1);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1087_, 2);
v___x_1098_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_a_1096_, v_a_1097_);
return v___x_1098_;
}
else
{
lean_dec_ref_known(v_e_842_, 3);
return v___x_1087_;
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref_known(v_e_842_, 3);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_a_844_);
return v___x_1100_;
}
}
}
}
default: 
{
lean_object* v_map_1101_; lean_object* v_set_1102_; lean_object* v___x_1103_; 
v_map_1101_ = lean_ctor_get(v_a_844_, 0);
v_set_1102_ = lean_ctor_get(v_a_844_, 1);
v___x_1103_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1102_, v_e_842_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
lean_inc_ref(v_set_1102_);
lean_inc_ref(v_map_1101_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1114_ = lean_ctor_get(v_a_844_, 1);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_a_844_, 0);
lean_dec(v_unused_1115_);
v___x_1105_ = v_a_844_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_dec(v_a_844_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1107_ = lean_box(0);
lean_inc_ref(v_e_842_);
v___x_1108_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1102_, v_e_842_, v___x_1107_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_map_1101_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_e_842_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
return v___x_1111_;
}
}
}
else
{
lean_object* v_val_1116_; lean_object* v_fst_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v_e_842_);
v_val_1116_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1103_, 1);
v_fst_1117_ = lean_ctor_get(v_val_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_val_1116_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_val_1116_, 1);
lean_dec(v_unused_1125_);
v___x_1119_ = v_val_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_fst_1117_);
lean_dec(v_val_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v_a_844_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_fst_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_a_844_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
v___jp_845_:
{
if (lean_obj_tag(v___y_846_) == 0)
{
lean_object* v_a_847_; lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_847_ = lean_ctor_get(v___y_846_, 0);
lean_inc(v_a_847_);
v_a_848_ = lean_ctor_get(v___y_846_, 1);
lean_inc(v_a_848_);
lean_dec_ref_known(v___y_846_, 2);
v___x_849_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_a_847_, v_a_848_);
return v___x_849_;
}
else
{
lean_dec_ref(v_e_842_);
return v___y_846_;
}
}
v___jp_850_:
{
if (lean_obj_tag(v___y_851_) == 0)
{
lean_object* v_a_852_; lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_852_ = lean_ctor_get(v___y_851_, 0);
lean_inc(v_a_852_);
v_a_853_ = lean_ctor_get(v___y_851_, 1);
lean_inc(v_a_853_);
lean_dec_ref_known(v___y_851_, 2);
v___x_854_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_a_852_, v_a_853_);
return v___x_854_;
}
else
{
lean_dec_ref(v_e_842_);
return v___y_851_;
}
}
v___jp_855_:
{
if (lean_obj_tag(v___y_856_) == 0)
{
lean_object* v_a_857_; lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_857_ = lean_ctor_get(v___y_856_, 0);
lean_inc(v_a_857_);
v_a_858_ = lean_ctor_get(v___y_856_, 1);
lean_inc(v_a_858_);
lean_dec_ref_known(v___y_856_, 2);
v___x_859_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_a_857_, v_a_858_);
return v___x_859_;
}
else
{
lean_dec_ref(v_e_842_);
return v___y_856_;
}
}
v___jp_860_:
{
if (lean_obj_tag(v___y_861_) == 0)
{
lean_object* v_a_862_; lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_862_ = lean_ctor_get(v___y_861_, 0);
lean_inc(v_a_862_);
v_a_863_ = lean_ctor_get(v___y_861_, 1);
lean_inc(v_a_863_);
lean_dec_ref_known(v___y_861_, 2);
v___x_864_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_842_, v_a_862_, v_a_863_);
return v___x_864_;
}
else
{
lean_dec_ref(v_e_842_);
return v___y_861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1126_, v_a_1127_, v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1131_, v_x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1134_, v_x_1135_, v_x_1136_);
lean_dec_ref(v_x_1136_);
lean_dec_ref(v_x_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1138_, lean_object* v_m_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1139_, v_a_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1142_, lean_object* v_m_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1142_, v_m_1143_, v_a_1144_);
lean_dec_ref(v_a_1144_);
lean_dec_ref(v_m_1143_);
return v_res_1145_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1146_, lean_object* v_x_1147_, size_t v_x_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1147_, v_x_1148_, v_x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1147_ = stack[1].m_obj;
size_t v_x_1148_ = stack[2].m_num;
lean_object* v_x_1149_ = stack[3].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_box(0), v_x_1147_, v_x_1148_, v_x_1149_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
size_t v_x_11813__boxed_1156_; lean_object* v_res_1157_; 
v_x_11813__boxed_1156_ = lean_unbox_usize(v_x_1154_);
lean_dec(v_x_1154_);
v_res_1157_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1152_, v_x_1153_, v_x_11813__boxed_1156_, v_x_1155_);
lean_dec_ref(v_x_1155_);
lean_dec_ref(v_x_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1158_, lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1159_, v_x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1162_, lean_object* v_a_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1162_, v_a_1163_, v_x_1164_);
lean_dec(v_x_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1166_, lean_object* v_keys_1167_, lean_object* v_vals_1168_, lean_object* v_heq_1169_, lean_object* v_i_1170_, lean_object* v_k_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1167_, v_vals_1168_, v_i_1170_, v_k_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1173_, lean_object* v_keys_1174_, lean_object* v_vals_1175_, lean_object* v_heq_1176_, lean_object* v_i_1177_, lean_object* v_k_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1173_, v_keys_1174_, v_vals_1175_, v_heq_1176_, v_i_1177_, v_k_1178_);
lean_dec_ref(v_k_1178_);
lean_dec_ref(v_vals_1175_);
lean_dec_ref(v_keys_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1180_, lean_object* v_cache_1181_, lean_object* v_ctx_1182_, lean_object* v_s_1183_){
_start:
{
lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v___f_1184_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1185_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1180_);
v___x_1186_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1184_, v___f_1185_, v_s_1183_, v_e_1180_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_cache_1181_);
lean_ctor_set(v___x_1187_, 1, v_s_1183_);
v___x_1188_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1180_, v_ctx_1182_, v___x_1187_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 1);
v_a_1190_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v___x_1188_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1189_);
lean_inc(v_a_1190_);
lean_dec(v___x_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_set_1194_; lean_object* v___x_1196_; 
v_set_1194_ = lean_ctor_get(v_a_1189_, 1);
lean_inc_ref(v_set_1194_);
lean_dec(v_a_1189_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v_set_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1190_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_set_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v_a_1199_ = lean_ctor_get(v___x_1188_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1188_, 0);
lean_dec(v_unused_1209_);
v___x_1201_ = v___x_1188_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1188_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_map_1203_; lean_object* v_set_1204_; lean_object* v___x_1206_; 
v_map_1203_ = lean_ctor_get(v_a_1199_, 0);
lean_inc_ref(v_map_1203_);
v_set_1204_ = lean_ctor_get(v_a_1199_, 1);
lean_inc_ref(v_set_1204_);
lean_dec(v_a_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v_set_1204_);
lean_ctor_set(v___x_1201_, 0, v_map_1203_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_map_1203_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_set_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_val_1210_; lean_object* v_fst_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_cache_1181_);
lean_dec_ref(v_e_1180_);
v_val_1210_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v___x_1186_, 1);
v_fst_1211_ = lean_ctor_get(v_val_1210_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_val_1210_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_val_1210_, 1);
lean_dec(v_unused_1219_);
v___x_1213_ = v_val_1210_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_fst_1211_);
lean_dec(v_val_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v_s_1183_);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_fst_1211_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_s_1183_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1220_, lean_object* v_cache_1221_, lean_object* v_ctx_1222_, lean_object* v_s_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1220_, v_cache_1221_, v_ctx_1222_, v_s_1223_);
lean_dec_ref(v_ctx_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1227_; uint64_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1227_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1228_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1225_);
v___x_1229_ = lean_uint64_to_usize(v___x_1228_);
v___x_1230_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1229_, v_e_1225_, v___x_1227_);
v___x_1231_ = lean_ptr_addr(v___x_1230_);
v___x_1232_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1233_ = lean_usize_dec_eq(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref(v_e_1225_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1230_);
lean_ctor_set(v___x_1234_, 1, v_a_1226_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec_ref(v___x_1230_);
v___x_1235_ = lean_box(0);
lean_inc_ref(v_e_1225_);
v___x_1236_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1226_, v_e_1225_, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_e_1225_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1238_, v_a_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1242_, v_a_1243_, v_a_1244_);
lean_dec_ref(v_a_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1246_, lean_object* v_k_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___f_1250_; lean_object* v___x_1251_; uint64_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; uint8_t v___x_1257_; 
v___f_1250_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1251_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1252_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1246_);
v___x_1253_ = lean_uint64_to_usize(v___x_1252_);
lean_inc_ref(v_a_1249_);
v___x_1254_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1250_, v_a_1249_, v___x_1253_, v_e_1246_, v___x_1251_);
v___x_1255_ = lean_ptr_addr(v___x_1254_);
v___x_1256_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1257_ = lean_usize_dec_eq(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v_k_1247_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1254_);
lean_ctor_set(v___x_1258_, 1, v_a_1249_);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; 
lean_dec(v___x_1254_);
lean_inc_ref(v_a_1248_);
v___x_1259_ = lean_apply_2(v_k_1247_, v_a_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
v_a_1261_ = lean_ctor_get(v___x_1259_, 1);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1259_, 2);
v___x_1262_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1260_, v_a_1261_);
return v___x_1262_;
}
else
{
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1263_, lean_object* v_k_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1263_, v_k_1264_, v_a_1265_, v_a_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_unsigned_to_nat(16u);
v___x_1270_ = lean_mk_array(v___x_1269_, v___x_1268_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___y_1278_; lean_object* v___y_1283_; lean_object* v___y_1288_; lean_object* v___y_1293_; 
switch(lean_obj_tag(v_e_1274_))
{
case 4:
{
lean_object* v_declName_1297_; lean_object* v___x_1298_; uint64_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; size_t v___x_1302_; size_t v___x_1303_; uint8_t v___x_1304_; 
v_declName_1297_ = lean_ctor_get(v_e_1274_, 0);
v___x_1298_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1299_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1274_);
v___x_1300_ = lean_uint64_to_usize(v___x_1299_);
v___x_1301_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1276_, v___x_1300_, v_e_1274_, v___x_1298_);
v___x_1302_ = lean_ptr_addr(v___x_1301_);
v___x_1303_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1304_ = lean_usize_dec_eq(v___x_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref_known(v_e_1274_, 2);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1301_);
lean_ctor_set(v___x_1305_, 1, v_a_1276_);
return v___x_1305_;
}
else
{
uint8_t v___x_1306_; 
lean_dec_ref(v___x_1301_);
lean_inc(v_declName_1297_);
lean_inc_ref(v_a_1275_);
v___x_1306_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1275_, v_declName_1297_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_box(0);
lean_inc_ref(v_e_1274_);
v___x_1308_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1276_, v_e_1274_, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_e_1274_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec_ref_known(v_e_1274_, 2);
v___x_1310_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_a_1276_);
return v___x_1311_;
}
}
}
case 5:
{
lean_object* v_fn_1312_; lean_object* v_arg_1313_; lean_object* v___x_1314_; uint64_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; uint8_t v___x_1320_; 
v_fn_1312_ = lean_ctor_get(v_e_1274_, 0);
v_arg_1313_ = lean_ctor_get(v_e_1274_, 1);
v___x_1314_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1315_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1274_);
v___x_1316_ = lean_uint64_to_usize(v___x_1315_);
v___x_1317_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1276_, v___x_1316_, v_e_1274_, v___x_1314_);
v___x_1318_ = lean_ptr_addr(v___x_1317_);
v___x_1319_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1320_ = lean_usize_dec_eq(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_dec_ref_known(v_e_1274_, 2);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1317_);
lean_ctor_set(v___x_1321_, 1, v_a_1276_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; 
lean_dec_ref(v___x_1317_);
lean_inc_ref(v_fn_1312_);
v___x_1322_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1312_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v_a_1324_; lean_object* v___x_1325_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
v_a_1324_ = lean_ctor_get(v___x_1322_, 1);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1322_, 2);
lean_inc_ref(v_arg_1313_);
v___x_1325_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1313_, v_a_1275_, v_a_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v_a_1327_; size_t v___x_1328_; size_t v___x_1329_; uint8_t v___x_1330_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
v_a_1327_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1325_, 2);
v___x_1328_ = lean_ptr_addr(v_fn_1312_);
v___x_1329_ = lean_ptr_addr(v_a_1323_);
v___x_1330_ = lean_usize_dec_eq(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref_known(v_e_1274_, 2);
v___x_1331_ = l_Lean_Expr_app___override(v_a_1323_, v_a_1326_);
v___x_1332_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1331_, v_a_1327_);
return v___x_1332_;
}
else
{
size_t v___x_1333_; size_t v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_ptr_addr(v_arg_1313_);
v___x_1334_ = lean_ptr_addr(v_a_1326_);
v___x_1335_ = lean_usize_dec_eq(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref_known(v_e_1274_, 2);
v___x_1336_ = l_Lean_Expr_app___override(v_a_1323_, v_a_1326_);
v___x_1337_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1336_, v_a_1327_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; 
lean_dec(v_a_1326_);
lean_dec(v_a_1323_);
v___x_1338_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1274_, v_a_1327_);
return v___x_1338_;
}
}
}
else
{
lean_dec(v_a_1323_);
lean_dec_ref_known(v_e_1274_, 2);
v___y_1278_ = v___x_1325_;
goto v___jp_1277_;
}
}
else
{
lean_dec_ref_known(v_e_1274_, 2);
v___y_1278_ = v___x_1322_;
goto v___jp_1277_;
}
}
}
case 6:
{
lean_object* v_binderName_1339_; lean_object* v_binderType_1340_; lean_object* v_body_1341_; uint8_t v_binderInfo_1342_; lean_object* v___x_1343_; uint64_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; uint8_t v___x_1349_; 
v_binderName_1339_ = lean_ctor_get(v_e_1274_, 0);
v_binderType_1340_ = lean_ctor_get(v_e_1274_, 1);
v_body_1341_ = lean_ctor_get(v_e_1274_, 2);
v_binderInfo_1342_ = lean_ctor_get_uint8(v_e_1274_, sizeof(void*)*3 + 8);
v___x_1343_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1344_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1274_);
v___x_1345_ = lean_uint64_to_usize(v___x_1344_);
v___x_1346_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1276_, v___x_1345_, v_e_1274_, v___x_1343_);
v___x_1347_ = lean_ptr_addr(v___x_1346_);
v___x_1348_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1349_ = lean_usize_dec_eq(v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec_ref_known(v_e_1274_, 3);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1346_);
lean_ctor_set(v___x_1350_, 1, v_a_1276_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; 
lean_dec_ref(v___x_1346_);
lean_inc_ref(v_binderType_1340_);
v___x_1351_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1340_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
v_a_1353_ = lean_ctor_get(v___x_1351_, 1);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1351_, 2);
lean_inc_ref(v_body_1341_);
v___x_1354_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1341_, v_a_1275_, v_a_1353_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_a_1356_; size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
v_a_1356_ = lean_ctor_get(v___x_1354_, 1);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1354_, 2);
v___x_1357_ = lean_ptr_addr(v_binderType_1340_);
v___x_1358_ = lean_ptr_addr(v_a_1352_);
v___x_1359_ = lean_usize_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_inc(v_binderName_1339_);
lean_dec_ref_known(v_e_1274_, 3);
v___x_1360_ = l_Lean_Expr_lam___override(v_binderName_1339_, v_a_1352_, v_a_1355_, v_binderInfo_1342_);
v___x_1361_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1360_, v_a_1356_);
return v___x_1361_;
}
else
{
size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_ptr_addr(v_body_1341_);
v___x_1363_ = lean_ptr_addr(v_a_1355_);
v___x_1364_ = lean_usize_dec_eq(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc(v_binderName_1339_);
lean_dec_ref_known(v_e_1274_, 3);
v___x_1365_ = l_Lean_Expr_lam___override(v_binderName_1339_, v_a_1352_, v_a_1355_, v_binderInfo_1342_);
v___x_1366_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1365_, v_a_1356_);
return v___x_1366_;
}
else
{
uint8_t v___x_1367_; 
v___x_1367_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1342_, v_binderInfo_1342_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_inc(v_binderName_1339_);
lean_dec_ref_known(v_e_1274_, 3);
v___x_1368_ = l_Lean_Expr_lam___override(v_binderName_1339_, v_a_1352_, v_a_1355_, v_binderInfo_1342_);
v___x_1369_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1368_, v_a_1356_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; 
lean_dec(v_a_1355_);
lean_dec(v_a_1352_);
v___x_1370_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1274_, v_a_1356_);
return v___x_1370_;
}
}
}
}
else
{
lean_dec(v_a_1352_);
lean_dec_ref_known(v_e_1274_, 3);
v___y_1283_ = v___x_1354_;
goto v___jp_1282_;
}
}
else
{
lean_dec_ref_known(v_e_1274_, 3);
v___y_1283_ = v___x_1351_;
goto v___jp_1282_;
}
}
}
case 7:
{
lean_object* v_binderName_1371_; lean_object* v_binderType_1372_; lean_object* v_body_1373_; uint8_t v_binderInfo_1374_; lean_object* v___x_1375_; uint64_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; uint8_t v___x_1381_; 
v_binderName_1371_ = lean_ctor_get(v_e_1274_, 0);
v_binderType_1372_ = lean_ctor_get(v_e_1274_, 1);
v_body_1373_ = lean_ctor_get(v_e_1274_, 2);
v_binderInfo_1374_ = lean_ctor_get_uint8(v_e_1274_, sizeof(void*)*3 + 8);
v___x_1375_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1376_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1274_);
v___x_1377_ = lean_uint64_to_usize(v___x_1376_);
v___x_1378_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1276_, v___x_1377_, v_e_1274_, v___x_1375_);
v___x_1379_ = lean_ptr_addr(v___x_1378_);
v___x_1380_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1381_ = lean_usize_dec_eq(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref_known(v_e_1274_, 3);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1378_);
lean_ctor_set(v___x_1382_, 1, v_a_1276_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v___x_1378_);
lean_inc_ref(v_binderType_1372_);
v___x_1383_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1372_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
v_a_1385_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1383_, 2);
lean_inc_ref(v_body_1373_);
v___x_1386_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1373_, v_a_1275_, v_a_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v_a_1388_; size_t v___x_1389_; size_t v___x_1390_; uint8_t v___x_1391_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
v_a_1388_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1386_, 2);
v___x_1389_ = lean_ptr_addr(v_binderType_1372_);
v___x_1390_ = lean_ptr_addr(v_a_1384_);
v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_inc(v_binderName_1371_);
lean_dec_ref_known(v_e_1274_, 3);
v___x_1392_ = l_Lean_Expr_forallE___override(v_binderName_1371_, v_a_1384_, v_a_1387_, v_binderInfo_1374_);
v___x_1393_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1392_, v_a_1388_);
return v___x_1393_;
}
else
{
size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_ptr_addr(v_body_1373_);
v___x_1395_ = lean_ptr_addr(v_a_1387_);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc(v_binderName_1371_);
lean_dec_ref_known(v_e_1274_, 3);
v___x_1397_ = l_Lean_Expr_forallE___override(v_binderName_1371_, v_a_1384_, v_a_1387_, v_binderInfo_1374_);
v___x_1398_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1397_, v_a_1388_);
return v___x_1398_;
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1374_, v_binderInfo_1374_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_inc(v_binderName_1371_);
lean_dec_ref_known(v_e_1274_, 3);
v___x_1400_ = l_Lean_Expr_forallE___override(v_binderName_1371_, v_a_1384_, v_a_1387_, v_binderInfo_1374_);
v___x_1401_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1400_, v_a_1388_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; 
lean_dec(v_a_1387_);
lean_dec(v_a_1384_);
v___x_1402_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1274_, v_a_1388_);
return v___x_1402_;
}
}
}
}
else
{
lean_dec(v_a_1384_);
lean_dec_ref_known(v_e_1274_, 3);
v___y_1288_ = v___x_1386_;
goto v___jp_1287_;
}
}
else
{
lean_dec_ref_known(v_e_1274_, 3);
v___y_1288_ = v___x_1383_;
goto v___jp_1287_;
}
}
}
case 8:
{
lean_object* v_declName_1403_; lean_object* v_type_1404_; lean_object* v_value_1405_; lean_object* v_body_1406_; uint8_t v_nondep_1407_; lean_object* v___x_1408_; uint64_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; uint8_t v___x_1414_; 
v_declName_1403_ = lean_ctor_get(v_e_1274_, 0);
v_type_1404_ = lean_ctor_get(v_e_1274_, 1);
v_value_1405_ = lean_ctor_get(v_e_1274_, 2);
v_body_1406_ = lean_ctor_get(v_e_1274_, 3);
v_nondep_1407_ = lean_ctor_get_uint8(v_e_1274_, sizeof(void*)*4 + 8);
v___x_1408_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1409_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1274_);
v___x_1410_ = lean_uint64_to_usize(v___x_1409_);
v___x_1411_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1276_, v___x_1410_, v_e_1274_, v___x_1408_);
v___x_1412_ = lean_ptr_addr(v___x_1411_);
v___x_1413_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref_known(v_e_1274_, 4);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1411_);
lean_ctor_set(v___x_1415_, 1, v_a_1276_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; 
lean_dec_ref(v___x_1411_);
lean_inc_ref(v_type_1404_);
v___x_1416_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1404_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
v_a_1418_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1416_, 2);
lean_inc_ref(v_value_1405_);
v___x_1419_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1405_, v_a_1275_, v_a_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
v_a_1421_ = lean_ctor_get(v___x_1419_, 1);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1419_, 2);
lean_inc_ref(v_body_1406_);
v___x_1422_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1406_, v_a_1275_, v_a_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_a_1424_; size_t v___x_1425_; size_t v___x_1426_; uint8_t v___x_1427_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
v_a_1424_ = lean_ctor_get(v___x_1422_, 1);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1422_, 2);
v___x_1425_ = lean_ptr_addr(v_type_1404_);
v___x_1426_ = lean_ptr_addr(v_a_1417_);
v___x_1427_ = lean_usize_dec_eq(v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_inc(v_declName_1403_);
lean_dec_ref_known(v_e_1274_, 4);
v___x_1428_ = l_Lean_Expr_letE___override(v_declName_1403_, v_a_1417_, v_a_1420_, v_a_1423_, v_nondep_1407_);
v___x_1429_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1428_, v_a_1424_);
return v___x_1429_;
}
else
{
size_t v___x_1430_; size_t v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = lean_ptr_addr(v_value_1405_);
v___x_1431_ = lean_ptr_addr(v_a_1420_);
v___x_1432_ = lean_usize_dec_eq(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_inc(v_declName_1403_);
lean_dec_ref_known(v_e_1274_, 4);
v___x_1433_ = l_Lean_Expr_letE___override(v_declName_1403_, v_a_1417_, v_a_1420_, v_a_1423_, v_nondep_1407_);
v___x_1434_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1433_, v_a_1424_);
return v___x_1434_;
}
else
{
size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_ptr_addr(v_body_1406_);
v___x_1436_ = lean_ptr_addr(v_a_1423_);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_inc(v_declName_1403_);
lean_dec_ref_known(v_e_1274_, 4);
v___x_1438_ = l_Lean_Expr_letE___override(v_declName_1403_, v_a_1417_, v_a_1420_, v_a_1423_, v_nondep_1407_);
v___x_1439_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1438_, v_a_1424_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_a_1423_);
lean_dec(v_a_1420_);
lean_dec(v_a_1417_);
v___x_1440_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1274_, v_a_1424_);
return v___x_1440_;
}
}
}
}
else
{
lean_dec(v_a_1420_);
lean_dec(v_a_1417_);
lean_dec_ref_known(v_e_1274_, 4);
v___y_1293_ = v___x_1422_;
goto v___jp_1292_;
}
}
else
{
lean_dec(v_a_1417_);
lean_dec_ref_known(v_e_1274_, 4);
v___y_1293_ = v___x_1419_;
goto v___jp_1292_;
}
}
else
{
lean_dec_ref_known(v_e_1274_, 4);
v___y_1293_ = v___x_1416_;
goto v___jp_1292_;
}
}
}
case 10:
{
lean_object* v_data_1441_; lean_object* v_expr_1442_; lean_object* v___x_1443_; uint64_t v___x_1444_; size_t v___x_1445_; lean_object* v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; uint8_t v___x_1449_; 
v_data_1441_ = lean_ctor_get(v_e_1274_, 0);
v_expr_1442_ = lean_ctor_get(v_e_1274_, 1);
v___x_1443_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1444_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1274_);
v___x_1445_ = lean_uint64_to_usize(v___x_1444_);
v___x_1446_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1276_, v___x_1445_, v_e_1274_, v___x_1443_);
v___x_1447_ = lean_ptr_addr(v___x_1446_);
v___x_1448_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1449_ = lean_usize_dec_eq(v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref_known(v_e_1274_, 2);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1446_);
lean_ctor_set(v___x_1450_, 1, v_a_1276_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; 
lean_dec_ref(v___x_1446_);
lean_inc_ref(v_expr_1442_);
v___x_1451_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1442_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v_a_1453_; size_t v___x_1454_; size_t v___x_1455_; uint8_t v___x_1456_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
v_a_1453_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1451_, 2);
v___x_1454_ = lean_ptr_addr(v_expr_1442_);
v___x_1455_ = lean_ptr_addr(v_a_1452_);
v___x_1456_ = lean_usize_dec_eq(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_inc(v_data_1441_);
lean_dec_ref_known(v_e_1274_, 2);
v___x_1457_ = l_Lean_Expr_mdata___override(v_data_1441_, v_a_1452_);
v___x_1458_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1457_, v_a_1453_);
return v___x_1458_;
}
else
{
lean_object* v___x_1459_; 
lean_dec(v_a_1452_);
v___x_1459_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1274_, v_a_1453_);
return v___x_1459_;
}
}
else
{
lean_dec_ref_known(v_e_1274_, 2);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1460_; lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1460_);
v_a_1461_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1451_, 2);
v___x_1462_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1460_, v_a_1461_);
return v___x_1462_;
}
else
{
return v___x_1451_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1463_; lean_object* v_idx_1464_; lean_object* v_struct_1465_; lean_object* v___x_1466_; uint64_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; uint8_t v___x_1472_; 
v_typeName_1463_ = lean_ctor_get(v_e_1274_, 0);
v_idx_1464_ = lean_ctor_get(v_e_1274_, 1);
v_struct_1465_ = lean_ctor_get(v_e_1274_, 2);
v___x_1466_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1467_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1274_);
v___x_1468_ = lean_uint64_to_usize(v___x_1467_);
v___x_1469_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1276_, v___x_1468_, v_e_1274_, v___x_1466_);
v___x_1470_ = lean_ptr_addr(v___x_1469_);
v___x_1471_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1472_ = lean_usize_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec_ref_known(v_e_1274_, 3);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1469_);
lean_ctor_set(v___x_1473_, 1, v_a_1276_);
return v___x_1473_;
}
else
{
uint8_t v_checkProj_1474_; 
lean_dec_ref(v___x_1469_);
v_checkProj_1474_ = lean_ctor_get_uint8(v_a_1275_, sizeof(void*)*1 + 1);
if (v_checkProj_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_inc_ref(v_struct_1465_);
v___x_1475_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1465_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_a_1477_; size_t v___x_1478_; size_t v___x_1479_; uint8_t v___x_1480_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v_a_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1475_, 2);
v___x_1478_ = lean_ptr_addr(v_struct_1465_);
v___x_1479_ = lean_ptr_addr(v_a_1476_);
v___x_1480_ = lean_usize_dec_eq(v___x_1478_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_inc(v_idx_1464_);
lean_inc(v_typeName_1463_);
lean_dec_ref_known(v_e_1274_, 3);
v___x_1481_ = l_Lean_Expr_proj___override(v_typeName_1463_, v_idx_1464_, v_a_1476_);
v___x_1482_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1481_, v_a_1477_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; 
lean_dec(v_a_1476_);
v___x_1483_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1274_, v_a_1477_);
return v___x_1483_;
}
}
else
{
lean_dec_ref_known(v_e_1274_, 3);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1484_; lean_object* v_a_1485_; lean_object* v___x_1486_; 
v_a_1484_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1484_);
v_a_1485_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1475_, 2);
v___x_1486_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1484_, v_a_1485_);
return v___x_1486_;
}
else
{
return v___x_1475_;
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref_known(v_e_1274_, 3);
v___x_1487_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_a_1276_);
return v___x_1488_;
}
}
}
default: 
{
lean_object* v___x_1489_; 
v___x_1489_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1274_, v_a_1276_);
return v___x_1489_;
}
}
v___jp_1277_:
{
if (lean_obj_tag(v___y_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_a_1280_; lean_object* v___x_1281_; 
v_a_1279_ = lean_ctor_get(v___y_1278_, 0);
lean_inc(v_a_1279_);
v_a_1280_ = lean_ctor_get(v___y_1278_, 1);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___y_1278_, 2);
v___x_1281_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1279_, v_a_1280_);
return v___x_1281_;
}
else
{
return v___y_1278_;
}
}
v___jp_1282_:
{
if (lean_obj_tag(v___y_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___y_1283_, 0);
lean_inc(v_a_1284_);
v_a_1285_ = lean_ctor_get(v___y_1283_, 1);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___y_1283_, 2);
v___x_1286_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1284_, v_a_1285_);
return v___x_1286_;
}
else
{
return v___y_1283_;
}
}
v___jp_1287_:
{
if (lean_obj_tag(v___y_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1289_ = lean_ctor_get(v___y_1288_, 0);
lean_inc(v_a_1289_);
v_a_1290_ = lean_ctor_get(v___y_1288_, 1);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___y_1288_, 2);
v___x_1291_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1289_, v_a_1290_);
return v___x_1291_;
}
else
{
return v___y_1288_;
}
}
v___jp_1292_:
{
if (lean_obj_tag(v___y_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v_a_1295_; lean_object* v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___y_1293_, 0);
lean_inc(v_a_1294_);
v_a_1295_ = lean_ctor_get(v___y_1293_, 1);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___y_1293_, 2);
v___x_1296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1294_, v_a_1295_);
return v___x_1296_;
}
else
{
return v___y_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1490_, v_a_1491_, v_a_1492_);
lean_dec_ref(v_a_1491_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1494_, v_a_1495_, v_a_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1498_, v_a_1499_, v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1501_;
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

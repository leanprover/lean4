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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_545_, lean_object* v_r_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_map_548_; lean_object* v_set_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_573_; 
v_map_548_ = lean_ctor_get(v_a_547_, 0);
v_set_549_ = lean_ctor_get(v_a_547_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_573_ == 0)
{
v___x_551_ = v_a_547_;
v_isShared_552_ = v_isSharedCheck_573_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_set_549_);
lean_inc(v_map_548_);
lean_dec(v_a_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_573_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; uint64_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_553_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_554_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_546_);
v___x_555_ = lean_uint64_to_usize(v___x_554_);
v___x_556_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_549_, v___x_555_, v_r_546_, v___x_553_);
v___x_557_ = lean_ptr_addr(v___x_556_);
v___x_558_ = lean_ptr_addr(v___x_553_);
v___x_559_ = lean_usize_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec_ref(v_r_546_);
lean_inc_ref(v___x_556_);
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_548_, v_e_545_, v___x_556_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_560_);
v___x_562_ = v___x_551_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_set_549_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_556_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
return v___x_563_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec_ref(v___x_556_);
lean_inc_ref_n(v_r_546_, 4);
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_548_, v_e_545_, v_r_546_);
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_565_, v_r_546_, v_r_546_);
v___x_567_ = lean_box(0);
v___x_568_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_549_, v_r_546_, v___x_567_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_568_);
lean_ctor_set(v___x_551_, 0, v___x_566_);
v___x_570_ = v___x_551_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_r_546_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_574_, lean_object* v_r_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_574_, v_r_575_, v_a_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_579_, lean_object* v_r_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_579_, v_r_580_, v_a_581_, v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_584_, lean_object* v_x_585_, size_t v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_585_, v_x_586_, v_x_587_, v_x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
size_t v_x_2513__boxed_595_; lean_object* v_res_596_; 
v_x_2513__boxed_595_ = lean_unbox_usize(v_x_592_);
lean_dec(v_x_592_);
v_res_596_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_590_, v_x_591_, v_x_2513__boxed_595_, v_x_593_, v_x_594_);
lean_dec_ref(v_x_594_);
lean_dec_ref(v_x_593_);
lean_dec_ref(v_x_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_a_599_, lean_object* v_b_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_598_, v_a_599_, v_b_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_603_, v_x_604_, v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_607_, lean_object* v_keys_608_, lean_object* v_vals_609_, lean_object* v_heq_610_, lean_object* v_i_611_, lean_object* v_k_612_, lean_object* v_k_u2080_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_608_, v_i_611_, v_k_612_, v_k_u2080_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_615_, lean_object* v_keys_616_, lean_object* v_vals_617_, lean_object* v_heq_618_, lean_object* v_i_619_, lean_object* v_k_620_, lean_object* v_k_u2080_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_615_, v_keys_616_, v_vals_617_, v_heq_618_, v_i_619_, v_k_620_, v_k_u2080_621_);
lean_dec_ref(v_k_u2080_621_);
lean_dec_ref(v_k_620_);
lean_dec_ref(v_vals_617_);
lean_dec_ref(v_keys_616_);
return v_res_622_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_623_, lean_object* v_a_624_, lean_object* v_x_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_624_, v_x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_627_, lean_object* v_a_628_, lean_object* v_x_629_){
_start:
{
uint8_t v_res_630_; lean_object* v_r_631_; 
v_res_630_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_627_, v_a_628_, v_x_629_);
lean_dec(v_x_629_);
lean_dec_ref(v_a_628_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_632_, lean_object* v_data_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_635_, lean_object* v_a_636_, lean_object* v_b_637_, lean_object* v_x_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_636_, v_b_637_, v_x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_640_, lean_object* v_x_641_, size_t v_x_642_, size_t v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_641_, v_x_642_, v_x_643_, v_x_644_, v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
size_t v_x_2550__boxed_653_; size_t v_x_2551__boxed_654_; lean_object* v_res_655_; 
v_x_2550__boxed_653_ = lean_unbox_usize(v_x_649_);
lean_dec(v_x_649_);
v_x_2551__boxed_654_ = lean_unbox_usize(v_x_650_);
lean_dec(v_x_650_);
v_res_655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_647_, v_x_648_, v_x_2550__boxed_653_, v_x_2551__boxed_654_, v_x_651_, v_x_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_656_, lean_object* v_i_657_, lean_object* v_source_658_, lean_object* v_target_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_657_, v_source_658_, v_target_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_661_, lean_object* v_n_662_, lean_object* v_k_663_, lean_object* v_v_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_662_, v_k_663_, v_v_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_666_, size_t v_depth_667_, lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_heq_670_, lean_object* v_i_671_, lean_object* v_entries_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_667_, v_keys_668_, v_vals_669_, v_i_671_, v_entries_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_674_, lean_object* v_depth_675_, lean_object* v_keys_676_, lean_object* v_vals_677_, lean_object* v_heq_678_, lean_object* v_i_679_, lean_object* v_entries_680_){
_start:
{
size_t v_depth_boxed_681_; lean_object* v_res_682_; 
v_depth_boxed_681_ = lean_unbox_usize(v_depth_675_);
lean_dec(v_depth_675_);
v_res_682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_674_, v_depth_boxed_681_, v_keys_676_, v_vals_677_, v_heq_678_, v_i_679_, v_entries_680_);
lean_dec_ref(v_vals_677_);
lean_dec_ref(v_keys_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_684_, v_x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_687_, lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_688_, v_x_689_, v_x_690_, v_x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_695_, lean_object* v_k_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_map_699_; lean_object* v_set_700_; lean_object* v___f_701_; lean_object* v___f_702_; lean_object* v___x_703_; 
v_map_699_ = lean_ctor_get(v_a_698_, 0);
v_set_700_ = lean_ctor_get(v_a_698_, 1);
v___f_701_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_702_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_695_);
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_701_, v___f_702_, v_map_699_, v_e_695_);
if (lean_obj_tag(v___x_703_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_705_; 
lean_dec_ref(v_k_696_);
lean_dec_ref(v_e_695_);
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
lean_object* v___f_706_; lean_object* v___x_707_; uint64_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; size_t v___x_711_; size_t v___x_712_; uint8_t v___x_713_; 
lean_dec(v___x_703_);
v___f_706_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_707_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_708_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_695_);
v___x_709_ = lean_uint64_to_usize(v___x_708_);
lean_inc_ref(v_e_695_);
lean_inc_ref(v_set_700_);
v___x_710_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_706_, v_set_700_, v___x_709_, v_e_695_, v___x_707_);
v___x_711_ = lean_ptr_addr(v___x_710_);
v___x_712_ = lean_ptr_addr(v___x_707_);
v___x_713_ = lean_usize_dec_eq(v___x_711_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v_k_696_);
lean_dec_ref(v_e_695_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_710_);
lean_ctor_set(v___x_714_, 1, v_a_698_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; 
lean_dec(v___x_710_);
lean_inc_ref(v_a_697_);
v___x_715_ = lean_apply_2(v_k_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
v_a_717_ = lean_ctor_get(v___x_715_, 1);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_715_, 2);
v___x_718_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_695_, v_a_716_, v_a_717_);
return v___x_718_;
}
else
{
lean_dec_ref(v_e_695_);
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_719_, lean_object* v_k_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_719_, v_k_720_, v_a_721_, v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_724_, lean_object* v_x_725_){
_start:
{
if (lean_obj_tag(v_x_725_) == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
else
{
lean_object* v_key_727_; lean_object* v_value_728_; lean_object* v_tail_729_; size_t v___x_730_; size_t v___x_731_; uint8_t v___x_732_; 
v_key_727_ = lean_ctor_get(v_x_725_, 0);
v_value_728_ = lean_ctor_get(v_x_725_, 1);
v_tail_729_ = lean_ctor_get(v_x_725_, 2);
v___x_730_ = lean_ptr_addr(v_key_727_);
v___x_731_ = lean_ptr_addr(v_a_724_);
v___x_732_ = lean_usize_dec_eq(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
v_x_725_ = v_tail_729_;
goto _start;
}
else
{
lean_object* v___x_734_; 
lean_inc(v_value_728_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_value_728_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_735_, lean_object* v_x_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_735_, v_x_736_);
lean_dec(v_x_736_);
lean_dec_ref(v_a_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_buckets_740_; lean_object* v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; uint64_t v___x_745_; uint64_t v___x_746_; uint64_t v___x_747_; uint64_t v_fold_748_; uint64_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; size_t v___x_752_; size_t v___x_753_; size_t v___x_754_; size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_buckets_740_ = lean_ctor_get(v_m_738_, 1);
v___x_741_ = lean_array_get_size(v_buckets_740_);
v___x_742_ = lean_ptr_addr(v_a_739_);
v___x_743_ = ((size_t)3ULL);
v___x_744_ = lean_usize_shift_right(v___x_742_, v___x_743_);
v___x_745_ = lean_usize_to_uint64(v___x_744_);
v___x_746_ = 32ULL;
v___x_747_ = lean_uint64_shift_right(v___x_745_, v___x_746_);
v_fold_748_ = lean_uint64_xor(v___x_745_, v___x_747_);
v___x_749_ = 16ULL;
v___x_750_ = lean_uint64_shift_right(v_fold_748_, v___x_749_);
v___x_751_ = lean_uint64_xor(v_fold_748_, v___x_750_);
v___x_752_ = lean_uint64_to_usize(v___x_751_);
v___x_753_ = lean_usize_of_nat(v___x_741_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_sub(v___x_753_, v___x_754_);
v___x_756_ = lean_usize_land(v___x_752_, v___x_755_);
v___x_757_ = lean_array_uget_borrowed(v_buckets_740_, v___x_756_);
v___x_758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_739_, v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_759_, v_a_760_);
lean_dec_ref(v_a_760_);
lean_dec_ref(v_m_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_762_, lean_object* v_vals_763_, lean_object* v_i_764_, lean_object* v_k_765_){
_start:
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_array_get_size(v_keys_762_);
v___x_767_ = lean_nat_dec_lt(v_i_764_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec(v_i_764_);
v___x_768_ = lean_box(0);
return v___x_768_;
}
else
{
lean_object* v_k_x27_769_; uint8_t v___x_770_; 
v_k_x27_769_ = lean_array_fget_borrowed(v_keys_762_, v_i_764_);
v___x_770_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_765_, v_k_x27_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_i_764_, v___x_771_);
lean_dec(v_i_764_);
v_i_764_ = v___x_772_;
goto _start;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_array_fget_borrowed(v_vals_763_, v_i_764_);
lean_dec(v_i_764_);
lean_inc(v___x_774_);
lean_inc(v_k_x27_769_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_k_x27_769_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_777_, lean_object* v_vals_778_, lean_object* v_i_779_, lean_object* v_k_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_777_, v_vals_778_, v_i_779_, v_k_780_);
lean_dec_ref(v_k_780_);
lean_dec_ref(v_vals_778_);
lean_dec_ref(v_keys_777_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_782_, size_t v_x_783_, lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v_es_785_; lean_object* v___x_786_; size_t v___x_787_; size_t v___x_788_; lean_object* v_j_789_; lean_object* v___x_790_; 
v_es_785_ = lean_ctor_get(v_x_782_, 0);
v___x_786_ = lean_box(2);
v___x_787_ = ((size_t)31ULL);
v___x_788_ = lean_usize_land(v_x_783_, v___x_787_);
v_j_789_ = lean_usize_to_nat(v___x_788_);
v___x_790_ = lean_array_get_borrowed(v___x_786_, v_es_785_, v_j_789_);
lean_dec(v_j_789_);
switch(lean_obj_tag(v___x_790_))
{
case 0:
{
lean_object* v_key_791_; lean_object* v_val_792_; uint8_t v___x_793_; 
v_key_791_ = lean_ctor_get(v___x_790_, 0);
v_val_792_ = lean_ctor_get(v___x_790_, 1);
v___x_793_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_784_, v_key_791_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
v___x_794_ = lean_box(0);
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_inc(v_val_792_);
lean_inc(v_key_791_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_key_791_);
lean_ctor_set(v___x_795_, 1, v_val_792_);
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
case 1:
{
lean_object* v_node_797_; size_t v___x_798_; size_t v___x_799_; 
v_node_797_ = lean_ctor_get(v___x_790_, 0);
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_usize_shift_right(v_x_783_, v___x_798_);
v_x_782_ = v_node_797_;
v_x_783_ = v___x_799_;
goto _start;
}
default: 
{
lean_object* v___x_801_; 
v___x_801_ = lean_box(0);
return v___x_801_;
}
}
}
else
{
lean_object* v_ks_802_; lean_object* v_vs_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_ks_802_ = lean_ctor_get(v_x_782_, 0);
v_vs_803_ = lean_ctor_get(v_x_782_, 1);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_802_, v_vs_803_, v___x_804_, v_x_784_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_10839__boxed_809_; lean_object* v_res_810_; 
v_x_10839__boxed_809_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_810_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_806_, v_x_10839__boxed_809_, v_x_808_);
lean_dec_ref(v_x_808_);
lean_dec_ref(v_x_806_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
uint64_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_813_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_812_);
v___x_814_ = lean_uint64_to_usize(v___x_813_);
v___x_815_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_811_, v___x_814_, v_x_812_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_816_, v_x_817_);
lean_dec_ref(v_x_817_);
lean_dec_ref(v_x_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
switch(lean_obj_tag(v_e_819_))
{
case 4:
{
lean_object* v_declName_822_; lean_object* v_map_823_; lean_object* v_set_824_; lean_object* v___x_825_; 
v_declName_822_ = lean_ctor_get(v_e_819_, 0);
v_map_823_ = lean_ctor_get(v_a_821_, 0);
v_set_824_ = lean_ctor_get(v_a_821_, 1);
v___x_825_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_824_, v_e_819_);
if (lean_obj_tag(v___x_825_) == 0)
{
uint8_t v___x_826_; 
lean_inc(v_declName_822_);
lean_inc_ref(v_a_820_);
v___x_826_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_820_, v_declName_822_);
if (v___x_826_ == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_836_; 
lean_inc_ref(v_set_824_);
lean_inc_ref(v_map_823_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_821_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_837_ = lean_ctor_get(v_a_821_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_a_821_, 0);
lean_dec(v_unused_838_);
v___x_828_ = v_a_821_;
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_a_821_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_830_ = lean_box(0);
lean_inc_ref(v_e_819_);
v___x_831_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_824_, v_e_819_, v___x_830_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_map_823_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_831_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_e_819_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
return v___x_834_;
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref_known(v_e_819_, 2);
v___x_839_ = lean_box(0);
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_a_821_);
return v___x_840_;
}
}
else
{
lean_object* v_val_841_; lean_object* v_fst_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref_known(v_e_819_, 2);
v_val_841_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_825_, 1);
v_fst_842_ = lean_ctor_get(v_val_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_val_841_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_val_841_, 1);
lean_dec(v_unused_850_);
v___x_844_ = v_val_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_fst_842_);
lean_dec(v_val_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_a_821_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_fst_842_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_821_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
case 5:
{
lean_object* v_fn_851_; lean_object* v_arg_852_; lean_object* v_map_853_; lean_object* v_set_854_; lean_object* v___x_855_; 
v_fn_851_ = lean_ctor_get(v_e_819_, 0);
v_arg_852_ = lean_ctor_get(v_e_819_, 1);
v_map_853_ = lean_ctor_get(v_a_821_, 0);
v_set_854_ = lean_ctor_get(v_a_821_, 1);
v___x_855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_853_, v_e_819_);
if (lean_obj_tag(v___x_855_) == 1)
{
lean_object* v_val_856_; lean_object* v___x_857_; 
lean_dec_ref_known(v_e_819_, 2);
v_val_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_val_856_);
lean_ctor_set(v___x_857_, 1, v_a_821_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; uint64_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; uint8_t v___x_864_; 
lean_dec(v___x_855_);
v___x_858_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_859_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_819_);
v___x_860_ = lean_uint64_to_usize(v___x_859_);
v___x_861_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_854_, v___x_860_, v_e_819_, v___x_858_);
v___x_862_ = lean_ptr_addr(v___x_861_);
v___x_863_ = lean_ptr_addr(v___x_858_);
v___x_864_ = lean_usize_dec_eq(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec_ref_known(v_e_819_, 2);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_861_);
lean_ctor_set(v___x_865_, 1, v_a_821_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; 
lean_dec_ref(v___x_861_);
lean_inc_ref(v_fn_851_);
v___x_866_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_851_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
v_a_868_ = lean_ctor_get(v___x_866_, 1);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_866_, 2);
lean_inc_ref(v_arg_852_);
v___x_869_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_852_, v_a_820_, v_a_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_a_871_; size_t v___x_872_; size_t v___x_873_; uint8_t v___x_874_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
v_a_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_869_, 2);
v___x_872_ = lean_ptr_addr(v_fn_851_);
v___x_873_ = lean_ptr_addr(v_a_867_);
v___x_874_ = lean_usize_dec_eq(v___x_872_, v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = l_Lean_Expr_app___override(v_a_867_, v_a_870_);
v___x_876_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_875_, v_a_871_);
return v___x_876_;
}
else
{
size_t v___x_877_; size_t v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_ptr_addr(v_arg_852_);
v___x_878_ = lean_ptr_addr(v_a_870_);
v___x_879_ = lean_usize_dec_eq(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = l_Lean_Expr_app___override(v_a_867_, v_a_870_);
v___x_881_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_880_, v_a_871_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v_a_870_);
lean_dec(v_a_867_);
lean_inc_ref(v_e_819_);
v___x_882_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v_e_819_, v_a_871_);
return v___x_882_;
}
}
}
else
{
lean_dec(v_a_867_);
lean_dec_ref_known(v_e_819_, 2);
return v___x_869_;
}
}
else
{
lean_dec_ref_known(v_e_819_, 2);
return v___x_866_;
}
}
}
}
case 6:
{
lean_object* v_binderName_883_; lean_object* v_binderType_884_; lean_object* v_body_885_; uint8_t v_binderInfo_886_; lean_object* v_map_887_; lean_object* v_set_888_; lean_object* v___x_889_; 
v_binderName_883_ = lean_ctor_get(v_e_819_, 0);
v_binderType_884_ = lean_ctor_get(v_e_819_, 1);
v_body_885_ = lean_ctor_get(v_e_819_, 2);
v_binderInfo_886_ = lean_ctor_get_uint8(v_e_819_, sizeof(void*)*3 + 8);
v_map_887_ = lean_ctor_get(v_a_821_, 0);
v_set_888_ = lean_ctor_get(v_a_821_, 1);
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_887_, v_e_819_);
if (lean_obj_tag(v___x_889_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_891_; 
lean_dec_ref_known(v_e_819_, 3);
v_val_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_val_890_);
lean_ctor_set(v___x_891_, 1, v_a_821_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; uint64_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; size_t v___x_896_; size_t v___x_897_; uint8_t v___x_898_; 
lean_dec(v___x_889_);
v___x_892_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_893_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_819_);
v___x_894_ = lean_uint64_to_usize(v___x_893_);
v___x_895_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_888_, v___x_894_, v_e_819_, v___x_892_);
v___x_896_ = lean_ptr_addr(v___x_895_);
v___x_897_ = lean_ptr_addr(v___x_892_);
v___x_898_ = lean_usize_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec_ref_known(v_e_819_, 3);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_895_);
lean_ctor_set(v___x_899_, 1, v_a_821_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; 
lean_dec_ref(v___x_895_);
lean_inc_ref(v_binderType_884_);
v___x_900_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_884_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
v_a_902_ = lean_ctor_get(v___x_900_, 1);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_900_, 2);
lean_inc_ref(v_body_885_);
v___x_903_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_885_, v_a_820_, v_a_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v_a_905_; size_t v___x_906_; size_t v___x_907_; uint8_t v___x_908_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
v_a_905_ = lean_ctor_get(v___x_903_, 1);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_903_, 2);
v___x_906_ = lean_ptr_addr(v_binderType_884_);
v___x_907_ = lean_ptr_addr(v_a_901_);
v___x_908_ = lean_usize_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc(v_binderName_883_);
v___x_909_ = l_Lean_Expr_lam___override(v_binderName_883_, v_a_901_, v_a_904_, v_binderInfo_886_);
v___x_910_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_909_, v_a_905_);
return v___x_910_;
}
else
{
size_t v___x_911_; size_t v___x_912_; uint8_t v___x_913_; 
v___x_911_ = lean_ptr_addr(v_body_885_);
v___x_912_ = lean_ptr_addr(v_a_904_);
v___x_913_ = lean_usize_dec_eq(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_inc(v_binderName_883_);
v___x_914_ = l_Lean_Expr_lam___override(v_binderName_883_, v_a_901_, v_a_904_, v_binderInfo_886_);
v___x_915_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_914_, v_a_905_);
return v___x_915_;
}
else
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_886_, v_binderInfo_886_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_inc(v_binderName_883_);
v___x_917_ = l_Lean_Expr_lam___override(v_binderName_883_, v_a_901_, v_a_904_, v_binderInfo_886_);
v___x_918_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_917_, v_a_905_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; 
lean_dec(v_a_904_);
lean_dec(v_a_901_);
lean_inc_ref(v_e_819_);
v___x_919_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v_e_819_, v_a_905_);
return v___x_919_;
}
}
}
}
else
{
lean_dec(v_a_901_);
lean_dec_ref_known(v_e_819_, 3);
return v___x_903_;
}
}
else
{
lean_dec_ref_known(v_e_819_, 3);
return v___x_900_;
}
}
}
}
case 7:
{
lean_object* v_binderName_920_; lean_object* v_binderType_921_; lean_object* v_body_922_; uint8_t v_binderInfo_923_; lean_object* v_map_924_; lean_object* v_set_925_; lean_object* v___x_926_; 
v_binderName_920_ = lean_ctor_get(v_e_819_, 0);
v_binderType_921_ = lean_ctor_get(v_e_819_, 1);
v_body_922_ = lean_ctor_get(v_e_819_, 2);
v_binderInfo_923_ = lean_ctor_get_uint8(v_e_819_, sizeof(void*)*3 + 8);
v_map_924_ = lean_ctor_get(v_a_821_, 0);
v_set_925_ = lean_ctor_get(v_a_821_, 1);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_924_, v_e_819_);
if (lean_obj_tag(v___x_926_) == 1)
{
lean_object* v_val_927_; lean_object* v___x_928_; 
lean_dec_ref_known(v_e_819_, 3);
v_val_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_val_927_);
lean_ctor_set(v___x_928_, 1, v_a_821_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; uint64_t v___x_930_; size_t v___x_931_; lean_object* v___x_932_; size_t v___x_933_; size_t v___x_934_; uint8_t v___x_935_; 
lean_dec(v___x_926_);
v___x_929_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_930_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_819_);
v___x_931_ = lean_uint64_to_usize(v___x_930_);
v___x_932_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_925_, v___x_931_, v_e_819_, v___x_929_);
v___x_933_ = lean_ptr_addr(v___x_932_);
v___x_934_ = lean_ptr_addr(v___x_929_);
v___x_935_ = lean_usize_dec_eq(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec_ref_known(v_e_819_, 3);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_932_);
lean_ctor_set(v___x_936_, 1, v_a_821_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; 
lean_dec_ref(v___x_932_);
lean_inc_ref(v_binderType_921_);
v___x_937_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_921_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v_a_939_; lean_object* v___x_940_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
v_a_939_ = lean_ctor_get(v___x_937_, 1);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_937_, 2);
lean_inc_ref(v_body_922_);
v___x_940_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_922_, v_a_820_, v_a_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_a_942_; size_t v___x_943_; size_t v___x_944_; uint8_t v___x_945_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
v_a_942_ = lean_ctor_get(v___x_940_, 1);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_940_, 2);
v___x_943_ = lean_ptr_addr(v_binderType_921_);
v___x_944_ = lean_ptr_addr(v_a_938_);
v___x_945_ = lean_usize_dec_eq(v___x_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_inc(v_binderName_920_);
v___x_946_ = l_Lean_Expr_forallE___override(v_binderName_920_, v_a_938_, v_a_941_, v_binderInfo_923_);
v___x_947_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_946_, v_a_942_);
return v___x_947_;
}
else
{
size_t v___x_948_; size_t v___x_949_; uint8_t v___x_950_; 
v___x_948_ = lean_ptr_addr(v_body_922_);
v___x_949_ = lean_ptr_addr(v_a_941_);
v___x_950_ = lean_usize_dec_eq(v___x_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_inc(v_binderName_920_);
v___x_951_ = l_Lean_Expr_forallE___override(v_binderName_920_, v_a_938_, v_a_941_, v_binderInfo_923_);
v___x_952_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_951_, v_a_942_);
return v___x_952_;
}
else
{
uint8_t v___x_953_; 
v___x_953_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_923_, v_binderInfo_923_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_inc(v_binderName_920_);
v___x_954_ = l_Lean_Expr_forallE___override(v_binderName_920_, v_a_938_, v_a_941_, v_binderInfo_923_);
v___x_955_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_954_, v_a_942_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; 
lean_dec(v_a_941_);
lean_dec(v_a_938_);
lean_inc_ref(v_e_819_);
v___x_956_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v_e_819_, v_a_942_);
return v___x_956_;
}
}
}
}
else
{
lean_dec(v_a_938_);
lean_dec_ref_known(v_e_819_, 3);
return v___x_940_;
}
}
else
{
lean_dec_ref_known(v_e_819_, 3);
return v___x_937_;
}
}
}
}
case 8:
{
lean_object* v_declName_957_; lean_object* v_type_958_; lean_object* v_value_959_; lean_object* v_body_960_; uint8_t v_nondep_961_; lean_object* v_map_962_; lean_object* v_set_963_; lean_object* v___x_964_; 
v_declName_957_ = lean_ctor_get(v_e_819_, 0);
v_type_958_ = lean_ctor_get(v_e_819_, 1);
v_value_959_ = lean_ctor_get(v_e_819_, 2);
v_body_960_ = lean_ctor_get(v_e_819_, 3);
v_nondep_961_ = lean_ctor_get_uint8(v_e_819_, sizeof(void*)*4 + 8);
v_map_962_ = lean_ctor_get(v_a_821_, 0);
v_set_963_ = lean_ctor_get(v_a_821_, 1);
v___x_964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_962_, v_e_819_);
if (lean_obj_tag(v___x_964_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_966_; 
lean_dec_ref_known(v_e_819_, 4);
v_val_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_val_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_val_965_);
lean_ctor_set(v___x_966_, 1, v_a_821_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; uint64_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; size_t v___x_971_; size_t v___x_972_; uint8_t v___x_973_; 
lean_dec(v___x_964_);
v___x_967_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_968_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_819_);
v___x_969_ = lean_uint64_to_usize(v___x_968_);
v___x_970_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_963_, v___x_969_, v_e_819_, v___x_967_);
v___x_971_ = lean_ptr_addr(v___x_970_);
v___x_972_ = lean_ptr_addr(v___x_967_);
v___x_973_ = lean_usize_dec_eq(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec_ref_known(v_e_819_, 4);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_970_);
lean_ctor_set(v___x_974_, 1, v_a_821_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; 
lean_dec_ref(v___x_970_);
lean_inc_ref(v_type_958_);
v___x_975_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_958_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
v_a_977_ = lean_ctor_get(v___x_975_, 1);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_975_, 2);
lean_inc_ref(v_value_959_);
v___x_978_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_959_, v_a_820_, v_a_977_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
v_a_980_ = lean_ctor_get(v___x_978_, 1);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_978_, 2);
lean_inc_ref(v_body_960_);
v___x_981_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_960_, v_a_820_, v_a_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_a_983_; size_t v___x_984_; size_t v___x_985_; uint8_t v___x_986_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
v_a_983_ = lean_ctor_get(v___x_981_, 1);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_981_, 2);
v___x_984_ = lean_ptr_addr(v_type_958_);
v___x_985_ = lean_ptr_addr(v_a_976_);
v___x_986_ = lean_usize_dec_eq(v___x_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_inc(v_declName_957_);
v___x_987_ = l_Lean_Expr_letE___override(v_declName_957_, v_a_976_, v_a_979_, v_a_982_, v_nondep_961_);
v___x_988_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_987_, v_a_983_);
return v___x_988_;
}
else
{
size_t v___x_989_; size_t v___x_990_; uint8_t v___x_991_; 
v___x_989_ = lean_ptr_addr(v_value_959_);
v___x_990_ = lean_ptr_addr(v_a_979_);
v___x_991_ = lean_usize_dec_eq(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_inc(v_declName_957_);
v___x_992_ = l_Lean_Expr_letE___override(v_declName_957_, v_a_976_, v_a_979_, v_a_982_, v_nondep_961_);
v___x_993_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_992_, v_a_983_);
return v___x_993_;
}
else
{
size_t v___x_994_; size_t v___x_995_; uint8_t v___x_996_; 
v___x_994_ = lean_ptr_addr(v_body_960_);
v___x_995_ = lean_ptr_addr(v_a_982_);
v___x_996_ = lean_usize_dec_eq(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc(v_declName_957_);
v___x_997_ = l_Lean_Expr_letE___override(v_declName_957_, v_a_976_, v_a_979_, v_a_982_, v_nondep_961_);
v___x_998_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_997_, v_a_983_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; 
lean_dec(v_a_982_);
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_inc_ref(v_e_819_);
v___x_999_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v_e_819_, v_a_983_);
return v___x_999_;
}
}
}
}
else
{
lean_dec(v_a_979_);
lean_dec(v_a_976_);
lean_dec_ref_known(v_e_819_, 4);
return v___x_981_;
}
}
else
{
lean_dec(v_a_976_);
lean_dec_ref_known(v_e_819_, 4);
return v___x_978_;
}
}
else
{
lean_dec_ref_known(v_e_819_, 4);
return v___x_975_;
}
}
}
}
case 10:
{
lean_object* v_data_1000_; lean_object* v_expr_1001_; lean_object* v_map_1002_; lean_object* v_set_1003_; lean_object* v___x_1004_; 
v_data_1000_ = lean_ctor_get(v_e_819_, 0);
v_expr_1001_ = lean_ctor_get(v_e_819_, 1);
v_map_1002_ = lean_ctor_get(v_a_821_, 0);
v_set_1003_ = lean_ctor_get(v_a_821_, 1);
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1002_, v_e_819_);
if (lean_obj_tag(v___x_1004_) == 1)
{
lean_object* v_val_1005_; lean_object* v___x_1006_; 
lean_dec_ref_known(v_e_819_, 2);
v_val_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_val_1005_);
lean_ctor_set(v___x_1006_, 1, v_a_821_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; uint64_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; uint8_t v___x_1013_; 
lean_dec(v___x_1004_);
v___x_1007_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1008_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_819_);
v___x_1009_ = lean_uint64_to_usize(v___x_1008_);
v___x_1010_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1003_, v___x_1009_, v_e_819_, v___x_1007_);
v___x_1011_ = lean_ptr_addr(v___x_1010_);
v___x_1012_ = lean_ptr_addr(v___x_1007_);
v___x_1013_ = lean_usize_dec_eq(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec_ref_known(v_e_819_, 2);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1010_);
lean_ctor_set(v___x_1014_, 1, v_a_821_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_1010_);
lean_inc_ref(v_expr_1001_);
v___x_1015_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1001_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v_a_1017_; size_t v___x_1018_; size_t v___x_1019_; uint8_t v___x_1020_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
v_a_1017_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1015_, 2);
v___x_1018_ = lean_ptr_addr(v_expr_1001_);
v___x_1019_ = lean_ptr_addr(v_a_1016_);
v___x_1020_ = lean_usize_dec_eq(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_inc(v_data_1000_);
v___x_1021_ = l_Lean_Expr_mdata___override(v_data_1000_, v_a_1016_);
v___x_1022_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_1021_, v_a_1017_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; 
lean_dec(v_a_1016_);
lean_inc_ref(v_e_819_);
v___x_1023_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v_e_819_, v_a_1017_);
return v___x_1023_;
}
}
else
{
lean_dec_ref_known(v_e_819_, 2);
return v___x_1015_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1024_; lean_object* v_idx_1025_; lean_object* v_struct_1026_; lean_object* v_map_1027_; lean_object* v_set_1028_; lean_object* v___x_1029_; 
v_typeName_1024_ = lean_ctor_get(v_e_819_, 0);
v_idx_1025_ = lean_ctor_get(v_e_819_, 1);
v_struct_1026_ = lean_ctor_get(v_e_819_, 2);
v_map_1027_ = lean_ctor_get(v_a_821_, 0);
v_set_1028_ = lean_ctor_get(v_a_821_, 1);
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1027_, v_e_819_);
if (lean_obj_tag(v___x_1029_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1031_; 
lean_dec_ref_known(v_e_819_, 3);
v_val_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_val_1030_);
lean_ctor_set(v___x_1031_, 1, v_a_821_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; uint64_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; uint8_t v___x_1038_; 
lean_dec(v___x_1029_);
v___x_1032_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1033_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_819_);
v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
v___x_1035_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1028_, v___x_1034_, v_e_819_, v___x_1032_);
v___x_1036_ = lean_ptr_addr(v___x_1035_);
v___x_1037_ = lean_ptr_addr(v___x_1032_);
v___x_1038_ = lean_usize_dec_eq(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref_known(v_e_819_, 3);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1035_);
lean_ctor_set(v___x_1039_, 1, v_a_821_);
return v___x_1039_;
}
else
{
uint8_t v_checkProj_1040_; 
lean_dec_ref(v___x_1035_);
v_checkProj_1040_ = lean_ctor_get_uint8(v_a_820_, sizeof(void*)*1 + 1);
if (v_checkProj_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_inc_ref(v_struct_1026_);
v___x_1041_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1026_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v_a_1043_; size_t v___x_1044_; size_t v___x_1045_; uint8_t v___x_1046_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
v_a_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1041_, 2);
v___x_1044_ = lean_ptr_addr(v_struct_1026_);
v___x_1045_ = lean_ptr_addr(v_a_1042_);
v___x_1046_ = lean_usize_dec_eq(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_inc(v_idx_1025_);
lean_inc(v_typeName_1024_);
v___x_1047_ = l_Lean_Expr_proj___override(v_typeName_1024_, v_idx_1025_, v_a_1042_);
v___x_1048_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v___x_1047_, v_a_1043_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; 
lean_dec(v_a_1042_);
lean_inc_ref(v_e_819_);
v___x_1049_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_819_, v_e_819_, v_a_1043_);
return v___x_1049_;
}
}
else
{
lean_dec_ref_known(v_e_819_, 3);
return v___x_1041_;
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref_known(v_e_819_, 3);
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v_a_821_);
return v___x_1051_;
}
}
}
}
default: 
{
lean_object* v_map_1052_; lean_object* v_set_1053_; lean_object* v___x_1054_; 
v_map_1052_ = lean_ctor_get(v_a_821_, 0);
v_set_1053_ = lean_ctor_get(v_a_821_, 1);
v___x_1054_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1053_, v_e_819_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1064_; 
lean_inc_ref(v_set_1053_);
lean_inc_ref(v_map_1052_);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_821_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; lean_object* v_unused_1066_; 
v_unused_1065_ = lean_ctor_get(v_a_821_, 1);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_a_821_, 0);
lean_dec(v_unused_1066_);
v___x_1056_ = v_a_821_;
v_isShared_1057_ = v_isSharedCheck_1064_;
goto v_resetjp_1055_;
}
else
{
lean_dec(v_a_821_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1064_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = lean_box(0);
lean_inc_ref(v_e_819_);
v___x_1059_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1053_, v_e_819_, v___x_1058_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_map_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_e_819_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
return v___x_1062_;
}
}
}
else
{
lean_object* v_val_1067_; lean_object* v_fst_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_e_819_);
v_val_1067_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_val_1067_);
lean_dec_ref_known(v___x_1054_, 1);
v_fst_1068_ = lean_ctor_get(v_val_1067_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_val_1067_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_val_1067_, 1);
lean_dec(v_unused_1076_);
v___x_1070_ = v_val_1067_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_fst_1068_);
lean_dec(v_val_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v_a_821_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_fst_1068_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_821_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1077_, v_a_1078_, v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1082_, v_x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1085_, v_x_1086_, v_x_1087_);
lean_dec_ref(v_x_1087_);
lean_dec_ref(v_x_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1089_, lean_object* v_m_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1090_, v_a_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1093_, lean_object* v_m_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1093_, v_m_1094_, v_a_1095_);
lean_dec_ref(v_a_1095_);
lean_dec_ref(v_m_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1097_, lean_object* v_x_1098_, size_t v_x_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1098_, v_x_1099_, v_x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
size_t v_x_11413__boxed_1106_; lean_object* v_res_1107_; 
v_x_11413__boxed_1106_ = lean_unbox_usize(v_x_1104_);
lean_dec(v_x_1104_);
v_res_1107_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1102_, v_x_1103_, v_x_11413__boxed_1106_, v_x_1105_);
lean_dec_ref(v_x_1105_);
lean_dec_ref(v_x_1103_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1108_, lean_object* v_a_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1109_, v_x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1112_, lean_object* v_a_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1112_, v_a_1113_, v_x_1114_);
lean_dec(v_x_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1116_, lean_object* v_keys_1117_, lean_object* v_vals_1118_, lean_object* v_heq_1119_, lean_object* v_i_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1117_, v_vals_1118_, v_i_1120_, v_k_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1123_, lean_object* v_keys_1124_, lean_object* v_vals_1125_, lean_object* v_heq_1126_, lean_object* v_i_1127_, lean_object* v_k_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1123_, v_keys_1124_, v_vals_1125_, v_heq_1126_, v_i_1127_, v_k_1128_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_vals_1125_);
lean_dec_ref(v_keys_1124_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1130_, lean_object* v_cache_1131_, lean_object* v_ctx_1132_, lean_object* v_s_1133_){
_start:
{
lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
v___f_1134_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1135_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1130_);
v___x_1136_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1134_, v___f_1135_, v_s_1133_, v_e_1130_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_cache_1131_);
lean_ctor_set(v___x_1137_, 1, v_s_1133_);
v___x_1138_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1130_, v_ctx_1132_, v___x_1137_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1148_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 1);
v_a_1140_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1142_ = v___x_1138_;
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1139_);
lean_inc(v_a_1140_);
lean_dec(v___x_1138_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1148_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_set_1144_; lean_object* v___x_1146_; 
v_set_1144_ = lean_ctor_get(v_a_1139_, 1);
lean_inc_ref(v_set_1144_);
lean_dec(v_a_1139_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_set_1144_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1140_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_set_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
v_a_1149_ = lean_ctor_get(v___x_1138_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v___x_1138_, 0);
lean_dec(v_unused_1159_);
v___x_1151_ = v___x_1138_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1138_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_map_1153_; lean_object* v_set_1154_; lean_object* v___x_1156_; 
v_map_1153_ = lean_ctor_get(v_a_1149_, 0);
lean_inc_ref(v_map_1153_);
v_set_1154_ = lean_ctor_get(v_a_1149_, 1);
lean_inc_ref(v_set_1154_);
lean_dec(v_a_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_set_1154_);
lean_ctor_set(v___x_1151_, 0, v_map_1153_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_map_1153_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_set_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v_val_1160_; lean_object* v_fst_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_cache_1131_);
lean_dec_ref(v_e_1130_);
v_val_1160_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v___x_1136_, 1);
v_fst_1161_ = lean_ctor_get(v_val_1160_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_val_1160_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v_val_1160_, 1);
lean_dec(v_unused_1169_);
v___x_1163_ = v_val_1160_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_fst_1161_);
lean_dec(v_val_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_s_1133_);
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_fst_1161_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_s_1133_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1170_, lean_object* v_cache_1171_, lean_object* v_ctx_1172_, lean_object* v_s_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1170_, v_cache_1171_, v_ctx_1172_, v_s_1173_);
lean_dec_ref(v_ctx_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1177_; uint64_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1177_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1178_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1175_);
v___x_1179_ = lean_uint64_to_usize(v___x_1178_);
v___x_1180_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1176_, v___x_1179_, v_e_1175_, v___x_1177_);
v___x_1181_ = lean_ptr_addr(v___x_1180_);
v___x_1182_ = lean_ptr_addr(v___x_1177_);
v___x_1183_ = lean_usize_dec_eq(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_e_1175_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1180_);
lean_ctor_set(v___x_1184_, 1, v_a_1176_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v___x_1180_);
v___x_1185_ = lean_box(0);
lean_inc_ref(v_e_1175_);
v___x_1186_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1176_, v_e_1175_, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_e_1175_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1188_, v_a_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1192_, v_a_1193_, v_a_1194_);
lean_dec_ref(v_a_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1196_, lean_object* v_k_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___f_1200_; lean_object* v___x_1201_; uint64_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; uint8_t v___x_1207_; 
v___f_1200_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1201_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1202_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1196_);
v___x_1203_ = lean_uint64_to_usize(v___x_1202_);
lean_inc_ref(v_a_1199_);
v___x_1204_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1200_, v_a_1199_, v___x_1203_, v_e_1196_, v___x_1201_);
v___x_1205_ = lean_ptr_addr(v___x_1204_);
v___x_1206_ = lean_ptr_addr(v___x_1201_);
v___x_1207_ = lean_usize_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_dec_ref(v_k_1197_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1204_);
lean_ctor_set(v___x_1208_, 1, v_a_1199_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; 
lean_dec(v___x_1204_);
lean_inc_ref(v_a_1198_);
v___x_1209_ = lean_apply_2(v_k_1197_, v_a_1198_, v_a_1199_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_a_1211_; lean_object* v___x_1212_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
v_a_1211_ = lean_ctor_get(v___x_1209_, 1);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1209_, 2);
v___x_1212_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1210_, v_a_1211_);
return v___x_1212_;
}
else
{
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1213_, lean_object* v_k_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1213_, v_k_1214_, v_a_1215_, v_a_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_unsigned_to_nat(16u);
v___x_1220_ = lean_mk_array(v___x_1219_, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
switch(lean_obj_tag(v_e_1224_))
{
case 4:
{
lean_object* v_declName_1227_; lean_object* v___x_1228_; uint64_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; uint8_t v___x_1234_; 
v_declName_1227_ = lean_ctor_get(v_e_1224_, 0);
v___x_1228_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1229_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1224_);
v___x_1230_ = lean_uint64_to_usize(v___x_1229_);
v___x_1231_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1230_, v_e_1224_, v___x_1228_);
v___x_1232_ = lean_ptr_addr(v___x_1231_);
v___x_1233_ = lean_ptr_addr(v___x_1228_);
v___x_1234_ = lean_usize_dec_eq(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref_known(v_e_1224_, 2);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1231_);
lean_ctor_set(v___x_1235_, 1, v_a_1226_);
return v___x_1235_;
}
else
{
uint8_t v___x_1236_; 
lean_dec_ref(v___x_1231_);
lean_inc(v_declName_1227_);
lean_inc_ref(v_a_1225_);
v___x_1236_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1225_, v_declName_1227_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_box(0);
lean_inc_ref(v_e_1224_);
v___x_1238_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1226_, v_e_1224_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_e_1224_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref_known(v_e_1224_, 2);
v___x_1240_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_a_1226_);
return v___x_1241_;
}
}
}
case 5:
{
lean_object* v_fn_1242_; lean_object* v_arg_1243_; lean_object* v___x_1244_; uint64_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; uint8_t v___x_1250_; 
v_fn_1242_ = lean_ctor_get(v_e_1224_, 0);
v_arg_1243_ = lean_ctor_get(v_e_1224_, 1);
v___x_1244_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1245_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1224_);
v___x_1246_ = lean_uint64_to_usize(v___x_1245_);
v___x_1247_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1246_, v_e_1224_, v___x_1244_);
v___x_1248_ = lean_ptr_addr(v___x_1247_);
v___x_1249_ = lean_ptr_addr(v___x_1244_);
v___x_1250_ = lean_usize_dec_eq(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
lean_dec_ref_known(v_e_1224_, 2);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1247_);
lean_ctor_set(v___x_1251_, 1, v_a_1226_);
return v___x_1251_;
}
else
{
lean_object* v___x_1252_; 
lean_dec_ref(v___x_1247_);
lean_inc_ref(v_fn_1242_);
v___x_1252_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1242_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
v_a_1254_ = lean_ctor_get(v___x_1252_, 1);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1252_, 2);
lean_inc_ref(v_arg_1243_);
v___x_1255_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1243_, v_a_1225_, v_a_1254_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_a_1257_; size_t v___x_1258_; size_t v___x_1259_; uint8_t v___x_1260_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
v_a_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1255_, 2);
v___x_1258_ = lean_ptr_addr(v_fn_1242_);
v___x_1259_ = lean_ptr_addr(v_a_1253_);
v___x_1260_ = lean_usize_dec_eq(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec_ref_known(v_e_1224_, 2);
v___x_1261_ = l_Lean_Expr_app___override(v_a_1253_, v_a_1256_);
v___x_1262_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1261_, v_a_1257_);
return v___x_1262_;
}
else
{
size_t v___x_1263_; size_t v___x_1264_; uint8_t v___x_1265_; 
v___x_1263_ = lean_ptr_addr(v_arg_1243_);
v___x_1264_ = lean_ptr_addr(v_a_1256_);
v___x_1265_ = lean_usize_dec_eq(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref_known(v_e_1224_, 2);
v___x_1266_ = l_Lean_Expr_app___override(v_a_1253_, v_a_1256_);
v___x_1267_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1266_, v_a_1257_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; 
lean_dec(v_a_1256_);
lean_dec(v_a_1253_);
v___x_1268_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1224_, v_a_1257_);
return v___x_1268_;
}
}
}
else
{
lean_dec(v_a_1253_);
lean_dec_ref_known(v_e_1224_, 2);
return v___x_1255_;
}
}
else
{
lean_dec_ref_known(v_e_1224_, 2);
return v___x_1252_;
}
}
}
case 6:
{
lean_object* v_binderName_1269_; lean_object* v_binderType_1270_; lean_object* v_body_1271_; uint8_t v_binderInfo_1272_; lean_object* v___x_1273_; uint64_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; uint8_t v___x_1279_; 
v_binderName_1269_ = lean_ctor_get(v_e_1224_, 0);
v_binderType_1270_ = lean_ctor_get(v_e_1224_, 1);
v_body_1271_ = lean_ctor_get(v_e_1224_, 2);
v_binderInfo_1272_ = lean_ctor_get_uint8(v_e_1224_, sizeof(void*)*3 + 8);
v___x_1273_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1274_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1224_);
v___x_1275_ = lean_uint64_to_usize(v___x_1274_);
v___x_1276_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1275_, v_e_1224_, v___x_1273_);
v___x_1277_ = lean_ptr_addr(v___x_1276_);
v___x_1278_ = lean_ptr_addr(v___x_1273_);
v___x_1279_ = lean_usize_dec_eq(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref_known(v_e_1224_, 3);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1276_);
lean_ctor_set(v___x_1280_, 1, v_a_1226_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; 
lean_dec_ref(v___x_1276_);
lean_inc_ref(v_binderType_1270_);
v___x_1281_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1270_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
v_a_1283_ = lean_ctor_get(v___x_1281_, 1);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1281_, 2);
lean_inc_ref(v_body_1271_);
v___x_1284_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1271_, v_a_1225_, v_a_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_a_1286_; size_t v___x_1287_; size_t v___x_1288_; uint8_t v___x_1289_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
v_a_1286_ = lean_ctor_get(v___x_1284_, 1);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1284_, 2);
v___x_1287_ = lean_ptr_addr(v_binderType_1270_);
v___x_1288_ = lean_ptr_addr(v_a_1282_);
v___x_1289_ = lean_usize_dec_eq(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v_binderName_1269_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1290_ = l_Lean_Expr_lam___override(v_binderName_1269_, v_a_1282_, v_a_1285_, v_binderInfo_1272_);
v___x_1291_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1290_, v_a_1286_);
return v___x_1291_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = lean_ptr_addr(v_body_1271_);
v___x_1293_ = lean_ptr_addr(v_a_1285_);
v___x_1294_ = lean_usize_dec_eq(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_inc(v_binderName_1269_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1295_ = l_Lean_Expr_lam___override(v_binderName_1269_, v_a_1282_, v_a_1285_, v_binderInfo_1272_);
v___x_1296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1295_, v_a_1286_);
return v___x_1296_;
}
else
{
uint8_t v___x_1297_; 
v___x_1297_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1272_, v_binderInfo_1272_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_inc(v_binderName_1269_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1298_ = l_Lean_Expr_lam___override(v_binderName_1269_, v_a_1282_, v_a_1285_, v_binderInfo_1272_);
v___x_1299_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1298_, v_a_1286_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; 
lean_dec(v_a_1285_);
lean_dec(v_a_1282_);
v___x_1300_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1224_, v_a_1286_);
return v___x_1300_;
}
}
}
}
else
{
lean_dec(v_a_1282_);
lean_dec_ref_known(v_e_1224_, 3);
return v___x_1284_;
}
}
else
{
lean_dec_ref_known(v_e_1224_, 3);
return v___x_1281_;
}
}
}
case 7:
{
lean_object* v_binderName_1301_; lean_object* v_binderType_1302_; lean_object* v_body_1303_; uint8_t v_binderInfo_1304_; lean_object* v___x_1305_; uint64_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; uint8_t v___x_1311_; 
v_binderName_1301_ = lean_ctor_get(v_e_1224_, 0);
v_binderType_1302_ = lean_ctor_get(v_e_1224_, 1);
v_body_1303_ = lean_ctor_get(v_e_1224_, 2);
v_binderInfo_1304_ = lean_ctor_get_uint8(v_e_1224_, sizeof(void*)*3 + 8);
v___x_1305_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1306_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1224_);
v___x_1307_ = lean_uint64_to_usize(v___x_1306_);
v___x_1308_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1307_, v_e_1224_, v___x_1305_);
v___x_1309_ = lean_ptr_addr(v___x_1308_);
v___x_1310_ = lean_ptr_addr(v___x_1305_);
v___x_1311_ = lean_usize_dec_eq(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref_known(v_e_1224_, 3);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1308_);
lean_ctor_set(v___x_1312_, 1, v_a_1226_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; 
lean_dec_ref(v___x_1308_);
lean_inc_ref(v_binderType_1302_);
v___x_1313_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1302_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
v_a_1315_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1313_, 2);
lean_inc_ref(v_body_1303_);
v___x_1316_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1303_, v_a_1225_, v_a_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v_a_1318_; size_t v___x_1319_; size_t v___x_1320_; uint8_t v___x_1321_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
v_a_1318_ = lean_ctor_get(v___x_1316_, 1);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1316_, 2);
v___x_1319_ = lean_ptr_addr(v_binderType_1302_);
v___x_1320_ = lean_ptr_addr(v_a_1314_);
v___x_1321_ = lean_usize_dec_eq(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_inc(v_binderName_1301_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1322_ = l_Lean_Expr_forallE___override(v_binderName_1301_, v_a_1314_, v_a_1317_, v_binderInfo_1304_);
v___x_1323_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1322_, v_a_1318_);
return v___x_1323_;
}
else
{
size_t v___x_1324_; size_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1324_ = lean_ptr_addr(v_body_1303_);
v___x_1325_ = lean_ptr_addr(v_a_1317_);
v___x_1326_ = lean_usize_dec_eq(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_inc(v_binderName_1301_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1327_ = l_Lean_Expr_forallE___override(v_binderName_1301_, v_a_1314_, v_a_1317_, v_binderInfo_1304_);
v___x_1328_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1327_, v_a_1318_);
return v___x_1328_;
}
else
{
uint8_t v___x_1329_; 
v___x_1329_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1304_, v_binderInfo_1304_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_inc(v_binderName_1301_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1330_ = l_Lean_Expr_forallE___override(v_binderName_1301_, v_a_1314_, v_a_1317_, v_binderInfo_1304_);
v___x_1331_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1330_, v_a_1318_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; 
lean_dec(v_a_1317_);
lean_dec(v_a_1314_);
v___x_1332_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1224_, v_a_1318_);
return v___x_1332_;
}
}
}
}
else
{
lean_dec(v_a_1314_);
lean_dec_ref_known(v_e_1224_, 3);
return v___x_1316_;
}
}
else
{
lean_dec_ref_known(v_e_1224_, 3);
return v___x_1313_;
}
}
}
case 8:
{
lean_object* v_declName_1333_; lean_object* v_type_1334_; lean_object* v_value_1335_; lean_object* v_body_1336_; uint8_t v_nondep_1337_; lean_object* v___x_1338_; uint64_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; uint8_t v___x_1344_; 
v_declName_1333_ = lean_ctor_get(v_e_1224_, 0);
v_type_1334_ = lean_ctor_get(v_e_1224_, 1);
v_value_1335_ = lean_ctor_get(v_e_1224_, 2);
v_body_1336_ = lean_ctor_get(v_e_1224_, 3);
v_nondep_1337_ = lean_ctor_get_uint8(v_e_1224_, sizeof(void*)*4 + 8);
v___x_1338_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1339_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1224_);
v___x_1340_ = lean_uint64_to_usize(v___x_1339_);
v___x_1341_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1340_, v_e_1224_, v___x_1338_);
v___x_1342_ = lean_ptr_addr(v___x_1341_);
v___x_1343_ = lean_ptr_addr(v___x_1338_);
v___x_1344_ = lean_usize_dec_eq(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_dec_ref_known(v_e_1224_, 4);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1341_);
lean_ctor_set(v___x_1345_, 1, v_a_1226_);
return v___x_1345_;
}
else
{
lean_object* v___x_1346_; 
lean_dec_ref(v___x_1341_);
lean_inc_ref(v_type_1334_);
v___x_1346_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1334_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v_a_1348_; lean_object* v___x_1349_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
v_a_1348_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1346_, 2);
lean_inc_ref(v_value_1335_);
v___x_1349_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1335_, v_a_1225_, v_a_1348_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
v_a_1351_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1349_, 2);
lean_inc_ref(v_body_1336_);
v___x_1352_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1336_, v_a_1225_, v_a_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v_a_1354_; size_t v___x_1355_; size_t v___x_1356_; uint8_t v___x_1357_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
v_a_1354_ = lean_ctor_get(v___x_1352_, 1);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1352_, 2);
v___x_1355_ = lean_ptr_addr(v_type_1334_);
v___x_1356_ = lean_ptr_addr(v_a_1347_);
v___x_1357_ = lean_usize_dec_eq(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_inc(v_declName_1333_);
lean_dec_ref_known(v_e_1224_, 4);
v___x_1358_ = l_Lean_Expr_letE___override(v_declName_1333_, v_a_1347_, v_a_1350_, v_a_1353_, v_nondep_1337_);
v___x_1359_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1358_, v_a_1354_);
return v___x_1359_;
}
else
{
size_t v___x_1360_; size_t v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = lean_ptr_addr(v_value_1335_);
v___x_1361_ = lean_ptr_addr(v_a_1350_);
v___x_1362_ = lean_usize_dec_eq(v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc(v_declName_1333_);
lean_dec_ref_known(v_e_1224_, 4);
v___x_1363_ = l_Lean_Expr_letE___override(v_declName_1333_, v_a_1347_, v_a_1350_, v_a_1353_, v_nondep_1337_);
v___x_1364_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1363_, v_a_1354_);
return v___x_1364_;
}
else
{
size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = lean_ptr_addr(v_body_1336_);
v___x_1366_ = lean_ptr_addr(v_a_1353_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_inc(v_declName_1333_);
lean_dec_ref_known(v_e_1224_, 4);
v___x_1368_ = l_Lean_Expr_letE___override(v_declName_1333_, v_a_1347_, v_a_1350_, v_a_1353_, v_nondep_1337_);
v___x_1369_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1368_, v_a_1354_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; 
lean_dec(v_a_1353_);
lean_dec(v_a_1350_);
lean_dec(v_a_1347_);
v___x_1370_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1224_, v_a_1354_);
return v___x_1370_;
}
}
}
}
else
{
lean_dec(v_a_1350_);
lean_dec(v_a_1347_);
lean_dec_ref_known(v_e_1224_, 4);
return v___x_1352_;
}
}
else
{
lean_dec(v_a_1347_);
lean_dec_ref_known(v_e_1224_, 4);
return v___x_1349_;
}
}
else
{
lean_dec_ref_known(v_e_1224_, 4);
return v___x_1346_;
}
}
}
case 10:
{
lean_object* v_data_1371_; lean_object* v_expr_1372_; lean_object* v___x_1373_; uint64_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; 
v_data_1371_ = lean_ctor_get(v_e_1224_, 0);
v_expr_1372_ = lean_ctor_get(v_e_1224_, 1);
v___x_1373_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1374_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1224_);
v___x_1375_ = lean_uint64_to_usize(v___x_1374_);
v___x_1376_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1375_, v_e_1224_, v___x_1373_);
v___x_1377_ = lean_ptr_addr(v___x_1376_);
v___x_1378_ = lean_ptr_addr(v___x_1373_);
v___x_1379_ = lean_usize_dec_eq(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref_known(v_e_1224_, 2);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1376_);
lean_ctor_set(v___x_1380_, 1, v_a_1226_);
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; 
lean_dec_ref(v___x_1376_);
lean_inc_ref(v_expr_1372_);
v___x_1381_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1372_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_a_1383_; size_t v___x_1384_; size_t v___x_1385_; uint8_t v___x_1386_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
v_a_1383_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1381_, 2);
v___x_1384_ = lean_ptr_addr(v_expr_1372_);
v___x_1385_ = lean_ptr_addr(v_a_1382_);
v___x_1386_ = lean_usize_dec_eq(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_inc(v_data_1371_);
lean_dec_ref_known(v_e_1224_, 2);
v___x_1387_ = l_Lean_Expr_mdata___override(v_data_1371_, v_a_1382_);
v___x_1388_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1387_, v_a_1383_);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; 
lean_dec(v_a_1382_);
v___x_1389_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1224_, v_a_1383_);
return v___x_1389_;
}
}
else
{
lean_dec_ref_known(v_e_1224_, 2);
return v___x_1381_;
}
}
}
case 11:
{
lean_object* v_typeName_1390_; lean_object* v_idx_1391_; lean_object* v_struct_1392_; lean_object* v___x_1393_; uint64_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; uint8_t v___x_1399_; 
v_typeName_1390_ = lean_ctor_get(v_e_1224_, 0);
v_idx_1391_ = lean_ctor_get(v_e_1224_, 1);
v_struct_1392_ = lean_ctor_get(v_e_1224_, 2);
v___x_1393_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1394_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1224_);
v___x_1395_ = lean_uint64_to_usize(v___x_1394_);
v___x_1396_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1226_, v___x_1395_, v_e_1224_, v___x_1393_);
v___x_1397_ = lean_ptr_addr(v___x_1396_);
v___x_1398_ = lean_ptr_addr(v___x_1393_);
v___x_1399_ = lean_usize_dec_eq(v___x_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref_known(v_e_1224_, 3);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1396_);
lean_ctor_set(v___x_1400_, 1, v_a_1226_);
return v___x_1400_;
}
else
{
uint8_t v_checkProj_1401_; 
lean_dec_ref(v___x_1396_);
v_checkProj_1401_ = lean_ctor_get_uint8(v_a_1225_, sizeof(void*)*1 + 1);
if (v_checkProj_1401_ == 0)
{
lean_object* v___x_1402_; 
lean_inc_ref(v_struct_1392_);
v___x_1402_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1392_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_a_1404_; size_t v___x_1405_; size_t v___x_1406_; uint8_t v___x_1407_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
v_a_1404_ = lean_ctor_get(v___x_1402_, 1);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1402_, 2);
v___x_1405_ = lean_ptr_addr(v_struct_1392_);
v___x_1406_ = lean_ptr_addr(v_a_1403_);
v___x_1407_ = lean_usize_dec_eq(v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_inc(v_idx_1391_);
lean_inc(v_typeName_1390_);
lean_dec_ref_known(v_e_1224_, 3);
v___x_1408_ = l_Lean_Expr_proj___override(v_typeName_1390_, v_idx_1391_, v_a_1403_);
v___x_1409_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1408_, v_a_1404_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_a_1403_);
v___x_1410_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1224_, v_a_1404_);
return v___x_1410_;
}
}
else
{
lean_dec_ref_known(v_e_1224_, 3);
return v___x_1402_;
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref_known(v_e_1224_, 3);
v___x_1411_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_a_1226_);
return v___x_1412_;
}
}
}
default: 
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1224_, v_a_1226_);
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1414_, v_a_1415_, v_a_1416_);
lean_dec_ref(v_a_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1418_, v_a_1419_, v_a_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1422_, v_a_1423_, v_a_1424_);
lean_dec_ref(v_a_1423_);
return v_res_1425_;
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

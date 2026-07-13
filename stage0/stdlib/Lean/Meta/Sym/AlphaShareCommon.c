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
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static uint64_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0(void){
_start:
{
lean_object* v___x_27_; uint64_t v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(1723u);
v___x_28_ = lean_uint64_of_nat(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object* v_e_29_){
_start:
{
lean_object* v_d_31_; lean_object* v_b_32_; 
switch(lean_obj_tag(v_e_29_))
{
case 5:
{
lean_object* v_fn_36_; lean_object* v_arg_37_; uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; 
v_fn_36_ = lean_ctor_get(v_e_29_, 0);
v_arg_37_ = lean_ctor_get(v_e_29_, 1);
v___x_38_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_fn_36_);
v___x_39_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_arg_37_);
v___x_40_ = lean_uint64_mix_hash(v___x_38_, v___x_39_);
return v___x_40_;
}
case 6:
{
lean_object* v_binderType_41_; lean_object* v_body_42_; 
v_binderType_41_ = lean_ctor_get(v_e_29_, 1);
v_body_42_ = lean_ctor_get(v_e_29_, 2);
v_d_31_ = v_binderType_41_;
v_b_32_ = v_body_42_;
goto v___jp_30_;
}
case 7:
{
lean_object* v_binderType_43_; lean_object* v_body_44_; 
v_binderType_43_ = lean_ctor_get(v_e_29_, 1);
v_body_44_ = lean_ctor_get(v_e_29_, 2);
v_d_31_ = v_binderType_43_;
v_b_32_ = v_body_44_;
goto v___jp_30_;
}
case 8:
{
lean_object* v_value_45_; lean_object* v_body_46_; uint64_t v___x_47_; uint64_t v___x_48_; uint64_t v___x_49_; 
v_value_45_ = lean_ctor_get(v_e_29_, 2);
v_body_46_ = lean_ctor_get(v_e_29_, 3);
v___x_47_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_value_45_);
v___x_48_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_body_46_);
v___x_49_ = lean_uint64_mix_hash(v___x_47_, v___x_48_);
return v___x_49_;
}
case 10:
{
lean_object* v_expr_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; 
v_expr_50_ = lean_ctor_get(v_e_29_, 1);
v___x_51_ = 13ULL;
v___x_52_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_expr_50_);
v___x_53_ = lean_uint64_mix_hash(v___x_51_, v___x_52_);
return v___x_53_;
}
case 11:
{
lean_object* v_typeName_54_; lean_object* v_idx_55_; lean_object* v_struct_56_; uint64_t v___y_58_; 
v_typeName_54_ = lean_ctor_get(v_e_29_, 0);
v_idx_55_ = lean_ctor_get(v_e_29_, 1);
v_struct_56_ = lean_ctor_get(v_e_29_, 2);
if (lean_obj_tag(v_typeName_54_) == 0)
{
uint64_t v___x_63_; 
v___x_63_ = lean_uint64_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___closed__0);
v___y_58_ = v___x_63_;
goto v___jp_57_;
}
else
{
uint64_t v_hash_64_; 
v_hash_64_ = lean_ctor_get_uint64(v_typeName_54_, sizeof(void*)*2);
v___y_58_ = v_hash_64_;
goto v___jp_57_;
}
v___jp_57_:
{
uint64_t v___x_59_; uint64_t v___x_60_; uint64_t v___x_61_; uint64_t v___x_62_; 
v___x_59_ = lean_uint64_of_nat(v_idx_55_);
v___x_60_ = lean_uint64_mix_hash(v___y_58_, v___x_59_);
v___x_61_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_struct_56_);
v___x_62_ = lean_uint64_mix_hash(v___x_60_, v___x_61_);
return v___x_62_;
}
}
default: 
{
uint64_t v___x_65_; 
v___x_65_ = l_Lean_Expr_hash(v_e_29_);
return v___x_65_;
}
}
v___jp_30_:
{
uint64_t v___x_33_; uint64_t v___x_34_; uint64_t v___x_35_; 
v___x_33_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_d_31_);
v___x_34_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_hashChild(v_b_32_);
v___x_35_ = lean_uint64_mix_hash(v___x_33_, v___x_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object* v_e_66_){
_start:
{
uint64_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_66_);
lean_dec_ref(v_e_66_);
v_r_68_ = lean_box_uint64(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object* v_e_u2081_69_, lean_object* v_e_u2082_70_){
_start:
{
switch(lean_obj_tag(v_e_u2081_69_))
{
case 5:
{
if (lean_obj_tag(v_e_u2082_70_) == 5)
{
lean_object* v_fn_71_; lean_object* v_arg_72_; lean_object* v_fn_73_; lean_object* v_arg_74_; size_t v___x_75_; size_t v___x_76_; uint8_t v___x_77_; 
v_fn_71_ = lean_ctor_get(v_e_u2081_69_, 0);
lean_inc_ref(v_fn_71_);
v_arg_72_ = lean_ctor_get(v_e_u2081_69_, 1);
lean_inc_ref(v_arg_72_);
lean_dec_ref_known(v_e_u2081_69_, 2);
v_fn_73_ = lean_ctor_get(v_e_u2082_70_, 0);
lean_inc_ref(v_fn_73_);
v_arg_74_ = lean_ctor_get(v_e_u2082_70_, 1);
lean_inc_ref(v_arg_74_);
lean_dec_ref_known(v_e_u2082_70_, 2);
v___x_75_ = lean_ptr_addr(v_fn_71_);
lean_dec_ref(v_fn_71_);
v___x_76_ = lean_ptr_addr(v_fn_73_);
lean_dec_ref(v_fn_73_);
v___x_77_ = lean_usize_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec_ref(v_arg_74_);
lean_dec_ref(v_arg_72_);
return v___x_77_;
}
else
{
size_t v___x_78_; size_t v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_ptr_addr(v_arg_72_);
lean_dec_ref(v_arg_72_);
v___x_79_ = lean_ptr_addr(v_arg_74_);
lean_dec_ref(v_arg_74_);
v___x_80_ = lean_usize_dec_eq(v___x_78_, v___x_79_);
return v___x_80_;
}
}
else
{
uint8_t v___x_81_; 
lean_dec_ref_known(v_e_u2081_69_, 2);
lean_dec_ref(v_e_u2082_70_);
v___x_81_ = 0;
return v___x_81_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_70_) == 6)
{
lean_object* v_binderType_82_; lean_object* v_body_83_; lean_object* v_binderType_84_; lean_object* v_body_85_; size_t v___x_86_; size_t v___x_87_; uint8_t v___x_88_; 
v_binderType_82_ = lean_ctor_get(v_e_u2081_69_, 1);
lean_inc_ref(v_binderType_82_);
v_body_83_ = lean_ctor_get(v_e_u2081_69_, 2);
lean_inc_ref(v_body_83_);
lean_dec_ref_known(v_e_u2081_69_, 3);
v_binderType_84_ = lean_ctor_get(v_e_u2082_70_, 1);
lean_inc_ref(v_binderType_84_);
v_body_85_ = lean_ctor_get(v_e_u2082_70_, 2);
lean_inc_ref(v_body_85_);
lean_dec_ref_known(v_e_u2082_70_, 3);
v___x_86_ = lean_ptr_addr(v_binderType_82_);
lean_dec_ref(v_binderType_82_);
v___x_87_ = lean_ptr_addr(v_binderType_84_);
lean_dec_ref(v_binderType_84_);
v___x_88_ = lean_usize_dec_eq(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
lean_dec_ref(v_body_85_);
lean_dec_ref(v_body_83_);
return v___x_88_;
}
else
{
size_t v___x_89_; size_t v___x_90_; uint8_t v___x_91_; 
v___x_89_ = lean_ptr_addr(v_body_83_);
lean_dec_ref(v_body_83_);
v___x_90_ = lean_ptr_addr(v_body_85_);
lean_dec_ref(v_body_85_);
v___x_91_ = lean_usize_dec_eq(v___x_89_, v___x_90_);
return v___x_91_;
}
}
else
{
uint8_t v___x_92_; 
lean_dec_ref_known(v_e_u2081_69_, 3);
lean_dec_ref(v_e_u2082_70_);
v___x_92_ = 0;
return v___x_92_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_70_) == 7)
{
lean_object* v_binderType_93_; lean_object* v_body_94_; lean_object* v_binderType_95_; lean_object* v_body_96_; size_t v___x_97_; size_t v___x_98_; uint8_t v___x_99_; 
v_binderType_93_ = lean_ctor_get(v_e_u2081_69_, 1);
lean_inc_ref(v_binderType_93_);
v_body_94_ = lean_ctor_get(v_e_u2081_69_, 2);
lean_inc_ref(v_body_94_);
lean_dec_ref_known(v_e_u2081_69_, 3);
v_binderType_95_ = lean_ctor_get(v_e_u2082_70_, 1);
lean_inc_ref(v_binderType_95_);
v_body_96_ = lean_ctor_get(v_e_u2082_70_, 2);
lean_inc_ref(v_body_96_);
lean_dec_ref_known(v_e_u2082_70_, 3);
v___x_97_ = lean_ptr_addr(v_binderType_93_);
lean_dec_ref(v_binderType_93_);
v___x_98_ = lean_ptr_addr(v_binderType_95_);
lean_dec_ref(v_binderType_95_);
v___x_99_ = lean_usize_dec_eq(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_dec_ref(v_body_96_);
lean_dec_ref(v_body_94_);
return v___x_99_;
}
else
{
size_t v___x_100_; size_t v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_ptr_addr(v_body_94_);
lean_dec_ref(v_body_94_);
v___x_101_ = lean_ptr_addr(v_body_96_);
lean_dec_ref(v_body_96_);
v___x_102_ = lean_usize_dec_eq(v___x_100_, v___x_101_);
return v___x_102_;
}
}
else
{
uint8_t v___x_103_; 
lean_dec_ref_known(v_e_u2081_69_, 3);
lean_dec_ref(v_e_u2082_70_);
v___x_103_ = 0;
return v___x_103_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_70_) == 8)
{
lean_object* v_value_104_; lean_object* v_body_105_; lean_object* v_value_106_; lean_object* v_body_107_; size_t v___x_108_; size_t v___x_109_; uint8_t v___x_110_; 
v_value_104_ = lean_ctor_get(v_e_u2081_69_, 2);
lean_inc_ref(v_value_104_);
v_body_105_ = lean_ctor_get(v_e_u2081_69_, 3);
lean_inc_ref(v_body_105_);
lean_dec_ref_known(v_e_u2081_69_, 4);
v_value_106_ = lean_ctor_get(v_e_u2082_70_, 2);
lean_inc_ref(v_value_106_);
v_body_107_ = lean_ctor_get(v_e_u2082_70_, 3);
lean_inc_ref(v_body_107_);
lean_dec_ref_known(v_e_u2082_70_, 4);
v___x_108_ = lean_ptr_addr(v_value_104_);
lean_dec_ref(v_value_104_);
v___x_109_ = lean_ptr_addr(v_value_106_);
lean_dec_ref(v_value_106_);
v___x_110_ = lean_usize_dec_eq(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v_body_107_);
lean_dec_ref(v_body_105_);
return v___x_110_;
}
else
{
size_t v___x_111_; size_t v___x_112_; uint8_t v___x_113_; 
v___x_111_ = lean_ptr_addr(v_body_105_);
lean_dec_ref(v_body_105_);
v___x_112_ = lean_ptr_addr(v_body_107_);
lean_dec_ref(v_body_107_);
v___x_113_ = lean_usize_dec_eq(v___x_111_, v___x_112_);
return v___x_113_;
}
}
else
{
uint8_t v___x_114_; 
lean_dec_ref_known(v_e_u2081_69_, 4);
lean_dec_ref(v_e_u2082_70_);
v___x_114_ = 0;
return v___x_114_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_70_) == 10)
{
lean_object* v_data_115_; lean_object* v_expr_116_; lean_object* v_data_117_; lean_object* v_expr_118_; size_t v___x_119_; size_t v___x_120_; uint8_t v___x_121_; 
v_data_115_ = lean_ctor_get(v_e_u2081_69_, 0);
lean_inc(v_data_115_);
v_expr_116_ = lean_ctor_get(v_e_u2081_69_, 1);
lean_inc_ref(v_expr_116_);
lean_dec_ref_known(v_e_u2081_69_, 2);
v_data_117_ = lean_ctor_get(v_e_u2082_70_, 0);
lean_inc(v_data_117_);
v_expr_118_ = lean_ctor_get(v_e_u2082_70_, 1);
lean_inc_ref(v_expr_118_);
lean_dec_ref_known(v_e_u2082_70_, 2);
v___x_119_ = lean_ptr_addr(v_expr_116_);
lean_dec_ref(v_expr_116_);
v___x_120_ = lean_ptr_addr(v_expr_118_);
lean_dec_ref(v_expr_118_);
v___x_121_ = lean_usize_dec_eq(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_dec(v_data_117_);
lean_dec(v_data_115_);
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = l_Lean_KVMap_eqv(v_data_115_, v_data_117_);
return v___x_122_;
}
}
else
{
uint8_t v___x_123_; 
lean_dec_ref_known(v_e_u2081_69_, 2);
lean_dec_ref(v_e_u2082_70_);
v___x_123_ = 0;
return v___x_123_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_70_) == 11)
{
lean_object* v_typeName_124_; lean_object* v_idx_125_; lean_object* v_struct_126_; lean_object* v_typeName_127_; lean_object* v_idx_128_; lean_object* v_struct_129_; uint8_t v___y_131_; uint8_t v___x_135_; 
v_typeName_124_ = lean_ctor_get(v_e_u2081_69_, 0);
lean_inc(v_typeName_124_);
v_idx_125_ = lean_ctor_get(v_e_u2081_69_, 1);
lean_inc(v_idx_125_);
v_struct_126_ = lean_ctor_get(v_e_u2081_69_, 2);
lean_inc_ref(v_struct_126_);
lean_dec_ref_known(v_e_u2081_69_, 3);
v_typeName_127_ = lean_ctor_get(v_e_u2082_70_, 0);
lean_inc(v_typeName_127_);
v_idx_128_ = lean_ctor_get(v_e_u2082_70_, 1);
lean_inc(v_idx_128_);
v_struct_129_ = lean_ctor_get(v_e_u2082_70_, 2);
lean_inc_ref(v_struct_129_);
lean_dec_ref_known(v_e_u2082_70_, 3);
v___x_135_ = lean_name_eq(v_typeName_124_, v_typeName_127_);
lean_dec(v_typeName_127_);
lean_dec(v_typeName_124_);
if (v___x_135_ == 0)
{
lean_dec(v_idx_128_);
lean_dec(v_idx_125_);
v___y_131_ = v___x_135_;
goto v___jp_130_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = lean_nat_dec_eq(v_idx_125_, v_idx_128_);
lean_dec(v_idx_128_);
lean_dec(v_idx_125_);
v___y_131_ = v___x_136_;
goto v___jp_130_;
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
lean_dec_ref(v_struct_129_);
lean_dec_ref(v_struct_126_);
return v___y_131_;
}
else
{
size_t v___x_132_; size_t v___x_133_; uint8_t v___x_134_; 
v___x_132_ = lean_ptr_addr(v_struct_126_);
lean_dec_ref(v_struct_126_);
v___x_133_ = lean_ptr_addr(v_struct_129_);
lean_dec_ref(v_struct_129_);
v___x_134_ = lean_usize_dec_eq(v___x_132_, v___x_133_);
return v___x_134_;
}
}
}
else
{
uint8_t v___x_137_; 
lean_dec_ref_known(v_e_u2081_69_, 3);
lean_dec_ref(v_e_u2082_70_);
v___x_137_ = 0;
return v___x_137_;
}
}
default: 
{
uint8_t v___x_138_; 
v___x_138_ = lean_expr_eqv(v_e_u2081_69_, v_e_u2082_70_);
lean_dec_ref(v_e_u2082_70_);
lean_dec_ref(v_e_u2081_69_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object* v_e_u2081_139_, lean_object* v_e_u2082_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_e_u2081_139_, v_e_u2082_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_157_ = lean_name_eq(v_declName_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__5));
v___x_159_ = lean_name_eq(v_declName_155_, v___x_158_);
return v___x_159_;
}
else
{
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_160_);
lean_dec(v_declName_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object* v_env_163_, lean_object* v_declName_164_){
_start:
{
uint8_t v___x_165_; 
lean_inc(v_declName_164_);
lean_inc_ref(v_env_163_);
v___x_165_ = l_Lean_getReducibilityStatusCore(v_env_163_, v_declName_164_);
if (v___x_165_ == 0)
{
uint8_t v___x_166_; 
v___x_166_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_164_);
if (v___x_166_ == 0)
{
uint8_t v___x_167_; 
v___x_167_ = l_Lean_Environment_isProjectionFn(v_env_163_, v_declName_164_);
if (v___x_167_ == 0)
{
uint8_t v___x_168_; 
v___x_168_ = 1;
return v___x_168_;
}
else
{
return v___x_166_;
}
}
else
{
uint8_t v___x_169_; 
lean_dec(v_declName_164_);
lean_dec_ref(v_env_163_);
v___x_169_ = 0;
return v___x_169_;
}
}
else
{
uint8_t v___x_170_; 
lean_dec(v_declName_164_);
lean_dec_ref(v_env_163_);
v___x_170_ = 0;
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object* v_env_171_, lean_object* v_declName_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_171_, v_declName_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_175_){
_start:
{
uint64_t v___x_176_; 
v___x_176_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_177_){
_start:
{
uint64_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_177_);
lean_dec_ref(v_k_177_);
v_r_179_ = lean_box_uint64(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_182_, lean_object* v_k_u2082_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_182_, v_k_u2082_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_185_, lean_object* v_k_u2082_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_185_, v_k_u2082_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object* v_ctx_191_, lean_object* v_declName_192_){
_start:
{
uint8_t v_checkReducible_193_; 
v_checkReducible_193_ = lean_ctor_get_uint8(v_ctx_191_, sizeof(void*)*1);
if (v_checkReducible_193_ == 0)
{
lean_dec(v_declName_192_);
lean_dec_ref(v_ctx_191_);
return v_checkReducible_193_;
}
else
{
lean_object* v_env_194_; uint8_t v___x_195_; 
v_env_194_ = lean_ctor_get(v_ctx_191_, 0);
lean_inc_ref(v_env_194_);
lean_dec_ref(v_ctx_191_);
v___x_195_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_194_, v_declName_192_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object* v_ctx_196_, lean_object* v_declName_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_196_, v_declName_197_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_box(0);
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_205_ = l_Lean_mkConst(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_207_, lean_object* v_i_208_, lean_object* v_k_209_, lean_object* v_k_u2080_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_array_get_size(v_keys_207_);
v___x_212_ = lean_nat_dec_lt(v_i_208_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_k_209_);
lean_dec(v_i_208_);
lean_inc_ref(v_k_u2080_210_);
return v_k_u2080_210_;
}
else
{
lean_object* v_k_x27_213_; uint8_t v___x_214_; 
v_k_x27_213_ = lean_array_fget_borrowed(v_keys_207_, v_i_208_);
lean_inc(v_k_x27_213_);
lean_inc_ref(v_k_209_);
v___x_214_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_209_, v_k_x27_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_i_208_, v___x_215_);
lean_dec(v_i_208_);
v_i_208_ = v___x_216_;
goto _start;
}
else
{
lean_dec_ref(v_k_209_);
lean_dec(v_i_208_);
lean_inc(v_k_x27_213_);
return v_k_x27_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_218_, lean_object* v_i_219_, lean_object* v_k_220_, lean_object* v_k_u2080_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_218_, v_i_219_, v_k_220_, v_k_u2080_221_);
lean_dec_ref(v_k_u2080_221_);
lean_dec_ref(v_keys_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_223_, size_t v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v_es_227_; lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v_j_231_; lean_object* v___x_232_; 
v_es_227_ = lean_ctor_get(v_x_223_, 0);
lean_inc_ref(v_es_227_);
lean_dec_ref_known(v_x_223_, 1);
v___x_228_ = lean_box(2);
v___x_229_ = ((size_t)31ULL);
v___x_230_ = lean_usize_land(v_x_224_, v___x_229_);
v_j_231_ = lean_usize_to_nat(v___x_230_);
v___x_232_ = lean_array_get(v___x_228_, v_es_227_, v_j_231_);
lean_dec(v_j_231_);
lean_dec_ref(v_es_227_);
switch(lean_obj_tag(v___x_232_))
{
case 0:
{
lean_object* v_key_233_; uint8_t v___x_234_; 
v_key_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc_n(v_key_233_, 2);
lean_dec_ref_known(v___x_232_, 2);
v___x_234_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_225_, v_key_233_);
if (v___x_234_ == 0)
{
lean_dec(v_key_233_);
lean_inc_ref(v_x_226_);
return v_x_226_;
}
else
{
return v_key_233_;
}
}
case 1:
{
lean_object* v_node_235_; size_t v___x_236_; size_t v___x_237_; 
v_node_235_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_node_235_);
lean_dec_ref_known(v___x_232_, 1);
v___x_236_ = ((size_t)5ULL);
v___x_237_ = lean_usize_shift_right(v_x_224_, v___x_236_);
v_x_223_ = v_node_235_;
v_x_224_ = v___x_237_;
goto _start;
}
default: 
{
lean_dec_ref(v_x_225_);
lean_inc_ref(v_x_226_);
return v_x_226_;
}
}
}
else
{
lean_object* v_ks_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_ks_239_ = lean_ctor_get(v_x_223_, 0);
lean_inc_ref(v_ks_239_);
lean_dec_ref_known(v_x_223_, 2);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_239_, v___x_240_, v_x_225_, v_x_226_);
lean_dec_ref(v_ks_239_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
size_t v_x_2094__boxed_246_; lean_object* v_res_247_; 
v_x_2094__boxed_246_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_247_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_242_, v_x_2094__boxed_246_, v_x_244_, v_x_245_);
lean_dec_ref(v_x_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_ks_252_; lean_object* v_vs_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_277_; 
v_ks_252_ = lean_ctor_get(v_x_248_, 0);
v_vs_253_ = lean_ctor_get(v_x_248_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_277_ == 0)
{
v___x_255_ = v_x_248_;
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_vs_253_);
lean_inc(v_ks_252_);
lean_dec(v_x_248_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_ks_252_);
v___x_258_ = lean_nat_dec_lt(v_x_249_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_x_249_);
v___x_259_ = lean_array_push(v_ks_252_, v_x_250_);
v___x_260_ = lean_array_push(v_vs_253_, v_x_251_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_260_);
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v_k_x27_264_; uint8_t v___x_265_; 
v_k_x27_264_ = lean_array_fget_borrowed(v_ks_252_, v_x_249_);
lean_inc(v_k_x27_264_);
lean_inc_ref(v_x_250_);
v___x_265_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_250_, v_k_x27_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; 
if (v_isShared_256_ == 0)
{
v___x_267_ = v___x_255_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_ks_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_vs_253_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_x_249_, v___x_268_);
lean_dec(v_x_249_);
v_x_248_ = v___x_267_;
v_x_249_ = v___x_269_;
goto _start;
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_array_fset(v_ks_252_, v_x_249_, v_x_250_);
v___x_273_ = lean_array_fset(v_vs_253_, v_x_249_, v_x_251_);
lean_dec(v_x_249_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_273_);
lean_ctor_set(v___x_255_, 0, v___x_272_);
v___x_275_ = v___x_255_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_278_, lean_object* v_k_279_, lean_object* v_v_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_278_, v___x_281_, v_k_279_, v_v_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_284_, size_t v_x_285_, size_t v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_es_289_; size_t v___x_290_; size_t v___x_291_; lean_object* v_j_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_es_289_ = lean_ctor_get(v_x_284_, 0);
v___x_290_ = ((size_t)31ULL);
v___x_291_ = lean_usize_land(v_x_285_, v___x_290_);
v_j_292_ = lean_usize_to_nat(v___x_291_);
v___x_293_ = lean_array_get_size(v_es_289_);
v___x_294_ = lean_nat_dec_lt(v_j_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_dec(v_j_292_);
lean_dec(v_x_288_);
lean_dec_ref(v_x_287_);
return v_x_284_;
}
else
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_333_; 
lean_inc_ref(v_es_289_);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_x_284_, 0);
lean_dec(v_unused_334_);
v___x_296_ = v_x_284_;
v_isShared_297_ = v_isSharedCheck_333_;
goto v_resetjp_295_;
}
else
{
lean_dec(v_x_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_333_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_v_298_; lean_object* v___x_299_; lean_object* v_xs_x27_300_; lean_object* v___y_302_; 
v_v_298_ = lean_array_fget(v_es_289_, v_j_292_);
v___x_299_ = lean_box(0);
v_xs_x27_300_ = lean_array_fset(v_es_289_, v_j_292_, v___x_299_);
switch(lean_obj_tag(v_v_298_))
{
case 0:
{
lean_object* v_key_307_; lean_object* v_val_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_318_; 
v_key_307_ = lean_ctor_get(v_v_298_, 0);
v_val_308_ = lean_ctor_get(v_v_298_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_v_298_);
if (v_isSharedCheck_318_ == 0)
{
v___x_310_ = v_v_298_;
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_val_308_);
lean_inc(v_key_307_);
lean_dec(v_v_298_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
lean_inc(v_key_307_);
lean_inc_ref(v_x_287_);
v___x_312_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_287_, v_key_307_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_del_object(v___x_310_);
v___x_313_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_307_, v_val_308_, v_x_287_, v_x_288_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___y_302_ = v___x_314_;
goto v___jp_301_;
}
else
{
lean_object* v___x_316_; 
lean_dec(v_val_308_);
lean_dec(v_key_307_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v_x_288_);
lean_ctor_set(v___x_310_, 0, v_x_287_);
v___x_316_ = v___x_310_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_x_287_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_x_288_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v___y_302_ = v___x_316_;
goto v___jp_301_;
}
}
}
}
case 1:
{
lean_object* v_node_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_331_; 
v_node_319_ = lean_ctor_get(v_v_298_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_v_298_);
if (v_isSharedCheck_331_ == 0)
{
v___x_321_ = v_v_298_;
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_node_319_);
lean_dec(v_v_298_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_usize_shift_right(v_x_285_, v___x_323_);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_add(v_x_286_, v___x_325_);
v___x_327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_319_, v___x_324_, v___x_326_, v_x_287_, v_x_288_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_327_);
v___x_329_ = v___x_321_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v___y_302_ = v___x_329_;
goto v___jp_301_;
}
}
}
default: 
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_x_287_);
lean_ctor_set(v___x_332_, 1, v_x_288_);
v___y_302_ = v___x_332_;
goto v___jp_301_;
}
}
v___jp_301_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_array_fset(v_xs_x27_300_, v_j_292_, v___y_302_);
lean_dec(v_j_292_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_303_);
v___x_305_ = v___x_296_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
else
{
lean_object* v_ks_335_; lean_object* v_vs_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_356_; 
v_ks_335_ = lean_ctor_get(v_x_284_, 0);
v_vs_336_ = lean_ctor_get(v_x_284_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_356_ == 0)
{
v___x_338_ = v_x_284_;
v_isShared_339_ = v_isSharedCheck_356_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_vs_336_);
lean_inc(v_ks_335_);
lean_dec(v_x_284_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_356_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_ks_335_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_vs_336_);
v___x_341_ = v_reuseFailAlloc_355_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v_newNode_342_; uint8_t v___y_344_; size_t v___x_350_; uint8_t v___x_351_; 
v_newNode_342_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_341_, v_x_287_, v_x_288_);
v___x_350_ = ((size_t)7ULL);
v___x_351_ = lean_usize_dec_le(v___x_350_, v_x_286_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_342_);
v___x_353_ = lean_unsigned_to_nat(4u);
v___x_354_ = lean_nat_dec_lt(v___x_352_, v___x_353_);
lean_dec(v___x_352_);
v___y_344_ = v___x_354_;
goto v___jp_343_;
}
else
{
v___y_344_ = v___x_351_;
goto v___jp_343_;
}
v___jp_343_:
{
if (v___y_344_ == 0)
{
lean_object* v_ks_345_; lean_object* v_vs_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_ks_345_ = lean_ctor_get(v_newNode_342_, 0);
lean_inc_ref(v_ks_345_);
v_vs_346_ = lean_ctor_get(v_newNode_342_, 1);
lean_inc_ref(v_vs_346_);
lean_dec_ref(v_newNode_342_);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_286_, v_ks_345_, v_vs_346_, v___x_347_, v___x_348_);
lean_dec_ref(v_vs_346_);
lean_dec_ref(v_ks_345_);
return v___x_349_;
}
else
{
return v_newNode_342_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_357_, lean_object* v_keys_358_, lean_object* v_vals_359_, lean_object* v_i_360_, lean_object* v_entries_361_){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_array_get_size(v_keys_358_);
v___x_363_ = lean_nat_dec_lt(v_i_360_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v_i_360_);
return v_entries_361_;
}
else
{
lean_object* v_k_364_; lean_object* v_v_365_; uint64_t v___x_366_; size_t v_h_367_; size_t v___x_368_; lean_object* v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v_h_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_k_364_ = lean_array_fget_borrowed(v_keys_358_, v_i_360_);
v_v_365_ = lean_array_fget_borrowed(v_vals_359_, v_i_360_);
v___x_366_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_364_);
v_h_367_ = lean_uint64_to_usize(v___x_366_);
v___x_368_ = ((size_t)5ULL);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_sub(v_depth_357_, v___x_370_);
v___x_372_ = lean_usize_mul(v___x_368_, v___x_371_);
v_h_373_ = lean_usize_shift_right(v_h_367_, v___x_372_);
v___x_374_ = lean_nat_add(v_i_360_, v___x_369_);
lean_dec(v_i_360_);
lean_inc(v_v_365_);
lean_inc(v_k_364_);
v___x_375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_361_, v_h_373_, v_depth_357_, v_k_364_, v_v_365_);
v_i_360_ = v___x_374_;
v_entries_361_ = v___x_375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_377_, lean_object* v_keys_378_, lean_object* v_vals_379_, lean_object* v_i_380_, lean_object* v_entries_381_){
_start:
{
size_t v_depth_boxed_382_; lean_object* v_res_383_; 
v_depth_boxed_382_ = lean_unbox_usize(v_depth_377_);
lean_dec(v_depth_377_);
v_res_383_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_382_, v_keys_378_, v_vals_379_, v_i_380_, v_entries_381_);
lean_dec_ref(v_vals_379_);
lean_dec_ref(v_keys_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
size_t v_x_2212__boxed_389_; size_t v_x_2213__boxed_390_; lean_object* v_res_391_; 
v_x_2212__boxed_389_ = lean_unbox_usize(v_x_385_);
lean_dec(v_x_385_);
v_x_2213__boxed_390_ = lean_unbox_usize(v_x_386_);
lean_dec(v_x_386_);
v_res_391_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_384_, v_x_2212__boxed_389_, v_x_2213__boxed_390_, v_x_387_, v_x_388_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
uint64_t v___x_395_; size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_395_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_393_);
v___x_396_ = lean_uint64_to_usize(v___x_395_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_392_, v___x_396_, v___x_397_, v_x_393_, v_x_394_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_399_, lean_object* v_b_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_dec(v_b_400_);
lean_dec_ref(v_a_399_);
return v_x_401_;
}
else
{
lean_object* v_key_402_; lean_object* v_value_403_; lean_object* v_tail_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_418_; 
v_key_402_ = lean_ctor_get(v_x_401_, 0);
v_value_403_ = lean_ctor_get(v_x_401_, 1);
v_tail_404_ = lean_ctor_get(v_x_401_, 2);
v_isSharedCheck_418_ = !lean_is_exclusive(v_x_401_);
if (v_isSharedCheck_418_ == 0)
{
v___x_406_ = v_x_401_;
v_isShared_407_ = v_isSharedCheck_418_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_tail_404_);
lean_inc(v_value_403_);
lean_inc(v_key_402_);
lean_dec(v_x_401_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_418_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_ptr_addr(v_key_402_);
v___x_409_ = lean_ptr_addr(v_a_399_);
v___x_410_ = lean_usize_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_399_, v_b_400_, v_tail_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 2, v___x_411_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_key_402_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_value_403_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
else
{
lean_object* v___x_416_; 
lean_dec(v_value_403_);
lean_dec(v_key_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_b_400_);
lean_ctor_set(v___x_406_, 0, v_a_399_);
v___x_416_ = v___x_406_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_b_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_tail_404_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
return v_x_419_;
}
else
{
lean_object* v_key_421_; lean_object* v_value_422_; lean_object* v_tail_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_449_; 
v_key_421_ = lean_ctor_get(v_x_420_, 0);
v_value_422_ = lean_ctor_get(v_x_420_, 1);
v_tail_423_ = lean_ctor_get(v_x_420_, 2);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_449_ == 0)
{
v___x_425_ = v_x_420_;
v_isShared_426_ = v_isSharedCheck_449_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_tail_423_);
lean_inc(v_value_422_);
lean_inc(v_key_421_);
lean_dec(v_x_420_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_449_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v_fold_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_427_ = lean_array_get_size(v_x_419_);
v___x_428_ = lean_ptr_addr(v_key_421_);
v___x_429_ = ((size_t)3ULL);
v___x_430_ = lean_usize_shift_right(v___x_428_, v___x_429_);
v___x_431_ = lean_usize_to_uint64(v___x_430_);
v___x_432_ = 32ULL;
v___x_433_ = lean_uint64_shift_right(v___x_431_, v___x_432_);
v_fold_434_ = lean_uint64_xor(v___x_431_, v___x_433_);
v___x_435_ = 16ULL;
v___x_436_ = lean_uint64_shift_right(v_fold_434_, v___x_435_);
v___x_437_ = lean_uint64_xor(v_fold_434_, v___x_436_);
v___x_438_ = lean_uint64_to_usize(v___x_437_);
v___x_439_ = lean_usize_of_nat(v___x_427_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_sub(v___x_439_, v___x_440_);
v___x_442_ = lean_usize_land(v___x_438_, v___x_441_);
v___x_443_ = lean_array_uget_borrowed(v_x_419_, v___x_442_);
lean_inc(v___x_443_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 2, v___x_443_);
v___x_445_ = v___x_425_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_key_421_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_value_422_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v___x_443_);
v___x_445_ = v_reuseFailAlloc_448_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_array_uset(v_x_419_, v___x_442_, v___x_445_);
v_x_419_ = v___x_446_;
v_x_420_ = v_tail_423_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_450_, lean_object* v_source_451_, lean_object* v_target_452_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_get_size(v_source_451_);
v___x_454_ = lean_nat_dec_lt(v_i_450_, v___x_453_);
if (v___x_454_ == 0)
{
lean_dec_ref(v_source_451_);
lean_dec(v_i_450_);
return v_target_452_;
}
else
{
lean_object* v_es_455_; lean_object* v___x_456_; lean_object* v_source_457_; lean_object* v_target_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_es_455_ = lean_array_fget(v_source_451_, v_i_450_);
v___x_456_ = lean_box(0);
v_source_457_ = lean_array_fset(v_source_451_, v_i_450_, v___x_456_);
v_target_458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_452_, v_es_455_);
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_add(v_i_450_, v___x_459_);
lean_dec(v_i_450_);
v_i_450_ = v___x_460_;
v_source_451_ = v_source_457_;
v_target_452_ = v_target_458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_nbuckets_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_463_ = lean_array_get_size(v_data_462_);
v___x_464_ = lean_unsigned_to_nat(2u);
v_nbuckets_465_ = lean_nat_mul(v___x_463_, v___x_464_);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_box(0);
v___x_468_ = lean_mk_array(v_nbuckets_465_, v___x_467_);
v___x_469_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_466_, v_data_462_, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
uint8_t v___x_472_; 
v___x_472_ = 0;
return v___x_472_;
}
else
{
lean_object* v_key_473_; lean_object* v_tail_474_; size_t v___x_475_; size_t v___x_476_; uint8_t v___x_477_; 
v_key_473_ = lean_ctor_get(v_x_471_, 0);
v_tail_474_ = lean_ctor_get(v_x_471_, 2);
v___x_475_ = lean_ptr_addr(v_key_473_);
v___x_476_ = lean_ptr_addr(v_a_470_);
v___x_477_ = lean_usize_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
v_x_471_ = v_tail_474_;
goto _start;
}
else
{
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_479_, v_x_480_);
lean_dec(v_x_480_);
lean_dec_ref(v_a_479_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_483_, lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
lean_object* v_size_486_; lean_object* v_buckets_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_533_; 
v_size_486_ = lean_ctor_get(v_m_483_, 0);
v_buckets_487_ = lean_ctor_get(v_m_483_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_m_483_);
if (v_isSharedCheck_533_ == 0)
{
v___x_489_ = v_m_483_;
v_isShared_490_ = v_isSharedCheck_533_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_buckets_487_);
lean_inc(v_size_486_);
lean_dec(v_m_483_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_533_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v_fold_498_; uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v_bkt_507_; uint8_t v___x_508_; 
v___x_491_ = lean_array_get_size(v_buckets_487_);
v___x_492_ = lean_ptr_addr(v_a_484_);
v___x_493_ = ((size_t)3ULL);
v___x_494_ = lean_usize_shift_right(v___x_492_, v___x_493_);
v___x_495_ = lean_usize_to_uint64(v___x_494_);
v___x_496_ = 32ULL;
v___x_497_ = lean_uint64_shift_right(v___x_495_, v___x_496_);
v_fold_498_ = lean_uint64_xor(v___x_495_, v___x_497_);
v___x_499_ = 16ULL;
v___x_500_ = lean_uint64_shift_right(v_fold_498_, v___x_499_);
v___x_501_ = lean_uint64_xor(v_fold_498_, v___x_500_);
v___x_502_ = lean_uint64_to_usize(v___x_501_);
v___x_503_ = lean_usize_of_nat(v___x_491_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_sub(v___x_503_, v___x_504_);
v___x_506_ = lean_usize_land(v___x_502_, v___x_505_);
v_bkt_507_ = lean_array_uget_borrowed(v_buckets_487_, v___x_506_);
v___x_508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_484_, v_bkt_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v_size_x27_510_; lean_object* v___x_511_; lean_object* v_buckets_x27_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v_size_x27_510_ = lean_nat_add(v_size_486_, v___x_509_);
lean_dec(v_size_486_);
lean_inc(v_bkt_507_);
v___x_511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_511_, 0, v_a_484_);
lean_ctor_set(v___x_511_, 1, v_b_485_);
lean_ctor_set(v___x_511_, 2, v_bkt_507_);
v_buckets_x27_512_ = lean_array_uset(v_buckets_487_, v___x_506_, v___x_511_);
v___x_513_ = lean_unsigned_to_nat(4u);
v___x_514_ = lean_nat_mul(v_size_x27_510_, v___x_513_);
v___x_515_ = lean_unsigned_to_nat(3u);
v___x_516_ = lean_nat_div(v___x_514_, v___x_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_array_get_size(v_buckets_x27_512_);
v___x_518_ = lean_nat_dec_le(v___x_516_, v___x_517_);
lean_dec(v___x_516_);
if (v___x_518_ == 0)
{
lean_object* v_val_519_; lean_object* v___x_521_; 
v_val_519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_512_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_val_519_);
lean_ctor_set(v___x_489_, 0, v_size_x27_510_);
v___x_521_ = v___x_489_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_size_x27_510_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_val_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
lean_object* v___x_524_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_buckets_x27_512_);
lean_ctor_set(v___x_489_, 0, v_size_x27_510_);
v___x_524_ = v___x_489_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_size_x27_510_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_buckets_x27_512_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v___x_526_; lean_object* v_buckets_x27_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc(v_bkt_507_);
v___x_526_ = lean_box(0);
v_buckets_x27_527_ = lean_array_uset(v_buckets_487_, v___x_506_, v___x_526_);
v___x_528_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_484_, v_b_485_, v_bkt_507_);
v___x_529_ = lean_array_uset(v_buckets_x27_527_, v___x_506_, v___x_528_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_529_);
v___x_531_ = v___x_489_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_size_486_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_534_; size_t v___x_535_; 
v___x_534_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_535_ = lean_ptr_addr(v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_536_, lean_object* v_r_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_map_539_; lean_object* v_set_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_564_; 
v_map_539_ = lean_ctor_get(v_a_538_, 0);
v_set_540_ = lean_ctor_get(v_a_538_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_538_);
if (v_isSharedCheck_564_ == 0)
{
v___x_542_ = v_a_538_;
v_isShared_543_ = v_isSharedCheck_564_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_set_540_);
lean_inc(v_map_539_);
lean_dec(v_a_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_564_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; uint64_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_544_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_545_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_537_);
v___x_546_ = lean_uint64_to_usize(v___x_545_);
lean_inc_ref(v_r_537_);
lean_inc_ref(v_set_540_);
v___x_547_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_540_, v___x_546_, v_r_537_, v___x_544_);
v___x_548_ = lean_ptr_addr(v___x_547_);
v___x_549_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec_ref(v_r_537_);
lean_inc_ref(v___x_547_);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_539_, v_e_536_, v___x_547_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_551_);
v___x_553_ = v___x_542_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_set_540_);
v___x_553_ = v_reuseFailAlloc_555_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_547_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
return v___x_554_;
}
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec_ref(v___x_547_);
lean_inc_ref_n(v_r_537_, 4);
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_539_, v_e_536_, v_r_537_);
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_556_, v_r_537_, v_r_537_);
v___x_558_ = lean_box(0);
v___x_559_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_540_, v_r_537_, v___x_558_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v___x_559_);
lean_ctor_set(v___x_542_, 0, v___x_557_);
v___x_561_ = v___x_542_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_563_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_r_537_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_565_, lean_object* v_r_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_565_, v_r_566_, v_a_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_570_, lean_object* v_r_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_570_, v_r_571_, v_a_572_, v_a_573_);
lean_dec_ref(v_a_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_575_, lean_object* v_x_576_, size_t v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_576_, v_x_577_, v_x_578_, v_x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
size_t v_x_2667__boxed_586_; lean_object* v_res_587_; 
v_x_2667__boxed_586_ = lean_unbox_usize(v_x_583_);
lean_dec(v_x_583_);
v_res_587_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_581_, v_x_582_, v_x_2667__boxed_586_, v_x_584_, v_x_585_);
lean_dec_ref(v_x_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_588_, lean_object* v_m_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_589_, v_a_590_, v_b_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_594_, v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_598_, lean_object* v_keys_599_, lean_object* v_vals_600_, lean_object* v_heq_601_, lean_object* v_i_602_, lean_object* v_k_603_, lean_object* v_k_u2080_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_599_, v_i_602_, v_k_603_, v_k_u2080_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_606_, lean_object* v_keys_607_, lean_object* v_vals_608_, lean_object* v_heq_609_, lean_object* v_i_610_, lean_object* v_k_611_, lean_object* v_k_u2080_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_606_, v_keys_607_, v_vals_608_, v_heq_609_, v_i_610_, v_k_611_, v_k_u2080_612_);
lean_dec_ref(v_k_u2080_612_);
lean_dec_ref(v_vals_608_);
lean_dec_ref(v_keys_607_);
return v_res_613_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_614_, lean_object* v_a_615_, lean_object* v_x_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_615_, v_x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_618_, lean_object* v_a_619_, lean_object* v_x_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_618_, v_a_619_, v_x_620_);
lean_dec(v_x_620_);
lean_dec_ref(v_a_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_623_, lean_object* v_data_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_626_, lean_object* v_a_627_, lean_object* v_b_628_, lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_627_, v_b_628_, v_x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_631_, lean_object* v_x_632_, size_t v_x_633_, size_t v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_632_, v_x_633_, v_x_634_, v_x_635_, v_x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
size_t v_x_2704__boxed_644_; size_t v_x_2705__boxed_645_; lean_object* v_res_646_; 
v_x_2704__boxed_644_ = lean_unbox_usize(v_x_640_);
lean_dec(v_x_640_);
v_x_2705__boxed_645_ = lean_unbox_usize(v_x_641_);
lean_dec(v_x_641_);
v_res_646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_638_, v_x_639_, v_x_2704__boxed_644_, v_x_2705__boxed_645_, v_x_642_, v_x_643_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_647_, lean_object* v_i_648_, lean_object* v_source_649_, lean_object* v_target_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_648_, v_source_649_, v_target_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_652_, lean_object* v_n_653_, lean_object* v_k_654_, lean_object* v_v_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_653_, v_k_654_, v_v_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_657_, size_t v_depth_658_, lean_object* v_keys_659_, lean_object* v_vals_660_, lean_object* v_heq_661_, lean_object* v_i_662_, lean_object* v_entries_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_658_, v_keys_659_, v_vals_660_, v_i_662_, v_entries_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_665_, lean_object* v_depth_666_, lean_object* v_keys_667_, lean_object* v_vals_668_, lean_object* v_heq_669_, lean_object* v_i_670_, lean_object* v_entries_671_){
_start:
{
size_t v_depth_boxed_672_; lean_object* v_res_673_; 
v_depth_boxed_672_ = lean_unbox_usize(v_depth_666_);
lean_dec(v_depth_666_);
v_res_673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_665_, v_depth_boxed_672_, v_keys_667_, v_vals_668_, v_heq_669_, v_i_670_, v_entries_671_);
lean_dec_ref(v_vals_668_);
lean_dec_ref(v_keys_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_679_, v_x_680_, v_x_681_, v_x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_686_, lean_object* v_k_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_map_690_; lean_object* v_set_691_; lean_object* v___f_692_; lean_object* v___f_693_; lean_object* v___x_694_; 
v_map_690_ = lean_ctor_get(v_a_689_, 0);
v_set_691_ = lean_ctor_get(v_a_689_, 1);
v___f_692_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_693_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_686_);
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_692_, v___f_693_, v_map_690_, v_e_686_);
if (lean_obj_tag(v___x_694_) == 1)
{
lean_object* v_val_695_; lean_object* v___x_696_; 
lean_dec_ref(v_k_687_);
lean_dec_ref(v_e_686_);
v_val_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_val_695_);
lean_ctor_set(v___x_696_, 1, v_a_689_);
return v___x_696_;
}
else
{
lean_object* v___f_697_; lean_object* v___x_698_; uint64_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; size_t v___x_702_; size_t v___x_703_; uint8_t v___x_704_; 
lean_dec(v___x_694_);
v___f_697_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_698_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_699_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_686_);
v___x_700_ = lean_uint64_to_usize(v___x_699_);
lean_inc_ref(v_e_686_);
lean_inc_ref(v_set_691_);
v___x_701_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_697_, v_set_691_, v___x_700_, v_e_686_, v___x_698_);
v___x_702_ = lean_ptr_addr(v___x_701_);
v___x_703_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_704_ = lean_usize_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec_ref(v_k_687_);
lean_dec_ref(v_e_686_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_701_);
lean_ctor_set(v___x_705_, 1, v_a_689_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; 
lean_dec(v___x_701_);
lean_inc_ref(v_a_688_);
v___x_706_ = lean_apply_2(v_k_687_, v_a_688_, v_a_689_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
v_a_708_ = lean_ctor_get(v___x_706_, 1);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_706_, 2);
v___x_709_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_686_, v_a_707_, v_a_708_);
return v___x_709_;
}
else
{
lean_dec_ref(v_e_686_);
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_710_, lean_object* v_k_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_710_, v_k_711_, v_a_712_, v_a_713_);
lean_dec_ref(v_a_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_715_, lean_object* v_x_716_){
_start:
{
if (lean_obj_tag(v_x_716_) == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_box(0);
return v___x_717_;
}
else
{
lean_object* v_key_718_; lean_object* v_value_719_; lean_object* v_tail_720_; size_t v___x_721_; size_t v___x_722_; uint8_t v___x_723_; 
v_key_718_ = lean_ctor_get(v_x_716_, 0);
v_value_719_ = lean_ctor_get(v_x_716_, 1);
v_tail_720_ = lean_ctor_get(v_x_716_, 2);
v___x_721_ = lean_ptr_addr(v_key_718_);
v___x_722_ = lean_ptr_addr(v_a_715_);
v___x_723_ = lean_usize_dec_eq(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
v_x_716_ = v_tail_720_;
goto _start;
}
else
{
lean_object* v___x_725_; 
lean_inc(v_value_719_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_value_719_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_726_, v_x_727_);
lean_dec(v_x_727_);
lean_dec_ref(v_a_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_buckets_731_; lean_object* v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; uint64_t v___x_736_; uint64_t v___x_737_; uint64_t v___x_738_; uint64_t v_fold_739_; uint64_t v___x_740_; uint64_t v___x_741_; uint64_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_buckets_731_ = lean_ctor_get(v_m_729_, 1);
v___x_732_ = lean_array_get_size(v_buckets_731_);
v___x_733_ = lean_ptr_addr(v_a_730_);
v___x_734_ = ((size_t)3ULL);
v___x_735_ = lean_usize_shift_right(v___x_733_, v___x_734_);
v___x_736_ = lean_usize_to_uint64(v___x_735_);
v___x_737_ = 32ULL;
v___x_738_ = lean_uint64_shift_right(v___x_736_, v___x_737_);
v_fold_739_ = lean_uint64_xor(v___x_736_, v___x_738_);
v___x_740_ = 16ULL;
v___x_741_ = lean_uint64_shift_right(v_fold_739_, v___x_740_);
v___x_742_ = lean_uint64_xor(v_fold_739_, v___x_741_);
v___x_743_ = lean_uint64_to_usize(v___x_742_);
v___x_744_ = lean_usize_of_nat(v___x_732_);
v___x_745_ = ((size_t)1ULL);
v___x_746_ = lean_usize_sub(v___x_744_, v___x_745_);
v___x_747_ = lean_usize_land(v___x_743_, v___x_746_);
v___x_748_ = lean_array_uget_borrowed(v_buckets_731_, v___x_747_);
v___x_749_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_730_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_750_, v_a_751_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_m_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_i_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_keys_753_);
v___x_758_ = lean_nat_dec_lt(v_i_755_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec_ref(v_k_756_);
lean_dec(v_i_755_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
else
{
lean_object* v_k_x27_760_; uint8_t v___x_761_; 
v_k_x27_760_ = lean_array_fget_borrowed(v_keys_753_, v_i_755_);
lean_inc(v_k_x27_760_);
lean_inc_ref(v_k_756_);
v___x_761_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_756_, v_k_x27_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_i_755_, v___x_762_);
lean_dec(v_i_755_);
v_i_755_ = v___x_763_;
goto _start;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref(v_k_756_);
v___x_765_ = lean_array_fget_borrowed(v_vals_754_, v_i_755_);
lean_dec(v_i_755_);
lean_inc(v___x_765_);
lean_inc(v_k_x27_760_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_k_x27_760_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_768_, lean_object* v_vals_769_, lean_object* v_i_770_, lean_object* v_k_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_768_, v_vals_769_, v_i_770_, v_k_771_);
lean_dec_ref(v_vals_769_);
lean_dec_ref(v_keys_768_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_773_, size_t v_x_774_, lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v_es_776_; lean_object* v___x_777_; size_t v___x_778_; size_t v___x_779_; lean_object* v_j_780_; lean_object* v___x_781_; 
v_es_776_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_es_776_);
lean_dec_ref_known(v_x_773_, 1);
v___x_777_ = lean_box(2);
v___x_778_ = ((size_t)31ULL);
v___x_779_ = lean_usize_land(v_x_774_, v___x_778_);
v_j_780_ = lean_usize_to_nat(v___x_779_);
v___x_781_ = lean_array_get(v___x_777_, v_es_776_, v_j_780_);
lean_dec(v_j_780_);
lean_dec_ref(v_es_776_);
switch(lean_obj_tag(v___x_781_))
{
case 0:
{
lean_object* v_key_782_; lean_object* v_val_783_; uint8_t v___x_784_; 
v_key_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_n(v_key_782_, 2);
v_val_783_ = lean_ctor_get(v___x_781_, 1);
lean_inc(v_val_783_);
lean_dec_ref_known(v___x_781_, 2);
v___x_784_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_775_, v_key_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v_val_783_);
lean_dec(v_key_782_);
v___x_785_ = lean_box(0);
return v___x_785_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_key_782_);
lean_ctor_set(v___x_786_, 1, v_val_783_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
case 1:
{
lean_object* v_node_788_; size_t v___x_789_; size_t v___x_790_; 
v_node_788_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_node_788_);
lean_dec_ref_known(v___x_781_, 1);
v___x_789_ = ((size_t)5ULL);
v___x_790_ = lean_usize_shift_right(v_x_774_, v___x_789_);
v_x_773_ = v_node_788_;
v_x_774_ = v___x_790_;
goto _start;
}
default: 
{
lean_object* v___x_792_; 
lean_dec_ref(v_x_775_);
v___x_792_ = lean_box(0);
return v___x_792_;
}
}
}
else
{
lean_object* v_ks_793_; lean_object* v_vs_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_ks_793_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_ks_793_);
v_vs_794_ = lean_ctor_get(v_x_773_, 1);
lean_inc_ref(v_vs_794_);
lean_dec_ref_known(v_x_773_, 2);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_793_, v_vs_794_, v___x_795_, v_x_775_);
lean_dec_ref(v_vs_794_);
lean_dec_ref(v_ks_793_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
size_t v_x_11089__boxed_800_; lean_object* v_res_801_; 
v_x_11089__boxed_800_ = lean_unbox_usize(v_x_798_);
lean_dec(v_x_798_);
v_res_801_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_797_, v_x_11089__boxed_800_, v_x_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
uint64_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_803_);
v___x_805_ = lean_uint64_to_usize(v___x_804_);
lean_inc_ref(v_x_802_);
v___x_806_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_802_, v___x_805_, v_x_803_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_807_, v_x_808_);
lean_dec_ref(v_x_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___y_814_; lean_object* v___y_819_; lean_object* v___y_824_; lean_object* v___y_829_; 
switch(lean_obj_tag(v_e_810_))
{
case 4:
{
lean_object* v_declName_833_; lean_object* v_map_834_; lean_object* v_set_835_; lean_object* v___x_836_; 
v_declName_833_ = lean_ctor_get(v_e_810_, 0);
v_map_834_ = lean_ctor_get(v_a_812_, 0);
v_set_835_ = lean_ctor_get(v_a_812_, 1);
lean_inc_ref(v_e_810_);
v___x_836_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_835_, v_e_810_);
if (lean_obj_tag(v___x_836_) == 0)
{
uint8_t v___x_837_; 
lean_inc(v_declName_833_);
lean_inc_ref(v_a_811_);
v___x_837_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_811_, v_declName_833_);
if (v___x_837_ == 0)
{
lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_847_; 
lean_inc_ref(v_set_835_);
lean_inc_ref(v_map_834_);
v_isSharedCheck_847_ = !lean_is_exclusive(v_a_812_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_848_ = lean_ctor_get(v_a_812_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_a_812_, 0);
lean_dec(v_unused_849_);
v___x_839_ = v_a_812_;
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
else
{
lean_dec(v_a_812_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = lean_box(0);
lean_inc_ref(v_e_810_);
v___x_842_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_835_, v_e_810_, v___x_841_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_842_);
v___x_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_map_834_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_842_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_e_810_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
return v___x_845_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref_known(v_e_810_, 2);
v___x_850_ = lean_box(0);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_a_812_);
return v___x_851_;
}
}
else
{
lean_object* v_val_852_; lean_object* v_fst_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec_ref_known(v_e_810_, 2);
v_val_852_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v___x_836_, 1);
v_fst_853_ = lean_ctor_get(v_val_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_val_852_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_val_852_, 1);
lean_dec(v_unused_861_);
v___x_855_ = v_val_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_fst_853_);
lean_dec(v_val_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v_a_812_);
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_fst_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_a_812_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
case 5:
{
lean_object* v_fn_862_; lean_object* v_arg_863_; lean_object* v_map_864_; lean_object* v_set_865_; lean_object* v___x_866_; 
v_fn_862_ = lean_ctor_get(v_e_810_, 0);
v_arg_863_ = lean_ctor_get(v_e_810_, 1);
v_map_864_ = lean_ctor_get(v_a_812_, 0);
v_set_865_ = lean_ctor_get(v_a_812_, 1);
v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_864_, v_e_810_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_object* v_val_867_; lean_object* v___x_868_; 
lean_dec_ref_known(v_e_810_, 2);
v_val_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_val_867_);
lean_ctor_set(v___x_868_, 1, v_a_812_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; uint64_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; size_t v___x_873_; size_t v___x_874_; uint8_t v___x_875_; 
lean_dec(v___x_866_);
v___x_869_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_870_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_810_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
lean_inc_ref(v_e_810_);
lean_inc_ref(v_set_865_);
v___x_872_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_865_, v___x_871_, v_e_810_, v___x_869_);
v___x_873_ = lean_ptr_addr(v___x_872_);
v___x_874_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_875_ = lean_usize_dec_eq(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref_known(v_e_810_, 2);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_872_);
lean_ctor_set(v___x_876_, 1, v_a_812_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; 
lean_dec_ref(v___x_872_);
lean_inc_ref(v_fn_862_);
v___x_877_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_862_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v_a_879_; lean_object* v___x_880_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
v_a_879_ = lean_ctor_get(v___x_877_, 1);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_877_, 2);
lean_inc_ref(v_arg_863_);
v___x_880_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_863_, v_a_811_, v_a_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v_a_882_; uint8_t v___y_884_; size_t v___x_888_; size_t v___x_889_; uint8_t v___x_890_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
v_a_882_ = lean_ctor_get(v___x_880_, 1);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_880_, 2);
v___x_888_ = lean_ptr_addr(v_fn_862_);
v___x_889_ = lean_ptr_addr(v_a_878_);
v___x_890_ = lean_usize_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
v___y_884_ = v___x_890_;
goto v___jp_883_;
}
else
{
size_t v___x_891_; size_t v___x_892_; uint8_t v___x_893_; 
v___x_891_ = lean_ptr_addr(v_arg_863_);
v___x_892_ = lean_ptr_addr(v_a_881_);
v___x_893_ = lean_usize_dec_eq(v___x_891_, v___x_892_);
v___y_884_ = v___x_893_;
goto v___jp_883_;
}
v___jp_883_:
{
if (v___y_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Lean_Expr_app___override(v_a_878_, v_a_881_);
v___x_886_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_885_, v_a_882_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; 
lean_dec(v_a_881_);
lean_dec(v_a_878_);
lean_inc_ref(v_e_810_);
v___x_887_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_e_810_, v_a_882_);
return v___x_887_;
}
}
}
else
{
lean_dec(v_a_878_);
v___y_824_ = v___x_880_;
goto v___jp_823_;
}
}
else
{
v___y_824_ = v___x_877_;
goto v___jp_823_;
}
}
}
}
case 6:
{
lean_object* v_binderName_894_; lean_object* v_binderType_895_; lean_object* v_body_896_; uint8_t v_binderInfo_897_; lean_object* v_map_898_; lean_object* v_set_899_; lean_object* v___x_900_; 
v_binderName_894_ = lean_ctor_get(v_e_810_, 0);
v_binderType_895_ = lean_ctor_get(v_e_810_, 1);
v_body_896_ = lean_ctor_get(v_e_810_, 2);
v_binderInfo_897_ = lean_ctor_get_uint8(v_e_810_, sizeof(void*)*3 + 8);
v_map_898_ = lean_ctor_get(v_a_812_, 0);
v_set_899_ = lean_ctor_get(v_a_812_, 1);
v___x_900_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_898_, v_e_810_);
if (lean_obj_tag(v___x_900_) == 1)
{
lean_object* v_val_901_; lean_object* v___x_902_; 
lean_dec_ref_known(v_e_810_, 3);
v_val_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_val_901_);
lean_ctor_set(v___x_902_, 1, v_a_812_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; uint64_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; size_t v___x_907_; size_t v___x_908_; uint8_t v___x_909_; 
lean_dec(v___x_900_);
v___x_903_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_904_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_810_);
v___x_905_ = lean_uint64_to_usize(v___x_904_);
lean_inc_ref(v_e_810_);
lean_inc_ref(v_set_899_);
v___x_906_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_899_, v___x_905_, v_e_810_, v___x_903_);
v___x_907_ = lean_ptr_addr(v___x_906_);
v___x_908_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_909_ = lean_usize_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec_ref_known(v_e_810_, 3);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_906_);
lean_ctor_set(v___x_910_, 1, v_a_812_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; 
lean_dec_ref(v___x_906_);
lean_inc_ref(v_binderType_895_);
v___x_911_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_895_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
v_a_913_ = lean_ctor_get(v___x_911_, 1);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_911_, 2);
lean_inc_ref(v_body_896_);
v___x_914_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_896_, v_a_811_, v_a_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v_a_916_; uint8_t v___y_918_; size_t v___x_925_; size_t v___x_926_; uint8_t v___x_927_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
v_a_916_ = lean_ctor_get(v___x_914_, 1);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_914_, 2);
v___x_925_ = lean_ptr_addr(v_binderType_895_);
v___x_926_ = lean_ptr_addr(v_a_912_);
v___x_927_ = lean_usize_dec_eq(v___x_925_, v___x_926_);
if (v___x_927_ == 0)
{
v___y_918_ = v___x_927_;
goto v___jp_917_;
}
else
{
size_t v___x_928_; size_t v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_ptr_addr(v_body_896_);
v___x_929_ = lean_ptr_addr(v_a_915_);
v___x_930_ = lean_usize_dec_eq(v___x_928_, v___x_929_);
v___y_918_ = v___x_930_;
goto v___jp_917_;
}
v___jp_917_:
{
if (v___y_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_inc(v_binderName_894_);
v___x_919_ = l_Lean_Expr_lam___override(v_binderName_894_, v_a_912_, v_a_915_, v_binderInfo_897_);
v___x_920_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_919_, v_a_916_);
return v___x_920_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_897_, v_binderInfo_897_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_inc(v_binderName_894_);
v___x_922_ = l_Lean_Expr_lam___override(v_binderName_894_, v_a_912_, v_a_915_, v_binderInfo_897_);
v___x_923_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_922_, v_a_916_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v_a_915_);
lean_dec(v_a_912_);
lean_inc_ref(v_e_810_);
v___x_924_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_e_810_, v_a_916_);
return v___x_924_;
}
}
}
}
else
{
lean_dec(v_a_912_);
v___y_819_ = v___x_914_;
goto v___jp_818_;
}
}
else
{
v___y_819_ = v___x_911_;
goto v___jp_818_;
}
}
}
}
case 7:
{
lean_object* v_binderName_931_; lean_object* v_binderType_932_; lean_object* v_body_933_; uint8_t v_binderInfo_934_; lean_object* v_map_935_; lean_object* v_set_936_; lean_object* v___x_937_; 
v_binderName_931_ = lean_ctor_get(v_e_810_, 0);
v_binderType_932_ = lean_ctor_get(v_e_810_, 1);
v_body_933_ = lean_ctor_get(v_e_810_, 2);
v_binderInfo_934_ = lean_ctor_get_uint8(v_e_810_, sizeof(void*)*3 + 8);
v_map_935_ = lean_ctor_get(v_a_812_, 0);
v_set_936_ = lean_ctor_get(v_a_812_, 1);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_935_, v_e_810_);
if (lean_obj_tag(v___x_937_) == 1)
{
lean_object* v_val_938_; lean_object* v___x_939_; 
lean_dec_ref_known(v_e_810_, 3);
v_val_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_val_938_);
lean_dec_ref_known(v___x_937_, 1);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_val_938_);
lean_ctor_set(v___x_939_, 1, v_a_812_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; uint64_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; size_t v___x_944_; size_t v___x_945_; uint8_t v___x_946_; 
lean_dec(v___x_937_);
v___x_940_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_941_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_810_);
v___x_942_ = lean_uint64_to_usize(v___x_941_);
lean_inc_ref(v_e_810_);
lean_inc_ref(v_set_936_);
v___x_943_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_936_, v___x_942_, v_e_810_, v___x_940_);
v___x_944_ = lean_ptr_addr(v___x_943_);
v___x_945_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_946_ = lean_usize_dec_eq(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec_ref_known(v_e_810_, 3);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_943_);
lean_ctor_set(v___x_947_, 1, v_a_812_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; 
lean_dec_ref(v___x_943_);
lean_inc_ref(v_binderType_932_);
v___x_948_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_932_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v_a_950_; lean_object* v___x_951_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
v_a_950_ = lean_ctor_get(v___x_948_, 1);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_948_, 2);
lean_inc_ref(v_body_933_);
v___x_951_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_933_, v_a_811_, v_a_950_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_a_953_; uint8_t v___y_955_; size_t v___x_962_; size_t v___x_963_; uint8_t v___x_964_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
v_a_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_951_, 2);
v___x_962_ = lean_ptr_addr(v_binderType_932_);
v___x_963_ = lean_ptr_addr(v_a_949_);
v___x_964_ = lean_usize_dec_eq(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
v___y_955_ = v___x_964_;
goto v___jp_954_;
}
else
{
size_t v___x_965_; size_t v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_ptr_addr(v_body_933_);
v___x_966_ = lean_ptr_addr(v_a_952_);
v___x_967_ = lean_usize_dec_eq(v___x_965_, v___x_966_);
v___y_955_ = v___x_967_;
goto v___jp_954_;
}
v___jp_954_:
{
if (v___y_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_inc(v_binderName_931_);
v___x_956_ = l_Lean_Expr_forallE___override(v_binderName_931_, v_a_949_, v_a_952_, v_binderInfo_934_);
v___x_957_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_956_, v_a_953_);
return v___x_957_;
}
else
{
uint8_t v___x_958_; 
v___x_958_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_934_, v_binderInfo_934_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_inc(v_binderName_931_);
v___x_959_ = l_Lean_Expr_forallE___override(v_binderName_931_, v_a_949_, v_a_952_, v_binderInfo_934_);
v___x_960_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_959_, v_a_953_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; 
lean_dec(v_a_952_);
lean_dec(v_a_949_);
lean_inc_ref(v_e_810_);
v___x_961_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_e_810_, v_a_953_);
return v___x_961_;
}
}
}
}
else
{
lean_dec(v_a_949_);
v___y_829_ = v___x_951_;
goto v___jp_828_;
}
}
else
{
v___y_829_ = v___x_948_;
goto v___jp_828_;
}
}
}
}
case 8:
{
lean_object* v_declName_968_; lean_object* v_type_969_; lean_object* v_value_970_; lean_object* v_body_971_; uint8_t v_nondep_972_; lean_object* v_map_973_; lean_object* v_set_974_; lean_object* v___x_975_; 
v_declName_968_ = lean_ctor_get(v_e_810_, 0);
v_type_969_ = lean_ctor_get(v_e_810_, 1);
v_value_970_ = lean_ctor_get(v_e_810_, 2);
v_body_971_ = lean_ctor_get(v_e_810_, 3);
v_nondep_972_ = lean_ctor_get_uint8(v_e_810_, sizeof(void*)*4 + 8);
v_map_973_ = lean_ctor_get(v_a_812_, 0);
v_set_974_ = lean_ctor_get(v_a_812_, 1);
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_973_, v_e_810_);
if (lean_obj_tag(v___x_975_) == 1)
{
lean_object* v_val_976_; lean_object* v___x_977_; 
lean_dec_ref_known(v_e_810_, 4);
v_val_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_val_976_);
lean_ctor_set(v___x_977_, 1, v_a_812_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; uint64_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; size_t v___x_982_; size_t v___x_983_; uint8_t v___x_984_; 
lean_dec(v___x_975_);
v___x_978_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_979_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_810_);
v___x_980_ = lean_uint64_to_usize(v___x_979_);
lean_inc_ref(v_e_810_);
lean_inc_ref(v_set_974_);
v___x_981_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_974_, v___x_980_, v_e_810_, v___x_978_);
v___x_982_ = lean_ptr_addr(v___x_981_);
v___x_983_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_984_ = lean_usize_dec_eq(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec_ref_known(v_e_810_, 4);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_981_);
lean_ctor_set(v___x_985_, 1, v_a_812_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; 
lean_dec_ref(v___x_981_);
lean_inc_ref(v_type_969_);
v___x_986_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_969_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
v_a_988_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_986_, 2);
lean_inc_ref(v_value_970_);
v___x_989_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_970_, v_a_811_, v_a_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
v_a_991_ = lean_ctor_get(v___x_989_, 1);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_989_, 2);
lean_inc_ref(v_body_971_);
v___x_992_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_971_, v_a_811_, v_a_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v_a_994_; uint8_t v___y_996_; size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
v_a_994_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_992_, 2);
v___x_1005_ = lean_ptr_addr(v_type_969_);
v___x_1006_ = lean_ptr_addr(v_a_987_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
v___y_996_ = v___x_1007_;
goto v___jp_995_;
}
else
{
size_t v___x_1008_; size_t v___x_1009_; uint8_t v___x_1010_; 
v___x_1008_ = lean_ptr_addr(v_value_970_);
v___x_1009_ = lean_ptr_addr(v_a_990_);
v___x_1010_ = lean_usize_dec_eq(v___x_1008_, v___x_1009_);
v___y_996_ = v___x_1010_;
goto v___jp_995_;
}
v___jp_995_:
{
if (v___y_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc(v_declName_968_);
v___x_997_ = l_Lean_Expr_letE___override(v_declName_968_, v_a_987_, v_a_990_, v_a_993_, v_nondep_972_);
v___x_998_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_997_, v_a_994_);
return v___x_998_;
}
else
{
size_t v___x_999_; size_t v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = lean_ptr_addr(v_body_971_);
v___x_1000_ = lean_ptr_addr(v_a_993_);
v___x_1001_ = lean_usize_dec_eq(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_inc(v_declName_968_);
v___x_1002_ = l_Lean_Expr_letE___override(v_declName_968_, v_a_987_, v_a_990_, v_a_993_, v_nondep_972_);
v___x_1003_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_1002_, v_a_994_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; 
lean_dec(v_a_993_);
lean_dec(v_a_990_);
lean_dec(v_a_987_);
lean_inc_ref(v_e_810_);
v___x_1004_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_e_810_, v_a_994_);
return v___x_1004_;
}
}
}
}
else
{
lean_dec(v_a_990_);
lean_dec(v_a_987_);
v___y_814_ = v___x_992_;
goto v___jp_813_;
}
}
else
{
lean_dec(v_a_987_);
v___y_814_ = v___x_989_;
goto v___jp_813_;
}
}
else
{
v___y_814_ = v___x_986_;
goto v___jp_813_;
}
}
}
}
case 10:
{
lean_object* v_data_1011_; lean_object* v_expr_1012_; lean_object* v_map_1013_; lean_object* v_set_1014_; lean_object* v___x_1015_; 
v_data_1011_ = lean_ctor_get(v_e_810_, 0);
v_expr_1012_ = lean_ctor_get(v_e_810_, 1);
v_map_1013_ = lean_ctor_get(v_a_812_, 0);
v_set_1014_ = lean_ctor_get(v_a_812_, 1);
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1013_, v_e_810_);
if (lean_obj_tag(v___x_1015_) == 1)
{
lean_object* v_val_1016_; lean_object* v___x_1017_; 
lean_dec_ref_known(v_e_810_, 2);
v_val_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v_val_1016_);
lean_ctor_set(v___x_1017_, 1, v_a_812_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; uint64_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; uint8_t v___x_1024_; 
lean_dec(v___x_1015_);
v___x_1018_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1019_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_810_);
v___x_1020_ = lean_uint64_to_usize(v___x_1019_);
lean_inc_ref(v_e_810_);
lean_inc_ref(v_set_1014_);
v___x_1021_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1014_, v___x_1020_, v_e_810_, v___x_1018_);
v___x_1022_ = lean_ptr_addr(v___x_1021_);
v___x_1023_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1024_ = lean_usize_dec_eq(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref_known(v_e_810_, 2);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1021_);
lean_ctor_set(v___x_1025_, 1, v_a_812_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; 
lean_dec_ref(v___x_1021_);
lean_inc_ref(v_expr_1012_);
v___x_1026_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1012_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v_a_1028_; size_t v___x_1029_; size_t v___x_1030_; uint8_t v___x_1031_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
v_a_1028_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1026_, 2);
v___x_1029_ = lean_ptr_addr(v_expr_1012_);
v___x_1030_ = lean_ptr_addr(v_a_1027_);
v___x_1031_ = lean_usize_dec_eq(v___x_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_inc(v_data_1011_);
v___x_1032_ = l_Lean_Expr_mdata___override(v_data_1011_, v_a_1027_);
v___x_1033_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_1032_, v_a_1028_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_a_1027_);
lean_inc_ref(v_e_810_);
v___x_1034_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_e_810_, v_a_1028_);
return v___x_1034_;
}
}
else
{
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1035_; lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1035_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1035_);
v_a_1036_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1026_, 2);
v___x_1037_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_a_1035_, v_a_1036_);
return v___x_1037_;
}
else
{
lean_dec_ref_known(v_e_810_, 2);
return v___x_1026_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1038_; lean_object* v_idx_1039_; lean_object* v_struct_1040_; lean_object* v_map_1041_; lean_object* v_set_1042_; lean_object* v___x_1043_; 
v_typeName_1038_ = lean_ctor_get(v_e_810_, 0);
v_idx_1039_ = lean_ctor_get(v_e_810_, 1);
v_struct_1040_ = lean_ctor_get(v_e_810_, 2);
v_map_1041_ = lean_ctor_get(v_a_812_, 0);
v_set_1042_ = lean_ctor_get(v_a_812_, 1);
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1041_, v_e_810_);
if (lean_obj_tag(v___x_1043_) == 1)
{
lean_object* v_val_1044_; lean_object* v___x_1045_; 
lean_dec_ref_known(v_e_810_, 3);
v_val_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_val_1044_);
lean_ctor_set(v___x_1045_, 1, v_a_812_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; uint64_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; uint8_t v___x_1052_; 
lean_dec(v___x_1043_);
v___x_1046_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1047_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_810_);
v___x_1048_ = lean_uint64_to_usize(v___x_1047_);
lean_inc_ref(v_e_810_);
lean_inc_ref(v_set_1042_);
v___x_1049_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1042_, v___x_1048_, v_e_810_, v___x_1046_);
v___x_1050_ = lean_ptr_addr(v___x_1049_);
v___x_1051_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1052_ = lean_usize_dec_eq(v___x_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref_known(v_e_810_, 3);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1049_);
lean_ctor_set(v___x_1053_, 1, v_a_812_);
return v___x_1053_;
}
else
{
uint8_t v_checkProj_1054_; 
lean_dec_ref(v___x_1049_);
v_checkProj_1054_ = lean_ctor_get_uint8(v_a_811_, sizeof(void*)*1 + 1);
if (v_checkProj_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_inc_ref(v_struct_1040_);
v___x_1055_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1040_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v_a_1057_; size_t v___x_1058_; size_t v___x_1059_; uint8_t v___x_1060_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
v_a_1057_ = lean_ctor_get(v___x_1055_, 1);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1055_, 2);
v___x_1058_ = lean_ptr_addr(v_struct_1040_);
v___x_1059_ = lean_ptr_addr(v_a_1056_);
v___x_1060_ = lean_usize_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_inc(v_idx_1039_);
lean_inc(v_typeName_1038_);
v___x_1061_ = l_Lean_Expr_proj___override(v_typeName_1038_, v_idx_1039_, v_a_1056_);
v___x_1062_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v___x_1061_, v_a_1057_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; 
lean_dec(v_a_1056_);
lean_inc_ref(v_e_810_);
v___x_1063_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_e_810_, v_a_1057_);
return v___x_1063_;
}
}
else
{
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1064_; lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1064_);
v_a_1065_ = lean_ctor_get(v___x_1055_, 1);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1055_, 2);
v___x_1066_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_a_1064_, v_a_1065_);
return v___x_1066_;
}
else
{
lean_dec_ref_known(v_e_810_, 3);
return v___x_1055_;
}
}
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref_known(v_e_810_, 3);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v_a_812_);
return v___x_1068_;
}
}
}
}
default: 
{
lean_object* v_map_1069_; lean_object* v_set_1070_; lean_object* v___x_1071_; 
v_map_1069_ = lean_ctor_get(v_a_812_, 0);
v_set_1070_ = lean_ctor_get(v_a_812_, 1);
lean_inc_ref(v_e_810_);
v___x_1071_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1070_, v_e_810_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1081_; 
lean_inc_ref(v_set_1070_);
lean_inc_ref(v_map_1069_);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_a_812_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; 
v_unused_1082_ = lean_ctor_get(v_a_812_, 1);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_a_812_, 0);
lean_dec(v_unused_1083_);
v___x_1073_ = v_a_812_;
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v_a_812_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1075_ = lean_box(0);
lean_inc_ref(v_e_810_);
v___x_1076_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1070_, v_e_810_, v___x_1075_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1076_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_map_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_e_810_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
return v___x_1079_;
}
}
}
else
{
lean_object* v_val_1084_; lean_object* v_fst_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v_e_810_);
v_val_1084_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v___x_1071_, 1);
v_fst_1085_ = lean_ctor_get(v_val_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_val_1084_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v_val_1084_, 1);
lean_dec(v_unused_1093_);
v___x_1087_ = v_val_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_fst_1085_);
lean_dec(v_val_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v_a_812_);
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_fst_1085_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_a_812_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
v___jp_813_:
{
if (lean_obj_tag(v___y_814_) == 0)
{
lean_object* v_a_815_; lean_object* v_a_816_; lean_object* v___x_817_; 
v_a_815_ = lean_ctor_get(v___y_814_, 0);
lean_inc(v_a_815_);
v_a_816_ = lean_ctor_get(v___y_814_, 1);
lean_inc(v_a_816_);
lean_dec_ref_known(v___y_814_, 2);
v___x_817_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_a_815_, v_a_816_);
return v___x_817_;
}
else
{
lean_dec_ref(v_e_810_);
return v___y_814_;
}
}
v___jp_818_:
{
if (lean_obj_tag(v___y_819_) == 0)
{
lean_object* v_a_820_; lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_820_ = lean_ctor_get(v___y_819_, 0);
lean_inc(v_a_820_);
v_a_821_ = lean_ctor_get(v___y_819_, 1);
lean_inc(v_a_821_);
lean_dec_ref_known(v___y_819_, 2);
v___x_822_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_a_820_, v_a_821_);
return v___x_822_;
}
else
{
lean_dec_ref(v_e_810_);
return v___y_819_;
}
}
v___jp_823_:
{
if (lean_obj_tag(v___y_824_) == 0)
{
lean_object* v_a_825_; lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_825_ = lean_ctor_get(v___y_824_, 0);
lean_inc(v_a_825_);
v_a_826_ = lean_ctor_get(v___y_824_, 1);
lean_inc(v_a_826_);
lean_dec_ref_known(v___y_824_, 2);
v___x_827_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_a_825_, v_a_826_);
return v___x_827_;
}
else
{
lean_dec_ref(v_e_810_);
return v___y_824_;
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
v___x_832_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_810_, v_a_830_, v_a_831_);
return v___x_832_;
}
else
{
lean_dec_ref(v_e_810_);
return v___y_829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1094_, v_a_1095_, v_a_1096_);
lean_dec_ref(v_a_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1099_, v_x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1102_, v_x_1103_, v_x_1104_);
lean_dec_ref(v_x_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1106_, lean_object* v_m_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1107_, v_a_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1110_, lean_object* v_m_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1110_, v_m_1111_, v_a_1112_);
lean_dec_ref(v_a_1112_);
lean_dec_ref(v_m_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, size_t v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v___x_1118_; 
lean_inc_ref(v_x_1115_);
v___x_1118_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1115_, v_x_1116_, v_x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
size_t v_x_11735__boxed_1123_; lean_object* v_res_1124_; 
v_x_11735__boxed_1123_ = lean_unbox_usize(v_x_1121_);
lean_dec(v_x_1121_);
v_res_1124_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1119_, v_x_1120_, v_x_11735__boxed_1123_, v_x_1122_);
lean_dec_ref(v_x_1120_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1125_, lean_object* v_a_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1126_, v_x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1129_, lean_object* v_a_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1129_, v_a_1130_, v_x_1131_);
lean_dec(v_x_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1133_, lean_object* v_keys_1134_, lean_object* v_vals_1135_, lean_object* v_heq_1136_, lean_object* v_i_1137_, lean_object* v_k_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1134_, v_vals_1135_, v_i_1137_, v_k_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_heq_1143_, lean_object* v_i_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1140_, v_keys_1141_, v_vals_1142_, v_heq_1143_, v_i_1144_, v_k_1145_);
lean_dec_ref(v_vals_1142_);
lean_dec_ref(v_keys_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1147_, lean_object* v_cache_1148_, lean_object* v_ctx_1149_, lean_object* v_s_1150_){
_start:
{
lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; 
v___f_1151_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1152_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1147_);
v___x_1153_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1151_, v___f_1152_, v_s_1150_, v_e_1147_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_cache_1148_);
lean_ctor_set(v___x_1154_, 1, v_s_1150_);
v___x_1155_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1147_, v_ctx_1149_, v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 1);
v_a_1157_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v___x_1155_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1156_);
lean_inc(v_a_1157_);
lean_dec(v___x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_set_1161_; lean_object* v___x_1163_; 
v_set_1161_ = lean_ctor_get(v_a_1156_, 1);
lean_inc_ref(v_set_1161_);
lean_dec(v_a_1156_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_set_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1157_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_set_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1175_; 
v_a_1166_ = lean_ctor_get(v___x_1155_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v___x_1155_, 0);
lean_dec(v_unused_1176_);
v___x_1168_ = v___x_1155_;
v_isShared_1169_ = v_isSharedCheck_1175_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1155_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1175_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_map_1170_; lean_object* v_set_1171_; lean_object* v___x_1173_; 
v_map_1170_ = lean_ctor_get(v_a_1166_, 0);
lean_inc_ref(v_map_1170_);
v_set_1171_ = lean_ctor_get(v_a_1166_, 1);
lean_inc_ref(v_set_1171_);
lean_dec(v_a_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_set_1171_);
lean_ctor_set(v___x_1168_, 0, v_map_1170_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_map_1170_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_set_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_val_1177_; lean_object* v_fst_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_cache_1148_);
lean_dec_ref(v_e_1147_);
v_val_1177_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_val_1177_);
lean_dec_ref_known(v___x_1153_, 1);
v_fst_1178_ = lean_ctor_get(v_val_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_val_1177_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v_val_1177_, 1);
lean_dec(v_unused_1186_);
v___x_1180_ = v_val_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_fst_1178_);
lean_dec(v_val_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_s_1150_);
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_fst_1178_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_s_1150_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1187_, lean_object* v_cache_1188_, lean_object* v_ctx_1189_, lean_object* v_s_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1187_, v_cache_1188_, v_ctx_1189_, v_s_1190_);
lean_dec_ref(v_ctx_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1194_; uint64_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1194_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1195_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1192_);
v___x_1196_ = lean_uint64_to_usize(v___x_1195_);
lean_inc_ref(v_e_1192_);
lean_inc_ref(v_a_1193_);
v___x_1197_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1193_, v___x_1196_, v_e_1192_, v___x_1194_);
v___x_1198_ = lean_ptr_addr(v___x_1197_);
v___x_1199_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1200_ = lean_usize_dec_eq(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec_ref(v_e_1192_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1197_);
lean_ctor_set(v___x_1201_, 1, v_a_1193_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v___x_1197_);
v___x_1202_ = lean_box(0);
lean_inc_ref(v_e_1192_);
v___x_1203_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1193_, v_e_1192_, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_e_1192_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1205_, v_a_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1209_, v_a_1210_, v_a_1211_);
lean_dec_ref(v_a_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1213_, lean_object* v_k_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___f_1217_; lean_object* v___x_1218_; uint64_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; uint8_t v___x_1224_; 
v___f_1217_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1218_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1219_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1213_);
v___x_1220_ = lean_uint64_to_usize(v___x_1219_);
lean_inc_ref(v_a_1216_);
v___x_1221_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1217_, v_a_1216_, v___x_1220_, v_e_1213_, v___x_1218_);
v___x_1222_ = lean_ptr_addr(v___x_1221_);
v___x_1223_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1224_ = lean_usize_dec_eq(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v_k_1214_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1221_);
lean_ctor_set(v___x_1225_, 1, v_a_1216_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; 
lean_dec(v___x_1221_);
lean_inc_ref(v_a_1215_);
v___x_1226_ = lean_apply_2(v_k_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v_a_1228_; lean_object* v___x_1229_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
v_a_1228_ = lean_ctor_get(v___x_1226_, 1);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1226_, 2);
v___x_1229_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1227_, v_a_1228_);
return v___x_1229_;
}
else
{
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1230_, lean_object* v_k_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1230_, v_k_1231_, v_a_1232_, v_a_1233_);
lean_dec_ref(v_a_1232_);
return v_res_1234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_unsigned_to_nat(16u);
v___x_1237_ = lean_mk_array(v___x_1236_, v___x_1235_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___y_1245_; lean_object* v___y_1250_; lean_object* v___y_1255_; lean_object* v___y_1260_; 
switch(lean_obj_tag(v_e_1241_))
{
case 4:
{
lean_object* v_declName_1264_; lean_object* v___x_1265_; uint64_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; uint8_t v___x_1271_; 
v_declName_1264_ = lean_ctor_get(v_e_1241_, 0);
v___x_1265_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1266_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1241_);
v___x_1267_ = lean_uint64_to_usize(v___x_1266_);
lean_inc_ref(v_e_1241_);
lean_inc_ref(v_a_1243_);
v___x_1268_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1243_, v___x_1267_, v_e_1241_, v___x_1265_);
v___x_1269_ = lean_ptr_addr(v___x_1268_);
v___x_1270_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1271_ = lean_usize_dec_eq(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_dec_ref_known(v_e_1241_, 2);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1268_);
lean_ctor_set(v___x_1272_, 1, v_a_1243_);
return v___x_1272_;
}
else
{
uint8_t v___x_1273_; 
lean_dec_ref(v___x_1268_);
lean_inc(v_declName_1264_);
lean_inc_ref(v_a_1242_);
v___x_1273_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1242_, v_declName_1264_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(0);
lean_inc_ref(v_e_1241_);
v___x_1275_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1243_, v_e_1241_, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_e_1241_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref_known(v_e_1241_, 2);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v_a_1243_);
return v___x_1278_;
}
}
}
case 5:
{
lean_object* v_fn_1279_; lean_object* v_arg_1280_; lean_object* v___x_1281_; uint64_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; uint8_t v___x_1287_; 
v_fn_1279_ = lean_ctor_get(v_e_1241_, 0);
v_arg_1280_ = lean_ctor_get(v_e_1241_, 1);
v___x_1281_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1282_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1241_);
v___x_1283_ = lean_uint64_to_usize(v___x_1282_);
lean_inc_ref(v_e_1241_);
lean_inc_ref(v_a_1243_);
v___x_1284_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1243_, v___x_1283_, v_e_1241_, v___x_1281_);
v___x_1285_ = lean_ptr_addr(v___x_1284_);
v___x_1286_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1287_ = lean_usize_dec_eq(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
lean_dec_ref_known(v_e_1241_, 2);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1284_);
lean_ctor_set(v___x_1288_, 1, v_a_1243_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; 
lean_dec_ref(v___x_1284_);
lean_inc_ref(v_fn_1279_);
v___x_1289_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1279_, v_a_1242_, v_a_1243_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v_a_1291_; lean_object* v___x_1292_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
v_a_1291_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1289_, 2);
lean_inc_ref(v_arg_1280_);
v___x_1292_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1280_, v_a_1242_, v_a_1291_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v_a_1294_; uint8_t v___y_1296_; size_t v___x_1300_; size_t v___x_1301_; uint8_t v___x_1302_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
v_a_1294_ = lean_ctor_get(v___x_1292_, 1);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1292_, 2);
v___x_1300_ = lean_ptr_addr(v_fn_1279_);
v___x_1301_ = lean_ptr_addr(v_a_1290_);
v___x_1302_ = lean_usize_dec_eq(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
v___y_1296_ = v___x_1302_;
goto v___jp_1295_;
}
else
{
size_t v___x_1303_; size_t v___x_1304_; uint8_t v___x_1305_; 
v___x_1303_ = lean_ptr_addr(v_arg_1280_);
v___x_1304_ = lean_ptr_addr(v_a_1293_);
v___x_1305_ = lean_usize_dec_eq(v___x_1303_, v___x_1304_);
v___y_1296_ = v___x_1305_;
goto v___jp_1295_;
}
v___jp_1295_:
{
if (v___y_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec_ref_known(v_e_1241_, 2);
v___x_1297_ = l_Lean_Expr_app___override(v_a_1290_, v_a_1293_);
v___x_1298_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1297_, v_a_1294_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; 
lean_dec(v_a_1293_);
lean_dec(v_a_1290_);
v___x_1299_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1241_, v_a_1294_);
return v___x_1299_;
}
}
}
else
{
lean_dec(v_a_1290_);
lean_dec_ref_known(v_e_1241_, 2);
v___y_1255_ = v___x_1292_;
goto v___jp_1254_;
}
}
else
{
lean_dec_ref_known(v_e_1241_, 2);
v___y_1255_ = v___x_1289_;
goto v___jp_1254_;
}
}
}
case 6:
{
lean_object* v_binderName_1306_; lean_object* v_binderType_1307_; lean_object* v_body_1308_; uint8_t v_binderInfo_1309_; lean_object* v___x_1310_; uint64_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; uint8_t v___x_1316_; 
v_binderName_1306_ = lean_ctor_get(v_e_1241_, 0);
v_binderType_1307_ = lean_ctor_get(v_e_1241_, 1);
v_body_1308_ = lean_ctor_get(v_e_1241_, 2);
v_binderInfo_1309_ = lean_ctor_get_uint8(v_e_1241_, sizeof(void*)*3 + 8);
v___x_1310_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1311_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1241_);
v___x_1312_ = lean_uint64_to_usize(v___x_1311_);
lean_inc_ref(v_e_1241_);
lean_inc_ref(v_a_1243_);
v___x_1313_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1243_, v___x_1312_, v_e_1241_, v___x_1310_);
v___x_1314_ = lean_ptr_addr(v___x_1313_);
v___x_1315_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1316_ = lean_usize_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref_known(v_e_1241_, 3);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1313_);
lean_ctor_set(v___x_1317_, 1, v_a_1243_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
lean_dec_ref(v___x_1313_);
lean_inc_ref(v_binderType_1307_);
v___x_1318_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1307_, v_a_1242_, v_a_1243_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_a_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
v_a_1320_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1318_, 2);
lean_inc_ref(v_body_1308_);
v___x_1321_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1308_, v_a_1242_, v_a_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v_a_1323_; uint8_t v___y_1325_; size_t v___x_1332_; size_t v___x_1333_; uint8_t v___x_1334_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
v_a_1323_ = lean_ctor_get(v___x_1321_, 1);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1321_, 2);
v___x_1332_ = lean_ptr_addr(v_binderType_1307_);
v___x_1333_ = lean_ptr_addr(v_a_1319_);
v___x_1334_ = lean_usize_dec_eq(v___x_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
v___y_1325_ = v___x_1334_;
goto v___jp_1324_;
}
else
{
size_t v___x_1335_; size_t v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = lean_ptr_addr(v_body_1308_);
v___x_1336_ = lean_ptr_addr(v_a_1322_);
v___x_1337_ = lean_usize_dec_eq(v___x_1335_, v___x_1336_);
v___y_1325_ = v___x_1337_;
goto v___jp_1324_;
}
v___jp_1324_:
{
if (v___y_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_inc(v_binderName_1306_);
lean_dec_ref_known(v_e_1241_, 3);
v___x_1326_ = l_Lean_Expr_lam___override(v_binderName_1306_, v_a_1319_, v_a_1322_, v_binderInfo_1309_);
v___x_1327_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1326_, v_a_1323_);
return v___x_1327_;
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1309_, v_binderInfo_1309_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_inc(v_binderName_1306_);
lean_dec_ref_known(v_e_1241_, 3);
v___x_1329_ = l_Lean_Expr_lam___override(v_binderName_1306_, v_a_1319_, v_a_1322_, v_binderInfo_1309_);
v___x_1330_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1329_, v_a_1323_);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; 
lean_dec(v_a_1322_);
lean_dec(v_a_1319_);
v___x_1331_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1241_, v_a_1323_);
return v___x_1331_;
}
}
}
}
else
{
lean_dec(v_a_1319_);
lean_dec_ref_known(v_e_1241_, 3);
v___y_1250_ = v___x_1321_;
goto v___jp_1249_;
}
}
else
{
lean_dec_ref_known(v_e_1241_, 3);
v___y_1250_ = v___x_1318_;
goto v___jp_1249_;
}
}
}
case 7:
{
lean_object* v_binderName_1338_; lean_object* v_binderType_1339_; lean_object* v_body_1340_; uint8_t v_binderInfo_1341_; lean_object* v___x_1342_; uint64_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; uint8_t v___x_1348_; 
v_binderName_1338_ = lean_ctor_get(v_e_1241_, 0);
v_binderType_1339_ = lean_ctor_get(v_e_1241_, 1);
v_body_1340_ = lean_ctor_get(v_e_1241_, 2);
v_binderInfo_1341_ = lean_ctor_get_uint8(v_e_1241_, sizeof(void*)*3 + 8);
v___x_1342_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1343_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1241_);
v___x_1344_ = lean_uint64_to_usize(v___x_1343_);
lean_inc_ref(v_e_1241_);
lean_inc_ref(v_a_1243_);
v___x_1345_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1243_, v___x_1344_, v_e_1241_, v___x_1342_);
v___x_1346_ = lean_ptr_addr(v___x_1345_);
v___x_1347_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1348_ = lean_usize_dec_eq(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref_known(v_e_1241_, 3);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1345_);
lean_ctor_set(v___x_1349_, 1, v_a_1243_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; 
lean_dec_ref(v___x_1345_);
lean_inc_ref(v_binderType_1339_);
v___x_1350_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1339_, v_a_1242_, v_a_1243_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
v_a_1352_ = lean_ctor_get(v___x_1350_, 1);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1350_, 2);
lean_inc_ref(v_body_1340_);
v___x_1353_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1340_, v_a_1242_, v_a_1352_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v_a_1355_; uint8_t v___y_1357_; size_t v___x_1364_; size_t v___x_1365_; uint8_t v___x_1366_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
v_a_1355_ = lean_ctor_get(v___x_1353_, 1);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1353_, 2);
v___x_1364_ = lean_ptr_addr(v_binderType_1339_);
v___x_1365_ = lean_ptr_addr(v_a_1351_);
v___x_1366_ = lean_usize_dec_eq(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
v___y_1357_ = v___x_1366_;
goto v___jp_1356_;
}
else
{
size_t v___x_1367_; size_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_ptr_addr(v_body_1340_);
v___x_1368_ = lean_ptr_addr(v_a_1354_);
v___x_1369_ = lean_usize_dec_eq(v___x_1367_, v___x_1368_);
v___y_1357_ = v___x_1369_;
goto v___jp_1356_;
}
v___jp_1356_:
{
if (v___y_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_inc(v_binderName_1338_);
lean_dec_ref_known(v_e_1241_, 3);
v___x_1358_ = l_Lean_Expr_forallE___override(v_binderName_1338_, v_a_1351_, v_a_1354_, v_binderInfo_1341_);
v___x_1359_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1358_, v_a_1355_);
return v___x_1359_;
}
else
{
uint8_t v___x_1360_; 
v___x_1360_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1341_, v_binderInfo_1341_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_inc(v_binderName_1338_);
lean_dec_ref_known(v_e_1241_, 3);
v___x_1361_ = l_Lean_Expr_forallE___override(v_binderName_1338_, v_a_1351_, v_a_1354_, v_binderInfo_1341_);
v___x_1362_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1361_, v_a_1355_);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; 
lean_dec(v_a_1354_);
lean_dec(v_a_1351_);
v___x_1363_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1241_, v_a_1355_);
return v___x_1363_;
}
}
}
}
else
{
lean_dec(v_a_1351_);
lean_dec_ref_known(v_e_1241_, 3);
v___y_1260_ = v___x_1353_;
goto v___jp_1259_;
}
}
else
{
lean_dec_ref_known(v_e_1241_, 3);
v___y_1260_ = v___x_1350_;
goto v___jp_1259_;
}
}
}
case 8:
{
lean_object* v_declName_1370_; lean_object* v_type_1371_; lean_object* v_value_1372_; lean_object* v_body_1373_; uint8_t v_nondep_1374_; lean_object* v___x_1375_; uint64_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; uint8_t v___x_1381_; 
v_declName_1370_ = lean_ctor_get(v_e_1241_, 0);
v_type_1371_ = lean_ctor_get(v_e_1241_, 1);
v_value_1372_ = lean_ctor_get(v_e_1241_, 2);
v_body_1373_ = lean_ctor_get(v_e_1241_, 3);
v_nondep_1374_ = lean_ctor_get_uint8(v_e_1241_, sizeof(void*)*4 + 8);
v___x_1375_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1376_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1241_);
v___x_1377_ = lean_uint64_to_usize(v___x_1376_);
lean_inc_ref(v_e_1241_);
lean_inc_ref(v_a_1243_);
v___x_1378_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1243_, v___x_1377_, v_e_1241_, v___x_1375_);
v___x_1379_ = lean_ptr_addr(v___x_1378_);
v___x_1380_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1381_ = lean_usize_dec_eq(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref_known(v_e_1241_, 4);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1378_);
lean_ctor_set(v___x_1382_, 1, v_a_1243_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v___x_1378_);
lean_inc_ref(v_type_1371_);
v___x_1383_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1371_, v_a_1242_, v_a_1243_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
v_a_1385_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1383_, 2);
lean_inc_ref(v_value_1372_);
v___x_1386_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1372_, v_a_1242_, v_a_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v_a_1388_; lean_object* v___x_1389_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
v_a_1388_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1386_, 2);
lean_inc_ref(v_body_1373_);
v___x_1389_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1373_, v_a_1242_, v_a_1388_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v_a_1391_; uint8_t v___y_1393_; size_t v___x_1402_; size_t v___x_1403_; uint8_t v___x_1404_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
v_a_1391_ = lean_ctor_get(v___x_1389_, 1);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1389_, 2);
v___x_1402_ = lean_ptr_addr(v_type_1371_);
v___x_1403_ = lean_ptr_addr(v_a_1384_);
v___x_1404_ = lean_usize_dec_eq(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
v___y_1393_ = v___x_1404_;
goto v___jp_1392_;
}
else
{
size_t v___x_1405_; size_t v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = lean_ptr_addr(v_value_1372_);
v___x_1406_ = lean_ptr_addr(v_a_1387_);
v___x_1407_ = lean_usize_dec_eq(v___x_1405_, v___x_1406_);
v___y_1393_ = v___x_1407_;
goto v___jp_1392_;
}
v___jp_1392_:
{
if (v___y_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_inc(v_declName_1370_);
lean_dec_ref_known(v_e_1241_, 4);
v___x_1394_ = l_Lean_Expr_letE___override(v_declName_1370_, v_a_1384_, v_a_1387_, v_a_1390_, v_nondep_1374_);
v___x_1395_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1394_, v_a_1391_);
return v___x_1395_;
}
else
{
size_t v___x_1396_; size_t v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_ptr_addr(v_body_1373_);
v___x_1397_ = lean_ptr_addr(v_a_1390_);
v___x_1398_ = lean_usize_dec_eq(v___x_1396_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_inc(v_declName_1370_);
lean_dec_ref_known(v_e_1241_, 4);
v___x_1399_ = l_Lean_Expr_letE___override(v_declName_1370_, v_a_1384_, v_a_1387_, v_a_1390_, v_nondep_1374_);
v___x_1400_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1399_, v_a_1391_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; 
lean_dec(v_a_1390_);
lean_dec(v_a_1387_);
lean_dec(v_a_1384_);
v___x_1401_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1241_, v_a_1391_);
return v___x_1401_;
}
}
}
}
else
{
lean_dec(v_a_1387_);
lean_dec(v_a_1384_);
lean_dec_ref_known(v_e_1241_, 4);
v___y_1245_ = v___x_1389_;
goto v___jp_1244_;
}
}
else
{
lean_dec(v_a_1384_);
lean_dec_ref_known(v_e_1241_, 4);
v___y_1245_ = v___x_1386_;
goto v___jp_1244_;
}
}
else
{
lean_dec_ref_known(v_e_1241_, 4);
v___y_1245_ = v___x_1383_;
goto v___jp_1244_;
}
}
}
case 10:
{
lean_object* v_data_1408_; lean_object* v_expr_1409_; lean_object* v___x_1410_; uint64_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v_data_1408_ = lean_ctor_get(v_e_1241_, 0);
v_expr_1409_ = lean_ctor_get(v_e_1241_, 1);
v___x_1410_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1411_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1241_);
v___x_1412_ = lean_uint64_to_usize(v___x_1411_);
lean_inc_ref(v_e_1241_);
lean_inc_ref(v_a_1243_);
v___x_1413_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1243_, v___x_1412_, v_e_1241_, v___x_1410_);
v___x_1414_ = lean_ptr_addr(v___x_1413_);
v___x_1415_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1416_ = lean_usize_dec_eq(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref_known(v_e_1241_, 2);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1413_);
lean_ctor_set(v___x_1417_, 1, v_a_1243_);
return v___x_1417_;
}
else
{
lean_object* v___x_1418_; 
lean_dec_ref(v___x_1413_);
lean_inc_ref(v_expr_1409_);
v___x_1418_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1409_, v_a_1242_, v_a_1243_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v_a_1420_; size_t v___x_1421_; size_t v___x_1422_; uint8_t v___x_1423_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
v_a_1420_ = lean_ctor_get(v___x_1418_, 1);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1418_, 2);
v___x_1421_ = lean_ptr_addr(v_expr_1409_);
v___x_1422_ = lean_ptr_addr(v_a_1419_);
v___x_1423_ = lean_usize_dec_eq(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_inc(v_data_1408_);
lean_dec_ref_known(v_e_1241_, 2);
v___x_1424_ = l_Lean_Expr_mdata___override(v_data_1408_, v_a_1419_);
v___x_1425_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1424_, v_a_1420_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_a_1419_);
v___x_1426_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1241_, v_a_1420_);
return v___x_1426_;
}
}
else
{
lean_dec_ref_known(v_e_1241_, 2);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1427_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1427_);
v_a_1428_ = lean_ctor_get(v___x_1418_, 1);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1418_, 2);
v___x_1429_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1427_, v_a_1428_);
return v___x_1429_;
}
else
{
return v___x_1418_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1430_; lean_object* v_idx_1431_; lean_object* v_struct_1432_; lean_object* v___x_1433_; uint64_t v___x_1434_; size_t v___x_1435_; lean_object* v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; uint8_t v___x_1439_; 
v_typeName_1430_ = lean_ctor_get(v_e_1241_, 0);
v_idx_1431_ = lean_ctor_get(v_e_1241_, 1);
v_struct_1432_ = lean_ctor_get(v_e_1241_, 2);
v___x_1433_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1434_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1241_);
v___x_1435_ = lean_uint64_to_usize(v___x_1434_);
lean_inc_ref(v_e_1241_);
lean_inc_ref(v_a_1243_);
v___x_1436_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1243_, v___x_1435_, v_e_1241_, v___x_1433_);
v___x_1437_ = lean_ptr_addr(v___x_1436_);
v___x_1438_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1439_ = lean_usize_dec_eq(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec_ref_known(v_e_1241_, 3);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1436_);
lean_ctor_set(v___x_1440_, 1, v_a_1243_);
return v___x_1440_;
}
else
{
uint8_t v_checkProj_1441_; 
lean_dec_ref(v___x_1436_);
v_checkProj_1441_ = lean_ctor_get_uint8(v_a_1242_, sizeof(void*)*1 + 1);
if (v_checkProj_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_inc_ref(v_struct_1432_);
v___x_1442_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1432_, v_a_1242_, v_a_1243_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v_a_1444_; size_t v___x_1445_; size_t v___x_1446_; uint8_t v___x_1447_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
v_a_1444_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1442_, 2);
v___x_1445_ = lean_ptr_addr(v_struct_1432_);
v___x_1446_ = lean_ptr_addr(v_a_1443_);
v___x_1447_ = lean_usize_dec_eq(v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_inc(v_idx_1431_);
lean_inc(v_typeName_1430_);
lean_dec_ref_known(v_e_1241_, 3);
v___x_1448_ = l_Lean_Expr_proj___override(v_typeName_1430_, v_idx_1431_, v_a_1443_);
v___x_1449_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1448_, v_a_1444_);
return v___x_1449_;
}
else
{
lean_object* v___x_1450_; 
lean_dec(v_a_1443_);
v___x_1450_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1241_, v_a_1444_);
return v___x_1450_;
}
}
else
{
lean_dec_ref_known(v_e_1241_, 3);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1451_; lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1451_);
v_a_1452_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1442_, 2);
v___x_1453_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1451_, v_a_1452_);
return v___x_1453_;
}
else
{
return v___x_1442_;
}
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref_known(v_e_1241_, 3);
v___x_1454_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v_a_1243_);
return v___x_1455_;
}
}
}
default: 
{
lean_object* v___x_1456_; 
v___x_1456_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1241_, v_a_1243_);
return v___x_1456_;
}
}
v___jp_1244_:
{
if (lean_obj_tag(v___y_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___y_1245_, 0);
lean_inc(v_a_1246_);
v_a_1247_ = lean_ctor_get(v___y_1245_, 1);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___y_1245_, 2);
v___x_1248_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1246_, v_a_1247_);
return v___x_1248_;
}
else
{
return v___y_1245_;
}
}
v___jp_1249_:
{
if (lean_obj_tag(v___y_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_a_1252_; lean_object* v___x_1253_; 
v_a_1251_ = lean_ctor_get(v___y_1250_, 0);
lean_inc(v_a_1251_);
v_a_1252_ = lean_ctor_get(v___y_1250_, 1);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___y_1250_, 2);
v___x_1253_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1251_, v_a_1252_);
return v___x_1253_;
}
else
{
return v___y_1250_;
}
}
v___jp_1254_:
{
if (lean_obj_tag(v___y_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_a_1257_; lean_object* v___x_1258_; 
v_a_1256_ = lean_ctor_get(v___y_1255_, 0);
lean_inc(v_a_1256_);
v_a_1257_ = lean_ctor_get(v___y_1255_, 1);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___y_1255_, 2);
v___x_1258_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1256_, v_a_1257_);
return v___x_1258_;
}
else
{
return v___y_1255_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1457_, v_a_1458_, v_a_1459_);
lean_dec_ref(v_a_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1461_, v_a_1462_, v_a_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1465_, v_a_1466_, v_a_1467_);
lean_dec_ref(v_a_1466_);
return v_res_1468_;
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

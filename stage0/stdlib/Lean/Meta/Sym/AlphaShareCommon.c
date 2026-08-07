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
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_155_ = lean_name_eq(v_declName_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_Meta_Sym_isGrindGadget___closed__5));
v___x_157_ = lean_name_eq(v_declName_153_, v___x_156_);
return v___x_157_;
}
else
{
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_158_);
lean_dec(v_declName_158_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isUnfoldReducibleCandidate(lean_object* v_env_161_, lean_object* v_declName_162_){
_start:
{
uint8_t v___x_163_; 
lean_inc(v_declName_162_);
lean_inc_ref(v_env_161_);
v___x_163_ = l_Lean_getReducibilityStatusCore(v_env_161_, v_declName_162_);
if (v___x_163_ == 0)
{
uint8_t v___x_164_; 
v___x_164_ = l_Lean_Meta_Sym_isGrindGadget(v_declName_162_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; 
v___x_165_ = l_Lean_Environment_isProjectionFn(v_env_161_, v_declName_162_);
if (v___x_165_ == 0)
{
uint8_t v___x_166_; 
v___x_166_ = 1;
return v___x_166_;
}
else
{
return v___x_164_;
}
}
else
{
uint8_t v___x_167_; 
lean_dec(v_declName_162_);
lean_dec_ref(v_env_161_);
v___x_167_ = 0;
return v___x_167_;
}
}
else
{
uint8_t v___x_168_; 
lean_dec(v_declName_162_);
lean_dec_ref(v_env_161_);
v___x_168_ = 0;
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isUnfoldReducibleCandidate___boxed(lean_object* v_env_169_, lean_object* v_declName_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_169_, v_declName_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Sym_instHashableAlphaKey___private__1(lean_object* v_k_173_){
_start:
{
uint64_t v___x_174_; 
v___x_174_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instHashableAlphaKey___private__1___boxed(lean_object* v_k_175_){
_start:
{
uint64_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Lean_Meta_Sym_instHashableAlphaKey___private__1(v_k_175_);
lean_dec_ref(v_k_175_);
v_r_177_ = lean_box_uint64(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_instBEqAlphaKey___private__1(lean_object* v_k_u2081_180_, lean_object* v_k_u2082_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_u2081_180_, v_k_u2082_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instBEqAlphaKey___private__1___boxed(lean_object* v_k_u2081_183_, lean_object* v_k_u2082_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Meta_Sym_instBEqAlphaKey___private__1(v_k_u2081_183_, v_k_u2082_184_);
lean_dec_ref(v_k_u2082_184_);
lean_dec_ref(v_k_u2081_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(lean_object* v_ctx_189_, lean_object* v_declName_190_){
_start:
{
uint8_t v_checkReducible_191_; 
v_checkReducible_191_ = lean_ctor_get_uint8(v_ctx_189_, sizeof(void*)*1);
if (v_checkReducible_191_ == 0)
{
lean_dec(v_declName_190_);
lean_dec_ref(v_ctx_189_);
return v_checkReducible_191_;
}
else
{
lean_object* v_env_192_; uint8_t v___x_193_; 
v_env_192_ = lean_ctor_get(v_ctx_189_, 0);
lean_inc_ref(v_env_192_);
lean_dec_ref(v_ctx_189_);
v___x_193_ = l_Lean_Meta_Sym_isUnfoldReducibleCandidate(v_env_192_, v_declName_190_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible___boxed(lean_object* v_ctx_194_, lean_object* v_declName_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_ctx_194_, v_declName_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_box(0);
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__1));
v___x_203_ = l_Lean_mkConst(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy___closed__2);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_keys_205_, lean_object* v_i_206_, lean_object* v_k_207_, lean_object* v_k_u2080_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_array_get_size(v_keys_205_);
v___x_210_ = lean_nat_dec_lt(v_i_206_, v___x_209_);
if (v___x_210_ == 0)
{
lean_dec(v_i_206_);
lean_inc_ref(v_k_u2080_208_);
return v_k_u2080_208_;
}
else
{
lean_object* v_k_x27_211_; uint8_t v___x_212_; 
v_k_x27_211_ = lean_array_fget_borrowed(v_keys_205_, v_i_206_);
v___x_212_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_207_, v_k_x27_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_i_206_, v___x_213_);
lean_dec(v_i_206_);
v_i_206_ = v___x_214_;
goto _start;
}
else
{
lean_dec(v_i_206_);
lean_inc(v_k_x27_211_);
return v_k_x27_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_keys_216_, lean_object* v_i_217_, lean_object* v_k_218_, lean_object* v_k_u2080_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_216_, v_i_217_, v_k_218_, v_k_u2080_219_);
lean_dec_ref(v_k_u2080_219_);
lean_dec_ref(v_k_218_);
lean_dec_ref(v_keys_216_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_x_221_, size_t v_x_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_object* v_es_225_; lean_object* v___x_226_; size_t v___x_227_; size_t v___x_228_; lean_object* v_j_229_; lean_object* v___x_230_; 
v_es_225_ = lean_ctor_get(v_x_221_, 0);
v___x_226_ = lean_box(2);
v___x_227_ = ((size_t)31ULL);
v___x_228_ = lean_usize_land(v_x_222_, v___x_227_);
v_j_229_ = lean_usize_to_nat(v___x_228_);
v___x_230_ = lean_array_get_borrowed(v___x_226_, v_es_225_, v_j_229_);
lean_dec(v_j_229_);
switch(lean_obj_tag(v___x_230_))
{
case 0:
{
lean_object* v_key_231_; uint8_t v___x_232_; 
v_key_231_ = lean_ctor_get(v___x_230_, 0);
v___x_232_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_223_, v_key_231_);
if (v___x_232_ == 0)
{
lean_inc_ref(v_x_224_);
return v_x_224_;
}
else
{
lean_inc(v_key_231_);
return v_key_231_;
}
}
case 1:
{
lean_object* v_node_233_; size_t v___x_234_; size_t v___x_235_; 
v_node_233_ = lean_ctor_get(v___x_230_, 0);
v___x_234_ = ((size_t)5ULL);
v___x_235_ = lean_usize_shift_right(v_x_222_, v___x_234_);
v_x_221_ = v_node_233_;
v_x_222_ = v___x_235_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_224_);
return v_x_224_;
}
}
}
else
{
lean_object* v_ks_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_ks_237_ = lean_ctor_get(v_x_221_, 0);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_ks_237_, v___x_238_, v_x_223_, v_x_224_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg___boxed(lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
size_t v_x_2094__boxed_244_; lean_object* v_res_245_; 
v_x_2094__boxed_244_ = lean_unbox_usize(v_x_241_);
lean_dec(v_x_241_);
v_res_245_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_240_, v_x_2094__boxed_244_, v_x_242_, v_x_243_);
lean_dec_ref(v_x_243_);
lean_dec_ref(v_x_242_);
lean_dec_ref(v_x_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
lean_object* v_ks_250_; lean_object* v_vs_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_275_; 
v_ks_250_ = lean_ctor_get(v_x_246_, 0);
v_vs_251_ = lean_ctor_get(v_x_246_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_275_ == 0)
{
v___x_253_ = v_x_246_;
v_isShared_254_ = v_isSharedCheck_275_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_vs_251_);
lean_inc(v_ks_250_);
lean_dec(v_x_246_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_275_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_get_size(v_ks_250_);
v___x_256_ = lean_nat_dec_lt(v_x_247_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec(v_x_247_);
v___x_257_ = lean_array_push(v_ks_250_, v_x_248_);
v___x_258_ = lean_array_push(v_vs_251_, v_x_249_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v___x_258_);
lean_ctor_set(v___x_253_, 0, v___x_257_);
v___x_260_ = v___x_253_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
else
{
lean_object* v_k_x27_262_; uint8_t v___x_263_; 
v_k_x27_262_ = lean_array_fget_borrowed(v_ks_250_, v_x_247_);
v___x_263_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_248_, v_k_x27_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_265_; 
if (v_isShared_254_ == 0)
{
v___x_265_ = v___x_253_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_ks_250_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_vs_251_);
v___x_265_ = v_reuseFailAlloc_269_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_add(v_x_247_, v___x_266_);
lean_dec(v_x_247_);
v_x_246_ = v___x_265_;
v_x_247_ = v___x_267_;
goto _start;
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = lean_array_fset(v_ks_250_, v_x_247_, v_x_248_);
v___x_271_ = lean_array_fset(v_vs_251_, v_x_247_, v_x_249_);
lean_dec(v_x_247_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v___x_271_);
lean_ctor_set(v___x_253_, 0, v___x_270_);
v___x_273_ = v___x_253_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(lean_object* v_n_276_, lean_object* v_k_277_, lean_object* v_v_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_n_276_, v___x_279_, v_k_277_, v_v_278_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(lean_object* v_x_282_, size_t v_x_283_, size_t v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
lean_object* v_es_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v_j_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_es_287_ = lean_ctor_get(v_x_282_, 0);
v___x_288_ = ((size_t)31ULL);
v___x_289_ = lean_usize_land(v_x_283_, v___x_288_);
v_j_290_ = lean_usize_to_nat(v___x_289_);
v___x_291_ = lean_array_get_size(v_es_287_);
v___x_292_ = lean_nat_dec_lt(v_j_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_dec(v_j_290_);
lean_dec(v_x_286_);
lean_dec_ref(v_x_285_);
return v_x_282_;
}
else
{
lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_331_; 
lean_inc_ref(v_es_287_);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_x_282_, 0);
lean_dec(v_unused_332_);
v___x_294_ = v_x_282_;
v_isShared_295_ = v_isSharedCheck_331_;
goto v_resetjp_293_;
}
else
{
lean_dec(v_x_282_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_331_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v_v_296_; lean_object* v___x_297_; lean_object* v_xs_x27_298_; lean_object* v___y_300_; 
v_v_296_ = lean_array_fget(v_es_287_, v_j_290_);
v___x_297_ = lean_box(0);
v_xs_x27_298_ = lean_array_fset(v_es_287_, v_j_290_, v___x_297_);
switch(lean_obj_tag(v_v_296_))
{
case 0:
{
lean_object* v_key_305_; lean_object* v_val_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_316_; 
v_key_305_ = lean_ctor_get(v_v_296_, 0);
v_val_306_ = lean_ctor_get(v_v_296_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_v_296_);
if (v_isSharedCheck_316_ == 0)
{
v___x_308_ = v_v_296_;
v_isShared_309_ = v_isSharedCheck_316_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_val_306_);
lean_inc(v_key_305_);
lean_dec(v_v_296_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_316_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
uint8_t v___x_310_; 
v___x_310_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_285_, v_key_305_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_del_object(v___x_308_);
v___x_311_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_305_, v_val_306_, v_x_285_, v_x_286_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
v___y_300_ = v___x_312_;
goto v___jp_299_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v_val_306_);
lean_dec(v_key_305_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_x_286_);
lean_ctor_set(v___x_308_, 0, v_x_285_);
v___x_314_ = v___x_308_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_x_285_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_x_286_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
v___y_300_ = v___x_314_;
goto v___jp_299_;
}
}
}
}
case 1:
{
lean_object* v_node_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_329_; 
v_node_317_ = lean_ctor_get(v_v_296_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_v_296_);
if (v_isSharedCheck_329_ == 0)
{
v___x_319_ = v_v_296_;
v_isShared_320_ = v_isSharedCheck_329_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_node_317_);
lean_dec(v_v_296_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_329_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_321_ = ((size_t)5ULL);
v___x_322_ = lean_usize_shift_right(v_x_283_, v___x_321_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_x_284_, v___x_323_);
v___x_325_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_node_317_, v___x_322_, v___x_324_, v_x_285_, v_x_286_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_325_);
v___x_327_ = v___x_319_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v___y_300_ = v___x_327_;
goto v___jp_299_;
}
}
}
default: 
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_x_285_);
lean_ctor_set(v___x_330_, 1, v_x_286_);
v___y_300_ = v___x_330_;
goto v___jp_299_;
}
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_array_fset(v_xs_x27_298_, v_j_290_, v___y_300_);
lean_dec(v_j_290_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_301_);
v___x_303_ = v___x_294_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
lean_object* v_ks_333_; lean_object* v_vs_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_354_; 
v_ks_333_ = lean_ctor_get(v_x_282_, 0);
v_vs_334_ = lean_ctor_get(v_x_282_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_354_ == 0)
{
v___x_336_ = v_x_282_;
v_isShared_337_ = v_isSharedCheck_354_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_vs_334_);
lean_inc(v_ks_333_);
lean_dec(v_x_282_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_354_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_ks_333_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_vs_334_);
v___x_339_ = v_reuseFailAlloc_353_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v_newNode_340_; uint8_t v___y_342_; size_t v___x_348_; uint8_t v___x_349_; 
v_newNode_340_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v___x_339_, v_x_285_, v_x_286_);
v___x_348_ = ((size_t)7ULL);
v___x_349_ = lean_usize_dec_le(v___x_348_, v_x_284_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_350_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_340_);
v___x_351_ = lean_unsigned_to_nat(4u);
v___x_352_ = lean_nat_dec_lt(v___x_350_, v___x_351_);
lean_dec(v___x_350_);
v___y_342_ = v___x_352_;
goto v___jp_341_;
}
else
{
v___y_342_ = v___x_349_;
goto v___jp_341_;
}
v___jp_341_:
{
if (v___y_342_ == 0)
{
lean_object* v_ks_343_; lean_object* v_vs_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_ks_343_ = lean_ctor_get(v_newNode_340_, 0);
lean_inc_ref(v_ks_343_);
v_vs_344_ = lean_ctor_get(v_newNode_340_, 1);
lean_inc_ref(v_vs_344_);
lean_dec_ref(v_newNode_340_);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___closed__0);
v___x_347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_x_284_, v_ks_343_, v_vs_344_, v___x_345_, v___x_346_);
lean_dec_ref(v_vs_344_);
lean_dec_ref(v_ks_343_);
return v___x_347_;
}
else
{
return v_newNode_340_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(size_t v_depth_355_, lean_object* v_keys_356_, lean_object* v_vals_357_, lean_object* v_i_358_, lean_object* v_entries_359_){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_array_get_size(v_keys_356_);
v___x_361_ = lean_nat_dec_lt(v_i_358_, v___x_360_);
if (v___x_361_ == 0)
{
lean_dec(v_i_358_);
return v_entries_359_;
}
else
{
lean_object* v_k_362_; lean_object* v_v_363_; uint64_t v___x_364_; size_t v_h_365_; size_t v___x_366_; lean_object* v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v_h_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_k_362_ = lean_array_fget_borrowed(v_keys_356_, v_i_358_);
v_v_363_ = lean_array_fget_borrowed(v_vals_357_, v_i_358_);
v___x_364_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_362_);
v_h_365_ = lean_uint64_to_usize(v___x_364_);
v___x_366_ = ((size_t)5ULL);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_sub(v_depth_355_, v___x_368_);
v___x_370_ = lean_usize_mul(v___x_366_, v___x_369_);
v_h_371_ = lean_usize_shift_right(v_h_365_, v___x_370_);
v___x_372_ = lean_nat_add(v_i_358_, v___x_367_);
lean_dec(v_i_358_);
lean_inc(v_v_363_);
lean_inc(v_k_362_);
v___x_373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_entries_359_, v_h_371_, v_depth_355_, v_k_362_, v_v_363_);
v_i_358_ = v___x_372_;
v_entries_359_ = v___x_373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_depth_375_, lean_object* v_keys_376_, lean_object* v_vals_377_, lean_object* v_i_378_, lean_object* v_entries_379_){
_start:
{
size_t v_depth_boxed_380_; lean_object* v_res_381_; 
v_depth_boxed_380_ = lean_unbox_usize(v_depth_375_);
lean_dec(v_depth_375_);
v_res_381_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_boxed_380_, v_keys_376_, v_vals_377_, v_i_378_, v_entries_379_);
lean_dec_ref(v_vals_377_);
lean_dec_ref(v_keys_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg___boxed(lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
size_t v_x_2212__boxed_387_; size_t v_x_2213__boxed_388_; lean_object* v_res_389_; 
v_x_2212__boxed_387_ = lean_unbox_usize(v_x_383_);
lean_dec(v_x_383_);
v_x_2213__boxed_388_ = lean_unbox_usize(v_x_384_);
lean_dec(v_x_384_);
v_res_389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_382_, v_x_2212__boxed_387_, v_x_2213__boxed_388_, v_x_385_, v_x_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
uint64_t v___x_393_; size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_393_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_391_);
v___x_394_ = lean_uint64_to_usize(v___x_393_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_390_, v___x_394_, v___x_395_, v_x_391_, v_x_392_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(lean_object* v_a_397_, lean_object* v_b_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_dec(v_b_398_);
lean_dec_ref(v_a_397_);
return v_x_399_;
}
else
{
lean_object* v_key_400_; lean_object* v_value_401_; lean_object* v_tail_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_416_; 
v_key_400_ = lean_ctor_get(v_x_399_, 0);
v_value_401_ = lean_ctor_get(v_x_399_, 1);
v_tail_402_ = lean_ctor_get(v_x_399_, 2);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_399_);
if (v_isSharedCheck_416_ == 0)
{
v___x_404_ = v_x_399_;
v_isShared_405_ = v_isSharedCheck_416_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_tail_402_);
lean_inc(v_value_401_);
lean_inc(v_key_400_);
lean_dec(v_x_399_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_416_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
size_t v___x_406_; size_t v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_ptr_addr(v_key_400_);
v___x_407_ = lean_ptr_addr(v_a_397_);
v___x_408_ = lean_usize_dec_eq(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_397_, v_b_398_, v_tail_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 2, v___x_409_);
v___x_411_ = v___x_404_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_key_400_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_value_401_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
else
{
lean_object* v___x_414_; 
lean_dec(v_value_401_);
lean_dec(v_key_400_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_b_398_);
lean_ctor_set(v___x_404_, 0, v_a_397_);
v___x_414_ = v___x_404_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_397_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_b_398_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_tail_402_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
return v_x_417_;
}
else
{
lean_object* v_key_419_; lean_object* v_value_420_; lean_object* v_tail_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_447_; 
v_key_419_ = lean_ctor_get(v_x_418_, 0);
v_value_420_ = lean_ctor_get(v_x_418_, 1);
v_tail_421_ = lean_ctor_get(v_x_418_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_447_ == 0)
{
v___x_423_ = v_x_418_;
v_isShared_424_ = v_isSharedCheck_447_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_tail_421_);
lean_inc(v_value_420_);
lean_inc(v_key_419_);
lean_dec(v_x_418_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_447_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v_fold_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_425_ = lean_array_get_size(v_x_417_);
v___x_426_ = lean_ptr_addr(v_key_419_);
v___x_427_ = ((size_t)3ULL);
v___x_428_ = lean_usize_shift_right(v___x_426_, v___x_427_);
v___x_429_ = lean_usize_to_uint64(v___x_428_);
v___x_430_ = 32ULL;
v___x_431_ = lean_uint64_shift_right(v___x_429_, v___x_430_);
v_fold_432_ = lean_uint64_xor(v___x_429_, v___x_431_);
v___x_433_ = 16ULL;
v___x_434_ = lean_uint64_shift_right(v_fold_432_, v___x_433_);
v___x_435_ = lean_uint64_xor(v_fold_432_, v___x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = lean_usize_of_nat(v___x_425_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_sub(v___x_437_, v___x_438_);
v___x_440_ = lean_usize_land(v___x_436_, v___x_439_);
v___x_441_ = lean_array_uget_borrowed(v_x_417_, v___x_440_);
lean_inc(v___x_441_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 2, v___x_441_);
v___x_443_ = v___x_423_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_key_419_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_value_420_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v___x_441_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = lean_array_uset(v_x_417_, v___x_440_, v___x_443_);
v_x_417_ = v___x_444_;
v_x_418_ = v_tail_421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(lean_object* v_i_448_, lean_object* v_source_449_, lean_object* v_target_450_){
_start:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_array_get_size(v_source_449_);
v___x_452_ = lean_nat_dec_lt(v_i_448_, v___x_451_);
if (v___x_452_ == 0)
{
lean_dec_ref(v_source_449_);
lean_dec(v_i_448_);
return v_target_450_;
}
else
{
lean_object* v_es_453_; lean_object* v___x_454_; lean_object* v_source_455_; lean_object* v_target_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_es_453_ = lean_array_fget(v_source_449_, v_i_448_);
v___x_454_ = lean_box(0);
v_source_455_ = lean_array_fset(v_source_449_, v_i_448_, v___x_454_);
v_target_456_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_target_450_, v_es_453_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_i_448_, v___x_457_);
lean_dec(v_i_448_);
v_i_448_ = v___x_458_;
v_source_449_ = v_source_455_;
v_target_450_ = v_target_456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(lean_object* v_data_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_nbuckets_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_461_ = lean_array_get_size(v_data_460_);
v___x_462_ = lean_unsigned_to_nat(2u);
v_nbuckets_463_ = lean_nat_mul(v___x_461_, v___x_462_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_box(0);
v___x_466_ = lean_mk_array(v_nbuckets_463_, v___x_465_);
v___x_467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v___x_464_, v_data_460_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
else
{
lean_object* v_key_471_; lean_object* v_tail_472_; size_t v___x_473_; size_t v___x_474_; uint8_t v___x_475_; 
v_key_471_ = lean_ctor_get(v_x_469_, 0);
v_tail_472_ = lean_ctor_get(v_x_469_, 2);
v___x_473_ = lean_ptr_addr(v_key_471_);
v___x_474_ = lean_ptr_addr(v_a_468_);
v___x_475_ = lean_usize_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
v_x_469_ = v_tail_472_;
goto _start;
}
else
{
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg___boxed(lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_477_, v_x_478_);
lean_dec(v_x_478_);
lean_dec_ref(v_a_477_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(lean_object* v_m_481_, lean_object* v_a_482_, lean_object* v_b_483_){
_start:
{
lean_object* v_size_484_; lean_object* v_buckets_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_531_; 
v_size_484_ = lean_ctor_get(v_m_481_, 0);
v_buckets_485_ = lean_ctor_get(v_m_481_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_m_481_);
if (v_isSharedCheck_531_ == 0)
{
v___x_487_ = v_m_481_;
v_isShared_488_ = v_isSharedCheck_531_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_buckets_485_);
lean_inc(v_size_484_);
lean_dec(v_m_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_531_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v_bkt_505_; uint8_t v___x_506_; 
v___x_489_ = lean_array_get_size(v_buckets_485_);
v___x_490_ = lean_ptr_addr(v_a_482_);
v___x_491_ = ((size_t)3ULL);
v___x_492_ = lean_usize_shift_right(v___x_490_, v___x_491_);
v___x_493_ = lean_usize_to_uint64(v___x_492_);
v___x_494_ = 32ULL;
v___x_495_ = lean_uint64_shift_right(v___x_493_, v___x_494_);
v_fold_496_ = lean_uint64_xor(v___x_493_, v___x_495_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_489_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v_bkt_505_ = lean_array_uget_borrowed(v_buckets_485_, v___x_504_);
v___x_506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_482_, v_bkt_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v_size_x27_508_; lean_object* v___x_509_; lean_object* v_buckets_x27_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v_size_x27_508_ = lean_nat_add(v_size_484_, v___x_507_);
lean_dec(v_size_484_);
lean_inc(v_bkt_505_);
v___x_509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_509_, 0, v_a_482_);
lean_ctor_set(v___x_509_, 1, v_b_483_);
lean_ctor_set(v___x_509_, 2, v_bkt_505_);
v_buckets_x27_510_ = lean_array_uset(v_buckets_485_, v___x_504_, v___x_509_);
v___x_511_ = lean_unsigned_to_nat(4u);
v___x_512_ = lean_nat_mul(v_size_x27_508_, v___x_511_);
v___x_513_ = lean_unsigned_to_nat(3u);
v___x_514_ = lean_nat_div(v___x_512_, v___x_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_array_get_size(v_buckets_x27_510_);
v___x_516_ = lean_nat_dec_le(v___x_514_, v___x_515_);
lean_dec(v___x_514_);
if (v___x_516_ == 0)
{
lean_object* v_val_517_; lean_object* v___x_519_; 
v_val_517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_buckets_x27_510_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v_val_517_);
lean_ctor_set(v___x_487_, 0, v_size_x27_508_);
v___x_519_ = v___x_487_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_size_x27_508_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_val_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v___x_522_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v_buckets_x27_510_);
lean_ctor_set(v___x_487_, 0, v_size_x27_508_);
v___x_522_ = v___x_487_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_size_x27_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_buckets_x27_510_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v___x_524_; lean_object* v_buckets_x27_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
lean_inc(v_bkt_505_);
v___x_524_ = lean_box(0);
v_buckets_x27_525_ = lean_array_uset(v_buckets_485_, v___x_504_, v___x_524_);
v___x_526_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_482_, v_b_483_, v_bkt_505_);
v___x_527_ = lean_array_uset(v_buckets_x27_525_, v___x_504_, v___x_526_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_527_);
v___x_529_ = v___x_487_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_size_484_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
static size_t _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0(void){
_start:
{
lean_object* v___x_532_; size_t v___x_533_; 
v___x_532_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_533_ = lean_ptr_addr(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(lean_object* v_e_534_, lean_object* v_r_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_map_537_; lean_object* v_set_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_562_; 
v_map_537_ = lean_ctor_get(v_a_536_, 0);
v_set_538_ = lean_ctor_get(v_a_536_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_562_ == 0)
{
v___x_540_ = v_a_536_;
v_isShared_541_ = v_isSharedCheck_562_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_set_538_);
lean_inc(v_map_537_);
lean_dec(v_a_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_562_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; uint64_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; size_t v___x_546_; size_t v___x_547_; uint8_t v___x_548_; 
v___x_542_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_543_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_r_535_);
v___x_544_ = lean_uint64_to_usize(v___x_543_);
v___x_545_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_538_, v___x_544_, v_r_535_, v___x_542_);
v___x_546_ = lean_ptr_addr(v___x_545_);
v___x_547_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_548_ = lean_usize_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec_ref(v_r_535_);
lean_inc_ref(v___x_545_);
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_537_, v_e_534_, v___x_545_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_549_);
v___x_551_ = v___x_540_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_set_538_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_545_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
return v___x_552_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec_ref(v___x_545_);
lean_inc_ref_n(v_r_535_, 4);
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_map_537_, v_e_534_, v_r_535_);
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v___x_554_, v_r_535_, v_r_535_);
v___x_556_ = lean_box(0);
v___x_557_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_538_, v_r_535_, v___x_556_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_557_);
lean_ctor_set(v___x_540_, 0, v___x_555_);
v___x_559_ = v___x_540_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_r_535_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(lean_object* v_e_563_, lean_object* v_r_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_563_, v_r_564_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___boxed(lean_object* v_e_568_, lean_object* v_r_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save(v_e_568_, v_r_569_, v_a_570_, v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_573_, lean_object* v_x_574_, size_t v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_x_574_, v_x_575_, v_x_576_, v_x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___boxed(lean_object* v_00_u03b2_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_2667__boxed_584_; lean_object* v_res_585_; 
v_x_2667__boxed_584_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_res_585_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0(v_00_u03b2_579_, v_x_580_, v_x_2667__boxed_584_, v_x_582_, v_x_583_);
lean_dec_ref(v_x_583_);
lean_dec_ref(v_x_582_);
lean_dec_ref(v_x_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1(lean_object* v_00_u03b2_586_, lean_object* v_m_587_, lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1___redArg(v_m_587_, v_a_588_, v_b_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2(lean_object* v_00_u03b2_591_, lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_x_592_, v_x_593_, v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_596_, lean_object* v_keys_597_, lean_object* v_vals_598_, lean_object* v_heq_599_, lean_object* v_i_600_, lean_object* v_k_601_, lean_object* v_k_u2080_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_keys_597_, v_i_600_, v_k_601_, v_k_u2080_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_604_, lean_object* v_keys_605_, lean_object* v_vals_606_, lean_object* v_heq_607_, lean_object* v_i_608_, lean_object* v_k_609_, lean_object* v_k_u2080_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_604_, v_keys_605_, v_vals_606_, v_heq_607_, v_i_608_, v_k_609_, v_k_u2080_610_);
lean_dec_ref(v_k_u2080_610_);
lean_dec_ref(v_k_609_);
lean_dec_ref(v_vals_606_);
lean_dec_ref(v_keys_605_);
return v_res_611_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(lean_object* v_00_u03b2_612_, lean_object* v_a_613_, lean_object* v_x_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___redArg(v_a_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2___boxed(lean_object* v_00_u03b2_616_, lean_object* v_a_617_, lean_object* v_x_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__2(v_00_u03b2_616_, v_a_617_, v_x_618_);
lean_dec(v_x_618_);
lean_dec_ref(v_a_617_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3(lean_object* v_00_u03b2_621_, lean_object* v_data_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3___redArg(v_data_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4(lean_object* v_00_u03b2_624_, lean_object* v_a_625_, lean_object* v_b_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__4___redArg(v_a_625_, v_b_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, size_t v_x_631_, size_t v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___redArg(v_x_630_, v_x_631_, v_x_632_, v_x_633_, v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6___boxed(lean_object* v_00_u03b2_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
size_t v_x_2704__boxed_642_; size_t v_x_2705__boxed_643_; lean_object* v_res_644_; 
v_x_2704__boxed_642_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_x_2705__boxed_643_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_res_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6(v_00_u03b2_636_, v_x_637_, v_x_2704__boxed_642_, v_x_2705__boxed_643_, v_x_640_, v_x_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_645_, lean_object* v_i_646_, lean_object* v_source_647_, lean_object* v_target_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4___redArg(v_i_646_, v_source_647_, v_target_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8(lean_object* v_00_u03b2_650_, lean_object* v_n_651_, lean_object* v_k_652_, lean_object* v_v_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8___redArg(v_n_651_, v_k_652_, v_v_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_655_, size_t v_depth_656_, lean_object* v_keys_657_, lean_object* v_vals_658_, lean_object* v_heq_659_, lean_object* v_i_660_, lean_object* v_entries_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___redArg(v_depth_656_, v_keys_657_, v_vals_658_, v_i_660_, v_entries_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_663_, lean_object* v_depth_664_, lean_object* v_keys_665_, lean_object* v_vals_666_, lean_object* v_heq_667_, lean_object* v_i_668_, lean_object* v_entries_669_){
_start:
{
size_t v_depth_boxed_670_; lean_object* v_res_671_; 
v_depth_boxed_670_ = lean_unbox_usize(v_depth_664_);
lean_dec(v_depth_664_);
v_res_671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__9(v_00_u03b2_663_, v_depth_boxed_670_, v_keys_665_, v_vals_666_, v_heq_667_, v_i_668_, v_entries_669_);
lean_dec_ref(v_vals_666_);
lean_dec_ref(v_keys_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__1_spec__3_spec__4_spec__6___redArg(v_x_673_, v_x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2_spec__6_spec__8_spec__10___redArg(v_x_677_, v_x_678_, v_x_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(lean_object* v_e_684_, lean_object* v_k_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_map_688_; lean_object* v_set_689_; lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___x_692_; 
v_map_688_ = lean_ctor_get(v_a_687_, 0);
v_set_689_ = lean_ctor_get(v_a_687_, 1);
v___f_690_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__0));
v___f_691_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___closed__1));
lean_inc_ref(v_e_684_);
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_690_, v___f_691_, v_map_688_, v_e_684_);
if (lean_obj_tag(v___x_692_) == 1)
{
lean_object* v_val_693_; lean_object* v___x_694_; 
lean_dec_ref(v_k_685_);
lean_dec_ref(v_e_684_);
v_val_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_val_693_);
lean_ctor_set(v___x_694_, 1, v_a_687_);
return v___x_694_;
}
else
{
lean_object* v___f_695_; lean_object* v___x_696_; uint64_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; size_t v___x_700_; size_t v___x_701_; uint8_t v___x_702_; 
lean_dec(v___x_692_);
v___f_695_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_696_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_697_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_684_);
v___x_698_ = lean_uint64_to_usize(v___x_697_);
lean_inc_ref(v_e_684_);
lean_inc_ref(v_set_689_);
v___x_699_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_695_, v_set_689_, v___x_698_, v_e_684_, v___x_696_);
v___x_700_ = lean_ptr_addr(v___x_699_);
v___x_701_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_702_ = lean_usize_dec_eq(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_dec_ref(v_k_685_);
lean_dec_ref(v_e_684_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_699_);
lean_ctor_set(v___x_703_, 1, v_a_687_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec(v___x_699_);
lean_inc_ref(v_a_686_);
v___x_704_ = lean_apply_2(v_k_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v_a_706_; lean_object* v___x_707_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
v_a_706_ = lean_ctor_get(v___x_704_, 1);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_704_, 2);
v___x_707_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_684_, v_a_705_, v_a_706_);
return v___x_707_;
}
else
{
lean_dec_ref(v_e_684_);
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit___boxed(lean_object* v_e_708_, lean_object* v_k_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visit(v_e_708_, v_k_709_, v_a_710_, v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(lean_object* v_a_713_, lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_box(0);
return v___x_715_;
}
else
{
lean_object* v_key_716_; lean_object* v_value_717_; lean_object* v_tail_718_; size_t v___x_719_; size_t v___x_720_; uint8_t v___x_721_; 
v_key_716_ = lean_ctor_get(v_x_714_, 0);
v_value_717_ = lean_ctor_get(v_x_714_, 1);
v_tail_718_ = lean_ctor_get(v_x_714_, 2);
v___x_719_ = lean_ptr_addr(v_key_716_);
v___x_720_ = lean_ptr_addr(v_a_713_);
v___x_721_ = lean_usize_dec_eq(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
v_x_714_ = v_tail_718_;
goto _start;
}
else
{
lean_object* v___x_723_; 
lean_inc(v_value_717_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v_value_717_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_724_, lean_object* v_x_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_724_, v_x_725_);
lean_dec(v_x_725_);
lean_dec_ref(v_a_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(lean_object* v_m_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_buckets_729_; lean_object* v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v_fold_737_; uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_buckets_729_ = lean_ctor_get(v_m_727_, 1);
v___x_730_ = lean_array_get_size(v_buckets_729_);
v___x_731_ = lean_ptr_addr(v_a_728_);
v___x_732_ = ((size_t)3ULL);
v___x_733_ = lean_usize_shift_right(v___x_731_, v___x_732_);
v___x_734_ = lean_usize_to_uint64(v___x_733_);
v___x_735_ = 32ULL;
v___x_736_ = lean_uint64_shift_right(v___x_734_, v___x_735_);
v_fold_737_ = lean_uint64_xor(v___x_734_, v___x_736_);
v___x_738_ = 16ULL;
v___x_739_ = lean_uint64_shift_right(v_fold_737_, v___x_738_);
v___x_740_ = lean_uint64_xor(v_fold_737_, v___x_739_);
v___x_741_ = lean_uint64_to_usize(v___x_740_);
v___x_742_ = lean_usize_of_nat(v___x_730_);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_sub(v___x_742_, v___x_743_);
v___x_745_ = lean_usize_land(v___x_741_, v___x_744_);
v___x_746_ = lean_array_uget_borrowed(v_buckets_729_, v___x_745_);
v___x_747_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_728_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg___boxed(lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_748_, v_a_749_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_m_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_751_, lean_object* v_vals_752_, lean_object* v_i_753_, lean_object* v_k_754_){
_start:
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = lean_array_get_size(v_keys_751_);
v___x_756_ = lean_nat_dec_lt(v_i_753_, v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec(v_i_753_);
v___x_757_ = lean_box(0);
return v___x_757_;
}
else
{
lean_object* v_k_x27_758_; uint8_t v___x_759_; 
v_k_x27_758_ = lean_array_fget_borrowed(v_keys_751_, v_i_753_);
v___x_759_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_754_, v_k_x27_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_i_753_, v___x_760_);
lean_dec(v_i_753_);
v_i_753_ = v___x_761_;
goto _start;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_array_fget_borrowed(v_vals_752_, v_i_753_);
lean_dec(v_i_753_);
lean_inc(v___x_763_);
lean_inc(v_k_x27_758_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_k_x27_758_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_766_, lean_object* v_vals_767_, lean_object* v_i_768_, lean_object* v_k_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_766_, v_vals_767_, v_i_768_, v_k_769_);
lean_dec_ref(v_k_769_);
lean_dec_ref(v_vals_767_);
lean_dec_ref(v_keys_766_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(lean_object* v_x_771_, size_t v_x_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_object* v_es_774_; lean_object* v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v_j_778_; lean_object* v___x_779_; 
v_es_774_ = lean_ctor_get(v_x_771_, 0);
v___x_775_ = lean_box(2);
v___x_776_ = ((size_t)31ULL);
v___x_777_ = lean_usize_land(v_x_772_, v___x_776_);
v_j_778_ = lean_usize_to_nat(v___x_777_);
v___x_779_ = lean_array_get_borrowed(v___x_775_, v_es_774_, v_j_778_);
lean_dec(v_j_778_);
switch(lean_obj_tag(v___x_779_))
{
case 0:
{
lean_object* v_key_780_; lean_object* v_val_781_; uint8_t v___x_782_; 
v_key_780_ = lean_ctor_get(v___x_779_, 0);
v_val_781_ = lean_ctor_get(v___x_779_, 1);
v___x_782_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_773_, v_key_780_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
v___x_783_ = lean_box(0);
return v___x_783_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc(v_val_781_);
lean_inc(v_key_780_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_key_780_);
lean_ctor_set(v___x_784_, 1, v_val_781_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
case 1:
{
lean_object* v_node_786_; size_t v___x_787_; size_t v___x_788_; 
v_node_786_ = lean_ctor_get(v___x_779_, 0);
v___x_787_ = ((size_t)5ULL);
v___x_788_ = lean_usize_shift_right(v_x_772_, v___x_787_);
v_x_771_ = v_node_786_;
v_x_772_ = v___x_788_;
goto _start;
}
default: 
{
lean_object* v___x_790_; 
v___x_790_ = lean_box(0);
return v___x_790_;
}
}
}
else
{
lean_object* v_ks_791_; lean_object* v_vs_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_ks_791_ = lean_ctor_get(v_x_771_, 0);
v_vs_792_ = lean_ctor_get(v_x_771_, 1);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_ks_791_, v_vs_792_, v___x_793_, v_x_773_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
size_t v_x_11089__boxed_798_; lean_object* v_res_799_; 
v_x_11089__boxed_798_ = lean_unbox_usize(v_x_796_);
lean_dec(v_x_796_);
v_res_799_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_795_, v_x_11089__boxed_798_, v_x_797_);
lean_dec_ref(v_x_797_);
lean_dec_ref(v_x_795_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
uint64_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_801_);
v___x_803_ = lean_uint64_to_usize(v___x_802_);
v___x_804_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_800_, v___x_803_, v_x_801_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg___boxed(lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_805_, v_x_806_);
lean_dec_ref(v_x_806_);
lean_dec_ref(v_x_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(lean_object* v_e_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___y_812_; lean_object* v___y_817_; lean_object* v___y_822_; lean_object* v___y_827_; 
switch(lean_obj_tag(v_e_808_))
{
case 4:
{
lean_object* v_declName_831_; lean_object* v_map_832_; lean_object* v_set_833_; lean_object* v___x_834_; 
v_declName_831_ = lean_ctor_get(v_e_808_, 0);
v_map_832_ = lean_ctor_get(v_a_810_, 0);
v_set_833_ = lean_ctor_get(v_a_810_, 1);
v___x_834_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_833_, v_e_808_);
if (lean_obj_tag(v___x_834_) == 0)
{
uint8_t v___x_835_; 
lean_inc(v_declName_831_);
lean_inc_ref(v_a_809_);
v___x_835_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_809_, v_declName_831_);
if (v___x_835_ == 0)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
lean_inc_ref(v_set_833_);
lean_inc_ref(v_map_832_);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; lean_object* v_unused_847_; 
v_unused_846_ = lean_ctor_get(v_a_810_, 1);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_a_810_, 0);
lean_dec(v_unused_847_);
v___x_837_ = v_a_810_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_a_810_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_839_ = lean_box(0);
lean_inc_ref(v_e_808_);
v___x_840_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_833_, v_e_808_, v___x_839_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_840_);
v___x_842_ = v___x_837_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_map_832_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_840_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_e_808_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
return v___x_843_;
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref_known(v_e_808_, 2);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_a_810_);
return v___x_849_;
}
}
else
{
lean_object* v_val_850_; lean_object* v_fst_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref_known(v_e_808_, 2);
v_val_850_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v___x_834_, 1);
v_fst_851_ = lean_ctor_get(v_val_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_val_850_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_val_850_, 1);
lean_dec(v_unused_859_);
v___x_853_ = v_val_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_fst_851_);
lean_dec(v_val_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v_a_810_);
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_fst_851_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_a_810_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
case 5:
{
lean_object* v_fn_860_; lean_object* v_arg_861_; lean_object* v_map_862_; lean_object* v_set_863_; lean_object* v___x_864_; 
v_fn_860_ = lean_ctor_get(v_e_808_, 0);
v_arg_861_ = lean_ctor_get(v_e_808_, 1);
v_map_862_ = lean_ctor_get(v_a_810_, 0);
v_set_863_ = lean_ctor_get(v_a_810_, 1);
v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_862_, v_e_808_);
if (lean_obj_tag(v___x_864_) == 1)
{
lean_object* v_val_865_; lean_object* v___x_866_; 
lean_dec_ref_known(v_e_808_, 2);
v_val_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v___x_864_, 1);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_val_865_);
lean_ctor_set(v___x_866_, 1, v_a_810_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; uint64_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; size_t v___x_871_; size_t v___x_872_; uint8_t v___x_873_; 
lean_dec(v___x_864_);
v___x_867_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_868_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_808_);
v___x_869_ = lean_uint64_to_usize(v___x_868_);
v___x_870_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_863_, v___x_869_, v_e_808_, v___x_867_);
v___x_871_ = lean_ptr_addr(v___x_870_);
v___x_872_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_873_ = lean_usize_dec_eq(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref_known(v_e_808_, 2);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_870_);
lean_ctor_set(v___x_874_, 1, v_a_810_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; 
lean_dec_ref(v___x_870_);
lean_inc_ref(v_fn_860_);
v___x_875_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_fn_860_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
v_a_877_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_875_, 2);
lean_inc_ref(v_arg_861_);
v___x_878_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_arg_861_, v_a_809_, v_a_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v_a_880_; uint8_t v___y_882_; size_t v___x_886_; size_t v___x_887_; uint8_t v___x_888_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
v_a_880_ = lean_ctor_get(v___x_878_, 1);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_878_, 2);
v___x_886_ = lean_ptr_addr(v_fn_860_);
v___x_887_ = lean_ptr_addr(v_a_876_);
v___x_888_ = lean_usize_dec_eq(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
v___y_882_ = v___x_888_;
goto v___jp_881_;
}
else
{
size_t v___x_889_; size_t v___x_890_; uint8_t v___x_891_; 
v___x_889_ = lean_ptr_addr(v_arg_861_);
v___x_890_ = lean_ptr_addr(v_a_879_);
v___x_891_ = lean_usize_dec_eq(v___x_889_, v___x_890_);
v___y_882_ = v___x_891_;
goto v___jp_881_;
}
v___jp_881_:
{
if (v___y_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = l_Lean_Expr_app___override(v_a_876_, v_a_879_);
v___x_884_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_883_, v_a_880_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
lean_dec(v_a_879_);
lean_dec(v_a_876_);
lean_inc_ref(v_e_808_);
v___x_885_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_e_808_, v_a_880_);
return v___x_885_;
}
}
}
else
{
lean_dec(v_a_876_);
v___y_822_ = v___x_878_;
goto v___jp_821_;
}
}
else
{
v___y_822_ = v___x_875_;
goto v___jp_821_;
}
}
}
}
case 6:
{
lean_object* v_binderName_892_; lean_object* v_binderType_893_; lean_object* v_body_894_; uint8_t v_binderInfo_895_; lean_object* v_map_896_; lean_object* v_set_897_; lean_object* v___x_898_; 
v_binderName_892_ = lean_ctor_get(v_e_808_, 0);
v_binderType_893_ = lean_ctor_get(v_e_808_, 1);
v_body_894_ = lean_ctor_get(v_e_808_, 2);
v_binderInfo_895_ = lean_ctor_get_uint8(v_e_808_, sizeof(void*)*3 + 8);
v_map_896_ = lean_ctor_get(v_a_810_, 0);
v_set_897_ = lean_ctor_get(v_a_810_, 1);
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_896_, v_e_808_);
if (lean_obj_tag(v___x_898_) == 1)
{
lean_object* v_val_899_; lean_object* v___x_900_; 
lean_dec_ref_known(v_e_808_, 3);
v_val_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_val_899_);
lean_ctor_set(v___x_900_, 1, v_a_810_);
return v___x_900_;
}
else
{
lean_object* v___x_901_; uint64_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; size_t v___x_905_; size_t v___x_906_; uint8_t v___x_907_; 
lean_dec(v___x_898_);
v___x_901_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_902_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_808_);
v___x_903_ = lean_uint64_to_usize(v___x_902_);
v___x_904_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_897_, v___x_903_, v_e_808_, v___x_901_);
v___x_905_ = lean_ptr_addr(v___x_904_);
v___x_906_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_907_ = lean_usize_dec_eq(v___x_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec_ref_known(v_e_808_, 3);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_904_);
lean_ctor_set(v___x_908_, 1, v_a_810_);
return v___x_908_;
}
else
{
lean_object* v___x_909_; 
lean_dec_ref(v___x_904_);
lean_inc_ref(v_binderType_893_);
v___x_909_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_893_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_a_911_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
v_a_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_909_, 2);
lean_inc_ref(v_body_894_);
v___x_912_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_894_, v_a_809_, v_a_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v_a_914_; uint8_t v___y_916_; size_t v___x_923_; size_t v___x_924_; uint8_t v___x_925_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
v_a_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_912_, 2);
v___x_923_ = lean_ptr_addr(v_binderType_893_);
v___x_924_ = lean_ptr_addr(v_a_910_);
v___x_925_ = lean_usize_dec_eq(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
v___y_916_ = v___x_925_;
goto v___jp_915_;
}
else
{
size_t v___x_926_; size_t v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_ptr_addr(v_body_894_);
v___x_927_ = lean_ptr_addr(v_a_913_);
v___x_928_ = lean_usize_dec_eq(v___x_926_, v___x_927_);
v___y_916_ = v___x_928_;
goto v___jp_915_;
}
v___jp_915_:
{
if (v___y_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_inc(v_binderName_892_);
v___x_917_ = l_Lean_Expr_lam___override(v_binderName_892_, v_a_910_, v_a_913_, v_binderInfo_895_);
v___x_918_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_917_, v_a_914_);
return v___x_918_;
}
else
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_895_, v_binderInfo_895_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_inc(v_binderName_892_);
v___x_920_ = l_Lean_Expr_lam___override(v_binderName_892_, v_a_910_, v_a_913_, v_binderInfo_895_);
v___x_921_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_920_, v_a_914_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; 
lean_dec(v_a_913_);
lean_dec(v_a_910_);
lean_inc_ref(v_e_808_);
v___x_922_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_e_808_, v_a_914_);
return v___x_922_;
}
}
}
}
else
{
lean_dec(v_a_910_);
v___y_817_ = v___x_912_;
goto v___jp_816_;
}
}
else
{
v___y_817_ = v___x_909_;
goto v___jp_816_;
}
}
}
}
case 7:
{
lean_object* v_binderName_929_; lean_object* v_binderType_930_; lean_object* v_body_931_; uint8_t v_binderInfo_932_; lean_object* v_map_933_; lean_object* v_set_934_; lean_object* v___x_935_; 
v_binderName_929_ = lean_ctor_get(v_e_808_, 0);
v_binderType_930_ = lean_ctor_get(v_e_808_, 1);
v_body_931_ = lean_ctor_get(v_e_808_, 2);
v_binderInfo_932_ = lean_ctor_get_uint8(v_e_808_, sizeof(void*)*3 + 8);
v_map_933_ = lean_ctor_get(v_a_810_, 0);
v_set_934_ = lean_ctor_get(v_a_810_, 1);
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_933_, v_e_808_);
if (lean_obj_tag(v___x_935_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_937_; 
lean_dec_ref_known(v_e_808_, 3);
v_val_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_val_936_);
lean_ctor_set(v___x_937_, 1, v_a_810_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; uint64_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; size_t v___x_942_; size_t v___x_943_; uint8_t v___x_944_; 
lean_dec(v___x_935_);
v___x_938_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_939_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_808_);
v___x_940_ = lean_uint64_to_usize(v___x_939_);
v___x_941_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_934_, v___x_940_, v_e_808_, v___x_938_);
v___x_942_ = lean_ptr_addr(v___x_941_);
v___x_943_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_944_ = lean_usize_dec_eq(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_dec_ref_known(v_e_808_, 3);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_941_);
lean_ctor_set(v___x_945_, 1, v_a_810_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; 
lean_dec_ref(v___x_941_);
lean_inc_ref(v_binderType_930_);
v___x_946_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_binderType_930_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_a_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
v_a_948_ = lean_ctor_get(v___x_946_, 1);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_946_, 2);
lean_inc_ref(v_body_931_);
v___x_949_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_931_, v_a_809_, v_a_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_a_951_; uint8_t v___y_953_; size_t v___x_960_; size_t v___x_961_; uint8_t v___x_962_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
v_a_951_ = lean_ctor_get(v___x_949_, 1);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_949_, 2);
v___x_960_ = lean_ptr_addr(v_binderType_930_);
v___x_961_ = lean_ptr_addr(v_a_947_);
v___x_962_ = lean_usize_dec_eq(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
v___y_953_ = v___x_962_;
goto v___jp_952_;
}
else
{
size_t v___x_963_; size_t v___x_964_; uint8_t v___x_965_; 
v___x_963_ = lean_ptr_addr(v_body_931_);
v___x_964_ = lean_ptr_addr(v_a_950_);
v___x_965_ = lean_usize_dec_eq(v___x_963_, v___x_964_);
v___y_953_ = v___x_965_;
goto v___jp_952_;
}
v___jp_952_:
{
if (v___y_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_inc(v_binderName_929_);
v___x_954_ = l_Lean_Expr_forallE___override(v_binderName_929_, v_a_947_, v_a_950_, v_binderInfo_932_);
v___x_955_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_954_, v_a_951_);
return v___x_955_;
}
else
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_932_, v_binderInfo_932_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc(v_binderName_929_);
v___x_957_ = l_Lean_Expr_forallE___override(v_binderName_929_, v_a_947_, v_a_950_, v_binderInfo_932_);
v___x_958_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_957_, v_a_951_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_a_950_);
lean_dec(v_a_947_);
lean_inc_ref(v_e_808_);
v___x_959_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_e_808_, v_a_951_);
return v___x_959_;
}
}
}
}
else
{
lean_dec(v_a_947_);
v___y_827_ = v___x_949_;
goto v___jp_826_;
}
}
else
{
v___y_827_ = v___x_946_;
goto v___jp_826_;
}
}
}
}
case 8:
{
lean_object* v_declName_966_; lean_object* v_type_967_; lean_object* v_value_968_; lean_object* v_body_969_; uint8_t v_nondep_970_; lean_object* v_map_971_; lean_object* v_set_972_; lean_object* v___x_973_; 
v_declName_966_ = lean_ctor_get(v_e_808_, 0);
v_type_967_ = lean_ctor_get(v_e_808_, 1);
v_value_968_ = lean_ctor_get(v_e_808_, 2);
v_body_969_ = lean_ctor_get(v_e_808_, 3);
v_nondep_970_ = lean_ctor_get_uint8(v_e_808_, sizeof(void*)*4 + 8);
v_map_971_ = lean_ctor_get(v_a_810_, 0);
v_set_972_ = lean_ctor_get(v_a_810_, 1);
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_971_, v_e_808_);
if (lean_obj_tag(v___x_973_) == 1)
{
lean_object* v_val_974_; lean_object* v___x_975_; 
lean_dec_ref_known(v_e_808_, 4);
v_val_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_val_974_);
lean_ctor_set(v___x_975_, 1, v_a_810_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; uint64_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; size_t v___x_980_; size_t v___x_981_; uint8_t v___x_982_; 
lean_dec(v___x_973_);
v___x_976_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_977_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_808_);
v___x_978_ = lean_uint64_to_usize(v___x_977_);
v___x_979_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_972_, v___x_978_, v_e_808_, v___x_976_);
v___x_980_ = lean_ptr_addr(v___x_979_);
v___x_981_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_982_ = lean_usize_dec_eq(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_dec_ref_known(v_e_808_, 4);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_979_);
lean_ctor_set(v___x_983_, 1, v_a_810_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; 
lean_dec_ref(v___x_979_);
lean_inc_ref(v_type_967_);
v___x_984_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_type_967_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
v_a_986_ = lean_ctor_get(v___x_984_, 1);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_984_, 2);
lean_inc_ref(v_value_968_);
v___x_987_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_value_968_, v_a_809_, v_a_986_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
v_a_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_987_, 2);
lean_inc_ref(v_body_969_);
v___x_990_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_body_969_, v_a_809_, v_a_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v_a_992_; uint8_t v___y_994_; size_t v___x_1003_; size_t v___x_1004_; uint8_t v___x_1005_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
v_a_992_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_990_, 2);
v___x_1003_ = lean_ptr_addr(v_type_967_);
v___x_1004_ = lean_ptr_addr(v_a_985_);
v___x_1005_ = lean_usize_dec_eq(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
v___y_994_ = v___x_1005_;
goto v___jp_993_;
}
else
{
size_t v___x_1006_; size_t v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_ptr_addr(v_value_968_);
v___x_1007_ = lean_ptr_addr(v_a_988_);
v___x_1008_ = lean_usize_dec_eq(v___x_1006_, v___x_1007_);
v___y_994_ = v___x_1008_;
goto v___jp_993_;
}
v___jp_993_:
{
if (v___y_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_inc(v_declName_966_);
v___x_995_ = l_Lean_Expr_letE___override(v_declName_966_, v_a_985_, v_a_988_, v_a_991_, v_nondep_970_);
v___x_996_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_995_, v_a_992_);
return v___x_996_;
}
else
{
size_t v___x_997_; size_t v___x_998_; uint8_t v___x_999_; 
v___x_997_ = lean_ptr_addr(v_body_969_);
v___x_998_ = lean_ptr_addr(v_a_991_);
v___x_999_ = lean_usize_dec_eq(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_inc(v_declName_966_);
v___x_1000_ = l_Lean_Expr_letE___override(v_declName_966_, v_a_985_, v_a_988_, v_a_991_, v_nondep_970_);
v___x_1001_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_1000_, v_a_992_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; 
lean_dec(v_a_991_);
lean_dec(v_a_988_);
lean_dec(v_a_985_);
lean_inc_ref(v_e_808_);
v___x_1002_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_e_808_, v_a_992_);
return v___x_1002_;
}
}
}
}
else
{
lean_dec(v_a_988_);
lean_dec(v_a_985_);
v___y_812_ = v___x_990_;
goto v___jp_811_;
}
}
else
{
lean_dec(v_a_985_);
v___y_812_ = v___x_987_;
goto v___jp_811_;
}
}
else
{
v___y_812_ = v___x_984_;
goto v___jp_811_;
}
}
}
}
case 10:
{
lean_object* v_data_1009_; lean_object* v_expr_1010_; lean_object* v_map_1011_; lean_object* v_set_1012_; lean_object* v___x_1013_; 
v_data_1009_ = lean_ctor_get(v_e_808_, 0);
v_expr_1010_ = lean_ctor_get(v_e_808_, 1);
v_map_1011_ = lean_ctor_get(v_a_810_, 0);
v_set_1012_ = lean_ctor_get(v_a_810_, 1);
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1011_, v_e_808_);
if (lean_obj_tag(v___x_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v___x_1015_; 
lean_dec_ref_known(v_e_808_, 2);
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_val_1014_);
lean_ctor_set(v___x_1015_, 1, v_a_810_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; uint64_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; uint8_t v___x_1022_; 
lean_dec(v___x_1013_);
v___x_1016_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1017_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_808_);
v___x_1018_ = lean_uint64_to_usize(v___x_1017_);
v___x_1019_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1012_, v___x_1018_, v_e_808_, v___x_1016_);
v___x_1020_ = lean_ptr_addr(v___x_1019_);
v___x_1021_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1022_ = lean_usize_dec_eq(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_dec_ref_known(v_e_808_, 2);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1019_);
lean_ctor_set(v___x_1023_, 1, v_a_810_);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; 
lean_dec_ref(v___x_1019_);
lean_inc_ref(v_expr_1010_);
v___x_1024_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_expr_1010_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_a_1026_; size_t v___x_1027_; size_t v___x_1028_; uint8_t v___x_1029_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
v_a_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1024_, 2);
v___x_1027_ = lean_ptr_addr(v_expr_1010_);
v___x_1028_ = lean_ptr_addr(v_a_1025_);
v___x_1029_ = lean_usize_dec_eq(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_inc(v_data_1009_);
v___x_1030_ = l_Lean_Expr_mdata___override(v_data_1009_, v_a_1025_);
v___x_1031_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_1030_, v_a_1026_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; 
lean_dec(v_a_1025_);
lean_inc_ref(v_e_808_);
v___x_1032_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_e_808_, v_a_1026_);
return v___x_1032_;
}
}
else
{
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1033_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1033_);
v_a_1034_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1024_, 2);
v___x_1035_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_a_1033_, v_a_1034_);
return v___x_1035_;
}
else
{
lean_dec_ref_known(v_e_808_, 2);
return v___x_1024_;
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1036_; lean_object* v_idx_1037_; lean_object* v_struct_1038_; lean_object* v_map_1039_; lean_object* v_set_1040_; lean_object* v___x_1041_; 
v_typeName_1036_ = lean_ctor_get(v_e_808_, 0);
v_idx_1037_ = lean_ctor_get(v_e_808_, 1);
v_struct_1038_ = lean_ctor_get(v_e_808_, 2);
v_map_1039_ = lean_ctor_get(v_a_810_, 0);
v_set_1040_ = lean_ctor_get(v_a_810_, 1);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_map_1039_, v_e_808_);
if (lean_obj_tag(v___x_1041_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1043_; 
lean_dec_ref_known(v_e_808_, 3);
v_val_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_val_1042_);
lean_ctor_set(v___x_1043_, 1, v_a_810_);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; uint64_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; uint8_t v___x_1050_; 
lean_dec(v___x_1041_);
v___x_1044_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1045_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_808_);
v___x_1046_ = lean_uint64_to_usize(v___x_1045_);
v___x_1047_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_set_1040_, v___x_1046_, v_e_808_, v___x_1044_);
v___x_1048_ = lean_ptr_addr(v___x_1047_);
v___x_1049_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1050_ = lean_usize_dec_eq(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
lean_dec_ref_known(v_e_808_, 3);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1047_);
lean_ctor_set(v___x_1051_, 1, v_a_810_);
return v___x_1051_;
}
else
{
uint8_t v_checkProj_1052_; 
lean_dec_ref(v___x_1047_);
v_checkProj_1052_ = lean_ctor_get_uint8(v_a_809_, sizeof(void*)*1 + 1);
if (v_checkProj_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_inc_ref(v_struct_1038_);
v___x_1053_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_struct_1038_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v_a_1055_; size_t v___x_1056_; size_t v___x_1057_; uint8_t v___x_1058_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
v_a_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1053_, 2);
v___x_1056_ = lean_ptr_addr(v_struct_1038_);
v___x_1057_ = lean_ptr_addr(v_a_1054_);
v___x_1058_ = lean_usize_dec_eq(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_inc(v_idx_1037_);
lean_inc(v_typeName_1036_);
v___x_1059_ = l_Lean_Expr_proj___override(v_typeName_1036_, v_idx_1037_, v_a_1054_);
v___x_1060_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v___x_1059_, v_a_1055_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; 
lean_dec(v_a_1054_);
lean_inc_ref(v_e_808_);
v___x_1061_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_e_808_, v_a_1055_);
return v___x_1061_;
}
}
else
{
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1062_; lean_object* v_a_1063_; lean_object* v___x_1064_; 
v_a_1062_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1062_);
v_a_1063_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1053_, 2);
v___x_1064_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_a_1062_, v_a_1063_);
return v___x_1064_;
}
else
{
lean_dec_ref_known(v_e_808_, 3);
return v___x_1053_;
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref_known(v_e_808_, 3);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_a_810_);
return v___x_1066_;
}
}
}
}
default: 
{
lean_object* v_map_1067_; lean_object* v_set_1068_; lean_object* v___x_1069_; 
v_map_1067_ = lean_ctor_get(v_a_810_, 0);
v_set_1068_ = lean_ctor_get(v_a_810_, 1);
v___x_1069_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_set_1068_, v_e_808_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1079_; 
lean_inc_ref(v_set_1068_);
lean_inc_ref(v_map_1067_);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; lean_object* v_unused_1081_; 
v_unused_1080_ = lean_ctor_get(v_a_810_, 1);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_a_810_, 0);
lean_dec(v_unused_1081_);
v___x_1071_ = v_a_810_;
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v_a_810_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1073_ = lean_box(0);
lean_inc_ref(v_e_808_);
v___x_1074_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_set_1068_, v_e_808_, v___x_1073_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_map_1067_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_e_808_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
return v___x_1077_;
}
}
}
else
{
lean_object* v_val_1082_; lean_object* v_fst_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_e_808_);
v_val_1082_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v___x_1069_, 1);
v_fst_1083_ = lean_ctor_get(v_val_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_val_1082_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_val_1082_, 1);
lean_dec(v_unused_1091_);
v___x_1085_ = v_val_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_fst_1083_);
lean_dec(v_val_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v_a_810_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_fst_1083_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_a_810_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
v___jp_811_:
{
if (lean_obj_tag(v___y_812_) == 0)
{
lean_object* v_a_813_; lean_object* v_a_814_; lean_object* v___x_815_; 
v_a_813_ = lean_ctor_get(v___y_812_, 0);
lean_inc(v_a_813_);
v_a_814_ = lean_ctor_get(v___y_812_, 1);
lean_inc(v_a_814_);
lean_dec_ref_known(v___y_812_, 2);
v___x_815_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_a_813_, v_a_814_);
return v___x_815_;
}
else
{
lean_dec_ref(v_e_808_);
return v___y_812_;
}
}
v___jp_816_:
{
if (lean_obj_tag(v___y_817_) == 0)
{
lean_object* v_a_818_; lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_818_ = lean_ctor_get(v___y_817_, 0);
lean_inc(v_a_818_);
v_a_819_ = lean_ctor_get(v___y_817_, 1);
lean_inc(v_a_819_);
lean_dec_ref_known(v___y_817_, 2);
v___x_820_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_a_818_, v_a_819_);
return v___x_820_;
}
else
{
lean_dec_ref(v_e_808_);
return v___y_817_;
}
}
v___jp_821_:
{
if (lean_obj_tag(v___y_822_) == 0)
{
lean_object* v_a_823_; lean_object* v_a_824_; lean_object* v___x_825_; 
v_a_823_ = lean_ctor_get(v___y_822_, 0);
lean_inc(v_a_823_);
v_a_824_ = lean_ctor_get(v___y_822_, 1);
lean_inc(v_a_824_);
lean_dec_ref_known(v___y_822_, 2);
v___x_825_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_a_823_, v_a_824_);
return v___x_825_;
}
else
{
lean_dec_ref(v_e_808_);
return v___y_822_;
}
}
v___jp_826_:
{
if (lean_obj_tag(v___y_827_) == 0)
{
lean_object* v_a_828_; lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_828_ = lean_ctor_get(v___y_827_, 0);
lean_inc(v_a_828_);
v_a_829_ = lean_ctor_get(v___y_827_, 1);
lean_inc(v_a_829_);
lean_dec_ref_known(v___y_827_, 2);
v___x_830_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg(v_e_808_, v_a_828_, v_a_829_);
return v___x_830_;
}
else
{
lean_dec_ref(v_e_808_);
return v___y_827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go___boxed(lean_object* v_e_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1092_, v_a_1093_, v_a_1094_);
lean_dec_ref(v_a_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(lean_object* v_00_u03b2_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___redArg(v_x_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0(v_00_u03b2_1100_, v_x_1101_, v_x_1102_);
lean_dec_ref(v_x_1102_);
lean_dec_ref(v_x_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(lean_object* v_00_u03b2_1104_, lean_object* v_m_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___redArg(v_m_1105_, v_a_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_m_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1(v_00_u03b2_1108_, v_m_1109_, v_a_1110_);
lean_dec_ref(v_a_1110_);
lean_dec_ref(v_m_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, size_t v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___redArg(v_x_1113_, v_x_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
size_t v_x_11735__boxed_1121_; lean_object* v_res_1122_; 
v_x_11735__boxed_1121_ = lean_unbox_usize(v_x_1119_);
lean_dec(v_x_1119_);
v_res_1122_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0(v_00_u03b2_1117_, v_x_1118_, v_x_11735__boxed_1121_, v_x_1120_);
lean_dec_ref(v_x_1120_);
lean_dec_ref(v_x_1118_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(lean_object* v_00_u03b2_1123_, lean_object* v_a_1124_, lean_object* v_x_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___redArg(v_a_1124_, v_x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1127_, lean_object* v_a_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__1_spec__2(v_00_u03b2_1127_, v_a_1128_, v_x_1129_);
lean_dec(v_x_1129_);
lean_dec_ref(v_a_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1131_, lean_object* v_keys_1132_, lean_object* v_vals_1133_, lean_object* v_heq_1134_, lean_object* v_i_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___redArg(v_keys_1132_, v_vals_1133_, v_i_1135_, v_k_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1138_, lean_object* v_keys_1139_, lean_object* v_vals_1140_, lean_object* v_heq_1141_, lean_object* v_i_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go_spec__0_spec__0_spec__1(v_00_u03b2_1138_, v_keys_1139_, v_vals_1140_, v_heq_1141_, v_i_1142_, v_k_1143_);
lean_dec_ref(v_k_1143_);
lean_dec_ref(v_vals_1140_);
lean_dec_ref(v_keys_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha(lean_object* v_e_1145_, lean_object* v_cache_1146_, lean_object* v_ctx_1147_, lean_object* v_s_1148_){
_start:
{
lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; 
v___f_1149_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___f_1150_ = ((lean_object*)(l_Lean_Meta_Sym_instHashableAlphaKey___closed__0));
lean_inc_ref(v_e_1145_);
v___x_1151_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_1149_, v___f_1150_, v_s_1148_, v_e_1145_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_cache_1146_);
lean_ctor_set(v___x_1152_, 1, v_s_1148_);
v___x_1153_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(v_e_1145_, v_ctx_1147_, v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 1);
v_a_1155_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1157_ = v___x_1153_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1154_);
lean_inc(v_a_1155_);
lean_dec(v___x_1153_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_set_1159_; lean_object* v___x_1161_; 
v_set_1159_ = lean_ctor_get(v_a_1154_, 1);
lean_inc_ref(v_set_1159_);
lean_dec(v_a_1154_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_set_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1155_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_set_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1173_; 
v_a_1164_ = lean_ctor_get(v___x_1153_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v___x_1153_, 0);
lean_dec(v_unused_1174_);
v___x_1166_ = v___x_1153_;
v_isShared_1167_ = v_isSharedCheck_1173_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1153_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1173_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_map_1168_; lean_object* v_set_1169_; lean_object* v___x_1171_; 
v_map_1168_ = lean_ctor_get(v_a_1164_, 0);
lean_inc_ref(v_map_1168_);
v_set_1169_ = lean_ctor_get(v_a_1164_, 1);
lean_inc_ref(v_set_1169_);
lean_dec(v_a_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_set_1169_);
lean_ctor_set(v___x_1166_, 0, v_map_1168_);
v___x_1171_ = v___x_1166_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_map_1168_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_set_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_val_1175_; lean_object* v_fst_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_cache_1146_);
lean_dec_ref(v_e_1145_);
v_val_1175_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1151_, 1);
v_fst_1176_ = lean_ctor_get(v_val_1175_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_val_1175_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v_val_1175_, 1);
lean_dec(v_unused_1184_);
v___x_1178_ = v_val_1175_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_fst_1176_);
lean_dec(v_val_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_s_1148_);
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_fst_1176_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_s_1148_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlpha___boxed(lean_object* v_e_1185_, lean_object* v_cache_1186_, lean_object* v_ctx_1187_, lean_object* v_s_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Meta_Sym_shareCommonAlpha(v_e_1185_, v_cache_1186_, v_ctx_1187_, v_s_1188_);
lean_dec_ref(v_ctx_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(lean_object* v_e_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1192_; uint64_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1192_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1193_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1190_);
v___x_1194_ = lean_uint64_to_usize(v___x_1193_);
v___x_1195_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1191_, v___x_1194_, v_e_1190_, v___x_1192_);
v___x_1196_ = lean_ptr_addr(v___x_1195_);
v___x_1197_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1198_ = lean_usize_dec_eq(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_e_1190_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1195_);
lean_ctor_set(v___x_1199_, 1, v_a_1191_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec_ref(v___x_1195_);
v___x_1200_ = lean_box(0);
lean_inc_ref(v_e_1190_);
v___x_1201_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1191_, v_e_1190_, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_e_1190_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(lean_object* v_e_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1203_, v_a_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___boxed(lean_object* v_e_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc(v_e_1207_, v_a_1208_, v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(lean_object* v_e_1211_, lean_object* v_k_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___f_1215_; lean_object* v___x_1216_; uint64_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; uint8_t v___x_1222_; 
v___f_1215_ = ((lean_object*)(l_Lean_Meta_Sym_instBEqAlphaKey___closed__0));
v___x_1216_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1217_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1211_);
v___x_1218_ = lean_uint64_to_usize(v___x_1217_);
lean_inc_ref(v_a_1214_);
v___x_1219_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v___f_1215_, v_a_1214_, v___x_1218_, v_e_1211_, v___x_1216_);
v___x_1220_ = lean_ptr_addr(v___x_1219_);
v___x_1221_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1222_ = lean_usize_dec_eq(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
lean_dec_ref(v_k_1212_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1219_);
lean_ctor_set(v___x_1223_, 1, v_a_1214_);
return v___x_1223_;
}
else
{
lean_object* v___x_1224_; 
lean_dec(v___x_1219_);
lean_inc_ref(v_a_1213_);
v___x_1224_ = lean_apply_2(v_k_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
v_a_1226_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1224_, 2);
v___x_1227_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1225_, v_a_1226_);
return v___x_1227_;
}
else
{
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc___boxed(lean_object* v_e_1228_, lean_object* v_k_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_visitInc(v_e_1228_, v_k_1229_, v_a_1230_, v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_unsigned_to_nat(16u);
v___x_1235_ = lean_mk_array(v___x_1234_, v___x_1233_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__0);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(lean_object* v_e_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___y_1243_; lean_object* v___y_1248_; lean_object* v___y_1253_; lean_object* v___y_1258_; 
switch(lean_obj_tag(v_e_1239_))
{
case 4:
{
lean_object* v_declName_1262_; lean_object* v___x_1263_; uint64_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; uint8_t v___x_1269_; 
v_declName_1262_ = lean_ctor_get(v_e_1239_, 0);
v___x_1263_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1264_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1239_);
v___x_1265_ = lean_uint64_to_usize(v___x_1264_);
v___x_1266_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1241_, v___x_1265_, v_e_1239_, v___x_1263_);
v___x_1267_ = lean_ptr_addr(v___x_1266_);
v___x_1268_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1269_ = lean_usize_dec_eq(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref_known(v_e_1239_, 2);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1266_);
lean_ctor_set(v___x_1270_, 1, v_a_1241_);
return v___x_1270_;
}
else
{
uint8_t v___x_1271_; 
lean_dec_ref(v___x_1266_);
lean_inc(v_declName_1262_);
lean_inc_ref(v_a_1240_);
v___x_1271_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_isReducible(v_a_1240_, v_declName_1262_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_box(0);
lean_inc_ref(v_e_1239_);
v___x_1273_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__2___redArg(v_a_1241_, v_e_1239_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_e_1239_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref_known(v_e_1239_, 2);
v___x_1275_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1241_);
return v___x_1276_;
}
}
}
case 5:
{
lean_object* v_fn_1277_; lean_object* v_arg_1278_; lean_object* v___x_1279_; uint64_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; uint8_t v___x_1285_; 
v_fn_1277_ = lean_ctor_get(v_e_1239_, 0);
v_arg_1278_ = lean_ctor_get(v_e_1239_, 1);
v___x_1279_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1280_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1239_);
v___x_1281_ = lean_uint64_to_usize(v___x_1280_);
v___x_1282_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1241_, v___x_1281_, v_e_1239_, v___x_1279_);
v___x_1283_ = lean_ptr_addr(v___x_1282_);
v___x_1284_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1285_ = lean_usize_dec_eq(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_dec_ref_known(v_e_1239_, 2);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1282_);
lean_ctor_set(v___x_1286_, 1, v_a_1241_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; 
lean_dec_ref(v___x_1282_);
lean_inc_ref(v_fn_1277_);
v___x_1287_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_fn_1277_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
v_a_1289_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1287_, 2);
lean_inc_ref(v_arg_1278_);
v___x_1290_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_arg_1278_, v_a_1240_, v_a_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v_a_1292_; uint8_t v___y_1294_; size_t v___x_1298_; size_t v___x_1299_; uint8_t v___x_1300_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
v_a_1292_ = lean_ctor_get(v___x_1290_, 1);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1290_, 2);
v___x_1298_ = lean_ptr_addr(v_fn_1277_);
v___x_1299_ = lean_ptr_addr(v_a_1288_);
v___x_1300_ = lean_usize_dec_eq(v___x_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
v___y_1294_ = v___x_1300_;
goto v___jp_1293_;
}
else
{
size_t v___x_1301_; size_t v___x_1302_; uint8_t v___x_1303_; 
v___x_1301_ = lean_ptr_addr(v_arg_1278_);
v___x_1302_ = lean_ptr_addr(v_a_1291_);
v___x_1303_ = lean_usize_dec_eq(v___x_1301_, v___x_1302_);
v___y_1294_ = v___x_1303_;
goto v___jp_1293_;
}
v___jp_1293_:
{
if (v___y_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref_known(v_e_1239_, 2);
v___x_1295_ = l_Lean_Expr_app___override(v_a_1288_, v_a_1291_);
v___x_1296_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1295_, v_a_1292_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; 
lean_dec(v_a_1291_);
lean_dec(v_a_1288_);
v___x_1297_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1239_, v_a_1292_);
return v___x_1297_;
}
}
}
else
{
lean_dec(v_a_1288_);
lean_dec_ref_known(v_e_1239_, 2);
v___y_1253_ = v___x_1290_;
goto v___jp_1252_;
}
}
else
{
lean_dec_ref_known(v_e_1239_, 2);
v___y_1253_ = v___x_1287_;
goto v___jp_1252_;
}
}
}
case 6:
{
lean_object* v_binderName_1304_; lean_object* v_binderType_1305_; lean_object* v_body_1306_; uint8_t v_binderInfo_1307_; lean_object* v___x_1308_; uint64_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; uint8_t v___x_1314_; 
v_binderName_1304_ = lean_ctor_get(v_e_1239_, 0);
v_binderType_1305_ = lean_ctor_get(v_e_1239_, 1);
v_body_1306_ = lean_ctor_get(v_e_1239_, 2);
v_binderInfo_1307_ = lean_ctor_get_uint8(v_e_1239_, sizeof(void*)*3 + 8);
v___x_1308_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1309_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1239_);
v___x_1310_ = lean_uint64_to_usize(v___x_1309_);
v___x_1311_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1241_, v___x_1310_, v_e_1239_, v___x_1308_);
v___x_1312_ = lean_ptr_addr(v___x_1311_);
v___x_1313_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1314_ = lean_usize_dec_eq(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref_known(v_e_1239_, 3);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1311_);
lean_ctor_set(v___x_1315_, 1, v_a_1241_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; 
lean_dec_ref(v___x_1311_);
lean_inc_ref(v_binderType_1305_);
v___x_1316_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1305_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v_a_1318_; lean_object* v___x_1319_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
v_a_1318_ = lean_ctor_get(v___x_1316_, 1);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1316_, 2);
lean_inc_ref(v_body_1306_);
v___x_1319_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1306_, v_a_1240_, v_a_1318_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v_a_1321_; uint8_t v___y_1323_; size_t v___x_1330_; size_t v___x_1331_; uint8_t v___x_1332_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
v_a_1321_ = lean_ctor_get(v___x_1319_, 1);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1319_, 2);
v___x_1330_ = lean_ptr_addr(v_binderType_1305_);
v___x_1331_ = lean_ptr_addr(v_a_1317_);
v___x_1332_ = lean_usize_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
v___y_1323_ = v___x_1332_;
goto v___jp_1322_;
}
else
{
size_t v___x_1333_; size_t v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_ptr_addr(v_body_1306_);
v___x_1334_ = lean_ptr_addr(v_a_1320_);
v___x_1335_ = lean_usize_dec_eq(v___x_1333_, v___x_1334_);
v___y_1323_ = v___x_1335_;
goto v___jp_1322_;
}
v___jp_1322_:
{
if (v___y_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_inc(v_binderName_1304_);
lean_dec_ref_known(v_e_1239_, 3);
v___x_1324_ = l_Lean_Expr_lam___override(v_binderName_1304_, v_a_1317_, v_a_1320_, v_binderInfo_1307_);
v___x_1325_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1324_, v_a_1321_);
return v___x_1325_;
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1307_, v_binderInfo_1307_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_inc(v_binderName_1304_);
lean_dec_ref_known(v_e_1239_, 3);
v___x_1327_ = l_Lean_Expr_lam___override(v_binderName_1304_, v_a_1317_, v_a_1320_, v_binderInfo_1307_);
v___x_1328_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1327_, v_a_1321_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; 
lean_dec(v_a_1320_);
lean_dec(v_a_1317_);
v___x_1329_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1239_, v_a_1321_);
return v___x_1329_;
}
}
}
}
else
{
lean_dec(v_a_1317_);
lean_dec_ref_known(v_e_1239_, 3);
v___y_1248_ = v___x_1319_;
goto v___jp_1247_;
}
}
else
{
lean_dec_ref_known(v_e_1239_, 3);
v___y_1248_ = v___x_1316_;
goto v___jp_1247_;
}
}
}
case 7:
{
lean_object* v_binderName_1336_; lean_object* v_binderType_1337_; lean_object* v_body_1338_; uint8_t v_binderInfo_1339_; lean_object* v___x_1340_; uint64_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; uint8_t v___x_1346_; 
v_binderName_1336_ = lean_ctor_get(v_e_1239_, 0);
v_binderType_1337_ = lean_ctor_get(v_e_1239_, 1);
v_body_1338_ = lean_ctor_get(v_e_1239_, 2);
v_binderInfo_1339_ = lean_ctor_get_uint8(v_e_1239_, sizeof(void*)*3 + 8);
v___x_1340_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1341_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1239_);
v___x_1342_ = lean_uint64_to_usize(v___x_1341_);
v___x_1343_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1241_, v___x_1342_, v_e_1239_, v___x_1340_);
v___x_1344_ = lean_ptr_addr(v___x_1343_);
v___x_1345_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1346_ = lean_usize_dec_eq(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref_known(v_e_1239_, 3);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1343_);
lean_ctor_set(v___x_1347_, 1, v_a_1241_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; 
lean_dec_ref(v___x_1343_);
lean_inc_ref(v_binderType_1337_);
v___x_1348_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_binderType_1337_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
v_a_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1348_, 2);
lean_inc_ref(v_body_1338_);
v___x_1351_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1338_, v_a_1240_, v_a_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_a_1353_; uint8_t v___y_1355_; size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
v_a_1353_ = lean_ctor_get(v___x_1351_, 1);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1351_, 2);
v___x_1362_ = lean_ptr_addr(v_binderType_1337_);
v___x_1363_ = lean_ptr_addr(v_a_1349_);
v___x_1364_ = lean_usize_dec_eq(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
v___y_1355_ = v___x_1364_;
goto v___jp_1354_;
}
else
{
size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = lean_ptr_addr(v_body_1338_);
v___x_1366_ = lean_ptr_addr(v_a_1352_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
v___y_1355_ = v___x_1367_;
goto v___jp_1354_;
}
v___jp_1354_:
{
if (v___y_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_inc(v_binderName_1336_);
lean_dec_ref_known(v_e_1239_, 3);
v___x_1356_ = l_Lean_Expr_forallE___override(v_binderName_1336_, v_a_1349_, v_a_1352_, v_binderInfo_1339_);
v___x_1357_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1356_, v_a_1353_);
return v___x_1357_;
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1339_, v_binderInfo_1339_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_inc(v_binderName_1336_);
lean_dec_ref_known(v_e_1239_, 3);
v___x_1359_ = l_Lean_Expr_forallE___override(v_binderName_1336_, v_a_1349_, v_a_1352_, v_binderInfo_1339_);
v___x_1360_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1359_, v_a_1353_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; 
lean_dec(v_a_1352_);
lean_dec(v_a_1349_);
v___x_1361_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1239_, v_a_1353_);
return v___x_1361_;
}
}
}
}
else
{
lean_dec(v_a_1349_);
lean_dec_ref_known(v_e_1239_, 3);
v___y_1258_ = v___x_1351_;
goto v___jp_1257_;
}
}
else
{
lean_dec_ref_known(v_e_1239_, 3);
v___y_1258_ = v___x_1348_;
goto v___jp_1257_;
}
}
}
case 8:
{
lean_object* v_declName_1368_; lean_object* v_type_1369_; lean_object* v_value_1370_; lean_object* v_body_1371_; uint8_t v_nondep_1372_; lean_object* v___x_1373_; uint64_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; 
v_declName_1368_ = lean_ctor_get(v_e_1239_, 0);
v_type_1369_ = lean_ctor_get(v_e_1239_, 1);
v_value_1370_ = lean_ctor_get(v_e_1239_, 2);
v_body_1371_ = lean_ctor_get(v_e_1239_, 3);
v_nondep_1372_ = lean_ctor_get_uint8(v_e_1239_, sizeof(void*)*4 + 8);
v___x_1373_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1374_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1239_);
v___x_1375_ = lean_uint64_to_usize(v___x_1374_);
v___x_1376_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1241_, v___x_1375_, v_e_1239_, v___x_1373_);
v___x_1377_ = lean_ptr_addr(v___x_1376_);
v___x_1378_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1379_ = lean_usize_dec_eq(v___x_1377_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref_known(v_e_1239_, 4);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1376_);
lean_ctor_set(v___x_1380_, 1, v_a_1241_);
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; 
lean_dec_ref(v___x_1376_);
lean_inc_ref(v_type_1369_);
v___x_1381_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_type_1369_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_a_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
v_a_1383_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1381_, 2);
lean_inc_ref(v_value_1370_);
v___x_1384_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_value_1370_, v_a_1240_, v_a_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
v_a_1386_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1384_, 2);
lean_inc_ref(v_body_1371_);
v___x_1387_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_body_1371_, v_a_1240_, v_a_1386_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v_a_1389_; uint8_t v___y_1391_; size_t v___x_1400_; size_t v___x_1401_; uint8_t v___x_1402_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
v_a_1389_ = lean_ctor_get(v___x_1387_, 1);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1387_, 2);
v___x_1400_ = lean_ptr_addr(v_type_1369_);
v___x_1401_ = lean_ptr_addr(v_a_1382_);
v___x_1402_ = lean_usize_dec_eq(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
v___y_1391_ = v___x_1402_;
goto v___jp_1390_;
}
else
{
size_t v___x_1403_; size_t v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_ptr_addr(v_value_1370_);
v___x_1404_ = lean_ptr_addr(v_a_1385_);
v___x_1405_ = lean_usize_dec_eq(v___x_1403_, v___x_1404_);
v___y_1391_ = v___x_1405_;
goto v___jp_1390_;
}
v___jp_1390_:
{
if (v___y_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_inc(v_declName_1368_);
lean_dec_ref_known(v_e_1239_, 4);
v___x_1392_ = l_Lean_Expr_letE___override(v_declName_1368_, v_a_1382_, v_a_1385_, v_a_1388_, v_nondep_1372_);
v___x_1393_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1392_, v_a_1389_);
return v___x_1393_;
}
else
{
size_t v___x_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_ptr_addr(v_body_1371_);
v___x_1395_ = lean_ptr_addr(v_a_1388_);
v___x_1396_ = lean_usize_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc(v_declName_1368_);
lean_dec_ref_known(v_e_1239_, 4);
v___x_1397_ = l_Lean_Expr_letE___override(v_declName_1368_, v_a_1382_, v_a_1385_, v_a_1388_, v_nondep_1372_);
v___x_1398_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1397_, v_a_1389_);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; 
lean_dec(v_a_1388_);
lean_dec(v_a_1385_);
lean_dec(v_a_1382_);
v___x_1399_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1239_, v_a_1389_);
return v___x_1399_;
}
}
}
}
else
{
lean_dec(v_a_1385_);
lean_dec(v_a_1382_);
lean_dec_ref_known(v_e_1239_, 4);
v___y_1243_ = v___x_1387_;
goto v___jp_1242_;
}
}
else
{
lean_dec(v_a_1382_);
lean_dec_ref_known(v_e_1239_, 4);
v___y_1243_ = v___x_1384_;
goto v___jp_1242_;
}
}
else
{
lean_dec_ref_known(v_e_1239_, 4);
v___y_1243_ = v___x_1381_;
goto v___jp_1242_;
}
}
}
case 10:
{
lean_object* v_data_1406_; lean_object* v_expr_1407_; lean_object* v___x_1408_; uint64_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; uint8_t v___x_1414_; 
v_data_1406_ = lean_ctor_get(v_e_1239_, 0);
v_expr_1407_ = lean_ctor_get(v_e_1239_, 1);
v___x_1408_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1409_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1239_);
v___x_1410_ = lean_uint64_to_usize(v___x_1409_);
v___x_1411_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1241_, v___x_1410_, v_e_1239_, v___x_1408_);
v___x_1412_ = lean_ptr_addr(v___x_1411_);
v___x_1413_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1414_ = lean_usize_dec_eq(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref_known(v_e_1239_, 2);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1411_);
lean_ctor_set(v___x_1415_, 1, v_a_1241_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; 
lean_dec_ref(v___x_1411_);
lean_inc_ref(v_expr_1407_);
v___x_1416_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_expr_1407_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v_a_1418_; size_t v___x_1419_; size_t v___x_1420_; uint8_t v___x_1421_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
v_a_1418_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1416_, 2);
v___x_1419_ = lean_ptr_addr(v_expr_1407_);
v___x_1420_ = lean_ptr_addr(v_a_1417_);
v___x_1421_ = lean_usize_dec_eq(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_inc(v_data_1406_);
lean_dec_ref_known(v_e_1239_, 2);
v___x_1422_ = l_Lean_Expr_mdata___override(v_data_1406_, v_a_1417_);
v___x_1423_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1422_, v_a_1418_);
return v___x_1423_;
}
else
{
lean_object* v___x_1424_; 
lean_dec(v_a_1417_);
v___x_1424_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1239_, v_a_1418_);
return v___x_1424_;
}
}
else
{
lean_dec_ref_known(v_e_1239_, 2);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1425_; lean_object* v_a_1426_; lean_object* v___x_1427_; 
v_a_1425_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1425_);
v_a_1426_ = lean_ctor_get(v___x_1416_, 1);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1416_, 2);
v___x_1427_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1425_, v_a_1426_);
return v___x_1427_;
}
else
{
return v___x_1416_;
}
}
}
}
case 11:
{
lean_object* v_typeName_1428_; lean_object* v_idx_1429_; lean_object* v_struct_1430_; lean_object* v___x_1431_; uint64_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v_typeName_1428_ = lean_ctor_get(v_e_1239_, 0);
v_idx_1429_ = lean_ctor_get(v_e_1239_, 1);
v_struct_1430_ = lean_ctor_get(v_e_1239_, 2);
v___x_1431_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_dummy;
v___x_1432_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_1239_);
v___x_1433_ = lean_uint64_to_usize(v___x_1432_);
v___x_1434_ = l_Lean_PersistentHashMap_findKeyDAux___at___00__private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1241_, v___x_1433_, v_e_1239_, v___x_1431_);
v___x_1435_ = lean_ptr_addr(v___x_1434_);
v___x_1436_ = lean_usize_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_save___redArg___closed__0);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
lean_dec_ref_known(v_e_1239_, 3);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1434_);
lean_ctor_set(v___x_1438_, 1, v_a_1241_);
return v___x_1438_;
}
else
{
uint8_t v_checkProj_1439_; 
lean_dec_ref(v___x_1434_);
v_checkProj_1439_ = lean_ctor_get_uint8(v_a_1240_, sizeof(void*)*1 + 1);
if (v_checkProj_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_inc_ref(v_struct_1430_);
v___x_1440_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_struct_1430_, v_a_1240_, v_a_1241_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v_a_1442_; size_t v___x_1443_; size_t v___x_1444_; uint8_t v___x_1445_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
v_a_1442_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1440_, 2);
v___x_1443_ = lean_ptr_addr(v_struct_1430_);
v___x_1444_ = lean_ptr_addr(v_a_1441_);
v___x_1445_ = lean_usize_dec_eq(v___x_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_inc(v_idx_1429_);
lean_inc(v_typeName_1428_);
lean_dec_ref_known(v_e_1239_, 3);
v___x_1446_ = l_Lean_Expr_proj___override(v_typeName_1428_, v_idx_1429_, v_a_1441_);
v___x_1447_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v___x_1446_, v_a_1442_);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; 
lean_dec(v_a_1441_);
v___x_1448_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1239_, v_a_1442_);
return v___x_1448_;
}
}
else
{
lean_dec_ref_known(v_e_1239_, 3);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1449_; lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1449_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1449_);
v_a_1450_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1440_, 2);
v___x_1451_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1449_, v_a_1450_);
return v___x_1451_;
}
else
{
return v___x_1440_;
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref_known(v_e_1239_, 3);
v___x_1452_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1, &l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1_once, _init_l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___closed__1);
v___x_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v_a_1241_);
return v___x_1453_;
}
}
}
default: 
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_e_1239_, v_a_1241_);
return v___x_1454_;
}
}
v___jp_1242_:
{
if (lean_obj_tag(v___y_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1244_ = lean_ctor_get(v___y_1243_, 0);
lean_inc(v_a_1244_);
v_a_1245_ = lean_ctor_get(v___y_1243_, 1);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___y_1243_, 2);
v___x_1246_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1244_, v_a_1245_);
return v___x_1246_;
}
else
{
return v___y_1243_;
}
}
v___jp_1247_:
{
if (lean_obj_tag(v___y_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___y_1248_, 0);
lean_inc(v_a_1249_);
v_a_1250_ = lean_ctor_get(v___y_1248_, 1);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___y_1248_, 2);
v___x_1251_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1249_, v_a_1250_);
return v___x_1251_;
}
else
{
return v___y_1248_;
}
}
v___jp_1252_:
{
if (lean_obj_tag(v___y_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v_a_1255_; lean_object* v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___y_1253_, 0);
lean_inc(v_a_1254_);
v_a_1255_ = lean_ctor_get(v___y_1253_, 1);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___y_1253_, 2);
v___x_1256_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1254_, v_a_1255_);
return v___x_1256_;
}
else
{
return v___y_1253_;
}
}
v___jp_1257_:
{
if (lean_obj_tag(v___y_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v_a_1260_; lean_object* v___x_1261_; 
v_a_1259_ = lean_ctor_get(v___y_1258_, 0);
lean_inc(v_a_1259_);
v_a_1260_ = lean_ctor_get(v___y_1258_, 1);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___y_1258_, 2);
v___x_1261_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_saveInc___redArg(v_a_1259_, v_a_1260_);
return v___x_1261_;
}
else
{
return v___y_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go___boxed(lean_object* v_e_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1455_, v_a_1456_, v_a_1457_);
lean_dec_ref(v_a_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc(lean_object* v_e_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_1459_, v_a_1460_, v_a_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_shareCommonAlphaInc___boxed(lean_object* v_e_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_Sym_shareCommonAlphaInc(v_e_1463_, v_a_1464_, v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1466_;
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

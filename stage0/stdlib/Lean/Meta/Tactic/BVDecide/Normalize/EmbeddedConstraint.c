// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint
// Imports: public import Std.Tactic.BVDecide.Normalize.Bool public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_false_of_not_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 197, 166, 197, 7, 119, 67, 87)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(123, 183, 41, 160, 188, 151, 196, 147)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Chose min depth at: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__0_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "embeddedConstraintSubstitution"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__2_value),LEAN_SCALAR_PTR_LITERAL(152, 224, 35, 207, 121, 34, 254, 217)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__3_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1_, lean_object* v_vals_2_, lean_object* v_i_3_, lean_object* v_k_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_array_get_size(v_keys_1_);
v___x_6_ = lean_nat_dec_lt(v_i_3_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
lean_dec(v_i_3_);
v___x_7_ = lean_box(0);
return v___x_7_;
}
else
{
lean_object* v_k_x27_8_; size_t v___x_9_; size_t v___x_10_; uint8_t v___x_11_; 
v_k_x27_8_ = lean_array_fget_borrowed(v_keys_1_, v_i_3_);
v___x_9_ = lean_ptr_addr(v_k_4_);
v___x_10_ = lean_ptr_addr(v_k_x27_8_);
v___x_11_ = lean_usize_dec_eq(v___x_9_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_add(v_i_3_, v___x_12_);
lean_dec(v_i_3_);
v_i_3_ = v___x_13_;
goto _start;
}
else
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_array_fget_borrowed(v_vals_2_, v_i_3_);
lean_dec(v_i_3_);
lean_inc(v___x_15_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_17_, lean_object* v_vals_18_, lean_object* v_i_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg(v_keys_17_, v_vals_18_, v_i_19_, v_k_20_);
lean_dec_ref(v_k_20_);
lean_dec_ref(v_vals_18_);
lean_dec_ref(v_keys_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(lean_object* v_x_22_, size_t v_x_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_22_) == 0)
{
lean_object* v_es_25_; lean_object* v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v_j_29_; lean_object* v___x_30_; 
v_es_25_ = lean_ctor_get(v_x_22_, 0);
v___x_26_ = lean_box(2);
v___x_27_ = ((size_t)31ULL);
v___x_28_ = lean_usize_land(v_x_23_, v___x_27_);
v_j_29_ = lean_usize_to_nat(v___x_28_);
v___x_30_ = lean_array_get_borrowed(v___x_26_, v_es_25_, v_j_29_);
lean_dec(v_j_29_);
switch(lean_obj_tag(v___x_30_))
{
case 0:
{
lean_object* v_key_31_; lean_object* v_val_32_; size_t v___x_33_; size_t v___x_34_; uint8_t v___x_35_; 
v_key_31_ = lean_ctor_get(v___x_30_, 0);
v_val_32_ = lean_ctor_get(v___x_30_, 1);
v___x_33_ = lean_ptr_addr(v_x_24_);
v___x_34_ = lean_ptr_addr(v_key_31_);
v___x_35_ = lean_usize_dec_eq(v___x_33_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(0);
return v___x_36_;
}
else
{
lean_object* v___x_37_; 
lean_inc(v_val_32_);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v_val_32_);
return v___x_37_;
}
}
case 1:
{
lean_object* v_node_38_; size_t v___x_39_; size_t v___x_40_; 
v_node_38_ = lean_ctor_get(v___x_30_, 0);
v___x_39_ = ((size_t)5ULL);
v___x_40_ = lean_usize_shift_right(v_x_23_, v___x_39_);
v_x_22_ = v_node_38_;
v_x_23_ = v___x_40_;
goto _start;
}
default: 
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
}
else
{
lean_object* v_ks_43_; lean_object* v_vs_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_ks_43_ = lean_ctor_get(v_x_22_, 0);
v_vs_44_ = lean_ctor_get(v_x_22_, 1);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg(v_ks_43_, v_vs_44_, v___x_45_, v_x_24_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg___boxed(lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
size_t v_x_3077__boxed_50_; lean_object* v_res_51_; 
v_x_3077__boxed_50_ = lean_unbox_usize(v_x_48_);
lean_dec(v_x_48_);
v_res_51_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_47_, v_x_3077__boxed_50_, v_x_49_);
lean_dec_ref(v_x_49_);
lean_dec_ref(v_x_47_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
size_t v___x_54_; size_t v___x_55_; size_t v___x_56_; uint64_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v___x_54_ = lean_ptr_addr(v_x_53_);
v___x_55_ = ((size_t)3ULL);
v___x_56_ = lean_usize_shift_right(v___x_54_, v___x_55_);
v___x_57_ = lean_usize_to_uint64(v___x_56_);
v___x_58_ = lean_uint64_to_usize(v___x_57_);
v___x_59_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_52_, v___x_58_, v_x_53_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg___boxed(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(v_x_60_, v_x_61_);
lean_dec_ref(v_x_61_);
lean_dec_ref(v_x_60_);
return v_res_62_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2));
v___x_70_ = l_Lean_mkConst(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5));
v___x_77_ = l_Lean_mkConst(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_box(0);
v___x_91_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12));
v___x_92_ = l_Lean_mkConst(v___x_91_, v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(uint32_t v_minDepth_93_, lean_object* v_hypMap_94_, lean_object* v_e_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = l_Lean_Expr_approxDepth(v_e_95_);
v___x_104_ = lean_uint32_dec_lt(v___x_103_, v_minDepth_93_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(v_hypMap_94_, v_e_95_);
if (lean_obj_tag(v___x_105_) == 1)
{
lean_object* v_val_106_; lean_object* v_proof_107_; uint8_t v_negated_108_; uint8_t v___x_109_; 
v_val_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v___x_105_, 1);
v_proof_107_ = lean_ctor_get(v_val_106_, 0);
lean_inc_ref(v_proof_107_);
v_negated_108_ = lean_ctor_get_uint8(v_val_106_, sizeof(void*)*1);
lean_dec(v_val_106_);
v___x_109_ = 1;
if (v_negated_108_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec_ref(v_e_95_);
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3);
v___x_111_ = l_Lean_Meta_Sym_shareCommonInc(v___x_110_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_116_, 0, v_a_112_);
lean_ctor_set(v___x_116_, 1, v_proof_107_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*2, v___x_109_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*2 + 1, v_negated_108_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref(v_proof_107_);
v_a_121_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_111_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_111_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6);
v___x_130_ = l_Lean_Meta_Sym_shareCommonInc(v___x_129_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_141_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_141_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_141_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_141_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v_proof_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13);
v_proof_136_ = l_Lean_mkAppB(v___x_135_, v_e_95_, v_proof_107_);
v___x_137_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_137_, 0, v_a_131_);
lean_ctor_set(v___x_137_, 1, v_proof_136_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*2, v___x_109_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*2 + 1, v___x_104_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_137_);
v___x_139_ = v___x_133_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec_ref(v_proof_107_);
lean_dec_ref(v_e_95_);
v_a_142_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_130_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_130_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v___x_105_);
lean_dec_ref(v_e_95_);
v___x_150_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_150_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_150_, 1, v___x_104_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
else
{
uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v_e_95_);
v___x_152_ = 0;
v___x_153_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_153_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___boxed(lean_object* v_minDepth_155_, lean_object* v_hypMap_156_, lean_object* v_e_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
uint32_t v_minDepth_boxed_165_; lean_object* v_res_166_; 
v_minDepth_boxed_165_ = lean_unbox_uint32(v_minDepth_155_);
lean_dec(v_minDepth_155_);
v_res_166_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(v_minDepth_boxed_165_, v_hypMap_156_, v_e_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec_ref(v_hypMap_156_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc(uint32_t v_minDepth_167_, lean_object* v_hypMap_168_, lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(v_minDepth_167_, v_hypMap_168_, v_e_169_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed(lean_object* v_minDepth_181_, lean_object* v_hypMap_182_, lean_object* v_e_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
uint32_t v_minDepth_boxed_194_; lean_object* v_res_195_; 
v_minDepth_boxed_194_ = lean_unbox_uint32(v_minDepth_181_);
lean_dec(v_minDepth_181_);
v_res_195_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc(v_minDepth_boxed_194_, v_hypMap_182_, v_e_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_hypMap_182_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0(lean_object* v_00_u03b2_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(v_x_197_, v_x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___boxed(lean_object* v_00_u03b2_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0(v_00_u03b2_200_, v_x_201_, v_x_202_);
lean_dec_ref(v_x_202_);
lean_dec_ref(v_x_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0(lean_object* v_00_u03b2_204_, lean_object* v_x_205_, size_t v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_205_, v_x_206_, v_x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_209_, lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
size_t v_x_3355__boxed_213_; lean_object* v_res_214_; 
v_x_3355__boxed_213_ = lean_unbox_usize(v_x_211_);
lean_dec(v_x_211_);
v_res_214_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0(v_00_u03b2_209_, v_x_210_, v_x_3355__boxed_213_, v_x_212_);
lean_dec_ref(v_x_212_);
lean_dec_ref(v_x_210_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_215_, lean_object* v_keys_216_, lean_object* v_vals_217_, lean_object* v_heq_218_, lean_object* v_i_219_, lean_object* v_k_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg(v_keys_216_, v_vals_217_, v_i_219_, v_k_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_222_, lean_object* v_keys_223_, lean_object* v_vals_224_, lean_object* v_heq_225_, lean_object* v_i_226_, lean_object* v_k_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1(v_00_u03b2_222_, v_keys_223_, v_vals_224_, v_heq_225_, v_i_226_, v_k_227_);
lean_dec_ref(v_k_227_);
lean_dec_ref(v_vals_224_);
lean_dec_ref(v_keys_223_);
return v_res_228_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(lean_object* v_x_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg___boxed(lean_object* v_x_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_x_231_);
lean_dec_ref(v_x_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(lean_object* v_00_u03b2_234_, lean_object* v_x_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___boxed(lean_object* v_00_u03b2_237_, lean_object* v_x_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(v_00_u03b2_237_, v_x_238_);
lean_dec_ref(v_x_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___lam__0(lean_object* v_x_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
lean_inc(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
v___x_254_ = lean_apply_12(v_x_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, lean_box(0));
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___lam__0___boxed(lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___lam__0(v_x_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg(lean_object* v_mvarId_269_, lean_object* v_x_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___f_283_; lean_object* v___x_284_; 
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc(v___y_275_);
lean_inc_ref(v___y_274_);
lean_inc(v___y_273_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
v___f_283_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_283_, 0, v_x_270_);
lean_closure_set(v___f_283_, 1, v___y_271_);
lean_closure_set(v___f_283_, 2, v___y_272_);
lean_closure_set(v___f_283_, 3, v___y_273_);
lean_closure_set(v___f_283_, 4, v___y_274_);
lean_closure_set(v___f_283_, 5, v___y_275_);
lean_closure_set(v___f_283_, 6, v___y_276_);
lean_closure_set(v___f_283_, 7, v___y_277_);
v___x_284_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_269_, v___f_283_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_284_) == 0)
{
return v___x_284_;
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg___boxed(lean_object* v_mvarId_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg(v_mvarId_293_, v_x_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12(lean_object* v_00_u03b1_308_, lean_object* v_mvarId_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg(v_mvarId_309_, v_x_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___boxed(lean_object* v_00_u03b1_324_, lean_object* v_mvarId_325_, lean_object* v_x_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12(v_00_u03b1_324_, v_mvarId_325_, v_x_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(uint8_t v___x_340_, lean_object* v___f_341_, lean_object* v_____r_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_caches_356_; lean_object* v_typeAnalysis_357_; lean_object* v_target_358_; lean_object* v_hypotheses_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_369_; 
v___x_355_ = lean_st_ref_take(v___y_344_);
v_caches_356_ = lean_ctor_get(v___x_355_, 0);
v_typeAnalysis_357_ = lean_ctor_get(v___x_355_, 1);
v_target_358_ = lean_ctor_get(v___x_355_, 2);
v_hypotheses_359_ = lean_ctor_get(v___x_355_, 3);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_369_ == 0)
{
v___x_361_ = v___x_355_;
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_hypotheses_359_);
lean_inc(v_target_358_);
lean_inc(v_typeAnalysis_357_);
lean_inc(v_caches_356_);
lean_dec(v___x_355_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_caches_356_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_typeAnalysis_357_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_target_358_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_hypotheses_359_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*4, v___x_340_);
v___x_365_ = lean_st_ref_put(v___y_344_, v___x_364_);
v___x_366_ = lean_box(0);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
lean_inc(v___y_351_);
lean_inc_ref(v___y_350_);
lean_inc(v___y_349_);
lean_inc_ref(v___y_348_);
lean_inc(v___y_347_);
lean_inc_ref(v___y_346_);
lean_inc(v___y_345_);
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
v___x_367_ = lean_apply_13(v___f_341_, v___x_366_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, lean_box(0));
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed(lean_object* v___x_370_, lean_object* v___f_371_, lean_object* v_____r_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
uint8_t v___x_110027__boxed_385_; lean_object* v_res_386_; 
v___x_110027__boxed_385_ = lean_unbox(v___x_370_);
v_res_386_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(v___x_110027__boxed_385_, v___f_371_, v_____r_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(lean_object* v_m_387_, lean_object* v_query_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
lean_object* v_zero_392_; uint8_t v_isZero_393_; 
v_zero_392_ = lean_unsigned_to_nat(0u);
v_isZero_393_ = lean_nat_dec_eq(v_x_390_, v_zero_392_);
if (v_isZero_393_ == 1)
{
lean_dec(v_x_391_);
lean_dec(v_x_390_);
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_box(2);
return v___x_394_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
v_val_395_ = lean_ctor_get(v_x_389_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_389_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v_x_389_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_val_395_);
lean_dec(v_x_389_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_val_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_keyArray_403_; lean_object* v_valueArray_404_; lean_object* v___x_405_; uint8_t v_isSome_406_; 
v_keyArray_403_ = lean_ctor_get(v_m_387_, 1);
v_valueArray_404_ = lean_ctor_get(v_m_387_, 2);
v___x_405_ = lean_array_fget_borrowed(v_keyArray_403_, v_x_391_);
v_isSome_406_ = lean_noption_is_some(v___x_405_);
if (v_isSome_406_ == 0)
{
lean_dec(v_x_390_);
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v_x_391_);
return v___x_407_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec(v_x_391_);
v_val_408_ = lean_ctor_get(v_x_389_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_389_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v_x_389_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_val_408_);
lean_dec(v_x_389_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_val_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v_one_416_; lean_object* v_n_417_; lean_object* v___y_419_; 
v_one_416_ = lean_unsigned_to_nat(1u);
v_n_417_ = lean_nat_sub(v_x_390_, v_one_416_);
lean_dec(v_x_390_);
if (v_isSome_406_ == 0)
{
goto v___jp_425_;
}
else
{
lean_object* v___x_427_; uint8_t v_isSome_428_; 
v___x_427_ = lean_array_fget_borrowed(v_valueArray_404_, v_x_391_);
v_isSome_428_ = lean_noption_is_some(v___x_427_);
if (v_isSome_428_ == 0)
{
goto v___jp_425_;
}
else
{
lean_object* v_val_429_; uint8_t v___x_430_; 
lean_inc(v___x_405_);
v_val_429_ = lean_noption_get(v___x_405_);
v___x_430_ = lean_nat_dec_eq(v_val_429_, v_query_388_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
lean_dec(v_val_429_);
v___x_431_ = lean_array_get_size(v_keyArray_403_);
v___x_432_ = lean_nat_add(v_x_391_, v_one_416_);
lean_dec(v_x_391_);
v___x_433_ = lean_nat_dec_lt(v___x_432_, v___x_431_);
if (v___x_433_ == 0)
{
lean_dec(v___x_432_);
v_x_390_ = v_n_417_;
v_x_391_ = v_zero_392_;
goto _start;
}
else
{
v_x_390_ = v_n_417_;
v_x_391_ = v___x_432_;
goto _start;
}
}
else
{
lean_object* v_val_436_; lean_object* v___x_437_; 
lean_dec(v_n_417_);
lean_dec(v_x_389_);
lean_inc(v___x_427_);
v_val_436_ = lean_noption_get(v___x_427_);
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v_x_391_);
lean_ctor_set(v___x_437_, 1, v_val_429_);
lean_ctor_set(v___x_437_, 2, v_val_436_);
return v___x_437_;
}
}
}
v___jp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_array_get_size(v_keyArray_403_);
v___x_421_ = lean_nat_add(v_x_391_, v_one_416_);
lean_dec(v_x_391_);
v___x_422_ = lean_nat_dec_lt(v___x_421_, v___x_420_);
if (v___x_422_ == 0)
{
lean_dec(v___x_421_);
v_x_389_ = v___y_419_;
v_x_390_ = v_n_417_;
v_x_391_ = v_zero_392_;
goto _start;
}
else
{
v_x_389_ = v___y_419_;
v_x_390_ = v_n_417_;
v_x_391_ = v___x_421_;
goto _start;
}
}
v___jp_425_:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v___x_426_; 
lean_inc(v_x_391_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_x_391_);
v___y_419_ = v___x_426_;
goto v___jp_418_;
}
else
{
v___y_419_ = v_x_389_;
goto v___jp_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg___boxed(lean_object* v_m_438_, lean_object* v_query_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_m_438_, v_query_439_, v_x_440_, v_x_441_, v_x_442_);
lean_dec(v_query_439_);
lean_dec_ref(v_m_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(lean_object* v_m_444_, lean_object* v_query_445_){
_start:
{
lean_object* v_keyArray_446_; lean_object* v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v_fold_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_keyArray_446_ = lean_ctor_get(v_m_444_, 1);
v___x_447_ = lean_array_get_size(v_keyArray_446_);
v___x_448_ = lean_uint64_of_nat(v_query_445_);
v___x_449_ = 32ULL;
v___x_450_ = lean_uint64_shift_right(v___x_448_, v___x_449_);
v_fold_451_ = lean_uint64_xor(v___x_448_, v___x_450_);
v___x_452_ = 16ULL;
v___x_453_ = lean_uint64_shift_right(v_fold_451_, v___x_452_);
v___x_454_ = lean_uint64_xor(v_fold_451_, v___x_453_);
v___x_455_ = lean_uint64_to_usize(v___x_454_);
v___x_456_ = lean_usize_of_nat(v___x_447_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_sub(v___x_456_, v___x_457_);
v___x_459_ = lean_usize_land(v___x_455_, v___x_458_);
v___x_460_ = lean_usize_to_nat(v___x_459_);
v___x_461_ = lean_box(0);
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_m_444_, v_query_445_, v___x_461_, v___x_447_, v___x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg___boxed(lean_object* v_m_463_, lean_object* v_query_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_m_463_, v_query_464_);
lean_dec(v_query_464_);
lean_dec_ref(v_m_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(lean_object* v_m_466_, lean_object* v_query_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_m_466_, v_query_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_index_469_; lean_object* v_key_470_; lean_object* v_value_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_index_469_ = lean_ctor_get(v___x_468_, 0);
v_key_470_ = lean_ctor_get(v___x_468_, 1);
v_value_471_ = lean_ctor_get(v___x_468_, 2);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_468_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_value_471_);
lean_inc(v_key_470_);
lean_inc(v_index_469_);
lean_dec(v___x_468_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_index_469_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_key_470_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_value_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v___x_468_);
v___x_479_ = lean_box(1);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg___boxed(lean_object* v_m_480_, lean_object* v_query_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_m_480_, v_query_481_);
lean_dec(v_query_481_);
lean_dec_ref(v_m_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(lean_object* v_m_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_m_483_, v_a_484_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_value_486_; lean_object* v___x_487_; 
v_value_486_ = lean_ctor_get(v___x_485_, 2);
lean_inc(v_value_486_);
lean_dec_ref_known(v___x_485_, 3);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_value_486_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_box(0);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(lean_object* v_m_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_m_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(uint8_t v___x_492_, lean_object* v_x_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_504_, 0, v___x_492_);
lean_ctor_set_uint8(v___x_504_, 1, v___x_492_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed(lean_object* v___x_506_, lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v___x_110246__boxed_518_; lean_object* v_res_519_; 
v___x_110246__boxed_518_ = lean_unbox(v___x_506_);
v_res_519_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(v___x_110246__boxed_518_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_x_507_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(lean_object* v_snd_520_, lean_object* v_a_521_, lean_object* v___x_522_, lean_object* v_____r_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_536_ = lean_array_push(v_snd_520_, v_a_521_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_522_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed(lean_object* v_snd_540_, lean_object* v_a_541_, lean_object* v___x_542_, lean_object* v_____r_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_540_, v_a_541_, v___x_542_, v_____r_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(lean_object* v_msgData_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; lean_object* v_env_564_; lean_object* v___x_565_; lean_object* v_mctx_566_; lean_object* v_lctx_567_; lean_object* v_options_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_563_ = lean_st_ref_get(v___y_561_);
v_env_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_env_564_);
lean_dec(v___x_563_);
v___x_565_ = lean_st_ref_get(v___y_559_);
v_mctx_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_mctx_566_);
lean_dec(v___x_565_);
v_lctx_567_ = lean_ctor_get(v___y_558_, 2);
v_options_568_ = lean_ctor_get(v___y_560_, 2);
lean_inc_ref(v_options_568_);
lean_inc_ref(v_lctx_567_);
v___x_569_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_569_, 0, v_env_564_);
lean_ctor_set(v___x_569_, 1, v_mctx_566_);
lean_ctor_set(v___x_569_, 2, v_lctx_567_);
lean_ctor_set(v___x_569_, 3, v_options_568_);
v___x_570_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v_msgData_557_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1___boxed(lean_object* v_msgData_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msgData_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_578_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_579_; double v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_float_of_nat(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(lean_object* v_cls_584_, lean_object* v_msg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_ref_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_637_; 
v_ref_591_ = lean_ctor_get(v___y_588_, 5);
v___x_592_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msg_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_637_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_637_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_637_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_traceState_598_; lean_object* v_env_599_; lean_object* v_nextMacroScope_600_; lean_object* v_ngen_601_; lean_object* v_auxDeclNGen_602_; lean_object* v_cache_603_; lean_object* v_messages_604_; lean_object* v_infoState_605_; lean_object* v_snapshotTasks_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_636_; 
v___x_597_ = lean_st_ref_take(v___y_589_);
v_traceState_598_ = lean_ctor_get(v___x_597_, 4);
v_env_599_ = lean_ctor_get(v___x_597_, 0);
v_nextMacroScope_600_ = lean_ctor_get(v___x_597_, 1);
v_ngen_601_ = lean_ctor_get(v___x_597_, 2);
v_auxDeclNGen_602_ = lean_ctor_get(v___x_597_, 3);
v_cache_603_ = lean_ctor_get(v___x_597_, 5);
v_messages_604_ = lean_ctor_get(v___x_597_, 6);
v_infoState_605_ = lean_ctor_get(v___x_597_, 7);
v_snapshotTasks_606_ = lean_ctor_get(v___x_597_, 8);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_636_ == 0)
{
v___x_608_ = v___x_597_;
v_isShared_609_ = v_isSharedCheck_636_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snapshotTasks_606_);
lean_inc(v_infoState_605_);
lean_inc(v_messages_604_);
lean_inc(v_cache_603_);
lean_inc(v_traceState_598_);
lean_inc(v_auxDeclNGen_602_);
lean_inc(v_ngen_601_);
lean_inc(v_nextMacroScope_600_);
lean_inc(v_env_599_);
lean_dec(v___x_597_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_636_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint64_t v_tid_610_; lean_object* v_traces_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_635_; 
v_tid_610_ = lean_ctor_get_uint64(v_traceState_598_, sizeof(void*)*1);
v_traces_611_ = lean_ctor_get(v_traceState_598_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_traceState_598_);
if (v_isSharedCheck_635_ == 0)
{
v___x_613_ = v_traceState_598_;
v_isShared_614_ = v_isSharedCheck_635_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_traces_611_);
lean_dec(v_traceState_598_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_635_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; double v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_615_ = lean_box(0);
v___x_616_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0);
v___x_617_ = 0;
v___x_618_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1));
v___x_619_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_619_, 0, v_cls_584_);
lean_ctor_set(v___x_619_, 1, v___x_615_);
lean_ctor_set(v___x_619_, 2, v___x_618_);
lean_ctor_set_float(v___x_619_, sizeof(void*)*3, v___x_616_);
lean_ctor_set_float(v___x_619_, sizeof(void*)*3 + 8, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3 + 16, v___x_617_);
v___x_620_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2));
v___x_621_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v_a_593_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_inc(v_ref_591_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_ref_591_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_PersistentArray_push___redArg(v_traces_611_, v___x_622_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_623_);
v___x_625_ = v___x_613_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_623_);
lean_ctor_set_uint64(v_reuseFailAlloc_634_, sizeof(void*)*1, v_tid_610_);
v___x_625_ = v_reuseFailAlloc_634_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 4, v___x_625_);
v___x_627_ = v___x_608_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_env_599_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_nextMacroScope_600_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_ngen_601_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_auxDeclNGen_602_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_633_, 5, v_cache_603_);
lean_ctor_set(v_reuseFailAlloc_633_, 6, v_messages_604_);
lean_ctor_set(v_reuseFailAlloc_633_, 7, v_infoState_605_);
lean_ctor_set(v_reuseFailAlloc_633_, 8, v_snapshotTasks_606_);
v___x_627_ = v_reuseFailAlloc_633_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_st_ref_put(v___y_589_, v___x_627_);
v___x_629_ = lean_box(0);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_629_);
v___x_631_ = v___x_595_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___boxed(lean_object* v_cls_638_, lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_638_, v_msg_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__16(lean_object* v_xs_646_, lean_object* v_v_647_, lean_object* v_i_648_){
_start:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_array_get_size(v_xs_646_);
v___x_650_ = lean_nat_dec_lt(v_i_648_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec(v_i_648_);
v___x_651_ = lean_box(0);
return v___x_651_;
}
else
{
lean_object* v___x_652_; size_t v___x_653_; size_t v___x_654_; uint8_t v___x_655_; 
v___x_652_ = lean_array_fget_borrowed(v_xs_646_, v_i_648_);
v___x_653_ = lean_ptr_addr(v___x_652_);
v___x_654_ = lean_ptr_addr(v_v_647_);
v___x_655_ = lean_usize_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_i_648_, v___x_656_);
lean_dec(v_i_648_);
v_i_648_ = v___x_657_;
goto _start;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v_i_648_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__16___boxed(lean_object* v_xs_660_, lean_object* v_v_661_, lean_object* v_i_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__16(v_xs_660_, v_v_661_, v_i_662_);
lean_dec_ref(v_v_661_);
lean_dec_ref(v_xs_660_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(lean_object* v_xs_664_, lean_object* v_v_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__16(v_xs_664_, v_v_665_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7___boxed(lean_object* v_xs_668_, lean_object* v_v_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(v_xs_668_, v_v_669_);
lean_dec_ref(v_v_669_);
lean_dec_ref(v_xs_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(lean_object* v_x_671_, size_t v_x_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v_es_674_; lean_object* v___x_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v_j_678_; lean_object* v_entry_679_; 
v_es_674_ = lean_ctor_get(v_x_671_, 0);
v___x_675_ = lean_box(2);
v___x_676_ = ((size_t)31ULL);
v___x_677_ = lean_usize_land(v_x_672_, v___x_676_);
v_j_678_ = lean_usize_to_nat(v___x_677_);
v_entry_679_ = lean_array_get(v___x_675_, v_es_674_, v_j_678_);
switch(lean_obj_tag(v_entry_679_))
{
case 0:
{
lean_object* v_key_680_; size_t v___x_681_; size_t v___x_682_; uint8_t v___x_683_; 
v_key_680_ = lean_ctor_get(v_entry_679_, 0);
lean_inc(v_key_680_);
lean_dec_ref_known(v_entry_679_, 2);
v___x_681_ = lean_ptr_addr(v_x_673_);
v___x_682_ = lean_ptr_addr(v_key_680_);
lean_dec(v_key_680_);
v___x_683_ = lean_usize_dec_eq(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec(v_j_678_);
return v_x_671_;
}
else
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_691_; 
lean_inc_ref(v_es_674_);
v_isSharedCheck_691_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v_x_671_, 0);
lean_dec(v_unused_692_);
v___x_685_ = v_x_671_;
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
else
{
lean_dec(v_x_671_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_array_set(v_es_674_, v_j_678_, v___x_675_);
lean_dec(v_j_678_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
case 1:
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_727_; 
lean_inc_ref(v_es_674_);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_x_671_, 0);
lean_dec(v_unused_728_);
v___x_694_ = v_x_671_;
v_isShared_695_ = v_isSharedCheck_727_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_x_671_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_727_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_node_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_726_; 
v_node_696_ = lean_ctor_get(v_entry_679_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_entry_679_);
if (v_isSharedCheck_726_ == 0)
{
v___x_698_ = v_entry_679_;
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_node_696_);
lean_dec(v_entry_679_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
size_t v___x_700_; lean_object* v_entries_701_; size_t v___x_702_; lean_object* v_newNode_703_; lean_object* v___x_704_; 
v___x_700_ = ((size_t)5ULL);
v_entries_701_ = lean_array_set(v_es_674_, v_j_678_, v___x_675_);
v___x_702_ = lean_usize_shift_right(v_x_672_, v___x_700_);
v_newNode_703_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_node_696_, v___x_702_, v_x_673_);
lean_inc_ref(v_newNode_703_);
v___x_704_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_706_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_newNode_703_);
v___x_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_newNode_703_);
v___x_706_ = v_reuseFailAlloc_711_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_array_set(v_entries_701_, v_j_678_, v___x_706_);
lean_dec(v_j_678_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_707_);
v___x_709_ = v___x_694_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_val_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_newNode_703_);
lean_del_object(v___x_698_);
v_val_712_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_712_);
lean_dec_ref_known(v___x_704_, 1);
v_fst_713_ = lean_ctor_get(v_val_712_, 0);
v_snd_714_ = lean_ctor_get(v_val_712_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_val_712_);
if (v_isSharedCheck_725_ == 0)
{
v___x_716_ = v_val_712_;
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v_val_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_713_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_snd_714_);
v___x_719_ = v_reuseFailAlloc_724_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_array_set(v_entries_701_, v_j_678_, v___x_719_);
lean_dec(v_j_678_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_720_);
v___x_722_ = v___x_694_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_678_);
return v_x_671_;
}
}
}
else
{
lean_object* v_ks_729_; lean_object* v_vs_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_744_; 
v_ks_729_ = lean_ctor_get(v_x_671_, 0);
v_vs_730_ = lean_ctor_get(v_x_671_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_744_ == 0)
{
v___x_732_ = v_x_671_;
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_vs_730_);
lean_inc(v_ks_729_);
lean_dec(v_x_671_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_744_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; 
v___x_734_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(v_ks_729_, v_x_673_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_736_; 
if (v_isShared_733_ == 0)
{
v___x_736_ = v___x_732_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_ks_729_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_vs_730_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_object* v_val_738_; lean_object* v_keys_x27_739_; lean_object* v_vals_x27_740_; lean_object* v___x_742_; 
v_val_738_ = lean_ctor_get(v___x_734_, 0);
lean_inc_n(v_val_738_, 2);
lean_dec_ref_known(v___x_734_, 1);
v_keys_x27_739_ = l_Array_eraseIdx___redArg(v_ks_729_, v_val_738_);
v_vals_x27_740_ = l_Array_eraseIdx___redArg(v_vs_730_, v_val_738_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v_vals_x27_740_);
lean_ctor_set(v___x_732_, 0, v_keys_x27_739_);
v___x_742_ = v___x_732_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_keys_x27_739_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_vals_x27_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg___boxed(lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
size_t v_x_110492__boxed_748_; lean_object* v_res_749_; 
v_x_110492__boxed_748_ = lean_unbox_usize(v_x_746_);
lean_dec(v_x_746_);
v_res_749_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_745_, v_x_110492__boxed_748_, v_x_747_);
lean_dec_ref(v_x_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
size_t v___x_752_; size_t v___x_753_; size_t v___x_754_; uint64_t v___x_755_; size_t v_h_756_; lean_object* v___x_757_; 
v___x_752_ = lean_ptr_addr(v_x_751_);
v___x_753_ = ((size_t)3ULL);
v___x_754_ = lean_usize_shift_right(v___x_752_, v___x_753_);
v___x_755_ = lean_usize_to_uint64(v___x_754_);
v_h_756_ = lean_uint64_to_usize(v___x_755_);
v___x_757_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_750_, v_h_756_, v_x_751_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_758_, v_x_759_);
lean_dec_ref(v_x_759_);
return v_res_760_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4));
v___x_772_ = l_Lean_Name_append(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(lean_object* v_upperBound_776_, lean_object* v___x_777_, lean_object* v___x_778_, uint8_t v___x_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v_a_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___y_798_; lean_object* v___y_821_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; uint8_t v___x_850_; 
v___x_850_ = lean_nat_dec_lt(v_a_783_, v_upperBound_776_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec(v_a_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_780_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_b_784_);
return v___x_851_;
}
else
{
lean_object* v_snd_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_922_; 
v_snd_852_ = lean_ctor_get(v_b_784_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_b_784_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_b_784_, 0);
lean_dec(v_unused_923_);
v___x_854_ = v_b_784_;
v_isShared_855_ = v_isSharedCheck_922_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snd_852_);
lean_dec(v_b_784_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_922_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___y_861_; lean_object* v___x_919_; 
v___x_856_ = lean_box(v___x_779_);
v___f_857_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_857_, 0, v___x_856_);
v___x_858_ = lean_box(0);
v___x_859_ = lean_array_fget_borrowed(v___x_777_, v_a_783_);
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v___x_781_, v_a_783_);
if (lean_obj_tag(v___x_919_) == 1)
{
lean_object* v_val_920_; lean_object* v___x_921_; 
v_val_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v___x_919_, 1);
lean_inc_ref(v___x_782_);
v___x_921_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v___x_782_, v_val_920_);
lean_dec(v_val_920_);
v___y_861_ = v___x_921_;
goto v___jp_860_;
}
else
{
lean_dec(v___x_919_);
lean_inc_ref(v___x_782_);
v___y_861_ = v___x_782_;
goto v___jp_860_;
}
v___jp_860_:
{
lean_object* v_type_862_; uint32_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_type_862_ = lean_ctor_get(v___x_859_, 1);
v___x_863_ = lean_uint32_of_nat(v___x_778_);
v___x_864_ = lean_box_uint32(v___x_863_);
v___x_865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed), 13, 2);
lean_closure_set(v___x_865_, 0, v___x_864_);
lean_closure_set(v___x_865_, 1, v___y_861_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___f_857_);
lean_inc_ref(v_type_862_);
v___x_867_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_867_, 0, v_type_862_);
lean_inc_ref(v___x_780_);
v___x_868_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_867_, v___x_866_, v___x_780_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
lean_inc(v___x_859_);
v___x_870_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_859_, v_a_869_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v_type_872_; lean_object* v_value_873_; uint8_t v___x_874_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v_type_872_ = lean_ctor_get(v_a_871_, 1);
v_value_873_ = lean_ctor_get(v_a_871_, 2);
lean_inc_ref(v_type_872_);
v___x_874_ = l_Lean_Expr_isFalse(v_type_872_);
if (v___x_874_ == 0)
{
lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___f_877_; uint8_t v___x_878_; 
lean_del_object(v___x_854_);
lean_inc(v_a_871_);
lean_inc(v_snd_852_);
v___f_875_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_875_, 0, v_snd_852_);
lean_closure_set(v___f_875_, 1, v_a_871_);
lean_closure_set(v___f_875_, 2, v___x_858_);
v___x_876_ = lean_box(v___x_850_);
v___f_877_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed), 15, 2);
lean_closure_set(v___f_877_, 0, v___x_876_);
lean_closure_set(v___f_877_, 1, v___f_875_);
v___x_878_ = lean_expr_eqv(v_type_862_, v_type_872_);
if (v___x_878_ == 0)
{
lean_inc_ref(v_type_872_);
lean_dec(v_a_871_);
lean_dec(v_snd_852_);
lean_inc_ref(v_type_862_);
v___y_825_ = v___f_877_;
v___y_826_ = v_type_862_;
v___y_827_ = v_type_872_;
goto v___jp_824_;
}
else
{
if (v___x_874_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v___f_877_);
v___x_879_ = lean_box(0);
v___x_880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_852_, v_a_871_, v___x_858_, v___x_879_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
v___y_798_ = v___x_880_;
goto v___jp_797_;
}
else
{
lean_inc_ref(v_type_872_);
lean_dec(v_a_871_);
lean_dec(v_snd_852_);
lean_inc_ref(v_type_862_);
v___y_825_ = v___f_877_;
v___y_826_ = v_type_862_;
v___y_827_ = v_type_872_;
goto v___jp_824_;
}
}
}
else
{
lean_object* v___x_881_; 
lean_inc_ref(v_value_873_);
lean_dec(v_a_871_);
lean_dec(v_a_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_780_);
v___x_881_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_873_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_893_; 
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_881_, 0);
lean_dec(v_unused_894_);
v___x_883_ = v___x_881_;
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_881_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_893_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_885_ = lean_box(v___x_874_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_886_);
v___x_888_ = v___x_854_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_snd_852_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_888_);
v___x_890_ = v___x_883_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
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
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
v_a_895_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_881_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_881_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
lean_dec(v_a_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_780_);
v_a_903_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_870_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_870_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
lean_dec(v_a_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_780_);
v_a_911_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_868_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_868_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
v___jp_797_:
{
if (lean_obj_tag(v___y_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_811_; 
v_a_799_ = lean_ctor_get(v___y_798_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___y_798_);
if (v_isSharedCheck_811_ == 0)
{
v___x_801_ = v___y_798_;
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___y_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
if (lean_obj_tag(v_a_799_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; 
lean_dec(v_a_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_780_);
v_a_803_ = lean_ctor_get(v_a_799_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v_a_799_, 1);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_a_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_del_object(v___x_801_);
v_a_807_ = lean_ctor_get(v_a_799_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v_a_799_, 1);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_add(v_a_783_, v___x_808_);
lean_dec(v_a_783_);
v_a_783_ = v___x_809_;
v_b_784_ = v_a_807_;
goto _start;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_a_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_780_);
v_a_812_ = lean_ctor_get(v___y_798_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___y_798_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___y_798_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___y_798_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_box(0);
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
v___x_823_ = lean_apply_13(v___y_821_, v___x_822_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, lean_box(0));
v___y_798_ = v___x_823_;
goto v___jp_797_;
}
v___jp_824_:
{
lean_object* v_options_828_; uint8_t v_hasTrace_829_; 
v_options_828_ = lean_ctor_get(v___y_794_, 2);
v_hasTrace_829_ = lean_ctor_get_uint8(v_options_828_, sizeof(void*)*1);
if (v_hasTrace_829_ == 0)
{
lean_dec_ref(v___y_827_);
lean_dec_ref(v___y_826_);
v___y_821_ = v___y_825_;
goto v___jp_820_;
}
else
{
lean_object* v_inheritedTraceOptions_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_inheritedTraceOptions_830_ = lean_ctor_get(v___y_794_, 13);
v___x_831_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_832_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_833_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_830_, v_options_828_, v___x_832_);
if (v___x_833_ == 0)
{
lean_dec_ref(v___y_827_);
lean_dec_ref(v___y_826_);
v___y_821_ = v___y_825_;
goto v___jp_820_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = l_Lean_MessageData_ofExpr(v___y_826_);
v___x_835_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l_Lean_MessageData_ofExpr(v___y_827_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_831_, v___x_838_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
lean_inc(v___y_795_);
lean_inc_ref(v___y_794_);
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
v___x_841_ = lean_apply_13(v___y_825_, v_a_840_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, lean_box(0));
v___y_798_ = v___x_841_;
goto v___jp_797_;
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v___y_825_);
lean_dec(v_a_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_780_);
v_a_842_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_839_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_839_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_924_ = _args[0];
lean_object* v___x_925_ = _args[1];
lean_object* v___x_926_ = _args[2];
lean_object* v___x_927_ = _args[3];
lean_object* v___x_928_ = _args[4];
lean_object* v___x_929_ = _args[5];
lean_object* v___x_930_ = _args[6];
lean_object* v_a_931_ = _args[7];
lean_object* v_b_932_ = _args[8];
lean_object* v___y_933_ = _args[9];
lean_object* v___y_934_ = _args[10];
lean_object* v___y_935_ = _args[11];
lean_object* v___y_936_ = _args[12];
lean_object* v___y_937_ = _args[13];
lean_object* v___y_938_ = _args[14];
lean_object* v___y_939_ = _args[15];
lean_object* v___y_940_ = _args[16];
lean_object* v___y_941_ = _args[17];
lean_object* v___y_942_ = _args[18];
lean_object* v___y_943_ = _args[19];
lean_object* v___y_944_ = _args[20];
_start:
{
uint8_t v___x_110681__boxed_945_; lean_object* v_res_946_; 
v___x_110681__boxed_945_ = lean_unbox(v___x_927_);
v_res_946_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_924_, v___x_925_, v___x_926_, v___x_110681__boxed_945_, v___x_928_, v___x_929_, v___x_930_, v_a_931_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v___x_929_);
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
lean_dec(v_upperBound_924_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___redArg(lean_object* v_m_947_, lean_object* v_query_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
lean_object* v_zero_952_; uint8_t v_isZero_953_; 
v_zero_952_ = lean_unsigned_to_nat(0u);
v_isZero_953_ = lean_nat_dec_eq(v_x_950_, v_zero_952_);
if (v_isZero_953_ == 1)
{
lean_dec(v_x_951_);
lean_dec(v_x_950_);
if (lean_obj_tag(v_x_949_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = lean_box(2);
return v___x_954_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_val_955_ = lean_ctor_get(v_x_949_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_949_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v_x_949_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v_x_949_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_val_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v_keyArray_963_; lean_object* v_valueArray_964_; lean_object* v___x_965_; uint8_t v_isSome_966_; 
v_keyArray_963_ = lean_ctor_get(v_m_947_, 1);
v_valueArray_964_ = lean_ctor_get(v_m_947_, 2);
v___x_965_ = lean_array_fget_borrowed(v_keyArray_963_, v_x_951_);
v_isSome_966_ = lean_noption_is_some(v___x_965_);
if (v_isSome_966_ == 0)
{
lean_dec(v_x_950_);
if (lean_obj_tag(v_x_949_) == 0)
{
lean_object* v___x_967_; 
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_x_951_);
return v___x_967_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v_x_951_);
v_val_968_ = lean_ctor_get(v_x_949_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_949_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v_x_949_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v_x_949_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_val_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_one_976_; lean_object* v_n_977_; lean_object* v___y_979_; 
v_one_976_ = lean_unsigned_to_nat(1u);
v_n_977_ = lean_nat_sub(v_x_950_, v_one_976_);
lean_dec(v_x_950_);
if (v_isSome_966_ == 0)
{
goto v___jp_985_;
}
else
{
lean_object* v___x_987_; uint8_t v_isSome_988_; 
v___x_987_ = lean_array_fget_borrowed(v_valueArray_964_, v_x_951_);
v_isSome_988_ = lean_noption_is_some(v___x_987_);
if (v_isSome_988_ == 0)
{
goto v___jp_985_;
}
else
{
lean_object* v_val_989_; size_t v___x_990_; size_t v___x_991_; uint8_t v___x_992_; 
lean_inc(v___x_965_);
v_val_989_ = lean_noption_get(v___x_965_);
v___x_990_ = lean_ptr_addr(v_val_989_);
v___x_991_ = lean_ptr_addr(v_query_948_);
v___x_992_ = lean_usize_dec_eq(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
lean_dec(v_val_989_);
v___x_993_ = lean_array_get_size(v_keyArray_963_);
v___x_994_ = lean_nat_add(v_x_951_, v_one_976_);
lean_dec(v_x_951_);
v___x_995_ = lean_nat_dec_lt(v___x_994_, v___x_993_);
if (v___x_995_ == 0)
{
lean_dec(v___x_994_);
v_x_950_ = v_n_977_;
v_x_951_ = v_zero_952_;
goto _start;
}
else
{
v_x_950_ = v_n_977_;
v_x_951_ = v___x_994_;
goto _start;
}
}
else
{
lean_object* v_val_998_; lean_object* v___x_999_; 
lean_dec(v_n_977_);
lean_dec(v_x_949_);
lean_inc(v___x_987_);
v_val_998_ = lean_noption_get(v___x_987_);
v___x_999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_999_, 0, v_x_951_);
lean_ctor_set(v___x_999_, 1, v_val_989_);
lean_ctor_set(v___x_999_, 2, v_val_998_);
return v___x_999_;
}
}
}
v___jp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_array_get_size(v_keyArray_963_);
v___x_981_ = lean_nat_add(v_x_951_, v_one_976_);
lean_dec(v_x_951_);
v___x_982_ = lean_nat_dec_lt(v___x_981_, v___x_980_);
if (v___x_982_ == 0)
{
lean_dec(v___x_981_);
v_x_949_ = v___y_979_;
v_x_950_ = v_n_977_;
v_x_951_ = v_zero_952_;
goto _start;
}
else
{
v_x_949_ = v___y_979_;
v_x_950_ = v_n_977_;
v_x_951_ = v___x_981_;
goto _start;
}
}
v___jp_985_:
{
if (lean_obj_tag(v_x_949_) == 0)
{
lean_object* v___x_986_; 
lean_inc(v_x_951_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_x_951_);
v___y_979_ = v___x_986_;
goto v___jp_978_;
}
else
{
v___y_979_ = v_x_949_;
goto v___jp_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___redArg___boxed(lean_object* v_m_1000_, lean_object* v_query_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___redArg(v_m_1000_, v_query_1001_, v_x_1002_, v_x_1003_, v_x_1004_);
lean_dec_ref(v_query_1001_);
lean_dec_ref(v_m_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(lean_object* v_m_1006_, lean_object* v_query_1007_){
_start:
{
lean_object* v_keyArray_1008_; lean_object* v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v_fold_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_keyArray_1008_ = lean_ctor_get(v_m_1006_, 1);
v___x_1009_ = lean_array_get_size(v_keyArray_1008_);
v___x_1010_ = lean_ptr_addr(v_query_1007_);
v___x_1011_ = ((size_t)3ULL);
v___x_1012_ = lean_usize_shift_right(v___x_1010_, v___x_1011_);
v___x_1013_ = lean_usize_to_uint64(v___x_1012_);
v___x_1014_ = 32ULL;
v___x_1015_ = lean_uint64_shift_right(v___x_1013_, v___x_1014_);
v_fold_1016_ = lean_uint64_xor(v___x_1013_, v___x_1015_);
v___x_1017_ = 16ULL;
v___x_1018_ = lean_uint64_shift_right(v_fold_1016_, v___x_1017_);
v___x_1019_ = lean_uint64_xor(v_fold_1016_, v___x_1018_);
v___x_1020_ = lean_uint64_to_usize(v___x_1019_);
v___x_1021_ = lean_usize_of_nat(v___x_1009_);
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_sub(v___x_1021_, v___x_1022_);
v___x_1024_ = lean_usize_land(v___x_1020_, v___x_1023_);
v___x_1025_ = lean_usize_to_nat(v___x_1024_);
v___x_1026_ = lean_box(0);
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___redArg(v_m_1006_, v_query_1007_, v___x_1026_, v___x_1009_, v___x_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___boxed(lean_object* v_m_1028_, lean_object* v_query_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_m_1028_, v_query_1029_);
lean_dec_ref(v_query_1029_);
lean_dec_ref(v_m_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___redArg(lean_object* v_m_1031_, lean_object* v_query_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_m_1031_, v_query_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_index_1034_; lean_object* v_key_1035_; lean_object* v_value_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_index_1034_ = lean_ctor_get(v___x_1033_, 0);
v_key_1035_ = lean_ctor_get(v___x_1033_, 1);
v_value_1036_ = lean_ctor_get(v___x_1033_, 2);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1033_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_value_1036_);
lean_inc(v_key_1035_);
lean_inc(v_index_1034_);
lean_dec(v___x_1033_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_index_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_key_1035_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_value_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v___x_1044_; 
lean_dec(v___x_1033_);
v___x_1044_ = lean_box(1);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___redArg___boxed(lean_object* v_m_1045_, lean_object* v_query_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___redArg(v_m_1045_, v_query_1046_);
lean_dec_ref(v_query_1046_);
lean_dec_ref(v_m_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(lean_object* v_m_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___redArg(v_m_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
uint8_t v___x_1051_; 
lean_dec_ref_known(v___x_1050_, 3);
v___x_1051_ = 1;
return v___x_1051_;
}
else
{
uint8_t v___x_1052_; 
v___x_1052_ = 0;
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg___boxed(lean_object* v_m_1053_, lean_object* v_a_1054_){
_start:
{
uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_res_1055_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_m_1053_, v_a_1054_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_m_1053_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0(lean_object* v_fst_1057_, lean_object* v_snd_1058_, lean_object* v_fst_1059_, lean_object* v_fst_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_fst_1057_);
lean_ctor_set(v___x_1074_, 1, v_snd_1058_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_fst_1059_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_fst_1060_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_1079_ = _args[0];
lean_object* v_snd_1080_ = _args[1];
lean_object* v_fst_1081_ = _args[2];
lean_object* v_fst_1082_ = _args[3];
lean_object* v_x_1083_ = _args[4];
lean_object* v___y_1084_ = _args[5];
lean_object* v___y_1085_ = _args[6];
lean_object* v___y_1086_ = _args[7];
lean_object* v___y_1087_ = _args[8];
lean_object* v___y_1088_ = _args[9];
lean_object* v___y_1089_ = _args[10];
lean_object* v___y_1090_ = _args[11];
lean_object* v___y_1091_ = _args[12];
lean_object* v___y_1092_ = _args[13];
lean_object* v___y_1093_ = _args[14];
lean_object* v___y_1094_ = _args[15];
lean_object* v___y_1095_ = _args[16];
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0(v_fst_1079_, v_snd_1080_, v_fst_1081_, v_fst_1082_, v_x_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__1(lean_object* v_arg_1097_, lean_object* v_x_1098_){
_start:
{
uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = 0;
v___x_1100_ = lean_box(v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_arg_1097_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___redArg(lean_object* v_b_1102_, lean_object* v_acc_1103_, lean_object* v_i_1104_){
_start:
{
lean_object* v___y_1106_; lean_object* v_keyArray_1114_; lean_object* v_valueArray_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_keyArray_1114_ = lean_ctor_get(v_b_1102_, 1);
v_valueArray_1115_ = lean_ctor_get(v_b_1102_, 2);
v___x_1116_ = lean_array_get_size(v_keyArray_1114_);
v___x_1117_ = lean_nat_dec_lt(v_i_1104_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec(v_i_1104_);
return v_acc_1103_;
}
else
{
lean_object* v___x_1118_; uint8_t v_isSome_1119_; 
v___x_1118_ = lean_array_fget_borrowed(v_keyArray_1114_, v_i_1104_);
v_isSome_1119_ = lean_noption_is_some(v___x_1118_);
if (v_isSome_1119_ == 0)
{
goto v___jp_1110_;
}
else
{
lean_object* v___x_1120_; uint8_t v_isSome_1121_; 
v___x_1120_ = lean_array_fget_borrowed(v_valueArray_1115_, v_i_1104_);
v_isSome_1121_ = lean_noption_is_some(v___x_1120_);
if (v_isSome_1121_ == 0)
{
goto v___jp_1110_;
}
else
{
lean_object* v_val_1122_; lean_object* v_val_1123_; lean_object* v_i_1125_; lean_object* v___x_1130_; 
lean_inc(v___x_1118_);
v_val_1122_ = lean_noption_get(v___x_1118_);
lean_inc(v___x_1120_);
v_val_1123_ = lean_noption_get(v___x_1120_);
v___x_1130_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_acc_1103_, v_val_1122_);
switch(lean_obj_tag(v___x_1130_))
{
case 0:
{
lean_object* v_index_1131_; lean_object* v_size_1132_; lean_object* v___x_1133_; 
v_index_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_index_1131_);
lean_dec_ref_known(v___x_1130_, 3);
v_size_1132_ = lean_ctor_get(v_acc_1103_, 0);
lean_inc(v_size_1132_);
v___x_1133_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1103_, v_size_1132_, v_index_1131_, v_val_1122_, v_val_1123_);
lean_dec(v_index_1131_);
v___y_1106_ = v___x_1133_;
goto v___jp_1105_;
}
case 1:
{
lean_object* v_index_1134_; 
v_index_1134_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_index_1134_);
lean_dec_ref_known(v___x_1130_, 1);
v_i_1125_ = v_index_1134_;
goto v___jp_1124_;
}
default: 
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1103_, v___x_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_index_1137_; 
v_index_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_index_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v_i_1125_ = v_index_1137_;
goto v___jp_1124_;
}
else
{
lean_dec(v_val_1123_);
lean_dec(v_val_1122_);
v___y_1106_ = v_acc_1103_;
goto v___jp_1105_;
}
}
}
v___jp_1124_:
{
lean_object* v_size_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_size_1126_ = lean_ctor_get(v_acc_1103_, 0);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_size_1126_, v___x_1127_);
v___x_1129_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1103_, v___x_1128_, v_i_1125_, v_val_1122_, v_val_1123_);
lean_dec(v_i_1125_);
v___y_1106_ = v___x_1129_;
goto v___jp_1105_;
}
}
}
}
v___jp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_add(v_i_1104_, v___x_1107_);
lean_dec(v_i_1104_);
v_acc_1103_ = v___y_1106_;
v_i_1104_ = v___x_1108_;
goto _start;
}
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_i_1104_, v___x_1111_);
lean_dec(v_i_1104_);
v_i_1104_ = v___x_1112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___redArg___boxed(lean_object* v_b_1138_, lean_object* v_acc_1139_, lean_object* v_i_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___redArg(v_b_1138_, v_acc_1139_, v_i_1140_);
lean_dec_ref(v_b_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(lean_object* v_init_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___redArg(v_b_1143_, v_init_1142_, v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg___boxed(lean_object* v_init_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_init_1146_, v_b_1147_);
lean_dec_ref(v_b_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(lean_object* v_m_1149_){
_start:
{
lean_object* v_keyArray_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_cellCount_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_target_1157_; lean_object* v___x_1158_; 
v_keyArray_1150_ = lean_ctor_get(v_m_1149_, 1);
v___x_1151_ = lean_array_get_size(v_keyArray_1150_);
v___x_1152_ = lean_unsigned_to_nat(2u);
v_cellCount_1153_ = lean_nat_mul(v___x_1151_, v___x_1152_);
v___x_1154_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1153_);
v___x_1155_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1153_);
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1153_);
v_target_1157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1157_, 0, v___x_1154_);
lean_ctor_set(v_target_1157_, 1, v___x_1155_);
lean_ctor_set(v_target_1157_, 2, v___x_1156_);
v___x_1158_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_target_1157_, v_m_1149_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg___boxed(lean_object* v_m_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_m_1159_);
lean_dec_ref(v_m_1159_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___redArg(lean_object* v_b_1161_, lean_object* v_acc_1162_, lean_object* v_i_1163_){
_start:
{
lean_object* v___y_1165_; lean_object* v_keyArray_1173_; lean_object* v_valueArray_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v_keyArray_1173_ = lean_ctor_get(v_b_1161_, 1);
v_valueArray_1174_ = lean_ctor_get(v_b_1161_, 2);
v___x_1175_ = lean_array_get_size(v_keyArray_1173_);
v___x_1176_ = lean_nat_dec_lt(v_i_1163_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec(v_i_1163_);
return v_acc_1162_;
}
else
{
lean_object* v___x_1177_; uint8_t v_isSome_1178_; 
v___x_1177_ = lean_array_fget_borrowed(v_keyArray_1173_, v_i_1163_);
v_isSome_1178_ = lean_noption_is_some(v___x_1177_);
if (v_isSome_1178_ == 0)
{
goto v___jp_1169_;
}
else
{
lean_object* v___x_1179_; uint8_t v_isSome_1180_; 
v___x_1179_ = lean_array_fget_borrowed(v_valueArray_1174_, v_i_1163_);
v_isSome_1180_ = lean_noption_is_some(v___x_1179_);
if (v_isSome_1180_ == 0)
{
goto v___jp_1169_;
}
else
{
lean_object* v_val_1181_; lean_object* v_val_1182_; lean_object* v_i_1184_; lean_object* v___x_1189_; 
lean_inc(v___x_1177_);
v_val_1181_ = lean_noption_get(v___x_1177_);
lean_inc(v___x_1179_);
v_val_1182_ = lean_noption_get(v___x_1179_);
v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_acc_1162_, v_val_1181_);
switch(lean_obj_tag(v___x_1189_))
{
case 0:
{
lean_object* v_index_1190_; lean_object* v_size_1191_; lean_object* v___x_1192_; 
v_index_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_index_1190_);
lean_dec_ref_known(v___x_1189_, 3);
v_size_1191_ = lean_ctor_get(v_acc_1162_, 0);
lean_inc(v_size_1191_);
v___x_1192_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1162_, v_size_1191_, v_index_1190_, v_val_1181_, v_val_1182_);
lean_dec(v_index_1190_);
v___y_1165_ = v___x_1192_;
goto v___jp_1164_;
}
case 1:
{
lean_object* v_index_1193_; 
v_index_1193_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_index_1193_);
lean_dec_ref_known(v___x_1189_, 1);
v_i_1184_ = v_index_1193_;
goto v___jp_1183_;
}
default: 
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1162_, v___x_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_index_1196_; 
v_index_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_index_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v_i_1184_ = v_index_1196_;
goto v___jp_1183_;
}
else
{
lean_dec(v_val_1182_);
lean_dec(v_val_1181_);
v___y_1165_ = v_acc_1162_;
goto v___jp_1164_;
}
}
}
v___jp_1183_:
{
lean_object* v_size_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_size_1185_ = lean_ctor_get(v_acc_1162_, 0);
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_add(v_size_1185_, v___x_1186_);
v___x_1188_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1162_, v___x_1187_, v_i_1184_, v_val_1181_, v_val_1182_);
lean_dec(v_i_1184_);
v___y_1165_ = v___x_1188_;
goto v___jp_1164_;
}
}
}
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_nat_add(v_i_1163_, v___x_1166_);
lean_dec(v_i_1163_);
v_acc_1162_ = v___y_1165_;
v_i_1163_ = v___x_1167_;
goto _start;
}
v___jp_1169_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_add(v_i_1163_, v___x_1170_);
lean_dec(v_i_1163_);
v_i_1163_ = v___x_1171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_b_1197_, lean_object* v_acc_1198_, lean_object* v_i_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___redArg(v_b_1197_, v_acc_1198_, v_i_1199_);
lean_dec_ref(v_b_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___redArg(lean_object* v_init_1201_, lean_object* v_b_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___redArg(v_b_1202_, v_init_1201_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___redArg___boxed(lean_object* v_init_1205_, lean_object* v_b_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___redArg(v_init_1205_, v_b_1206_);
lean_dec_ref(v_b_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(lean_object* v_m_1208_){
_start:
{
lean_object* v_keyArray_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_cellCount_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_target_1216_; lean_object* v___x_1217_; 
v_keyArray_1209_ = lean_ctor_get(v_m_1208_, 1);
v___x_1210_ = lean_array_get_size(v_keyArray_1209_);
v___x_1211_ = lean_unsigned_to_nat(2u);
v_cellCount_1212_ = lean_nat_mul(v___x_1210_, v___x_1211_);
v___x_1213_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1212_);
v___x_1214_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1212_);
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1212_);
v_target_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1216_, 0, v___x_1213_);
lean_ctor_set(v_target_1216_, 1, v___x_1214_);
lean_ctor_set(v_target_1216_, 2, v___x_1215_);
v___x_1217_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___redArg(v_target_1216_, v_m_1208_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___boxed(lean_object* v_m_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_m_1218_);
lean_dec_ref(v_m_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11_spec__19___redArg(lean_object* v_x_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
lean_object* v_ks_1224_; lean_object* v_vs_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1251_; 
v_ks_1224_ = lean_ctor_get(v_x_1220_, 0);
v_vs_1225_ = lean_ctor_get(v_x_1220_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_x_1220_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1227_ = v_x_1220_;
v_isShared_1228_ = v_isSharedCheck_1251_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_vs_1225_);
lean_inc(v_ks_1224_);
lean_dec(v_x_1220_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1251_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_array_get_size(v_ks_1224_);
v___x_1230_ = lean_nat_dec_lt(v_x_1221_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
lean_dec(v_x_1221_);
v___x_1231_ = lean_array_push(v_ks_1224_, v_x_1222_);
v___x_1232_ = lean_array_push(v_vs_1225_, v_x_1223_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1232_);
lean_ctor_set(v___x_1227_, 0, v___x_1231_);
v___x_1234_ = v___x_1227_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
else
{
lean_object* v_k_x27_1236_; size_t v___x_1237_; size_t v___x_1238_; uint8_t v___x_1239_; 
v_k_x27_1236_ = lean_array_fget_borrowed(v_ks_1224_, v_x_1221_);
v___x_1237_ = lean_ptr_addr(v_x_1222_);
v___x_1238_ = lean_ptr_addr(v_k_x27_1236_);
v___x_1239_ = lean_usize_dec_eq(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1241_; 
if (v_isShared_1228_ == 0)
{
v___x_1241_ = v___x_1227_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_ks_1224_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_vs_1225_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_add(v_x_1221_, v___x_1242_);
lean_dec(v_x_1221_);
v_x_1220_ = v___x_1241_;
v_x_1221_ = v___x_1243_;
goto _start;
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1246_ = lean_array_fset(v_ks_1224_, v_x_1221_, v_x_1222_);
v___x_1247_ = lean_array_fset(v_vs_1225_, v_x_1221_, v_x_1223_);
lean_dec(v_x_1221_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1247_);
lean_ctor_set(v___x_1227_, 0, v___x_1246_);
v___x_1249_ = v___x_1227_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11___redArg(lean_object* v_n_1252_, lean_object* v_k_1253_, lean_object* v_v_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11_spec__19___redArg(v_n_1252_, v___x_1255_, v_k_1253_, v_v_1254_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(lean_object* v_x_1258_, size_t v_x_1259_, size_t v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v_es_1263_; size_t v___x_1264_; size_t v___x_1265_; lean_object* v_j_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_es_1263_ = lean_ctor_get(v_x_1258_, 0);
v___x_1264_ = ((size_t)31ULL);
v___x_1265_ = lean_usize_land(v_x_1259_, v___x_1264_);
v_j_1266_ = lean_usize_to_nat(v___x_1265_);
v___x_1267_ = lean_array_get_size(v_es_1263_);
v___x_1268_ = lean_nat_dec_lt(v_j_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec(v_j_1266_);
lean_dec(v_x_1262_);
lean_dec_ref(v_x_1261_);
return v_x_1258_;
}
else
{
lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1309_; 
lean_inc_ref(v_es_1263_);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_x_1258_, 0);
lean_dec(v_unused_1310_);
v___x_1270_ = v_x_1258_;
v_isShared_1271_ = v_isSharedCheck_1309_;
goto v_resetjp_1269_;
}
else
{
lean_dec(v_x_1258_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1309_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_v_1272_; lean_object* v___x_1273_; lean_object* v_xs_x27_1274_; lean_object* v___y_1276_; 
v_v_1272_ = lean_array_fget(v_es_1263_, v_j_1266_);
v___x_1273_ = lean_box(0);
v_xs_x27_1274_ = lean_array_fset(v_es_1263_, v_j_1266_, v___x_1273_);
switch(lean_obj_tag(v_v_1272_))
{
case 0:
{
lean_object* v_key_1281_; lean_object* v_val_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1294_; 
v_key_1281_ = lean_ctor_get(v_v_1272_, 0);
v_val_1282_ = lean_ctor_get(v_v_1272_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_v_1272_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1284_ = v_v_1272_;
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_val_1282_);
lean_inc(v_key_1281_);
lean_dec(v_v_1272_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
size_t v___x_1286_; size_t v___x_1287_; uint8_t v___x_1288_; 
v___x_1286_ = lean_ptr_addr(v_x_1261_);
v___x_1287_ = lean_ptr_addr(v_key_1281_);
v___x_1288_ = lean_usize_dec_eq(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_del_object(v___x_1284_);
v___x_1289_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1281_, v_val_1282_, v_x_1261_, v_x_1262_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
v___y_1276_ = v___x_1290_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1292_; 
lean_dec(v_val_1282_);
lean_dec(v_key_1281_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v_x_1262_);
lean_ctor_set(v___x_1284_, 0, v_x_1261_);
v___x_1292_ = v___x_1284_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_x_1261_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_x_1262_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
v___y_1276_ = v___x_1292_;
goto v___jp_1275_;
}
}
}
}
case 1:
{
lean_object* v_node_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1307_; 
v_node_1295_ = lean_ctor_get(v_v_1272_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_v_1272_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1297_ = v_v_1272_;
v_isShared_1298_ = v_isSharedCheck_1307_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_node_1295_);
lean_dec(v_v_1272_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1307_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1299_ = ((size_t)5ULL);
v___x_1300_ = lean_usize_shift_right(v_x_1259_, v___x_1299_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_x_1260_, v___x_1301_);
v___x_1303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_node_1295_, v___x_1300_, v___x_1302_, v_x_1261_, v_x_1262_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1303_);
v___x_1305_ = v___x_1297_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
v___y_1276_ = v___x_1305_;
goto v___jp_1275_;
}
}
}
default: 
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_x_1261_);
lean_ctor_set(v___x_1308_, 1, v_x_1262_);
v___y_1276_ = v___x_1308_;
goto v___jp_1275_;
}
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_array_fset(v_xs_x27_1274_, v_j_1266_, v___y_1276_);
lean_dec(v_j_1266_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1277_);
v___x_1279_ = v___x_1270_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
else
{
lean_object* v_ks_1311_; lean_object* v_vs_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1332_; 
v_ks_1311_ = lean_ctor_get(v_x_1258_, 0);
v_vs_1312_ = lean_ctor_get(v_x_1258_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1314_ = v_x_1258_;
v_isShared_1315_ = v_isSharedCheck_1332_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_vs_1312_);
lean_inc(v_ks_1311_);
lean_dec(v_x_1258_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1332_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_ks_1311_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_vs_1312_);
v___x_1317_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v_newNode_1318_; uint8_t v___y_1320_; size_t v___x_1326_; uint8_t v___x_1327_; 
v_newNode_1318_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11___redArg(v___x_1317_, v_x_1261_, v_x_1262_);
v___x_1326_ = ((size_t)7ULL);
v___x_1327_ = lean_usize_dec_le(v___x_1326_, v_x_1260_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1318_);
v___x_1329_ = lean_unsigned_to_nat(4u);
v___x_1330_ = lean_nat_dec_lt(v___x_1328_, v___x_1329_);
lean_dec(v___x_1328_);
v___y_1320_ = v___x_1330_;
goto v___jp_1319_;
}
else
{
v___y_1320_ = v___x_1327_;
goto v___jp_1319_;
}
v___jp_1319_:
{
if (v___y_1320_ == 0)
{
lean_object* v_ks_1321_; lean_object* v_vs_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_ks_1321_ = lean_ctor_get(v_newNode_1318_, 0);
lean_inc_ref(v_ks_1321_);
v_vs_1322_ = lean_ctor_get(v_newNode_1318_, 1);
lean_inc_ref(v_vs_1322_);
lean_dec_ref(v_newNode_1318_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___closed__0);
v___x_1325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___redArg(v_x_1260_, v_ks_1321_, v_vs_1322_, v___x_1323_, v___x_1324_);
lean_dec_ref(v_vs_1322_);
lean_dec_ref(v_ks_1321_);
return v___x_1325_;
}
else
{
return v_newNode_1318_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___redArg(size_t v_depth_1333_, lean_object* v_keys_1334_, lean_object* v_vals_1335_, lean_object* v_i_1336_, lean_object* v_entries_1337_){
_start:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_array_get_size(v_keys_1334_);
v___x_1339_ = lean_nat_dec_lt(v_i_1336_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec(v_i_1336_);
return v_entries_1337_;
}
else
{
lean_object* v_k_1340_; lean_object* v_v_1341_; size_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; uint64_t v___x_1345_; size_t v_h_1346_; size_t v___x_1347_; lean_object* v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v_h_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_k_1340_ = lean_array_fget_borrowed(v_keys_1334_, v_i_1336_);
v_v_1341_ = lean_array_fget_borrowed(v_vals_1335_, v_i_1336_);
v___x_1342_ = lean_ptr_addr(v_k_1340_);
v___x_1343_ = ((size_t)3ULL);
v___x_1344_ = lean_usize_shift_right(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_usize_to_uint64(v___x_1344_);
v_h_1346_ = lean_uint64_to_usize(v___x_1345_);
v___x_1347_ = ((size_t)5ULL);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_sub(v_depth_1333_, v___x_1349_);
v___x_1351_ = lean_usize_mul(v___x_1347_, v___x_1350_);
v_h_1352_ = lean_usize_shift_right(v_h_1346_, v___x_1351_);
v___x_1353_ = lean_nat_add(v_i_1336_, v___x_1348_);
lean_dec(v_i_1336_);
lean_inc(v_v_1341_);
lean_inc(v_k_1340_);
v___x_1354_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_entries_1337_, v_h_1352_, v_depth_1333_, v_k_1340_, v_v_1341_);
v_i_1336_ = v___x_1353_;
v_entries_1337_ = v___x_1354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_depth_1356_, lean_object* v_keys_1357_, lean_object* v_vals_1358_, lean_object* v_i_1359_, lean_object* v_entries_1360_){
_start:
{
size_t v_depth_boxed_1361_; lean_object* v_res_1362_; 
v_depth_boxed_1361_ = lean_unbox_usize(v_depth_1356_);
lean_dec(v_depth_1356_);
v_res_1362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___redArg(v_depth_boxed_1361_, v_keys_1357_, v_vals_1358_, v_i_1359_, v_entries_1360_);
lean_dec_ref(v_vals_1358_);
lean_dec_ref(v_keys_1357_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
size_t v_x_111431__boxed_1368_; size_t v_x_111432__boxed_1369_; lean_object* v_res_1370_; 
v_x_111431__boxed_1368_ = lean_unbox_usize(v_x_1364_);
lean_dec(v_x_1364_);
v_x_111432__boxed_1369_ = lean_unbox_usize(v_x_1365_);
lean_dec(v_x_1365_);
v_res_1370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_x_1363_, v_x_111431__boxed_1368_, v_x_111432__boxed_1369_, v_x_1366_, v_x_1367_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
size_t v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; uint64_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v___x_1374_ = lean_ptr_addr(v_x_1372_);
v___x_1375_ = ((size_t)3ULL);
v___x_1376_ = lean_usize_shift_right(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_usize_to_uint64(v___x_1376_);
v___x_1378_ = lean_uint64_to_usize(v___x_1377_);
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_x_1371_, v___x_1378_, v___x_1379_, v_x_1372_, v_x_1373_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg(lean_object* v_upperBound_1388_, lean_object* v___x_1389_, lean_object* v_a_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_a_1405_; lean_object* v___y_1410_; uint8_t v___x_1429_; 
v___x_1429_ = lean_nat_dec_lt(v_a_1390_, v_upperBound_1388_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_a_1390_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_b_1391_);
return v___x_1430_;
}
else
{
lean_object* v_snd_1431_; lean_object* v_snd_1432_; lean_object* v_fst_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1679_; 
v_snd_1431_ = lean_ctor_get(v_b_1391_, 1);
lean_inc(v_snd_1431_);
v_snd_1432_ = lean_ctor_get(v_snd_1431_, 1);
lean_inc(v_snd_1432_);
v_fst_1433_ = lean_ctor_get(v_b_1391_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_b_1391_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v_b_1391_, 1);
lean_dec(v_unused_1680_);
v___x_1435_ = v_b_1391_;
v_isShared_1436_ = v_isSharedCheck_1679_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_fst_1433_);
lean_dec(v_b_1391_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1679_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_fst_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1677_; 
v_fst_1437_ = lean_ctor_get(v_snd_1431_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_snd_1431_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_snd_1431_, 1);
lean_dec(v_unused_1678_);
v___x_1439_ = v_snd_1431_;
v_isShared_1440_ = v_isSharedCheck_1677_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_fst_1437_);
lean_dec(v_snd_1431_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1677_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_fst_1441_; lean_object* v_snd_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1676_; 
v_fst_1441_ = lean_ctor_get(v_snd_1432_, 0);
v_snd_1442_ = lean_ctor_get(v_snd_1432_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_snd_1432_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1444_ = v_snd_1432_;
v_isShared_1445_ = v_isSharedCheck_1676_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_snd_1442_);
lean_inc(v_fst_1441_);
lean_dec(v_snd_1432_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1676_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1456_; lean_object* v_type_1457_; lean_object* v_value_1458_; lean_object* v___y_1460_; uint8_t v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; uint8_t v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v_i_1483_; uint8_t v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1502_; uint8_t v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v_i_1506_; uint8_t v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; uint8_t v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v_i_1563_; uint8_t v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1582_; uint8_t v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v_i_1586_; uint8_t v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1456_ = lean_array_fget_borrowed(v___x_1389_, v_a_1390_);
v_type_1457_ = lean_ctor_get(v___x_1456_, 1);
v_value_1458_ = lean_ctor_get(v___x_1456_, 2);
lean_inc_ref(v_type_1457_);
v___x_1604_ = l_Lean_Expr_cleanupAnnotations(v_type_1457_);
v___x_1605_ = l_Lean_Expr_isApp(v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v___x_1604_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1435_);
v___x_1606_ = lean_box(0);
v___x_1607_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0(v_fst_1441_, v_snd_1442_, v_fst_1437_, v_fst_1433_, v___x_1606_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
v___y_1410_ = v___x_1607_;
goto v___jp_1409_;
}
else
{
lean_object* v_arg_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v_arg_1608_ = lean_ctor_get(v___x_1604_, 1);
lean_inc_ref(v_arg_1608_);
v___x_1609_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1604_);
v___x_1610_ = l_Lean_Expr_isApp(v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v___x_1609_);
lean_dec_ref(v_arg_1608_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1435_);
v___x_1611_ = lean_box(0);
v___x_1612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0(v_fst_1441_, v_snd_1442_, v_fst_1437_, v_fst_1433_, v___x_1611_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
v___y_1410_ = v___x_1612_;
goto v___jp_1409_;
}
else
{
lean_object* v_arg_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_arg_1613_ = lean_ctor_get(v___x_1609_, 1);
lean_inc_ref(v_arg_1613_);
v___x_1614_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1609_);
v___x_1615_ = l_Lean_Expr_isApp(v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v___x_1614_);
lean_dec_ref(v_arg_1613_);
lean_dec_ref(v_arg_1608_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1435_);
v___x_1616_ = lean_box(0);
v___x_1617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0(v_fst_1441_, v_snd_1442_, v_fst_1437_, v_fst_1433_, v___x_1616_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
v___y_1410_ = v___x_1617_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1614_);
v___x_1619_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__1));
v___x_1620_ = l_Lean_Expr_isConstOf(v___x_1618_, v___x_1619_);
lean_dec_ref(v___x_1618_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_arg_1613_);
lean_dec_ref(v_arg_1608_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1435_);
v___x_1621_ = lean_box(0);
v___x_1622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__0(v_fst_1441_, v_snd_1442_, v_fst_1437_, v_fst_1433_, v___x_1621_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
v___y_1410_ = v___x_1622_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v_fst_1627_; uint8_t v_snd_1628_; lean_object* v___y_1659_; 
v___x_1623_ = l_Lean_Expr_cleanupAnnotations(v_arg_1608_);
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2));
v___x_1625_ = l_Lean_Expr_isConstOf(v___x_1623_, v___x_1624_);
lean_dec_ref(v___x_1623_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v_arg_1613_);
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1435_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v_fst_1441_);
lean_ctor_set(v___x_1663_, 1, v_snd_1442_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_fst_1437_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v_fst_1433_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v_a_1405_ = v___x_1665_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
lean_inc_ref(v_arg_1613_);
v___x_1666_ = l_Lean_Expr_cleanupAnnotations(v_arg_1613_);
v___x_1667_ = l_Lean_Expr_isApp(v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v___x_1666_);
v___x_1668_ = lean_box(0);
v___x_1669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__1(v_arg_1613_, v___x_1668_);
v___y_1659_ = v___x_1669_;
goto v___jp_1658_;
}
else
{
lean_object* v_arg_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_arg_1670_ = lean_ctor_get(v___x_1666_, 1);
lean_inc_ref(v_arg_1670_);
v___x_1671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1666_);
v___x_1672_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___closed__3));
v___x_1673_ = l_Lean_Expr_isConstOf(v___x_1671_, v___x_1672_);
lean_dec_ref(v___x_1671_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref(v_arg_1670_);
v___x_1674_ = lean_box(0);
v___x_1675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___lam__1(v_arg_1613_, v___x_1674_);
v___y_1659_ = v___x_1675_;
goto v___jp_1658_;
}
else
{
lean_dec_ref(v_arg_1613_);
v_fst_1627_ = v_arg_1670_;
v_snd_1628_ = v___x_1673_;
goto v___jp_1626_;
}
}
}
v___jp_1626_:
{
uint8_t v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_fst_1441_, v_fst_1627_);
if (v___x_1629_ == 0)
{
if (v___x_1625_ == 0)
{
lean_dec_ref(v_fst_1627_);
goto v___jp_1446_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_del_object(v___x_1444_);
lean_del_object(v___x_1439_);
lean_del_object(v___x_1435_);
v___x_1630_ = lean_box(0);
v___x_1631_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_fst_1441_, v_fst_1627_);
switch(lean_obj_tag(v___x_1631_))
{
case 0:
{
lean_dec_ref_known(v___x_1631_, 3);
v___y_1525_ = v_snd_1628_;
v___y_1526_ = v_fst_1627_;
v___y_1527_ = v_fst_1441_;
goto v___jp_1524_;
}
case 1:
{
lean_object* v_index_1632_; lean_object* v_size_1633_; lean_object* v_keyArray_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_index_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_index_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v_size_1633_ = lean_ctor_get(v_fst_1441_, 0);
v_keyArray_1634_ = lean_ctor_get(v_fst_1441_, 1);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_size_1633_, v___x_1635_);
v___x_1637_ = lean_array_get_size(v_keyArray_1634_);
v___x_1638_ = lean_nat_dec_lt(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_dec(v___x_1636_);
lean_dec(v_index_1632_);
v___y_1569_ = v_snd_1628_;
v___y_1570_ = v___x_1630_;
v___y_1571_ = v_fst_1627_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1639_ = lean_unsigned_to_nat(4u);
v___x_1640_ = lean_nat_mul(v___x_1636_, v___x_1639_);
v___x_1641_ = lean_unsigned_to_nat(3u);
v___x_1642_ = lean_nat_mul(v___x_1637_, v___x_1641_);
v___x_1643_ = lean_nat_dec_le(v___x_1640_, v___x_1642_);
lean_dec(v___x_1642_);
lean_dec(v___x_1640_);
if (v___x_1643_ == 0)
{
lean_dec(v___x_1636_);
lean_dec(v_index_1632_);
v___y_1569_ = v_snd_1628_;
v___y_1570_ = v___x_1630_;
v___y_1571_ = v_fst_1627_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1644_; 
lean_inc_ref(v_fst_1627_);
v___x_1644_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1441_, v___x_1636_, v_index_1632_, v_fst_1627_, v___x_1630_);
lean_dec(v_index_1632_);
v___y_1525_ = v_snd_1628_;
v___y_1526_ = v_fst_1627_;
v___y_1527_ = v___x_1644_;
goto v___jp_1524_;
}
}
}
default: 
{
lean_object* v_size_1645_; lean_object* v_keyArray_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v_size_1645_ = lean_ctor_get(v_fst_1441_, 0);
v_keyArray_1646_ = lean_ctor_get(v_fst_1441_, 1);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_size_1645_, v___x_1647_);
v___x_1649_ = lean_array_get_size(v_keyArray_1646_);
v___x_1650_ = lean_nat_dec_lt(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
lean_dec(v___x_1648_);
v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_fst_1441_);
lean_dec(v_fst_1441_);
v___y_1592_ = v_snd_1628_;
v___y_1593_ = v___x_1630_;
v___y_1594_ = v_fst_1627_;
v___y_1595_ = v___x_1651_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1652_ = lean_unsigned_to_nat(4u);
v___x_1653_ = lean_nat_mul(v___x_1648_, v___x_1652_);
lean_dec(v___x_1648_);
v___x_1654_ = lean_unsigned_to_nat(3u);
v___x_1655_ = lean_nat_mul(v___x_1649_, v___x_1654_);
v___x_1656_ = lean_nat_dec_le(v___x_1653_, v___x_1655_);
lean_dec(v___x_1655_);
lean_dec(v___x_1653_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_fst_1441_);
lean_dec(v_fst_1441_);
v___y_1592_ = v_snd_1628_;
v___y_1593_ = v___x_1630_;
v___y_1594_ = v_fst_1627_;
v___y_1595_ = v___x_1657_;
goto v___jp_1591_;
}
else
{
v___y_1592_ = v_snd_1628_;
v___y_1593_ = v___x_1630_;
v___y_1594_ = v_fst_1627_;
v___y_1595_ = v_fst_1441_;
goto v___jp_1591_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_fst_1627_);
goto v___jp_1446_;
}
}
v___jp_1658_:
{
lean_object* v_fst_1660_; lean_object* v_snd_1661_; uint8_t v___x_1662_; 
v_fst_1660_ = lean_ctor_get(v___y_1659_, 0);
lean_inc(v_fst_1660_);
v_snd_1661_ = lean_ctor_get(v___y_1659_, 1);
lean_inc(v_snd_1661_);
lean_dec_ref(v___y_1659_);
v___x_1662_ = lean_unbox(v_snd_1661_);
lean_dec(v_snd_1661_);
v_fst_1627_ = v_fst_1660_;
v_snd_1628_ = v___x_1662_;
goto v___jp_1626_;
}
}
}
}
}
v___jp_1446_:
{
lean_object* v___x_1448_; 
if (v_isShared_1445_ == 0)
{
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_fst_1441_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_snd_1442_);
v___x_1448_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1448_);
v___x_1450_ = v___x_1439_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_fst_1437_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1450_);
v___x_1452_ = v___x_1435_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_fst_1433_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v_a_1405_ = v___x_1452_;
goto v___jp_1404_;
}
}
}
}
v___jp_1459_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_inc_ref(v_value_1458_);
v___x_1465_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1465_, 0, v_value_1458_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*1, v___y_1461_);
v___x_1466_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_fst_1433_, v___y_1462_, v___x_1465_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___y_1463_);
lean_ctor_set(v___x_1467_, 1, v___y_1464_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___y_1460_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1466_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v_a_1405_ = v___x_1469_;
goto v___jp_1404_;
}
v___jp_1470_:
{
uint32_t v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = l_Lean_Expr_approxDepth(v___y_1472_);
v___x_1476_ = lean_uint32_to_nat(v___x_1475_);
v___x_1477_ = lean_nat_dec_le(v_snd_1442_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_dec(v_snd_1442_);
v___y_1460_ = v___y_1474_;
v___y_1461_ = v___y_1471_;
v___y_1462_ = v___y_1472_;
v___y_1463_ = v___y_1473_;
v___y_1464_ = v___x_1476_;
goto v___jp_1459_;
}
else
{
lean_dec(v___x_1476_);
v___y_1460_ = v___y_1474_;
v___y_1461_ = v___y_1471_;
v___y_1462_ = v___y_1472_;
v___y_1463_ = v___y_1473_;
v___y_1464_ = v_snd_1442_;
goto v___jp_1459_;
}
}
v___jp_1478_:
{
lean_object* v_size_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_size_1484_ = lean_ctor_get(v___y_1479_, 0);
v___x_1485_ = lean_unsigned_to_nat(1u);
v___x_1486_ = lean_nat_add(v_size_1484_, v___x_1485_);
lean_inc_ref(v___y_1481_);
lean_inc(v_a_1390_);
v___x_1487_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1479_, v___x_1486_, v_i_1483_, v_a_1390_, v___y_1481_);
lean_dec(v_i_1483_);
v___y_1471_ = v___y_1480_;
v___y_1472_ = v___y_1481_;
v___y_1473_ = v___y_1482_;
v___y_1474_ = v___x_1487_;
goto v___jp_1470_;
}
v___jp_1488_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_fst_1437_);
lean_dec(v_fst_1437_);
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v___x_1492_, v_a_1390_);
switch(lean_obj_tag(v___x_1493_))
{
case 0:
{
lean_object* v_index_1494_; lean_object* v_size_1495_; lean_object* v___x_1496_; 
v_index_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_index_1494_);
lean_dec_ref_known(v___x_1493_, 3);
v_size_1495_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_size_1495_);
lean_inc_ref(v___y_1490_);
lean_inc(v_a_1390_);
v___x_1496_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1492_, v_size_1495_, v_index_1494_, v_a_1390_, v___y_1490_);
lean_dec(v_index_1494_);
v___y_1471_ = v___y_1489_;
v___y_1472_ = v___y_1490_;
v___y_1473_ = v___y_1491_;
v___y_1474_ = v___x_1496_;
goto v___jp_1470_;
}
case 1:
{
lean_object* v_index_1497_; 
v_index_1497_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_index_1497_);
lean_dec_ref_known(v___x_1493_, 1);
v___y_1479_ = v___x_1492_;
v___y_1480_ = v___y_1489_;
v___y_1481_ = v___y_1490_;
v___y_1482_ = v___y_1491_;
v_i_1483_ = v_index_1497_;
goto v___jp_1478_;
}
default: 
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1492_, v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_index_1500_; 
v_index_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_index_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___y_1479_ = v___x_1492_;
v___y_1480_ = v___y_1489_;
v___y_1481_ = v___y_1490_;
v___y_1482_ = v___y_1491_;
v_i_1483_ = v_index_1500_;
goto v___jp_1478_;
}
else
{
v___y_1471_ = v___y_1489_;
v___y_1472_ = v___y_1490_;
v___y_1473_ = v___y_1491_;
v___y_1474_ = v___x_1492_;
goto v___jp_1470_;
}
}
}
}
v___jp_1501_:
{
lean_object* v_size_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_size_1507_ = lean_ctor_get(v___y_1502_, 0);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_add(v_size_1507_, v___x_1508_);
lean_inc_ref(v___y_1504_);
lean_inc(v_a_1390_);
v___x_1510_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1502_, v___x_1509_, v_i_1506_, v_a_1390_, v___y_1504_);
lean_dec(v_i_1506_);
v___y_1471_ = v___y_1503_;
v___y_1472_ = v___y_1504_;
v___y_1473_ = v___y_1505_;
v___y_1474_ = v___x_1510_;
goto v___jp_1470_;
}
v___jp_1511_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v___y_1515_, v_a_1390_);
switch(lean_obj_tag(v___x_1516_))
{
case 0:
{
lean_object* v_index_1517_; lean_object* v_size_1518_; lean_object* v___x_1519_; 
v_index_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_index_1517_);
lean_dec_ref_known(v___x_1516_, 3);
v_size_1518_ = lean_ctor_get(v___y_1515_, 0);
lean_inc(v_size_1518_);
lean_inc_ref(v___y_1513_);
lean_inc(v_a_1390_);
v___x_1519_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1515_, v_size_1518_, v_index_1517_, v_a_1390_, v___y_1513_);
lean_dec(v_index_1517_);
v___y_1471_ = v___y_1512_;
v___y_1472_ = v___y_1513_;
v___y_1473_ = v___y_1514_;
v___y_1474_ = v___x_1519_;
goto v___jp_1470_;
}
case 1:
{
lean_object* v_index_1520_; 
v_index_1520_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_index_1520_);
lean_dec_ref_known(v___x_1516_, 1);
v___y_1502_ = v___y_1515_;
v___y_1503_ = v___y_1512_;
v___y_1504_ = v___y_1513_;
v___y_1505_ = v___y_1514_;
v_i_1506_ = v_index_1520_;
goto v___jp_1501_;
}
default: 
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1515_, v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_index_1523_; 
v_index_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_index_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1502_ = v___y_1515_;
v___y_1503_ = v___y_1512_;
v___y_1504_ = v___y_1513_;
v___y_1505_ = v___y_1514_;
v_i_1506_ = v_index_1523_;
goto v___jp_1501_;
}
else
{
v___y_1471_ = v___y_1512_;
v___y_1472_ = v___y_1513_;
v___y_1473_ = v___y_1514_;
v___y_1474_ = v___y_1515_;
goto v___jp_1470_;
}
}
}
}
v___jp_1524_:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_fst_1437_, v_a_1390_);
switch(lean_obj_tag(v___x_1528_))
{
case 0:
{
lean_object* v_index_1529_; lean_object* v_size_1530_; lean_object* v___x_1531_; 
v_index_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_index_1529_);
lean_dec_ref_known(v___x_1528_, 3);
v_size_1530_ = lean_ctor_get(v_fst_1437_, 0);
lean_inc(v_size_1530_);
lean_inc_ref(v___y_1526_);
lean_inc(v_a_1390_);
v___x_1531_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1437_, v_size_1530_, v_index_1529_, v_a_1390_, v___y_1526_);
lean_dec(v_index_1529_);
v___y_1471_ = v___y_1525_;
v___y_1472_ = v___y_1526_;
v___y_1473_ = v___y_1527_;
v___y_1474_ = v___x_1531_;
goto v___jp_1470_;
}
case 1:
{
lean_object* v_index_1532_; lean_object* v_size_1533_; lean_object* v_keyArray_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_index_1532_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_index_1532_);
lean_dec_ref_known(v___x_1528_, 1);
v_size_1533_ = lean_ctor_get(v_fst_1437_, 0);
v_keyArray_1534_ = lean_ctor_get(v_fst_1437_, 1);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_add(v_size_1533_, v___x_1535_);
v___x_1537_ = lean_array_get_size(v_keyArray_1534_);
v___x_1538_ = lean_nat_dec_lt(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec(v___x_1536_);
lean_dec(v_index_1532_);
v___y_1489_ = v___y_1525_;
v___y_1490_ = v___y_1526_;
v___y_1491_ = v___y_1527_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1539_ = lean_unsigned_to_nat(4u);
v___x_1540_ = lean_nat_mul(v___x_1536_, v___x_1539_);
v___x_1541_ = lean_unsigned_to_nat(3u);
v___x_1542_ = lean_nat_mul(v___x_1537_, v___x_1541_);
v___x_1543_ = lean_nat_dec_le(v___x_1540_, v___x_1542_);
lean_dec(v___x_1542_);
lean_dec(v___x_1540_);
if (v___x_1543_ == 0)
{
lean_dec(v___x_1536_);
lean_dec(v_index_1532_);
v___y_1489_ = v___y_1525_;
v___y_1490_ = v___y_1526_;
v___y_1491_ = v___y_1527_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1544_; 
lean_inc_ref(v___y_1526_);
lean_inc(v_a_1390_);
v___x_1544_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1437_, v___x_1536_, v_index_1532_, v_a_1390_, v___y_1526_);
lean_dec(v_index_1532_);
v___y_1471_ = v___y_1525_;
v___y_1472_ = v___y_1526_;
v___y_1473_ = v___y_1527_;
v___y_1474_ = v___x_1544_;
goto v___jp_1470_;
}
}
}
default: 
{
lean_object* v_size_1545_; lean_object* v_keyArray_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_size_1545_ = lean_ctor_get(v_fst_1437_, 0);
v_keyArray_1546_ = lean_ctor_get(v_fst_1437_, 1);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_size_1545_, v___x_1547_);
v___x_1549_ = lean_array_get_size(v_keyArray_1546_);
v___x_1550_ = lean_nat_dec_lt(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v___x_1548_);
v___x_1551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_fst_1437_);
lean_dec(v_fst_1437_);
v___y_1512_ = v___y_1525_;
v___y_1513_ = v___y_1526_;
v___y_1514_ = v___y_1527_;
v___y_1515_ = v___x_1551_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1552_ = lean_unsigned_to_nat(4u);
v___x_1553_ = lean_nat_mul(v___x_1548_, v___x_1552_);
lean_dec(v___x_1548_);
v___x_1554_ = lean_unsigned_to_nat(3u);
v___x_1555_ = lean_nat_mul(v___x_1549_, v___x_1554_);
v___x_1556_ = lean_nat_dec_le(v___x_1553_, v___x_1555_);
lean_dec(v___x_1555_);
lean_dec(v___x_1553_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_fst_1437_);
lean_dec(v_fst_1437_);
v___y_1512_ = v___y_1525_;
v___y_1513_ = v___y_1526_;
v___y_1514_ = v___y_1527_;
v___y_1515_ = v___x_1557_;
goto v___jp_1511_;
}
else
{
v___y_1512_ = v___y_1525_;
v___y_1513_ = v___y_1526_;
v___y_1514_ = v___y_1527_;
v___y_1515_ = v_fst_1437_;
goto v___jp_1511_;
}
}
}
}
}
v___jp_1558_:
{
lean_object* v_size_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_size_1564_ = lean_ctor_get(v___y_1560_, 0);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_size_1564_, v___x_1565_);
lean_inc_ref(v___y_1562_);
v___x_1567_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1560_, v___x_1566_, v_i_1563_, v___y_1562_, v___y_1561_);
lean_dec(v_i_1563_);
v___y_1525_ = v___y_1559_;
v___y_1526_ = v___y_1562_;
v___y_1527_ = v___x_1567_;
goto v___jp_1524_;
}
v___jp_1568_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_fst_1441_);
lean_dec(v_fst_1441_);
v___x_1573_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v___x_1572_, v___y_1571_);
switch(lean_obj_tag(v___x_1573_))
{
case 0:
{
lean_object* v_index_1574_; lean_object* v_size_1575_; lean_object* v___x_1576_; 
v_index_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_index_1574_);
lean_dec_ref_known(v___x_1573_, 3);
v_size_1575_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_size_1575_);
lean_inc_ref(v___y_1571_);
v___x_1576_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1572_, v_size_1575_, v_index_1574_, v___y_1571_, v___y_1570_);
lean_dec(v_index_1574_);
v___y_1525_ = v___y_1569_;
v___y_1526_ = v___y_1571_;
v___y_1527_ = v___x_1576_;
goto v___jp_1524_;
}
case 1:
{
lean_object* v_index_1577_; 
v_index_1577_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_index_1577_);
lean_dec_ref_known(v___x_1573_, 1);
v___y_1559_ = v___y_1569_;
v___y_1560_ = v___x_1572_;
v___y_1561_ = v___y_1570_;
v___y_1562_ = v___y_1571_;
v_i_1563_ = v_index_1577_;
goto v___jp_1558_;
}
default: 
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1572_, v___x_1578_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_index_1580_; 
v_index_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_index_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___y_1559_ = v___y_1569_;
v___y_1560_ = v___x_1572_;
v___y_1561_ = v___y_1570_;
v___y_1562_ = v___y_1571_;
v_i_1563_ = v_index_1580_;
goto v___jp_1558_;
}
else
{
v___y_1525_ = v___y_1569_;
v___y_1526_ = v___y_1571_;
v___y_1527_ = v___x_1572_;
goto v___jp_1524_;
}
}
}
}
v___jp_1581_:
{
lean_object* v_size_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_size_1587_ = lean_ctor_get(v___y_1582_, 0);
v___x_1588_ = lean_unsigned_to_nat(1u);
v___x_1589_ = lean_nat_add(v_size_1587_, v___x_1588_);
lean_inc_ref(v___y_1585_);
v___x_1590_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1582_, v___x_1589_, v_i_1586_, v___y_1585_, v___y_1584_);
lean_dec(v_i_1586_);
v___y_1525_ = v___y_1583_;
v___y_1526_ = v___y_1585_;
v___y_1527_ = v___x_1590_;
goto v___jp_1524_;
}
v___jp_1591_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v___y_1595_, v___y_1594_);
switch(lean_obj_tag(v___x_1596_))
{
case 0:
{
lean_object* v_index_1597_; lean_object* v_size_1598_; lean_object* v___x_1599_; 
v_index_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_index_1597_);
lean_dec_ref_known(v___x_1596_, 3);
v_size_1598_ = lean_ctor_get(v___y_1595_, 0);
lean_inc(v_size_1598_);
lean_inc_ref(v___y_1594_);
v___x_1599_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1595_, v_size_1598_, v_index_1597_, v___y_1594_, v___y_1593_);
lean_dec(v_index_1597_);
v___y_1525_ = v___y_1592_;
v___y_1526_ = v___y_1594_;
v___y_1527_ = v___x_1599_;
goto v___jp_1524_;
}
case 1:
{
lean_object* v_index_1600_; 
v_index_1600_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_index_1600_);
lean_dec_ref_known(v___x_1596_, 1);
v___y_1582_ = v___y_1595_;
v___y_1583_ = v___y_1592_;
v___y_1584_ = v___y_1593_;
v___y_1585_ = v___y_1594_;
v_i_1586_ = v_index_1600_;
goto v___jp_1581_;
}
default: 
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1595_, v___x_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_index_1603_; 
v_index_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_index_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v___y_1582_ = v___y_1595_;
v___y_1583_ = v___y_1592_;
v___y_1584_ = v___y_1593_;
v___y_1585_ = v___y_1594_;
v_i_1586_ = v_index_1603_;
goto v___jp_1581_;
}
else
{
v___y_1525_ = v___y_1592_;
v___y_1526_ = v___y_1594_;
v___y_1527_ = v___y_1595_;
goto v___jp_1524_;
}
}
}
}
}
}
}
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_unsigned_to_nat(1u);
v___x_1407_ = lean_nat_add(v_a_1390_, v___x_1406_);
lean_dec(v_a_1390_);
v_a_1390_ = v___x_1407_;
v_b_1391_ = v_a_1405_;
goto _start;
}
v___jp_1409_:
{
if (lean_obj_tag(v___y_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1420_; 
v_a_1411_ = lean_ctor_get(v___y_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___y_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1413_ = v___y_1410_;
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___y_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
if (lean_obj_tag(v_a_1411_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; 
lean_dec(v_a_1390_);
v_a_1415_ = lean_ctor_get(v_a_1411_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v_a_1411_, 1);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v_a_1415_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
lean_object* v_a_1419_; 
lean_del_object(v___x_1413_);
v_a_1419_ = lean_ctor_get(v_a_1411_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v_a_1411_, 1);
v_a_1405_ = v_a_1419_;
goto v___jp_1404_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_a_1390_);
v_a_1421_ = lean_ctor_get(v___y_1410_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___y_1410_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___y_1410_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___y_1410_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg___boxed(lean_object* v_upperBound_1681_, lean_object* v___x_1682_, lean_object* v_a_1683_, lean_object* v_b_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg(v_upperBound_1681_, v___x_1682_, v_a_1683_, v_b_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___x_1682_);
lean_dec(v_upperBound_1681_);
return v_res_1697_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1699_; lean_object* v_relevantHypsMap_1700_; 
v___x_1699_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0);
v_relevantHypsMap_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_relevantHypsMap_1700_, 0, v___x_1699_);
return v_relevantHypsMap_1700_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2(void){
_start:
{
lean_object* v_cellCount_1701_; lean_object* v___x_1702_; 
v_cellCount_1701_ = lean_unsigned_to_nat(16u);
v___x_1702_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3(void){
_start:
{
lean_object* v_cellCount_1703_; lean_object* v___x_1704_; 
v_cellCount_1703_ = lean_unsigned_to_nat(16u);
v___x_1704_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1703_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v_relevantHypsIdxMap_1708_; 
v___x_1705_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1706_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2);
v___x_1707_ = lean_unsigned_to_nat(0u);
v_relevantHypsIdxMap_1708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_relevantHypsIdxMap_1708_, 0, v___x_1707_);
lean_ctor_set(v_relevantHypsIdxMap_1708_, 1, v___x_1706_);
lean_ctor_set(v_relevantHypsIdxMap_1708_, 2, v___x_1705_);
return v_relevantHypsIdxMap_1708_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5(void){
_start:
{
lean_object* v_minDepth_1709_; lean_object* v_relevantHypsIdxMap_1710_; lean_object* v___x_1711_; 
v_minDepth_1709_ = lean_cstr_to_nat("4294967296");
v_relevantHypsIdxMap_1710_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_relevantHypsIdxMap_1710_);
lean_ctor_set(v___x_1711_, 1, v_minDepth_1709_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1712_; lean_object* v_relevantHypsIdxMap_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5);
v_relevantHypsIdxMap_1713_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_relevantHypsIdxMap_1713_);
lean_ctor_set(v___x_1714_, 1, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1715_; lean_object* v_relevantHypsMap_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6);
v_relevantHypsMap_1716_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_relevantHypsMap_1716_);
lean_ctor_set(v___x_1717_, 1, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_hypotheses_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1733_ = lean_st_ref_get(v___y_1722_);
v_hypotheses_1734_ = lean_ctor_get(v___x_1733_, 3);
lean_inc_ref(v_hypotheses_1734_);
lean_dec(v___x_1733_);
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_array_get_size(v_hypotheses_1734_);
v___x_1737_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7);
v___x_1738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg(v___x_1736_, v_hypotheses_1734_, v___x_1735_, v___x_1737_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec_ref(v_hypotheses_1734_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1855_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1855_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1855_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_snd_1743_; lean_object* v_snd_1744_; lean_object* v_fst_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1853_; 
v_snd_1743_ = lean_ctor_get(v_a_1739_, 1);
lean_inc(v_snd_1743_);
v_snd_1744_ = lean_ctor_get(v_snd_1743_, 1);
lean_inc(v_snd_1744_);
v_fst_1745_ = lean_ctor_get(v_a_1739_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_a_1739_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_a_1739_, 1);
lean_dec(v_unused_1854_);
v___x_1747_ = v_a_1739_;
v_isShared_1748_ = v_isSharedCheck_1853_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_fst_1745_);
lean_dec(v_a_1739_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1853_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_fst_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1851_; 
v_fst_1749_ = lean_ctor_get(v_snd_1743_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_snd_1743_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v_snd_1743_, 1);
lean_dec(v_unused_1852_);
v___x_1751_ = v_snd_1743_;
v_isShared_1752_ = v_isSharedCheck_1851_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_fst_1749_);
lean_dec(v_snd_1743_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1851_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1849_; 
v_snd_1753_ = lean_ctor_get(v_snd_1744_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_snd_1744_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_snd_1744_, 0);
lean_dec(v_unused_1850_);
v___x_1755_ = v_snd_1744_;
v_isShared_1756_ = v_isSharedCheck_1849_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_dec(v_snd_1744_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1849_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v_options_1827_; uint8_t v_hasTrace_1828_; 
v_options_1827_ = lean_ctor_get(v___y_1730_, 2);
v_hasTrace_1828_ = lean_ctor_get_uint8(v_options_1827_, sizeof(void*)*1);
if (v_hasTrace_1828_ == 0)
{
lean_del_object(v___x_1747_);
v___y_1758_ = v___y_1721_;
v___y_1759_ = v___y_1722_;
v___y_1760_ = v___y_1723_;
v___y_1761_ = v___y_1724_;
v___y_1762_ = v___y_1725_;
v___y_1763_ = v___y_1726_;
v___y_1764_ = v___y_1727_;
v___y_1765_ = v___y_1728_;
v___y_1766_ = v___y_1729_;
v___y_1767_ = v___y_1730_;
v___y_1768_ = v___y_1731_;
goto v___jp_1757_;
}
else
{
lean_object* v_inheritedTraceOptions_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_inheritedTraceOptions_1829_ = lean_ctor_get(v___y_1730_, 13);
v___x_1830_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_1831_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_1832_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1829_, v_options_1827_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_del_object(v___x_1747_);
v___y_1758_ = v___y_1721_;
v___y_1759_ = v___y_1722_;
v___y_1760_ = v___y_1723_;
v___y_1761_ = v___y_1724_;
v___y_1762_ = v___y_1725_;
v___y_1763_ = v___y_1726_;
v___y_1764_ = v___y_1727_;
v___y_1765_ = v___y_1728_;
v___y_1766_ = v___y_1729_;
v___y_1767_ = v___y_1730_;
v___y_1768_ = v___y_1731_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1833_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__9);
lean_inc(v_snd_1753_);
v___x_1834_ = l_Nat_reprFast(v_snd_1753_);
v___x_1835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
v___x_1836_ = l_Lean_MessageData_ofFormat(v___x_1835_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set_tag(v___x_1747_, 7);
lean_ctor_set(v___x_1747_, 1, v___x_1836_);
lean_ctor_set(v___x_1747_, 0, v___x_1833_);
v___x_1838_ = v___x_1747_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_1830_, v___x_1838_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_dec_ref_known(v___x_1839_, 1);
v___y_1758_ = v___y_1721_;
v___y_1759_ = v___y_1722_;
v___y_1760_ = v___y_1723_;
v___y_1761_ = v___y_1724_;
v___y_1762_ = v___y_1725_;
v___y_1763_ = v___y_1726_;
v___y_1764_ = v___y_1727_;
v___y_1765_ = v___y_1728_;
v___y_1766_ = v___y_1729_;
v___y_1767_ = v___y_1730_;
v___y_1768_ = v___y_1731_;
goto v___jp_1757_;
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_del_object(v___x_1751_);
lean_dec(v_fst_1749_);
lean_dec(v_fst_1745_);
lean_del_object(v___x_1741_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
v___jp_1757_:
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fst_1745_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v_config_1771_; lean_object* v_hypotheses_1772_; lean_object* v_maxSteps_1773_; lean_object* v___x_1774_; lean_object* v_newHyps_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
lean_del_object(v___x_1741_);
v___x_1770_ = lean_st_ref_get(v___y_1759_);
v_config_1771_ = lean_ctor_get(v___y_1758_, 0);
v_hypotheses_1772_ = lean_ctor_get(v___x_1770_, 3);
lean_inc_ref(v_hypotheses_1772_);
lean_dec(v___x_1770_);
v_maxSteps_1773_ = lean_ctor_get(v_config_1771_, 1);
v___x_1774_ = lean_array_get_size(v_hypotheses_1772_);
v_newHyps_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
v___x_1776_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1773_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___x_1776_);
lean_ctor_set(v___x_1751_, 0, v_maxSteps_1773_);
v___x_1778_ = v___x_1751_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_maxSteps_1773_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_box(0);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v_newHyps_1775_);
lean_ctor_set(v___x_1755_, 0, v___x_1779_);
v___x_1781_ = v___x_1755_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_newHyps_1775_);
v___x_1781_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v___x_1774_, v_hypotheses_1772_, v_snd_1753_, v___x_1769_, v___x_1778_, v_fst_1749_, v_fst_1745_, v___x_1735_, v___x_1781_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v_fst_1749_);
lean_dec(v_snd_1753_);
lean_dec_ref(v_hypotheses_1772_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1811_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1811_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1811_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_fst_1787_; 
v_fst_1787_ = lean_ctor_get(v_a_1783_, 0);
if (lean_obj_tag(v_fst_1787_) == 0)
{
lean_object* v_snd_1788_; lean_object* v___x_1789_; lean_object* v_caches_1790_; lean_object* v_typeAnalysis_1791_; lean_object* v_target_1792_; uint8_t v_didChange_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1805_; 
v_snd_1788_ = lean_ctor_get(v_a_1783_, 1);
lean_inc(v_snd_1788_);
lean_dec(v_a_1783_);
v___x_1789_ = lean_st_ref_take(v___y_1759_);
v_caches_1790_ = lean_ctor_get(v___x_1789_, 0);
v_typeAnalysis_1791_ = lean_ctor_get(v___x_1789_, 1);
v_target_1792_ = lean_ctor_get(v___x_1789_, 2);
v_didChange_1793_ = lean_ctor_get_uint8(v___x_1789_, sizeof(void*)*4);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v___x_1789_, 3);
lean_dec(v_unused_1806_);
v___x_1795_ = v___x_1789_;
v_isShared_1796_ = v_isSharedCheck_1805_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_target_1792_);
lean_inc(v_typeAnalysis_1791_);
lean_inc(v_caches_1790_);
lean_dec(v___x_1789_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1805_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 3, v_snd_1788_);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_caches_1790_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_typeAnalysis_1791_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_target_1792_);
lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_snd_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*4, v_didChange_1793_);
v___x_1798_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = lean_st_ref_put(v___y_1759_, v___x_1798_);
v___x_1800_ = lean_box(v___x_1769_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1800_);
v___x_1802_ = v___x_1785_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_val_1807_; lean_object* v___x_1809_; 
lean_inc_ref(v_fst_1787_);
lean_dec(v_a_1783_);
v_val_1807_ = lean_ctor_get(v_fst_1787_, 0);
lean_inc(v_val_1807_);
lean_dec_ref_known(v_fst_1787_, 1);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v_val_1807_);
v___x_1809_ = v___x_1785_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_val_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1782_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1782_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
}
else
{
uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_del_object(v___x_1751_);
lean_dec(v_fst_1749_);
lean_dec(v_fst_1745_);
v___x_1822_ = 0;
v___x_1823_ = lean_box(v___x_1822_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1823_);
v___x_1825_ = v___x_1741_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1738_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1738_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(lean_object* v___f_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v_target_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1890_ = lean_st_ref_get(v___y_1879_);
v_target_1891_ = lean_ctor_get(v___x_1890_, 2);
lean_inc_ref(v_target_1891_);
lean_dec(v___x_1890_);
v___x_1892_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1891_);
lean_dec_ref(v_target_1891_);
v___x_1893_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__12___redArg(v___x_1892_, v___f_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object* v___f_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(v___f_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(lean_object* v_cls_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_1918_, v_msg_1919_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___boxed(lean_object* v_cls_1933_, lean_object* v_msg_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(v_cls_1933_, v_msg_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(lean_object* v_00_u03b2_1948_, lean_object* v_m_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_1949_, v_a_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object* v_00_u03b2_1952_, lean_object* v_m_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(v_00_u03b2_1952_, v_m_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_m_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(lean_object* v_00_u03b2_1956_, lean_object* v_x_1957_, lean_object* v_x_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_1957_, v_x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object* v_00_u03b2_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(v_00_u03b2_1960_, v_x_1961_, v_x_1962_);
lean_dec_ref(v_x_1962_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(lean_object* v_upperBound_1964_, lean_object* v___x_1965_, lean_object* v___x_1966_, uint8_t v___x_1967_, lean_object* v___x_1968_, lean_object* v___x_1969_, lean_object* v___x_1970_, lean_object* v_inst_1971_, lean_object* v_R_1972_, lean_object* v_a_1973_, lean_object* v_b_1974_, lean_object* v_c_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_1964_, v___x_1965_, v___x_1966_, v___x_1967_, v___x_1968_, v___x_1969_, v___x_1970_, v_a_1973_, v_b_1974_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_1989_ = _args[0];
lean_object* v___x_1990_ = _args[1];
lean_object* v___x_1991_ = _args[2];
lean_object* v___x_1992_ = _args[3];
lean_object* v___x_1993_ = _args[4];
lean_object* v___x_1994_ = _args[5];
lean_object* v___x_1995_ = _args[6];
lean_object* v_inst_1996_ = _args[7];
lean_object* v_R_1997_ = _args[8];
lean_object* v_a_1998_ = _args[9];
lean_object* v_b_1999_ = _args[10];
lean_object* v_c_2000_ = _args[11];
lean_object* v___y_2001_ = _args[12];
lean_object* v___y_2002_ = _args[13];
lean_object* v___y_2003_ = _args[14];
lean_object* v___y_2004_ = _args[15];
lean_object* v___y_2005_ = _args[16];
lean_object* v___y_2006_ = _args[17];
lean_object* v___y_2007_ = _args[18];
lean_object* v___y_2008_ = _args[19];
lean_object* v___y_2009_ = _args[20];
lean_object* v___y_2010_ = _args[21];
lean_object* v___y_2011_ = _args[22];
lean_object* v___y_2012_ = _args[23];
_start:
{
uint8_t v___x_112627__boxed_2013_; lean_object* v_res_2014_; 
v___x_112627__boxed_2013_ = lean_unbox(v___x_1992_);
v_res_2014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(v_upperBound_1989_, v___x_1990_, v___x_1991_, v___x_112627__boxed_2013_, v___x_1993_, v___x_1994_, v___x_1995_, v_inst_1996_, v_R_1997_, v_a_1998_, v_b_1999_, v_c_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec_ref(v___x_1994_);
lean_dec(v___x_1991_);
lean_dec_ref(v___x_1990_);
lean_dec(v_upperBound_1989_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_object* v_00_u03b2_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_x_2016_, v_x_2017_, v_x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(lean_object* v_00_u03b2_2020_, lean_object* v_m_2021_, lean_object* v_query_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_m_2021_, v_query_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___boxed(lean_object* v_00_u03b2_2024_, lean_object* v_m_2025_, lean_object* v_query_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(v_00_u03b2_2024_, v_m_2025_, v_query_2026_);
lean_dec(v_query_2026_);
lean_dec_ref(v_m_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(lean_object* v_00_u03b2_2028_, lean_object* v_m_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_m_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___boxed(lean_object* v_00_u03b2_2031_, lean_object* v_m_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(v_00_u03b2_2031_, v_m_2032_);
lean_dec_ref(v_m_2032_);
return v_res_2033_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(lean_object* v_00_u03b2_2034_, lean_object* v_m_2035_, lean_object* v_a_2036_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_m_2035_, v_a_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___boxed(lean_object* v_00_u03b2_2038_, lean_object* v_m_2039_, lean_object* v_a_2040_){
_start:
{
uint8_t v_res_2041_; lean_object* v_r_2042_; 
v_res_2041_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(v_00_u03b2_2038_, v_m_2039_, v_a_2040_);
lean_dec_ref(v_a_2040_);
lean_dec_ref(v_m_2039_);
v_r_2042_ = lean_box(v_res_2041_);
return v_r_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(lean_object* v_00_u03b2_2043_, lean_object* v_m_2044_, lean_object* v_query_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_m_2044_, v_query_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___boxed(lean_object* v_00_u03b2_2047_, lean_object* v_m_2048_, lean_object* v_query_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(v_00_u03b2_2047_, v_m_2048_, v_query_2049_);
lean_dec_ref(v_query_2049_);
lean_dec_ref(v_m_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(lean_object* v_00_u03b2_2051_, lean_object* v_m_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_m_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___boxed(lean_object* v_00_u03b2_2054_, lean_object* v_m_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(v_00_u03b2_2054_, v_m_2055_);
lean_dec_ref(v_m_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11(lean_object* v_upperBound_2057_, lean_object* v___x_2058_, lean_object* v_inst_2059_, lean_object* v_R_2060_, lean_object* v_a_2061_, lean_object* v_b_2062_, lean_object* v_c_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___redArg(v_upperBound_2057_, v___x_2058_, v_a_2061_, v_b_2062_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_2077_ = _args[0];
lean_object* v___x_2078_ = _args[1];
lean_object* v_inst_2079_ = _args[2];
lean_object* v_R_2080_ = _args[3];
lean_object* v_a_2081_ = _args[4];
lean_object* v_b_2082_ = _args[5];
lean_object* v_c_2083_ = _args[6];
lean_object* v___y_2084_ = _args[7];
lean_object* v___y_2085_ = _args[8];
lean_object* v___y_2086_ = _args[9];
lean_object* v___y_2087_ = _args[10];
lean_object* v___y_2088_ = _args[11];
lean_object* v___y_2089_ = _args[12];
lean_object* v___y_2090_ = _args[13];
lean_object* v___y_2091_ = _args[14];
lean_object* v___y_2092_ = _args[15];
lean_object* v___y_2093_ = _args[16];
lean_object* v___y_2094_ = _args[17];
lean_object* v___y_2095_ = _args[18];
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__11(v_upperBound_2077_, v___x_2078_, v_inst_2079_, v_R_2080_, v_a_2081_, v_b_2082_, v_c_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v___x_2078_);
lean_dec(v_upperBound_2077_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(lean_object* v_00_u03b2_2097_, lean_object* v_m_2098_, lean_object* v_query_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_m_2098_, v_query_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2101_, lean_object* v_m_2102_, lean_object* v_query_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(v_00_u03b2_2101_, v_m_2102_, v_query_2103_);
lean_dec(v_query_2103_);
lean_dec_ref(v_m_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_object* v_00_u03b2_2105_, lean_object* v_x_2106_, size_t v_x_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_2106_, v_x_2107_, v_x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
size_t v_x_112754__boxed_2114_; lean_object* v_res_2115_; 
v_x_112754__boxed_2114_ = lean_unbox_usize(v_x_2112_);
lean_dec(v_x_2112_);
v_res_2115_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(v_00_u03b2_2110_, v_x_2111_, v_x_112754__boxed_2114_, v_x_2113_);
lean_dec_ref(v_x_2113_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_object* v_00_u03b2_2116_, lean_object* v_x_2117_, size_t v_x_2118_, size_t v_x_2119_, lean_object* v_x_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_x_2117_, v_x_2118_, v_x_2119_, v_x_2120_, v_x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
size_t v_x_112765__boxed_2129_; size_t v_x_112766__boxed_2130_; lean_object* v_res_2131_; 
v_x_112765__boxed_2129_ = lean_unbox_usize(v_x_2125_);
lean_dec(v_x_2125_);
v_x_112766__boxed_2130_ = lean_unbox_usize(v_x_2126_);
lean_dec(v_x_2126_);
v_res_2131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(v_00_u03b2_2123_, v_x_2124_, v_x_112765__boxed_2129_, v_x_112766__boxed_2130_, v_x_2127_, v_x_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(lean_object* v_00_u03b2_2132_, lean_object* v_m_2133_, lean_object* v_query_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_m_2133_, v_query_2134_, v_x_2135_, v_x_2136_, v_x_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2140_, lean_object* v_m_2141_, lean_object* v_query_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(v_00_u03b2_2140_, v_m_2141_, v_query_2142_, v_x_2143_, v_x_2144_, v_x_2145_, v_x_2146_);
lean_dec(v_query_2142_);
lean_dec_ref(v_m_2141_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_object* v_00_u03b2_2148_, lean_object* v_init_2149_, lean_object* v_b_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_init_2149_, v_b_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___boxed(lean_object* v_00_u03b2_2152_, lean_object* v_init_2153_, lean_object* v_b_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(v_00_u03b2_2152_, v_init_2153_, v_b_2154_);
lean_dec_ref(v_b_2154_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14(lean_object* v_00_u03b2_2156_, lean_object* v_m_2157_, lean_object* v_query_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___redArg(v_m_2157_, v_query_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14___boxed(lean_object* v_00_u03b2_2160_, lean_object* v_m_2161_, lean_object* v_query_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__14(v_00_u03b2_2160_, v_m_2161_, v_query_2162_);
lean_dec_ref(v_query_2162_);
lean_dec_ref(v_m_2161_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16(lean_object* v_00_u03b2_2164_, lean_object* v_m_2165_, lean_object* v_query_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___redArg(v_m_2165_, v_query_2166_, v_x_2167_, v_x_2168_, v_x_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16___boxed(lean_object* v_00_u03b2_2172_, lean_object* v_m_2173_, lean_object* v_query_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_spec__16(v_00_u03b2_2172_, v_m_2173_, v_query_2174_, v_x_2175_, v_x_2176_, v_x_2177_, v_x_2178_);
lean_dec_ref(v_query_2174_);
lean_dec_ref(v_m_2173_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18(lean_object* v_00_u03b2_2180_, lean_object* v_init_2181_, lean_object* v_b_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___redArg(v_init_2181_, v_b_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18___boxed(lean_object* v_00_u03b2_2184_, lean_object* v_init_2185_, lean_object* v_b_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18(v_00_u03b2_2184_, v_init_2185_, v_b_2186_);
lean_dec_ref(v_b_2186_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_2188_, lean_object* v_n_2189_, lean_object* v_k_2190_, lean_object* v_v_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11___redArg(v_n_2189_, v_k_2190_, v_v_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_2193_, size_t v_depth_2194_, lean_object* v_keys_2195_, lean_object* v_vals_2196_, lean_object* v_heq_2197_, lean_object* v_i_2198_, lean_object* v_entries_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___redArg(v_depth_2194_, v_keys_2195_, v_vals_2196_, v_i_2198_, v_entries_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2201_, lean_object* v_depth_2202_, lean_object* v_keys_2203_, lean_object* v_vals_2204_, lean_object* v_heq_2205_, lean_object* v_i_2206_, lean_object* v_entries_2207_){
_start:
{
size_t v_depth_boxed_2208_; lean_object* v_res_2209_; 
v_depth_boxed_2208_ = lean_unbox_usize(v_depth_2202_);
lean_dec(v_depth_2202_);
v_res_2209_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__12(v_00_u03b2_2201_, v_depth_boxed_2208_, v_keys_2203_, v_vals_2204_, v_heq_2205_, v_i_2206_, v_entries_2207_);
lean_dec_ref(v_vals_2204_);
lean_dec_ref(v_keys_2203_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_2210_, lean_object* v_b_2211_, lean_object* v_acc_2212_, lean_object* v_i_2213_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___redArg(v_b_2211_, v_acc_2212_, v_i_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17___boxed(lean_object* v_00_u03b2_2215_, lean_object* v_b_2216_, lean_object* v_acc_2217_, lean_object* v_i_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_spec__17(v_00_u03b2_2215_, v_b_2216_, v_acc_2217_, v_i_2218_);
lean_dec_ref(v_b_2216_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_2220_, lean_object* v_b_2221_, lean_object* v_acc_2222_, lean_object* v_i_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___redArg(v_b_2221_, v_acc_2222_, v_i_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24___boxed(lean_object* v_00_u03b2_2225_, lean_object* v_b_2226_, lean_object* v_acc_2227_, lean_object* v_i_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_spec__18_spec__24(v_00_u03b2_2225_, v_b_2226_, v_acc_2227_, v_i_2228_);
lean_dec_ref(v_b_2226_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11_spec__19(lean_object* v_00_u03b2_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_spec__11_spec__19___redArg(v_x_2231_, v_x_2232_, v_x_2233_, v_x_2234_);
return v___x_2235_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
}
#ifdef __cplusplus
}
#endif

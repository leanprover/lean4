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
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_false_of_not_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 197, 166, 197, 7, 119, 67, 87)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(123, 183, 41, 160, 188, 151, 196, 147)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Chose min depth at: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_2602__boxed_50_; lean_object* v_res_51_; 
v_x_2602__boxed_50_ = lean_unbox_usize(v_x_48_);
lean_dec(v_x_48_);
v_res_51_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_47_, v_x_2602__boxed_50_, v_x_49_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_box(0);
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9));
v___x_85_ = l_Lean_mkConst(v___x_84_, v___x_83_);
return v___x_85_;
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
lean_object* v___x_129_; lean_object* v_proof_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10);
v_proof_130_ = l_Lean_mkAppB(v___x_129_, v_e_95_, v_proof_107_);
v___x_131_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13);
v___x_132_ = l_Lean_Meta_Sym_shareCommonInc(v___x_131_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_141_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_137_, 0, v_a_133_);
lean_ctor_set(v___x_137_, 1, v_proof_130_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*2, v___x_109_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*2 + 1, v___x_104_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
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
lean_dec_ref(v_proof_130_);
v_a_142_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_132_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_132_);
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
size_t v_x_2880__boxed_213_; lean_object* v_res_214_; 
v_x_2880__boxed_213_ = lean_unbox_usize(v_x_211_);
lean_dec(v_x_211_);
v_res_214_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0(v_00_u03b2_209_, v_x_210_, v_x_2880__boxed_213_, v_x_212_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0(lean_object* v_x_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0___boxed(lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0(v_x_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(lean_object* v_mvarId_269_, lean_object* v_x_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
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
v___f_283_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0___boxed), 13, 8);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___boxed(lean_object* v_mvarId_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_mvarId_293_, v_x_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(lean_object* v_00_u03b1_308_, lean_object* v_mvarId_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_mvarId_309_, v_x_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___boxed(lean_object* v_00_u03b1_324_, lean_object* v_mvarId_325_, lean_object* v_x_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(v_00_u03b1_324_, v_mvarId_325_, v_x_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
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
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
if (v_isShared_362_ == 0)
{
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_caches_356_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_typeAnalysis_357_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_target_358_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_hypotheses_359_);
v___x_365_ = v_reuseFailAlloc_368_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*4, v___x_340_);
v___x_366_ = lean_st_ref_put(v___y_344_, v___x_365_);
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
v___x_367_ = lean_apply_13(v___f_341_, v___x_363_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, lean_box(0));
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed(lean_object* v___x_370_, lean_object* v___f_371_, lean_object* v_____r_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
uint8_t v___x_78082__boxed_385_; lean_object* v_res_386_; 
v___x_78082__boxed_385_ = lean_unbox(v___x_370_);
v_res_386_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(v___x_78082__boxed_385_, v___f_371_, v_____r_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(lean_object* v_a_387_, lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
lean_object* v_key_390_; lean_object* v_value_391_; lean_object* v_tail_392_; uint8_t v___x_393_; 
v_key_390_ = lean_ctor_get(v_x_388_, 0);
v_value_391_ = lean_ctor_get(v_x_388_, 1);
v_tail_392_ = lean_ctor_get(v_x_388_, 2);
v___x_393_ = lean_nat_dec_eq(v_key_390_, v_a_387_);
if (v___x_393_ == 0)
{
v_x_388_ = v_tail_392_;
goto _start;
}
else
{
lean_object* v___x_395_; 
lean_inc(v_value_391_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_value_391_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg___boxed(lean_object* v_a_396_, lean_object* v_x_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_396_, v_x_397_);
lean_dec(v_x_397_);
lean_dec(v_a_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_buckets_401_; lean_object* v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v_fold_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_buckets_401_ = lean_ctor_get(v_m_399_, 1);
v___x_402_ = lean_array_get_size(v_buckets_401_);
v___x_403_ = lean_uint64_of_nat(v_a_400_);
v___x_404_ = 32ULL;
v___x_405_ = lean_uint64_shift_right(v___x_403_, v___x_404_);
v_fold_406_ = lean_uint64_xor(v___x_403_, v___x_405_);
v___x_407_ = 16ULL;
v___x_408_ = lean_uint64_shift_right(v_fold_406_, v___x_407_);
v___x_409_ = lean_uint64_xor(v_fold_406_, v___x_408_);
v___x_410_ = lean_uint64_to_usize(v___x_409_);
v___x_411_ = lean_usize_of_nat(v___x_402_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_sub(v___x_411_, v___x_412_);
v___x_414_ = lean_usize_land(v___x_410_, v___x_413_);
v___x_415_ = lean_array_uget_borrowed(v_buckets_401_, v___x_414_);
v___x_416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_400_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_m_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14(lean_object* v_xs_420_, lean_object* v_v_421_, lean_object* v_i_422_){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_array_get_size(v_xs_420_);
v___x_424_ = lean_nat_dec_lt(v_i_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_dec(v_i_422_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
else
{
lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; uint8_t v___x_429_; 
v___x_426_ = lean_array_fget_borrowed(v_xs_420_, v_i_422_);
v___x_427_ = lean_ptr_addr(v___x_426_);
v___x_428_ = lean_ptr_addr(v_v_421_);
v___x_429_ = lean_usize_dec_eq(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_i_422_, v___x_430_);
lean_dec(v_i_422_);
v_i_422_ = v___x_431_;
goto _start;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v_i_422_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14___boxed(lean_object* v_xs_434_, lean_object* v_v_435_, lean_object* v_i_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14(v_xs_434_, v_v_435_, v_i_436_);
lean_dec_ref(v_v_435_);
lean_dec_ref(v_xs_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(lean_object* v_xs_438_, lean_object* v_v_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14(v_xs_438_, v_v_439_, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7___boxed(lean_object* v_xs_442_, lean_object* v_v_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(v_xs_442_, v_v_443_);
lean_dec_ref(v_v_443_);
lean_dec_ref(v_xs_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(lean_object* v_x_445_, size_t v_x_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_es_448_; lean_object* v___x_449_; size_t v___x_450_; size_t v___x_451_; lean_object* v_j_452_; lean_object* v_entry_453_; 
v_es_448_ = lean_ctor_get(v_x_445_, 0);
v___x_449_ = lean_box(2);
v___x_450_ = ((size_t)31ULL);
v___x_451_ = lean_usize_land(v_x_446_, v___x_450_);
v_j_452_ = lean_usize_to_nat(v___x_451_);
v_entry_453_ = lean_array_get(v___x_449_, v_es_448_, v_j_452_);
switch(lean_obj_tag(v_entry_453_))
{
case 0:
{
lean_object* v_key_454_; size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v_key_454_ = lean_ctor_get(v_entry_453_, 0);
lean_inc(v_key_454_);
lean_dec_ref_known(v_entry_453_, 2);
v___x_455_ = lean_ptr_addr(v_x_447_);
v___x_456_ = lean_ptr_addr(v_key_454_);
lean_dec(v_key_454_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_dec(v_j_452_);
return v_x_445_;
}
else
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
lean_inc_ref(v_es_448_);
v_isSharedCheck_465_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_x_445_, 0);
lean_dec(v_unused_466_);
v___x_459_ = v_x_445_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_x_445_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_array_set(v_es_448_, v_j_452_, v___x_449_);
lean_dec(v_j_452_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
case 1:
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_501_; 
lean_inc_ref(v_es_448_);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_x_445_, 0);
lean_dec(v_unused_502_);
v___x_468_ = v_x_445_;
v_isShared_469_ = v_isSharedCheck_501_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_x_445_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_501_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_node_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_500_; 
v_node_470_ = lean_ctor_get(v_entry_453_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_entry_453_);
if (v_isSharedCheck_500_ == 0)
{
v___x_472_ = v_entry_453_;
v_isShared_473_ = v_isSharedCheck_500_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_node_470_);
lean_dec(v_entry_453_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_500_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
size_t v___x_474_; lean_object* v_entries_475_; size_t v___x_476_; lean_object* v_newNode_477_; lean_object* v___x_478_; 
v___x_474_ = ((size_t)5ULL);
v_entries_475_ = lean_array_set(v_es_448_, v_j_452_, v___x_449_);
v___x_476_ = lean_usize_shift_right(v_x_446_, v___x_474_);
v_newNode_477_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_node_470_, v___x_476_, v_x_447_);
lean_inc_ref(v_newNode_477_);
v___x_478_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_480_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v_newNode_477_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_newNode_477_);
v___x_480_ = v_reuseFailAlloc_485_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_array_set(v_entries_475_, v_j_452_, v___x_480_);
lean_dec(v_j_452_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_481_);
v___x_483_ = v___x_468_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_val_486_; lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_499_; 
lean_dec_ref(v_newNode_477_);
lean_del_object(v___x_472_);
v_val_486_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v___x_478_, 1);
v_fst_487_ = lean_ctor_get(v_val_486_, 0);
v_snd_488_ = lean_ctor_get(v_val_486_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_val_486_);
if (v_isSharedCheck_499_ == 0)
{
v___x_490_ = v_val_486_;
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v_val_486_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_499_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_fst_487_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_snd_488_);
v___x_493_ = v_reuseFailAlloc_498_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_array_set(v_entries_475_, v_j_452_, v___x_493_);
lean_dec(v_j_452_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_494_);
v___x_496_ = v___x_468_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_452_);
return v_x_445_;
}
}
}
else
{
lean_object* v_ks_503_; lean_object* v_vs_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_518_; 
v_ks_503_ = lean_ctor_get(v_x_445_, 0);
v_vs_504_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_518_ == 0)
{
v___x_506_ = v_x_445_;
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_vs_504_);
lean_inc(v_ks_503_);
lean_dec(v_x_445_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(v_ks_503_, v_x_447_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v___x_510_; 
if (v_isShared_507_ == 0)
{
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_ks_503_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_vs_504_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_val_512_; lean_object* v_keys_x27_513_; lean_object* v_vals_x27_514_; lean_object* v___x_516_; 
v_val_512_ = lean_ctor_get(v___x_508_, 0);
lean_inc_n(v_val_512_, 2);
lean_dec_ref_known(v___x_508_, 1);
v_keys_x27_513_ = l_Array_eraseIdx___redArg(v_ks_503_, v_val_512_);
v_vals_x27_514_ = l_Array_eraseIdx___redArg(v_vs_504_, v_val_512_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_vals_x27_514_);
lean_ctor_set(v___x_506_, 0, v_keys_x27_513_);
v___x_516_ = v___x_506_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_keys_x27_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_vals_x27_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg___boxed(lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
size_t v_x_78224__boxed_522_; lean_object* v_res_523_; 
v_x_78224__boxed_522_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_523_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_519_, v_x_78224__boxed_522_, v_x_521_);
lean_dec_ref(v_x_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; uint64_t v___x_529_; size_t v_h_530_; lean_object* v___x_531_; 
v___x_526_ = lean_ptr_addr(v_x_525_);
v___x_527_ = ((size_t)3ULL);
v___x_528_ = lean_usize_shift_right(v___x_526_, v___x_527_);
v___x_529_ = lean_usize_to_uint64(v___x_528_);
v_h_530_ = lean_uint64_to_usize(v___x_529_);
v___x_531_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_524_, v_h_530_, v_x_525_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_532_, v_x_533_);
lean_dec_ref(v_x_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(uint8_t v___x_535_, lean_object* v_x_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_547_, 0, v___x_535_);
lean_ctor_set_uint8(v___x_547_, 1, v___x_535_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed(lean_object* v___x_549_, lean_object* v_x_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___x_78379__boxed_561_; lean_object* v_res_562_; 
v___x_78379__boxed_561_ = lean_unbox(v___x_549_);
v_res_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(v___x_78379__boxed_561_, v_x_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v_x_550_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(lean_object* v_snd_563_, lean_object* v_a_564_, lean_object* v___x_565_, lean_object* v_____r_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = lean_array_push(v_snd_563_, v_a_564_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_565_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed(lean_object* v_snd_583_, lean_object* v_a_584_, lean_object* v___x_585_, lean_object* v_____r_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_583_, v_a_584_, v___x_585_, v_____r_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(lean_object* v_msgData_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v_env_607_; lean_object* v___x_608_; lean_object* v_toCold_609_; lean_object* v_mctx_610_; lean_object* v_lctx_611_; lean_object* v_options_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_606_ = lean_st_ref_get(v___y_604_);
v_env_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc_ref(v_env_607_);
lean_dec(v___x_606_);
v___x_608_ = lean_st_ref_get(v___y_602_);
v_toCold_609_ = lean_ctor_get(v___y_603_, 0);
v_mctx_610_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_mctx_610_);
lean_dec(v___x_608_);
v_lctx_611_ = lean_ctor_get(v___y_601_, 2);
v_options_612_ = lean_ctor_get(v_toCold_609_, 2);
lean_inc_ref(v_options_612_);
lean_inc_ref(v_lctx_611_);
v___x_613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_613_, 0, v_env_607_);
lean_ctor_set(v___x_613_, 1, v_mctx_610_);
lean_ctor_set(v___x_613_, 2, v_lctx_611_);
lean_ctor_set(v___x_613_, 3, v_options_612_);
v___x_614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_msgData_600_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1___boxed(lean_object* v_msgData_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msgData_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_623_; double v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_float_of_nat(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(lean_object* v_cls_628_, lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_ref_635_; lean_object* v___x_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_682_; 
v_ref_635_ = lean_ctor_get(v___y_632_, 2);
v___x_636_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_682_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_682_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_682_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v_traceState_642_; lean_object* v_env_643_; lean_object* v_nextMacroScope_644_; lean_object* v_ngen_645_; lean_object* v_auxDeclNGen_646_; lean_object* v_cache_647_; lean_object* v_recordedDeps_648_; lean_object* v_messages_649_; lean_object* v_infoState_650_; lean_object* v_snapshotTasks_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_681_; 
v___x_641_ = lean_st_ref_take(v___y_633_);
v_traceState_642_ = lean_ctor_get(v___x_641_, 4);
v_env_643_ = lean_ctor_get(v___x_641_, 0);
v_nextMacroScope_644_ = lean_ctor_get(v___x_641_, 1);
v_ngen_645_ = lean_ctor_get(v___x_641_, 2);
v_auxDeclNGen_646_ = lean_ctor_get(v___x_641_, 3);
v_cache_647_ = lean_ctor_get(v___x_641_, 5);
v_recordedDeps_648_ = lean_ctor_get(v___x_641_, 6);
v_messages_649_ = lean_ctor_get(v___x_641_, 7);
v_infoState_650_ = lean_ctor_get(v___x_641_, 8);
v_snapshotTasks_651_ = lean_ctor_get(v___x_641_, 9);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_681_ == 0)
{
v___x_653_ = v___x_641_;
v_isShared_654_ = v_isSharedCheck_681_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_snapshotTasks_651_);
lean_inc(v_infoState_650_);
lean_inc(v_messages_649_);
lean_inc(v_recordedDeps_648_);
lean_inc(v_cache_647_);
lean_inc(v_traceState_642_);
lean_inc(v_auxDeclNGen_646_);
lean_inc(v_ngen_645_);
lean_inc(v_nextMacroScope_644_);
lean_inc(v_env_643_);
lean_dec(v___x_641_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_681_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint64_t v_tid_655_; lean_object* v_traces_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_680_; 
v_tid_655_ = lean_ctor_get_uint64(v_traceState_642_, sizeof(void*)*1);
v_traces_656_ = lean_ctor_get(v_traceState_642_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_traceState_642_);
if (v_isSharedCheck_680_ == 0)
{
v___x_658_ = v_traceState_642_;
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_traces_656_);
lean_dec(v_traceState_642_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_680_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; double v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_660_ = lean_box(0);
v___x_661_ = lean_box(0);
v___x_662_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0);
v___x_663_ = 0;
v___x_664_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1));
v___x_665_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_665_, 0, v_cls_628_);
lean_ctor_set(v___x_665_, 1, v___x_661_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
lean_ctor_set_float(v___x_665_, sizeof(void*)*3, v___x_662_);
lean_ctor_set_float(v___x_665_, sizeof(void*)*3 + 8, v___x_662_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*3 + 16, v___x_663_);
v___x_666_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2));
v___x_667_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v_a_637_);
lean_ctor_set(v___x_667_, 2, v___x_666_);
lean_inc(v_ref_635_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_ref_635_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_PersistentArray_push___redArg(v_traces_656_, v___x_668_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_669_);
v___x_671_ = v___x_658_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_669_);
lean_ctor_set_uint64(v_reuseFailAlloc_679_, sizeof(void*)*1, v_tid_655_);
v___x_671_ = v_reuseFailAlloc_679_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v___x_671_);
v___x_673_ = v___x_653_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_env_643_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_nextMacroScope_644_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_ngen_645_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_auxDeclNGen_646_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v_cache_647_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_recordedDeps_648_);
lean_ctor_set(v_reuseFailAlloc_678_, 7, v_messages_649_);
lean_ctor_set(v_reuseFailAlloc_678_, 8, v_infoState_650_);
lean_ctor_set(v_reuseFailAlloc_678_, 9, v_snapshotTasks_651_);
v___x_673_ = v_reuseFailAlloc_678_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_st_ref_put(v___y_633_, v___x_673_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_660_);
v___x_676_ = v___x_639_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_660_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___boxed(lean_object* v_cls_683_, lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_683_, v_msg_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_701_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4));
v___x_702_ = l_Lean_Name_append(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(lean_object* v_upperBound_706_, lean_object* v___x_707_, lean_object* v___x_708_, uint8_t v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v_a_713_, lean_object* v_b_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___y_728_; lean_object* v___y_751_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; uint8_t v___x_781_; 
v___x_781_ = lean_nat_dec_lt(v_a_713_, v_upperBound_706_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_710_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v_b_714_);
return v___x_782_;
}
else
{
lean_object* v_snd_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_853_; 
v_snd_783_ = lean_ctor_get(v_b_714_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_b_714_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_b_714_, 0);
lean_dec(v_unused_854_);
v___x_785_ = v_b_714_;
v_isShared_786_ = v_isSharedCheck_853_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snd_783_);
lean_dec(v_b_714_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_853_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___y_792_; lean_object* v___x_850_; 
v___x_787_ = lean_box(v___x_709_);
v___f_788_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_788_, 0, v___x_787_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_array_fget_borrowed(v___x_707_, v_a_713_);
v___x_850_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v___x_711_, v_a_713_);
if (lean_obj_tag(v___x_850_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_852_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_850_, 1);
lean_inc_ref(v___x_712_);
v___x_852_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v___x_712_, v_val_851_);
lean_dec(v_val_851_);
v___y_792_ = v___x_852_;
goto v___jp_791_;
}
else
{
lean_dec(v___x_850_);
lean_inc_ref(v___x_712_);
v___y_792_ = v___x_712_;
goto v___jp_791_;
}
v___jp_791_:
{
lean_object* v_type_793_; uint32_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_type_793_ = lean_ctor_get(v___x_790_, 1);
v___x_794_ = lean_uint32_of_nat(v___x_708_);
v___x_795_ = lean_box_uint32(v___x_794_);
v___x_796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed), 13, 2);
lean_closure_set(v___x_796_, 0, v___x_795_);
lean_closure_set(v___x_796_, 1, v___y_792_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___f_788_);
lean_inc_ref(v_type_793_);
v___x_798_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_798_, 0, v_type_793_);
lean_inc_ref(v___x_710_);
v___x_799_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_798_, v___x_797_, v___x_710_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
lean_inc(v___x_790_);
v___x_801_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_790_, v_a_800_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v_type_803_; lean_object* v_value_804_; uint8_t v___x_805_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
v_type_803_ = lean_ctor_get(v_a_802_, 1);
v_value_804_ = lean_ctor_get(v_a_802_, 2);
lean_inc_ref(v_type_803_);
v___x_805_ = l_Lean_Expr_isFalse(v_type_803_);
if (v___x_805_ == 0)
{
lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___f_808_; uint8_t v___x_809_; 
lean_del_object(v___x_785_);
lean_inc(v_a_802_);
lean_inc(v_snd_783_);
v___f_806_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_806_, 0, v_snd_783_);
lean_closure_set(v___f_806_, 1, v_a_802_);
lean_closure_set(v___f_806_, 2, v___x_789_);
v___x_807_ = lean_box(v___x_781_);
v___f_808_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed), 15, 2);
lean_closure_set(v___f_808_, 0, v___x_807_);
lean_closure_set(v___f_808_, 1, v___f_806_);
v___x_809_ = lean_expr_eqv(v_type_793_, v_type_803_);
if (v___x_809_ == 0)
{
lean_inc_ref(v_type_803_);
lean_dec(v_a_802_);
lean_dec(v_snd_783_);
lean_inc_ref(v_type_793_);
v___y_755_ = v_type_793_;
v___y_756_ = v_type_803_;
v___y_757_ = v___f_808_;
goto v___jp_754_;
}
else
{
if (v___x_805_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec_ref(v___f_808_);
v___x_810_ = lean_box(0);
v___x_811_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_783_, v_a_802_, v___x_789_, v___x_810_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
v___y_728_ = v___x_811_;
goto v___jp_727_;
}
else
{
lean_inc_ref(v_type_803_);
lean_dec(v_a_802_);
lean_dec(v_snd_783_);
lean_inc_ref(v_type_793_);
v___y_755_ = v_type_793_;
v___y_756_ = v_type_803_;
v___y_757_ = v___f_808_;
goto v___jp_754_;
}
}
}
else
{
lean_object* v___x_812_; 
lean_inc_ref(v_value_804_);
lean_dec(v_a_802_);
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_710_);
v___x_812_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_804_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_824_; 
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_825_);
v___x_814_ = v___x_812_;
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
else
{
lean_dec(v___x_812_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_816_ = lean_box(v___x_781_);
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_817_);
v___x_819_ = v___x_785_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_snd_783_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_819_);
v___x_821_ = v___x_814_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_del_object(v___x_785_);
lean_dec(v_snd_783_);
v_a_826_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_812_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_812_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_del_object(v___x_785_);
lean_dec(v_snd_783_);
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_710_);
v_a_834_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_801_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_801_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_del_object(v___x_785_);
lean_dec(v_snd_783_);
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_710_);
v_a_842_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_799_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_799_);
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
v___jp_727_:
{
if (lean_obj_tag(v___y_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_741_; 
v_a_729_ = lean_ctor_get(v___y_728_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___y_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_731_ = v___y_728_;
v_isShared_732_ = v_isSharedCheck_741_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___y_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_741_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
if (lean_obj_tag(v_a_729_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; 
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_710_);
v_a_733_ = lean_ctor_get(v_a_729_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v_a_729_, 1);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v_a_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_del_object(v___x_731_);
v_a_737_ = lean_ctor_get(v_a_729_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v_a_729_, 1);
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_add(v_a_713_, v___x_738_);
lean_dec(v_a_713_);
v_a_713_ = v___x_739_;
v_b_714_ = v_a_737_;
goto _start;
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_710_);
v_a_742_ = lean_ctor_get(v___y_728_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___y_728_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___y_728_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___y_728_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
v___jp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
v___x_753_ = lean_apply_13(v___y_751_, v___x_752_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, lean_box(0));
v___y_728_ = v___x_753_;
goto v___jp_727_;
}
v___jp_754_:
{
lean_object* v_toCold_758_; lean_object* v_options_759_; uint8_t v_hasTrace_760_; 
v_toCold_758_ = lean_ctor_get(v___y_724_, 0);
v_options_759_ = lean_ctor_get(v_toCold_758_, 2);
v_hasTrace_760_ = lean_ctor_get_uint8(v_options_759_, sizeof(void*)*1);
if (v_hasTrace_760_ == 0)
{
lean_dec_ref(v___y_756_);
lean_dec_ref(v___y_755_);
v___y_751_ = v___y_757_;
goto v___jp_750_;
}
else
{
lean_object* v_inheritedTraceOptions_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_inheritedTraceOptions_761_ = lean_ctor_get(v_toCold_758_, 11);
v___x_762_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_763_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_761_, v_options_759_, v___x_763_);
if (v___x_764_ == 0)
{
lean_dec_ref(v___y_756_);
lean_dec_ref(v___y_755_);
v___y_751_ = v___y_757_;
goto v___jp_750_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_765_ = l_Lean_MessageData_ofExpr(v___y_755_);
v___x_766_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_MessageData_ofExpr(v___y_756_);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_762_, v___x_769_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
v___x_772_ = lean_apply_13(v___y_757_, v_a_771_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, lean_box(0));
v___y_728_ = v___x_772_;
goto v___jp_727_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v___y_757_);
lean_dec(v_a_713_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_710_);
v_a_773_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_770_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_770_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_855_ = _args[0];
lean_object* v___x_856_ = _args[1];
lean_object* v___x_857_ = _args[2];
lean_object* v___x_858_ = _args[3];
lean_object* v___x_859_ = _args[4];
lean_object* v___x_860_ = _args[5];
lean_object* v___x_861_ = _args[6];
lean_object* v_a_862_ = _args[7];
lean_object* v_b_863_ = _args[8];
lean_object* v___y_864_ = _args[9];
lean_object* v___y_865_ = _args[10];
lean_object* v___y_866_ = _args[11];
lean_object* v___y_867_ = _args[12];
lean_object* v___y_868_ = _args[13];
lean_object* v___y_869_ = _args[14];
lean_object* v___y_870_ = _args[15];
lean_object* v___y_871_ = _args[16];
lean_object* v___y_872_ = _args[17];
lean_object* v___y_873_ = _args[18];
lean_object* v___y_874_ = _args[19];
lean_object* v___y_875_ = _args[20];
_start:
{
uint8_t v___x_78632__boxed_876_; lean_object* v_res_877_; 
v___x_78632__boxed_876_ = lean_unbox(v___x_858_);
v_res_877_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_855_, v___x_856_, v___x_857_, v___x_78632__boxed_876_, v___x_859_, v___x_860_, v___x_861_, v_a_862_, v_b_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v___x_860_);
lean_dec(v___x_857_);
lean_dec_ref(v___x_856_);
lean_dec(v_upperBound_855_);
return v_res_877_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(lean_object* v_a_878_, lean_object* v_x_879_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
uint8_t v___x_880_; 
v___x_880_ = 0;
return v___x_880_;
}
else
{
lean_object* v_key_881_; lean_object* v_tail_882_; size_t v___x_883_; size_t v___x_884_; uint8_t v___x_885_; 
v_key_881_ = lean_ctor_get(v_x_879_, 0);
v_tail_882_ = lean_ctor_get(v_x_879_, 2);
v___x_883_ = lean_ptr_addr(v_key_881_);
v___x_884_ = lean_ptr_addr(v_a_878_);
v___x_885_ = lean_usize_dec_eq(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
v_x_879_ = v_tail_882_;
goto _start;
}
else
{
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___boxed(lean_object* v_a_887_, lean_object* v_x_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_887_, v_x_888_);
lean_dec(v_x_888_);
lean_dec_ref(v_a_887_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(lean_object* v_m_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_buckets_893_; lean_object* v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v_fold_901_; uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v___x_904_; size_t v___x_905_; size_t v___x_906_; size_t v___x_907_; size_t v___x_908_; size_t v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_buckets_893_ = lean_ctor_get(v_m_891_, 1);
v___x_894_ = lean_array_get_size(v_buckets_893_);
v___x_895_ = lean_ptr_addr(v_a_892_);
v___x_896_ = ((size_t)3ULL);
v___x_897_ = lean_usize_shift_right(v___x_895_, v___x_896_);
v___x_898_ = lean_usize_to_uint64(v___x_897_);
v___x_899_ = 32ULL;
v___x_900_ = lean_uint64_shift_right(v___x_898_, v___x_899_);
v_fold_901_ = lean_uint64_xor(v___x_898_, v___x_900_);
v___x_902_ = 16ULL;
v___x_903_ = lean_uint64_shift_right(v_fold_901_, v___x_902_);
v___x_904_ = lean_uint64_xor(v_fold_901_, v___x_903_);
v___x_905_ = lean_uint64_to_usize(v___x_904_);
v___x_906_ = lean_usize_of_nat(v___x_894_);
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_sub(v___x_906_, v___x_907_);
v___x_909_ = lean_usize_land(v___x_905_, v___x_908_);
v___x_910_ = lean_array_uget_borrowed(v_buckets_893_, v___x_909_);
v___x_911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_892_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg___boxed(lean_object* v_m_912_, lean_object* v_a_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_912_, v_a_913_);
lean_dec_ref(v_a_913_);
lean_dec_ref(v_m_912_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(lean_object* v_arg_916_, lean_object* v_x_917_){
_start:
{
uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = 0;
v___x_919_ = lean_box(v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_arg_916_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
return v_x_921_;
}
else
{
lean_object* v_key_923_; lean_object* v_value_924_; lean_object* v_tail_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_948_; 
v_key_923_ = lean_ctor_get(v_x_922_, 0);
v_value_924_ = lean_ctor_get(v_x_922_, 1);
v_tail_925_ = lean_ctor_get(v_x_922_, 2);
v_isSharedCheck_948_ = !lean_is_exclusive(v_x_922_);
if (v_isSharedCheck_948_ == 0)
{
v___x_927_ = v_x_922_;
v_isShared_928_ = v_isSharedCheck_948_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_tail_925_);
lean_inc(v_value_924_);
lean_inc(v_key_923_);
lean_dec(v_x_922_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_948_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v___x_932_; uint64_t v_fold_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v___x_939_; size_t v___x_940_; size_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_929_ = lean_array_get_size(v_x_921_);
v___x_930_ = lean_uint64_of_nat(v_key_923_);
v___x_931_ = 32ULL;
v___x_932_ = lean_uint64_shift_right(v___x_930_, v___x_931_);
v_fold_933_ = lean_uint64_xor(v___x_930_, v___x_932_);
v___x_934_ = 16ULL;
v___x_935_ = lean_uint64_shift_right(v_fold_933_, v___x_934_);
v___x_936_ = lean_uint64_xor(v_fold_933_, v___x_935_);
v___x_937_ = lean_uint64_to_usize(v___x_936_);
v___x_938_ = lean_usize_of_nat(v___x_929_);
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_sub(v___x_938_, v___x_939_);
v___x_941_ = lean_usize_land(v___x_937_, v___x_940_);
v___x_942_ = lean_array_uget_borrowed(v_x_921_, v___x_941_);
lean_inc(v___x_942_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 2, v___x_942_);
v___x_944_ = v___x_927_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_key_923_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_value_924_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v___x_942_);
v___x_944_ = v_reuseFailAlloc_947_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_array_uset(v_x_921_, v___x_941_, v___x_944_);
v_x_921_ = v___x_945_;
v_x_922_ = v_tail_925_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(lean_object* v_i_949_, lean_object* v_source_950_, lean_object* v_target_951_){
_start:
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = lean_array_get_size(v_source_950_);
v___x_953_ = lean_nat_dec_lt(v_i_949_, v___x_952_);
if (v___x_953_ == 0)
{
lean_dec_ref(v_source_950_);
lean_dec(v_i_949_);
return v_target_951_;
}
else
{
lean_object* v_es_954_; lean_object* v___x_955_; lean_object* v_source_956_; lean_object* v_target_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_es_954_ = lean_array_fget(v_source_950_, v_i_949_);
v___x_955_ = lean_box(0);
v_source_956_ = lean_array_fset(v_source_950_, v_i_949_, v___x_955_);
v_target_957_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_target_951_, v_es_954_);
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_nat_add(v_i_949_, v___x_958_);
lean_dec(v_i_949_);
v_i_949_ = v___x_959_;
v_source_950_ = v_source_956_;
v_target_951_ = v_target_957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(lean_object* v_data_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_nbuckets_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_962_ = lean_array_get_size(v_data_961_);
v___x_963_ = lean_unsigned_to_nat(2u);
v_nbuckets_964_ = lean_nat_mul(v___x_962_, v___x_963_);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_box(0);
v___x_967_ = lean_mk_array(v_nbuckets_964_, v___x_966_);
v___x_968_ = lean_array_propagate_mark(v_data_961_, v___x_967_);
v___x_969_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v___x_965_, v_data_961_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(lean_object* v_a_970_, lean_object* v_x_971_){
_start:
{
if (lean_obj_tag(v_x_971_) == 0)
{
uint8_t v___x_972_; 
v___x_972_ = 0;
return v___x_972_;
}
else
{
lean_object* v_key_973_; lean_object* v_tail_974_; uint8_t v___x_975_; 
v_key_973_ = lean_ctor_get(v_x_971_, 0);
v_tail_974_ = lean_ctor_get(v_x_971_, 2);
v___x_975_ = lean_nat_dec_eq(v_key_973_, v_a_970_);
if (v___x_975_ == 0)
{
v_x_971_ = v_tail_974_;
goto _start;
}
else
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg___boxed(lean_object* v_a_977_, lean_object* v_x_978_){
_start:
{
uint8_t v_res_979_; lean_object* v_r_980_; 
v_res_979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_977_, v_x_978_);
lean_dec(v_x_978_);
lean_dec(v_a_977_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(lean_object* v_a_981_, lean_object* v_b_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
lean_dec(v_b_982_);
lean_dec(v_a_981_);
return v_x_983_;
}
else
{
lean_object* v_key_984_; lean_object* v_value_985_; lean_object* v_tail_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_998_; 
v_key_984_ = lean_ctor_get(v_x_983_, 0);
v_value_985_ = lean_ctor_get(v_x_983_, 1);
v_tail_986_ = lean_ctor_get(v_x_983_, 2);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_983_);
if (v_isSharedCheck_998_ == 0)
{
v___x_988_ = v_x_983_;
v_isShared_989_ = v_isSharedCheck_998_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_tail_986_);
lean_inc(v_value_985_);
lean_inc(v_key_984_);
lean_dec(v_x_983_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_998_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = lean_nat_dec_eq(v_key_984_, v_a_981_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_981_, v_b_982_, v_tail_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 2, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_key_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_value_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v___x_996_; 
lean_dec(v_value_985_);
lean_dec(v_key_984_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v_b_982_);
lean_ctor_set(v___x_988_, 0, v_a_981_);
v___x_996_ = v___x_988_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_981_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_b_982_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_tail_986_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(lean_object* v_m_999_, lean_object* v_a_1000_, lean_object* v_b_1001_){
_start:
{
lean_object* v_size_1002_; lean_object* v_buckets_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1046_; 
v_size_1002_ = lean_ctor_get(v_m_999_, 0);
v_buckets_1003_ = lean_ctor_get(v_m_999_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_m_999_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1005_ = v_m_999_;
v_isShared_1006_ = v_isSharedCheck_1046_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_buckets_1003_);
lean_inc(v_size_1002_);
lean_dec(v_m_999_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1046_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; uint64_t v___x_1008_; uint64_t v___x_1009_; uint64_t v___x_1010_; uint64_t v_fold_1011_; uint64_t v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; lean_object* v_bkt_1020_; uint8_t v___x_1021_; 
v___x_1007_ = lean_array_get_size(v_buckets_1003_);
v___x_1008_ = lean_uint64_of_nat(v_a_1000_);
v___x_1009_ = 32ULL;
v___x_1010_ = lean_uint64_shift_right(v___x_1008_, v___x_1009_);
v_fold_1011_ = lean_uint64_xor(v___x_1008_, v___x_1010_);
v___x_1012_ = 16ULL;
v___x_1013_ = lean_uint64_shift_right(v_fold_1011_, v___x_1012_);
v___x_1014_ = lean_uint64_xor(v_fold_1011_, v___x_1013_);
v___x_1015_ = lean_uint64_to_usize(v___x_1014_);
v___x_1016_ = lean_usize_of_nat(v___x_1007_);
v___x_1017_ = ((size_t)1ULL);
v___x_1018_ = lean_usize_sub(v___x_1016_, v___x_1017_);
v___x_1019_ = lean_usize_land(v___x_1015_, v___x_1018_);
v_bkt_1020_ = lean_array_uget_borrowed(v_buckets_1003_, v___x_1019_);
v___x_1021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_1000_, v_bkt_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v_size_x27_1023_; lean_object* v___x_1024_; lean_object* v_buckets_x27_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v_size_x27_1023_ = lean_nat_add(v_size_1002_, v___x_1022_);
lean_dec(v_size_1002_);
lean_inc(v_bkt_1020_);
v___x_1024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1024_, 0, v_a_1000_);
lean_ctor_set(v___x_1024_, 1, v_b_1001_);
lean_ctor_set(v___x_1024_, 2, v_bkt_1020_);
v_buckets_x27_1025_ = lean_array_uset(v_buckets_1003_, v___x_1019_, v___x_1024_);
v___x_1026_ = lean_unsigned_to_nat(4u);
v___x_1027_ = lean_nat_mul(v_size_x27_1023_, v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(3u);
v___x_1029_ = lean_nat_div(v___x_1027_, v___x_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_array_get_size(v_buckets_x27_1025_);
v___x_1031_ = lean_nat_dec_le(v___x_1029_, v___x_1030_);
lean_dec(v___x_1029_);
if (v___x_1031_ == 0)
{
lean_object* v_val_1032_; lean_object* v___x_1034_; 
v_val_1032_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_buckets_x27_1025_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_val_1032_);
lean_ctor_set(v___x_1005_, 0, v_size_x27_1023_);
v___x_1034_ = v___x_1005_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_size_x27_1023_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_val_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
else
{
lean_object* v___x_1037_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_buckets_x27_1025_);
lean_ctor_set(v___x_1005_, 0, v_size_x27_1023_);
v___x_1037_ = v___x_1005_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_size_x27_1023_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_buckets_x27_1025_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v___x_1039_; lean_object* v_buckets_x27_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_inc(v_bkt_1020_);
v___x_1039_ = lean_box(0);
v_buckets_x27_1040_ = lean_array_uset(v_buckets_1003_, v___x_1019_, v___x_1039_);
v___x_1041_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1000_, v_b_1001_, v_bkt_1020_);
v___x_1042_ = lean_array_uset(v_buckets_x27_1040_, v___x_1019_, v___x_1041_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v___x_1042_);
v___x_1044_ = v___x_1005_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_size_1002_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
if (lean_obj_tag(v_x_1048_) == 0)
{
return v_x_1047_;
}
else
{
lean_object* v_key_1049_; lean_object* v_value_1050_; lean_object* v_tail_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1077_; 
v_key_1049_ = lean_ctor_get(v_x_1048_, 0);
v_value_1050_ = lean_ctor_get(v_x_1048_, 1);
v_tail_1051_ = lean_ctor_get(v_x_1048_, 2);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_x_1048_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1053_ = v_x_1048_;
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_tail_1051_);
lean_inc(v_value_1050_);
lean_inc(v_key_1049_);
lean_dec(v_x_1048_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; uint64_t v___x_1059_; uint64_t v___x_1060_; uint64_t v___x_1061_; uint64_t v_fold_1062_; uint64_t v___x_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1055_ = lean_array_get_size(v_x_1047_);
v___x_1056_ = lean_ptr_addr(v_key_1049_);
v___x_1057_ = ((size_t)3ULL);
v___x_1058_ = lean_usize_shift_right(v___x_1056_, v___x_1057_);
v___x_1059_ = lean_usize_to_uint64(v___x_1058_);
v___x_1060_ = 32ULL;
v___x_1061_ = lean_uint64_shift_right(v___x_1059_, v___x_1060_);
v_fold_1062_ = lean_uint64_xor(v___x_1059_, v___x_1061_);
v___x_1063_ = 16ULL;
v___x_1064_ = lean_uint64_shift_right(v_fold_1062_, v___x_1063_);
v___x_1065_ = lean_uint64_xor(v_fold_1062_, v___x_1064_);
v___x_1066_ = lean_uint64_to_usize(v___x_1065_);
v___x_1067_ = lean_usize_of_nat(v___x_1055_);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_sub(v___x_1067_, v___x_1068_);
v___x_1070_ = lean_usize_land(v___x_1066_, v___x_1069_);
v___x_1071_ = lean_array_uget_borrowed(v_x_1047_, v___x_1070_);
lean_inc(v___x_1071_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 2, v___x_1071_);
v___x_1073_ = v___x_1053_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_key_1049_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_value_1050_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_array_uset(v_x_1047_, v___x_1070_, v___x_1073_);
v_x_1047_ = v___x_1074_;
v_x_1048_ = v_tail_1051_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(lean_object* v_i_1078_, lean_object* v_source_1079_, lean_object* v_target_1080_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = lean_array_get_size(v_source_1079_);
v___x_1082_ = lean_nat_dec_lt(v_i_1078_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v_source_1079_);
lean_dec(v_i_1078_);
return v_target_1080_;
}
else
{
lean_object* v_es_1083_; lean_object* v___x_1084_; lean_object* v_source_1085_; lean_object* v_target_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_es_1083_ = lean_array_fget(v_source_1079_, v_i_1078_);
v___x_1084_ = lean_box(0);
v_source_1085_ = lean_array_fset(v_source_1079_, v_i_1078_, v___x_1084_);
v_target_1086_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_target_1080_, v_es_1083_);
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = lean_nat_add(v_i_1078_, v___x_1087_);
lean_dec(v_i_1078_);
v_i_1078_ = v___x_1088_;
v_source_1079_ = v_source_1085_;
v_target_1080_ = v_target_1086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(lean_object* v_data_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_nbuckets_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1091_ = lean_array_get_size(v_data_1090_);
v___x_1092_ = lean_unsigned_to_nat(2u);
v_nbuckets_1093_ = lean_nat_mul(v___x_1091_, v___x_1092_);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_mk_array(v_nbuckets_1093_, v___x_1095_);
v___x_1097_ = lean_array_propagate_mark(v_data_1090_, v___x_1096_);
v___x_1098_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v___x_1094_, v_data_1090_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(lean_object* v_m_1099_, lean_object* v_a_1100_, lean_object* v_b_1101_){
_start:
{
lean_object* v_size_1102_; lean_object* v_buckets_1103_; lean_object* v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v_fold_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v_bkt_1120_; uint8_t v___x_1121_; 
v_size_1102_ = lean_ctor_get(v_m_1099_, 0);
v_buckets_1103_ = lean_ctor_get(v_m_1099_, 1);
v___x_1104_ = lean_array_get_size(v_buckets_1103_);
v___x_1105_ = lean_ptr_addr(v_a_1100_);
v___x_1106_ = ((size_t)3ULL);
v___x_1107_ = lean_usize_shift_right(v___x_1105_, v___x_1106_);
v___x_1108_ = lean_usize_to_uint64(v___x_1107_);
v___x_1109_ = 32ULL;
v___x_1110_ = lean_uint64_shift_right(v___x_1108_, v___x_1109_);
v_fold_1111_ = lean_uint64_xor(v___x_1108_, v___x_1110_);
v___x_1112_ = 16ULL;
v___x_1113_ = lean_uint64_shift_right(v_fold_1111_, v___x_1112_);
v___x_1114_ = lean_uint64_xor(v_fold_1111_, v___x_1113_);
v___x_1115_ = lean_uint64_to_usize(v___x_1114_);
v___x_1116_ = lean_usize_of_nat(v___x_1104_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_sub(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_usize_land(v___x_1115_, v___x_1118_);
v_bkt_1120_ = lean_array_uget_borrowed(v_buckets_1103_, v___x_1119_);
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1100_, v_bkt_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1142_; 
lean_inc_ref(v_buckets_1103_);
lean_inc(v_size_1102_);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_m_1099_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; 
v_unused_1143_ = lean_ctor_get(v_m_1099_, 1);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_m_1099_, 0);
lean_dec(v_unused_1144_);
v___x_1123_ = v_m_1099_;
v_isShared_1124_ = v_isSharedCheck_1142_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v_m_1099_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1142_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v_size_x27_1126_; lean_object* v___x_1127_; lean_object* v_buckets_x27_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v_size_x27_1126_ = lean_nat_add(v_size_1102_, v___x_1125_);
lean_dec(v_size_1102_);
lean_inc(v_bkt_1120_);
v___x_1127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1127_, 0, v_a_1100_);
lean_ctor_set(v___x_1127_, 1, v_b_1101_);
lean_ctor_set(v___x_1127_, 2, v_bkt_1120_);
v_buckets_x27_1128_ = lean_array_uset(v_buckets_1103_, v___x_1119_, v___x_1127_);
v___x_1129_ = lean_unsigned_to_nat(4u);
v___x_1130_ = lean_nat_mul(v_size_x27_1126_, v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(3u);
v___x_1132_ = lean_nat_div(v___x_1130_, v___x_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_array_get_size(v_buckets_x27_1128_);
v___x_1134_ = lean_nat_dec_le(v___x_1132_, v___x_1133_);
lean_dec(v___x_1132_);
if (v___x_1134_ == 0)
{
lean_object* v_val_1135_; lean_object* v___x_1137_; 
v_val_1135_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_buckets_x27_1128_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v_val_1135_);
lean_ctor_set(v___x_1123_, 0, v_size_x27_1126_);
v___x_1137_ = v___x_1123_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_size_x27_1126_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_val_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v___x_1140_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v_buckets_x27_1128_);
lean_ctor_set(v___x_1123_, 0, v_size_x27_1126_);
v___x_1140_ = v___x_1123_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_size_x27_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_buckets_x27_1128_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_dec(v_b_1101_);
lean_dec_ref(v_a_1100_);
return v_m_1099_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(lean_object* v_fst_1145_, lean_object* v_snd_1146_, lean_object* v_fst_1147_, lean_object* v_fst_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_fst_1145_);
lean_ctor_set(v___x_1162_, 1, v_snd_1146_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_fst_1147_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_fst_1148_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_1167_ = _args[0];
lean_object* v_snd_1168_ = _args[1];
lean_object* v_fst_1169_ = _args[2];
lean_object* v_fst_1170_ = _args[3];
lean_object* v_x_1171_ = _args[4];
lean_object* v___y_1172_ = _args[5];
lean_object* v___y_1173_ = _args[6];
lean_object* v___y_1174_ = _args[7];
lean_object* v___y_1175_ = _args[8];
lean_object* v___y_1176_ = _args[9];
lean_object* v___y_1177_ = _args[10];
lean_object* v___y_1178_ = _args[11];
lean_object* v___y_1179_ = _args[12];
lean_object* v___y_1180_ = _args[13];
lean_object* v___y_1181_ = _args[14];
lean_object* v___y_1182_ = _args[15];
lean_object* v___y_1183_ = _args[16];
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1167_, v_snd_1168_, v_fst_1169_, v_fst_1170_, v_x_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v_ks_1189_; lean_object* v_vs_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1216_; 
v_ks_1189_ = lean_ctor_get(v_x_1185_, 0);
v_vs_1190_ = lean_ctor_get(v_x_1185_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1192_ = v_x_1185_;
v_isShared_1193_ = v_isSharedCheck_1216_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_vs_1190_);
lean_inc(v_ks_1189_);
lean_dec(v_x_1185_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1216_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_array_get_size(v_ks_1189_);
v___x_1195_ = lean_nat_dec_lt(v_x_1186_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_dec(v_x_1186_);
v___x_1196_ = lean_array_push(v_ks_1189_, v_x_1187_);
v___x_1197_ = lean_array_push(v_vs_1190_, v_x_1188_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1197_);
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1199_ = v___x_1192_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v_k_x27_1201_; size_t v___x_1202_; size_t v___x_1203_; uint8_t v___x_1204_; 
v_k_x27_1201_ = lean_array_fget_borrowed(v_ks_1189_, v_x_1186_);
v___x_1202_ = lean_ptr_addr(v_x_1187_);
v___x_1203_ = lean_ptr_addr(v_k_x27_1201_);
v___x_1204_ = lean_usize_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1206_; 
if (v_isShared_1193_ == 0)
{
v___x_1206_ = v___x_1192_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_ks_1189_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_vs_1190_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_x_1186_, v___x_1207_);
lean_dec(v_x_1186_);
v_x_1185_ = v___x_1206_;
v_x_1186_ = v___x_1208_;
goto _start;
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = lean_array_fset(v_ks_1189_, v_x_1186_, v_x_1187_);
v___x_1212_ = lean_array_fset(v_vs_1190_, v_x_1186_, v_x_1188_);
lean_dec(v_x_1186_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1212_);
lean_ctor_set(v___x_1192_, 0, v___x_1211_);
v___x_1214_ = v___x_1192_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(lean_object* v_n_1217_, lean_object* v_k_1218_, lean_object* v_v_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_n_1217_, v___x_1220_, v_k_1218_, v_v_1219_);
return v___x_1221_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(lean_object* v_x_1223_, size_t v_x_1224_, size_t v_x_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1223_) == 0)
{
lean_object* v_es_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v_j_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_es_1228_ = lean_ctor_get(v_x_1223_, 0);
v___x_1229_ = ((size_t)31ULL);
v___x_1230_ = lean_usize_land(v_x_1224_, v___x_1229_);
v_j_1231_ = lean_usize_to_nat(v___x_1230_);
v___x_1232_ = lean_array_get_size(v_es_1228_);
v___x_1233_ = lean_nat_dec_lt(v_j_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v_j_1231_);
lean_dec(v_x_1227_);
lean_dec_ref(v_x_1226_);
return v_x_1223_;
}
else
{
lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1274_; 
lean_inc_ref(v_es_1228_);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1223_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_x_1223_, 0);
lean_dec(v_unused_1275_);
v___x_1235_ = v_x_1223_;
v_isShared_1236_ = v_isSharedCheck_1274_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v_x_1223_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1274_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_v_1237_; lean_object* v___x_1238_; lean_object* v_xs_x27_1239_; lean_object* v___y_1241_; 
v_v_1237_ = lean_array_fget(v_es_1228_, v_j_1231_);
v___x_1238_ = lean_box(0);
v_xs_x27_1239_ = lean_array_fset(v_es_1228_, v_j_1231_, v___x_1238_);
switch(lean_obj_tag(v_v_1237_))
{
case 0:
{
lean_object* v_key_1246_; lean_object* v_val_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
v_key_1246_ = lean_ctor_get(v_v_1237_, 0);
v_val_1247_ = lean_ctor_get(v_v_1237_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_v_1237_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1249_ = v_v_1237_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_val_1247_);
lean_inc(v_key_1246_);
lean_dec(v_v_1237_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
size_t v___x_1251_; size_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_ptr_addr(v_x_1226_);
v___x_1252_ = lean_ptr_addr(v_key_1246_);
v___x_1253_ = lean_usize_dec_eq(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_del_object(v___x_1249_);
v___x_1254_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1246_, v_val_1247_, v_x_1226_, v_x_1227_);
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
v___y_1241_ = v___x_1255_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_val_1247_);
lean_dec(v_key_1246_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v_x_1227_);
lean_ctor_set(v___x_1249_, 0, v_x_1226_);
v___x_1257_ = v___x_1249_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_x_1226_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_x_1227_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
v___y_1241_ = v___x_1257_;
goto v___jp_1240_;
}
}
}
}
case 1:
{
lean_object* v_node_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1272_; 
v_node_1260_ = lean_ctor_get(v_v_1237_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_v_1237_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1262_ = v_v_1237_;
v_isShared_1263_ = v_isSharedCheck_1272_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_node_1260_);
lean_dec(v_v_1237_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1272_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
size_t v___x_1264_; size_t v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1264_ = ((size_t)5ULL);
v___x_1265_ = lean_usize_shift_right(v_x_1224_, v___x_1264_);
v___x_1266_ = ((size_t)1ULL);
v___x_1267_ = lean_usize_add(v_x_1225_, v___x_1266_);
v___x_1268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_node_1260_, v___x_1265_, v___x_1267_, v_x_1226_, v_x_1227_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1268_);
v___x_1270_ = v___x_1262_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v___y_1241_ = v___x_1270_;
goto v___jp_1240_;
}
}
}
default: 
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_x_1226_);
lean_ctor_set(v___x_1273_, 1, v_x_1227_);
v___y_1241_ = v___x_1273_;
goto v___jp_1240_;
}
}
v___jp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_array_fset(v_xs_x27_1239_, v_j_1231_, v___y_1241_);
lean_dec(v_j_1231_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1242_);
v___x_1244_ = v___x_1235_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_object* v_ks_1276_; lean_object* v_vs_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1295_; 
v_ks_1276_ = lean_ctor_get(v_x_1223_, 0);
v_vs_1277_ = lean_ctor_get(v_x_1223_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_x_1223_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1279_ = v_x_1223_;
v_isShared_1280_ = v_isSharedCheck_1295_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_vs_1277_);
lean_inc(v_ks_1276_);
lean_dec(v_x_1223_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1295_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_ks_1276_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_vs_1277_);
v___x_1282_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v_newNode_1283_; size_t v___x_1284_; uint8_t v___x_1285_; 
v_newNode_1283_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v___x_1282_, v_x_1226_, v_x_1227_);
v___x_1284_ = ((size_t)7ULL);
v___x_1285_ = lean_usize_dec_le(v___x_1284_, v_x_1225_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1286_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1283_);
v___x_1287_ = lean_unsigned_to_nat(4u);
v___x_1288_ = lean_nat_dec_lt(v___x_1286_, v___x_1287_);
lean_dec(v___x_1286_);
if (v___x_1288_ == 0)
{
lean_object* v_ks_1289_; lean_object* v_vs_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_ks_1289_ = lean_ctor_get(v_newNode_1283_, 0);
lean_inc_ref(v_ks_1289_);
v_vs_1290_ = lean_ctor_get(v_newNode_1283_, 1);
lean_inc_ref(v_vs_1290_);
lean_dec_ref(v_newNode_1283_);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0);
v___x_1293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_x_1225_, v_ks_1289_, v_vs_1290_, v___x_1291_, v___x_1292_);
lean_dec_ref(v_vs_1290_);
lean_dec_ref(v_ks_1289_);
return v___x_1293_;
}
else
{
return v_newNode_1283_;
}
}
else
{
return v_newNode_1283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(size_t v_depth_1296_, lean_object* v_keys_1297_, lean_object* v_vals_1298_, lean_object* v_i_1299_, lean_object* v_entries_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_array_get_size(v_keys_1297_);
v___x_1302_ = lean_nat_dec_lt(v_i_1299_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec(v_i_1299_);
return v_entries_1300_;
}
else
{
lean_object* v_k_1303_; lean_object* v_v_1304_; size_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; uint64_t v___x_1308_; size_t v_h_1309_; size_t v___x_1310_; lean_object* v___x_1311_; size_t v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; size_t v_h_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_k_1303_ = lean_array_fget_borrowed(v_keys_1297_, v_i_1299_);
v_v_1304_ = lean_array_fget_borrowed(v_vals_1298_, v_i_1299_);
v___x_1305_ = lean_ptr_addr(v_k_1303_);
v___x_1306_ = ((size_t)3ULL);
v___x_1307_ = lean_usize_shift_right(v___x_1305_, v___x_1306_);
v___x_1308_ = lean_usize_to_uint64(v___x_1307_);
v_h_1309_ = lean_uint64_to_usize(v___x_1308_);
v___x_1310_ = ((size_t)5ULL);
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = ((size_t)1ULL);
v___x_1313_ = lean_usize_sub(v_depth_1296_, v___x_1312_);
v___x_1314_ = lean_usize_mul(v___x_1310_, v___x_1313_);
v_h_1315_ = lean_usize_shift_right(v_h_1309_, v___x_1314_);
v___x_1316_ = lean_nat_add(v_i_1299_, v___x_1311_);
lean_dec(v_i_1299_);
lean_inc(v_v_1304_);
lean_inc(v_k_1303_);
v___x_1317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_entries_1300_, v_h_1315_, v_depth_1296_, v_k_1303_, v_v_1304_);
v_i_1299_ = v___x_1316_;
v_entries_1300_ = v___x_1317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg___boxed(lean_object* v_depth_1319_, lean_object* v_keys_1320_, lean_object* v_vals_1321_, lean_object* v_i_1322_, lean_object* v_entries_1323_){
_start:
{
size_t v_depth_boxed_1324_; lean_object* v_res_1325_; 
v_depth_boxed_1324_ = lean_unbox_usize(v_depth_1319_);
lean_dec(v_depth_1319_);
v_res_1325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_boxed_1324_, v_keys_1320_, v_vals_1321_, v_i_1322_, v_entries_1323_);
lean_dec_ref(v_vals_1321_);
lean_dec_ref(v_keys_1320_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___boxed(lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
size_t v_x_79510__boxed_1331_; size_t v_x_79511__boxed_1332_; lean_object* v_res_1333_; 
v_x_79510__boxed_1331_ = lean_unbox_usize(v_x_1327_);
lean_dec(v_x_1327_);
v_x_79511__boxed_1332_ = lean_unbox_usize(v_x_1328_);
lean_dec(v_x_1328_);
v_res_1333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1326_, v_x_79510__boxed_1331_, v_x_79511__boxed_1332_, v_x_1329_, v_x_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; uint64_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1337_ = lean_ptr_addr(v_x_1335_);
v___x_1338_ = ((size_t)3ULL);
v___x_1339_ = lean_usize_shift_right(v___x_1337_, v___x_1338_);
v___x_1340_ = lean_usize_to_uint64(v___x_1339_);
v___x_1341_ = lean_uint64_to_usize(v___x_1340_);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1334_, v___x_1341_, v___x_1342_, v_x_1335_, v_x_1336_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(lean_object* v_upperBound_1351_, lean_object* v___x_1352_, lean_object* v_a_1353_, lean_object* v_b_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_a_1368_; lean_object* v___y_1373_; uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_lt(v_a_1353_, v_upperBound_1351_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_dec(v_a_1353_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_b_1354_);
return v___x_1393_;
}
else
{
lean_object* v_snd_1394_; lean_object* v_snd_1395_; lean_object* v_fst_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1486_; 
v_snd_1394_ = lean_ctor_get(v_b_1354_, 1);
lean_inc(v_snd_1394_);
v_snd_1395_ = lean_ctor_get(v_snd_1394_, 1);
lean_inc(v_snd_1395_);
v_fst_1396_ = lean_ctor_get(v_b_1354_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_b_1354_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_b_1354_, 1);
lean_dec(v_unused_1487_);
v___x_1398_ = v_b_1354_;
v_isShared_1399_ = v_isSharedCheck_1486_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_fst_1396_);
lean_dec(v_b_1354_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1486_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_fst_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1484_; 
v_fst_1400_ = lean_ctor_get(v_snd_1394_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_snd_1394_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_snd_1394_, 1);
lean_dec(v_unused_1485_);
v___x_1402_ = v_snd_1394_;
v_isShared_1403_ = v_isSharedCheck_1484_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_fst_1400_);
lean_dec(v_snd_1394_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1484_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1483_; 
v_fst_1404_ = lean_ctor_get(v_snd_1395_, 0);
v_snd_1405_ = lean_ctor_get(v_snd_1395_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_snd_1395_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1407_ = v_snd_1395_;
v_isShared_1408_ = v_isSharedCheck_1483_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_inc(v_fst_1404_);
lean_dec(v_snd_1395_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1483_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1419_; lean_object* v_type_1420_; lean_object* v_value_1421_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1419_ = lean_array_fget_borrowed(v___x_1352_, v_a_1353_);
v_type_1420_ = lean_ctor_get(v___x_1419_, 1);
v_value_1421_ = lean_ctor_get(v___x_1419_, 2);
lean_inc_ref(v_type_1420_);
v___x_1433_ = l_Lean_Expr_cleanupAnnotations(v_type_1420_);
v___x_1434_ = l_Lean_Expr_isApp(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v___x_1433_);
lean_del_object(v___x_1407_);
lean_del_object(v___x_1402_);
lean_del_object(v___x_1398_);
v___x_1435_ = lean_box(0);
v___x_1436_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1404_, v_snd_1405_, v_fst_1400_, v_fst_1396_, v___x_1435_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
v___y_1373_ = v___x_1436_;
goto v___jp_1372_;
}
else
{
lean_object* v_arg_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_arg_1437_ = lean_ctor_get(v___x_1433_, 1);
lean_inc_ref(v_arg_1437_);
v___x_1438_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1433_);
v___x_1439_ = l_Lean_Expr_isApp(v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref(v___x_1438_);
lean_dec_ref(v_arg_1437_);
lean_del_object(v___x_1407_);
lean_del_object(v___x_1402_);
lean_del_object(v___x_1398_);
v___x_1440_ = lean_box(0);
v___x_1441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1404_, v_snd_1405_, v_fst_1400_, v_fst_1396_, v___x_1440_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
v___y_1373_ = v___x_1441_;
goto v___jp_1372_;
}
else
{
lean_object* v_arg_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_arg_1442_ = lean_ctor_get(v___x_1438_, 1);
lean_inc_ref(v_arg_1442_);
v___x_1443_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1438_);
v___x_1444_ = l_Lean_Expr_isApp(v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v___x_1443_);
lean_dec_ref(v_arg_1442_);
lean_dec_ref(v_arg_1437_);
lean_del_object(v___x_1407_);
lean_del_object(v___x_1402_);
lean_del_object(v___x_1398_);
v___x_1445_ = lean_box(0);
v___x_1446_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1404_, v_snd_1405_, v_fst_1400_, v_fst_1396_, v___x_1445_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
v___y_1373_ = v___x_1446_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1443_);
v___x_1448_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__1));
v___x_1449_ = l_Lean_Expr_isConstOf(v___x_1447_, v___x_1448_);
lean_dec_ref(v___x_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec_ref(v_arg_1442_);
lean_dec_ref(v_arg_1437_);
lean_del_object(v___x_1407_);
lean_del_object(v___x_1402_);
lean_del_object(v___x_1398_);
v___x_1450_ = lean_box(0);
v___x_1451_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1404_, v_snd_1405_, v_fst_1400_, v_fst_1396_, v___x_1450_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
v___y_1373_ = v___x_1451_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v_fst_1456_; uint8_t v_snd_1457_; lean_object* v___y_1466_; 
v___x_1452_ = l_Lean_Expr_cleanupAnnotations(v_arg_1437_);
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2));
v___x_1454_ = l_Lean_Expr_isConstOf(v___x_1452_, v___x_1453_);
lean_dec_ref(v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec_ref(v_arg_1442_);
lean_del_object(v___x_1407_);
lean_del_object(v___x_1402_);
lean_del_object(v___x_1398_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_fst_1404_);
lean_ctor_set(v___x_1470_, 1, v_snd_1405_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_fst_1400_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_fst_1396_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v_a_1368_ = v___x_1472_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
lean_inc_ref(v_arg_1442_);
v___x_1473_ = l_Lean_Expr_cleanupAnnotations(v_arg_1442_);
v___x_1474_ = l_Lean_Expr_isApp(v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref(v___x_1473_);
v___x_1475_ = lean_box(0);
v___x_1476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1442_, v___x_1475_);
v___y_1466_ = v___x_1476_;
goto v___jp_1465_;
}
else
{
lean_object* v_arg_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_arg_1477_ = lean_ctor_get(v___x_1473_, 1);
lean_inc_ref(v_arg_1477_);
v___x_1478_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1473_);
v___x_1479_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3));
v___x_1480_ = l_Lean_Expr_isConstOf(v___x_1478_, v___x_1479_);
lean_dec_ref(v___x_1478_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref(v_arg_1477_);
v___x_1481_ = lean_box(0);
v___x_1482_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1442_, v___x_1481_);
v___y_1466_ = v___x_1482_;
goto v___jp_1465_;
}
else
{
lean_dec_ref(v_arg_1442_);
v_fst_1456_ = v_arg_1477_;
v_snd_1457_ = v___x_1480_;
goto v___jp_1455_;
}
}
}
v___jp_1455_:
{
uint8_t v___x_1458_; 
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_fst_1404_, v_fst_1456_);
if (v___x_1458_ == 0)
{
if (v___x_1454_ == 0)
{
lean_dec_ref(v_fst_1456_);
goto v___jp_1409_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint32_t v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
lean_del_object(v___x_1407_);
lean_del_object(v___x_1402_);
lean_del_object(v___x_1398_);
v___x_1459_ = lean_box(0);
lean_inc_ref_n(v_fst_1456_, 2);
v___x_1460_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_fst_1404_, v_fst_1456_, v___x_1459_);
lean_inc(v_a_1353_);
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_fst_1400_, v_a_1353_, v_fst_1456_);
v___x_1462_ = l_Lean_Expr_approxDepth(v_fst_1456_);
v___x_1463_ = lean_uint32_to_nat(v___x_1462_);
v___x_1464_ = lean_nat_dec_le(v_snd_1405_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v_snd_1405_);
v___y_1423_ = v___x_1461_;
v___y_1424_ = v_fst_1456_;
v___y_1425_ = v___x_1460_;
v___y_1426_ = v_snd_1457_;
v___y_1427_ = v___x_1463_;
goto v___jp_1422_;
}
else
{
lean_dec(v___x_1463_);
v___y_1423_ = v___x_1461_;
v___y_1424_ = v_fst_1456_;
v___y_1425_ = v___x_1460_;
v___y_1426_ = v_snd_1457_;
v___y_1427_ = v_snd_1405_;
goto v___jp_1422_;
}
}
}
else
{
lean_dec_ref(v_fst_1456_);
goto v___jp_1409_;
}
}
v___jp_1465_:
{
lean_object* v_fst_1467_; lean_object* v_snd_1468_; uint8_t v___x_1469_; 
v_fst_1467_ = lean_ctor_get(v___y_1466_, 0);
lean_inc(v_fst_1467_);
v_snd_1468_ = lean_ctor_get(v___y_1466_, 1);
lean_inc(v_snd_1468_);
lean_dec_ref(v___y_1466_);
v___x_1469_ = lean_unbox(v_snd_1468_);
lean_dec(v_snd_1468_);
v_fst_1456_ = v_fst_1467_;
v_snd_1457_ = v___x_1469_;
goto v___jp_1455_;
}
}
}
}
}
v___jp_1409_:
{
lean_object* v___x_1411_; 
if (v_isShared_1408_ == 0)
{
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_fst_1404_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_snd_1405_);
v___x_1411_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1411_);
v___x_1413_ = v___x_1402_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_fst_1400_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1413_);
v___x_1415_ = v___x_1398_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_fst_1396_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
v_a_1368_ = v___x_1415_;
goto v___jp_1367_;
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_inc_ref(v_value_1421_);
v___x_1428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1428_, 0, v_value_1421_);
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*1, v___y_1426_);
v___x_1429_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_fst_1396_, v___y_1424_, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___y_1425_);
lean_ctor_set(v___x_1430_, 1, v___y_1427_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1423_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v_a_1368_ = v___x_1432_;
goto v___jp_1367_;
}
}
}
}
}
v___jp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_a_1353_, v___x_1369_);
lean_dec(v_a_1353_);
v_a_1353_ = v___x_1370_;
v_b_1354_ = v_a_1368_;
goto _start;
}
v___jp_1372_:
{
if (lean_obj_tag(v___y_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1383_; 
v_a_1374_ = lean_ctor_get(v___y_1373_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___y_1373_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1376_ = v___y_1373_;
v_isShared_1377_ = v_isSharedCheck_1383_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___y_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1383_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
if (lean_obj_tag(v_a_1374_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; 
lean_dec(v_a_1353_);
v_a_1378_ = lean_ctor_get(v_a_1374_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v_a_1374_, 1);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v_a_1378_);
v___x_1380_ = v___x_1376_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v_a_1382_; 
lean_del_object(v___x_1376_);
v_a_1382_ = lean_ctor_get(v_a_1374_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v_a_1374_, 1);
v_a_1368_ = v_a_1382_;
goto v___jp_1367_;
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_a_1353_);
v_a_1384_ = lean_ctor_get(v___y_1373_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___y_1373_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___y_1373_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___y_1373_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___boxed(lean_object* v_upperBound_1488_, lean_object* v___x_1489_, lean_object* v_a_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1488_, v___x_1489_, v_a_1490_, v_b_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec_ref(v___x_1489_);
lean_dec(v_upperBound_1488_);
return v_res_1504_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1506_; lean_object* v_relevantHypsMap_1507_; 
v___x_1506_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0);
v_relevantHypsMap_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_relevantHypsMap_1507_, 0, v___x_1506_);
return v_relevantHypsMap_1507_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_unsigned_to_nat(16u);
v___x_1510_ = lean_mk_array(v___x_1509_, v___x_1508_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_relevantHypsIdxMap_1513_; 
v___x_1511_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2);
v___x_1512_ = lean_unsigned_to_nat(0u);
v_relevantHypsIdxMap_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_relevantHypsIdxMap_1513_, 0, v___x_1512_);
lean_ctor_set(v_relevantHypsIdxMap_1513_, 1, v___x_1511_);
return v_relevantHypsIdxMap_1513_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4(void){
_start:
{
lean_object* v_minDepth_1514_; lean_object* v_relevantHypsIdxMap_1515_; lean_object* v___x_1516_; 
v_minDepth_1514_ = lean_cstr_to_nat("4294967296");
v_relevantHypsIdxMap_1515_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_relevantHypsIdxMap_1515_);
lean_ctor_set(v___x_1516_, 1, v_minDepth_1514_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1517_; lean_object* v_relevantHypsIdxMap_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4);
v_relevantHypsIdxMap_1518_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_relevantHypsIdxMap_1518_);
lean_ctor_set(v___x_1519_, 1, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1520_; lean_object* v_relevantHypsMap_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5);
v_relevantHypsMap_1521_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_relevantHypsMap_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1520_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7));
v___x_1525_ = l_Lean_stringToMessageData(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v_hypotheses_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1538_ = lean_st_ref_get(v___y_1527_);
v_hypotheses_1539_ = lean_ctor_get(v___x_1538_, 3);
lean_inc_ref(v_hypotheses_1539_);
lean_dec(v___x_1538_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_array_get_size(v_hypotheses_1539_);
v___x_1542_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6);
v___x_1543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v___x_1541_, v_hypotheses_1539_, v___x_1540_, v___x_1542_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec_ref(v_hypotheses_1539_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1661_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1661_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1661_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_snd_1548_; lean_object* v_snd_1549_; lean_object* v_fst_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1659_; 
v_snd_1548_ = lean_ctor_get(v_a_1544_, 1);
lean_inc(v_snd_1548_);
v_snd_1549_ = lean_ctor_get(v_snd_1548_, 1);
lean_inc(v_snd_1549_);
v_fst_1550_ = lean_ctor_get(v_a_1544_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_a_1544_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_a_1544_, 1);
lean_dec(v_unused_1660_);
v___x_1552_ = v_a_1544_;
v_isShared_1553_ = v_isSharedCheck_1659_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_fst_1550_);
lean_dec(v_a_1544_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1659_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_fst_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1657_; 
v_fst_1554_ = lean_ctor_get(v_snd_1548_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_snd_1548_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_snd_1548_, 1);
lean_dec(v_unused_1658_);
v___x_1556_ = v_snd_1548_;
v_isShared_1557_ = v_isSharedCheck_1657_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_fst_1554_);
lean_dec(v_snd_1548_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1657_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_snd_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1655_; 
v_snd_1558_ = lean_ctor_get(v_snd_1549_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_snd_1549_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v_snd_1549_, 0);
lean_dec(v_unused_1656_);
v___x_1560_ = v_snd_1549_;
v_isShared_1561_ = v_isSharedCheck_1655_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_snd_1558_);
lean_dec(v_snd_1549_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1655_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_toCold_1632_; lean_object* v_options_1633_; uint8_t v_hasTrace_1634_; 
v_toCold_1632_ = lean_ctor_get(v___y_1535_, 0);
v_options_1633_ = lean_ctor_get(v_toCold_1632_, 2);
v_hasTrace_1634_ = lean_ctor_get_uint8(v_options_1633_, sizeof(void*)*1);
if (v_hasTrace_1634_ == 0)
{
lean_del_object(v___x_1552_);
v___y_1563_ = v___y_1526_;
v___y_1564_ = v___y_1527_;
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
v___y_1571_ = v___y_1534_;
v___y_1572_ = v___y_1535_;
v___y_1573_ = v___y_1536_;
goto v___jp_1562_;
}
else
{
lean_object* v_inheritedTraceOptions_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_inheritedTraceOptions_1635_ = lean_ctor_get(v_toCold_1632_, 11);
v___x_1636_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_1637_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_1638_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1635_, v_options_1633_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_del_object(v___x_1552_);
v___y_1563_ = v___y_1526_;
v___y_1564_ = v___y_1527_;
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
v___y_1571_ = v___y_1534_;
v___y_1572_ = v___y_1535_;
v___y_1573_ = v___y_1536_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1639_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8);
lean_inc(v_snd_1558_);
v___x_1640_ = l_Nat_reprFast(v_snd_1558_);
v___x_1641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
v___x_1642_ = l_Lean_MessageData_ofFormat(v___x_1641_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 7);
lean_ctor_set(v___x_1552_, 1, v___x_1642_);
lean_ctor_set(v___x_1552_, 0, v___x_1639_);
v___x_1644_ = v___x_1552_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_1636_, v___x_1644_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_dec_ref_known(v___x_1645_, 1);
v___y_1563_ = v___y_1526_;
v___y_1564_ = v___y_1527_;
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
v___y_1571_ = v___y_1534_;
v___y_1572_ = v___y_1535_;
v___y_1573_ = v___y_1536_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_del_object(v___x_1560_);
lean_dec(v_snd_1558_);
lean_del_object(v___x_1556_);
lean_dec(v_fst_1554_);
lean_dec(v_fst_1550_);
lean_del_object(v___x_1546_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
v___jp_1562_:
{
uint8_t v___x_1574_; 
v___x_1574_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fst_1550_);
if (v___x_1574_ == 0)
{
lean_object* v_config_1575_; lean_object* v_maxSteps_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
lean_del_object(v___x_1546_);
v_config_1575_ = lean_ctor_get(v___y_1563_, 0);
v_maxSteps_1576_ = lean_ctor_get(v_config_1575_, 1);
v___x_1577_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1576_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 1, v___x_1577_);
lean_ctor_set(v___x_1556_, 0, v_maxSteps_1576_);
v___x_1579_ = v___x_1556_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_maxSteps_1576_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v_hypotheses_1581_; lean_object* v___x_1582_; lean_object* v_newHyps_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1580_ = lean_st_ref_get(v___y_1564_);
v_hypotheses_1581_ = lean_ctor_get(v___x_1580_, 3);
lean_inc_ref(v_hypotheses_1581_);
lean_dec(v___x_1580_);
v___x_1582_ = lean_array_get_size(v_hypotheses_1581_);
v_newHyps_1583_ = lean_mk_empty_array_with_capacity(v___x_1582_);
v___x_1584_ = lean_box(0);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 1, v_newHyps_1583_);
lean_ctor_set(v___x_1560_, 0, v___x_1584_);
v___x_1586_ = v___x_1560_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_newHyps_1583_);
v___x_1586_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v___x_1582_, v_hypotheses_1581_, v_snd_1558_, v___x_1574_, v___x_1579_, v_fst_1554_, v_fst_1550_, v___x_1540_, v___x_1586_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v_fst_1554_);
lean_dec(v_snd_1558_);
lean_dec_ref(v_hypotheses_1581_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1616_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1616_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1616_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v_fst_1592_; 
v_fst_1592_ = lean_ctor_get(v_a_1588_, 0);
if (lean_obj_tag(v_fst_1592_) == 0)
{
lean_object* v_snd_1593_; lean_object* v___x_1594_; lean_object* v_caches_1595_; lean_object* v_typeAnalysis_1596_; lean_object* v_target_1597_; uint8_t v_didChange_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1610_; 
v_snd_1593_ = lean_ctor_get(v_a_1588_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_a_1588_);
v___x_1594_ = lean_st_ref_take(v___y_1564_);
v_caches_1595_ = lean_ctor_get(v___x_1594_, 0);
v_typeAnalysis_1596_ = lean_ctor_get(v___x_1594_, 1);
v_target_1597_ = lean_ctor_get(v___x_1594_, 2);
v_didChange_1598_ = lean_ctor_get_uint8(v___x_1594_, sizeof(void*)*4);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v___x_1594_, 3);
lean_dec(v_unused_1611_);
v___x_1600_ = v___x_1594_;
v_isShared_1601_ = v_isSharedCheck_1610_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_target_1597_);
lean_inc(v_typeAnalysis_1596_);
lean_inc(v_caches_1595_);
lean_dec(v___x_1594_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1610_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 3, v_snd_1593_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_caches_1595_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_typeAnalysis_1596_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_target_1597_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_snd_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*4, v_didChange_1598_);
v___x_1603_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1604_ = lean_st_ref_put(v___y_1564_, v___x_1603_);
v___x_1605_ = lean_box(v___x_1574_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1605_);
v___x_1607_ = v___x_1590_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1614_; 
lean_inc_ref(v_fst_1592_);
lean_dec(v_a_1588_);
v_val_1612_ = lean_ctor_get(v_fst_1592_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v_fst_1592_, 1);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_val_1612_);
v___x_1614_ = v___x_1590_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_val_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1587_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1587_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
else
{
uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_del_object(v___x_1560_);
lean_dec(v_snd_1558_);
lean_del_object(v___x_1556_);
lean_dec(v_fst_1554_);
lean_dec(v_fst_1550_);
v___x_1627_ = 0;
v___x_1628_ = lean_box(v___x_1627_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1628_);
v___x_1630_ = v___x_1546_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
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
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1543_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1543_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(lean_object* v___f_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v_target_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_st_ref_get(v___y_1685_);
v_target_1697_ = lean_ctor_get(v___x_1696_, 2);
lean_inc_ref(v_target_1697_);
lean_dec(v___x_1696_);
v___x_1698_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1697_);
lean_dec_ref(v_target_1697_);
v___x_1699_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v___x_1698_, v___f_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object* v___f_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(v___f_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(lean_object* v_cls_1724_, lean_object* v_msg_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_1724_, v_msg_1725_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___boxed(lean_object* v_cls_1739_, lean_object* v_msg_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(v_cls_1739_, v_msg_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(lean_object* v_00_u03b2_1754_, lean_object* v_m_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_1755_, v_a_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object* v_00_u03b2_1758_, lean_object* v_m_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(v_00_u03b2_1758_, v_m_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_m_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(lean_object* v_00_u03b2_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_1763_, v_x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object* v_00_u03b2_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(v_00_u03b2_1766_, v_x_1767_, v_x_1768_);
lean_dec_ref(v_x_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(lean_object* v_upperBound_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, uint8_t v___x_1773_, lean_object* v___x_1774_, lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v_inst_1777_, lean_object* v_R_1778_, lean_object* v_a_1779_, lean_object* v_b_1780_, lean_object* v_c_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_1770_, v___x_1771_, v___x_1772_, v___x_1773_, v___x_1774_, v___x_1775_, v___x_1776_, v_a_1779_, v_b_1780_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_1795_ = _args[0];
lean_object* v___x_1796_ = _args[1];
lean_object* v___x_1797_ = _args[2];
lean_object* v___x_1798_ = _args[3];
lean_object* v___x_1799_ = _args[4];
lean_object* v___x_1800_ = _args[5];
lean_object* v___x_1801_ = _args[6];
lean_object* v_inst_1802_ = _args[7];
lean_object* v_R_1803_ = _args[8];
lean_object* v_a_1804_ = _args[9];
lean_object* v_b_1805_ = _args[10];
lean_object* v_c_1806_ = _args[11];
lean_object* v___y_1807_ = _args[12];
lean_object* v___y_1808_ = _args[13];
lean_object* v___y_1809_ = _args[14];
lean_object* v___y_1810_ = _args[15];
lean_object* v___y_1811_ = _args[16];
lean_object* v___y_1812_ = _args[17];
lean_object* v___y_1813_ = _args[18];
lean_object* v___y_1814_ = _args[19];
lean_object* v___y_1815_ = _args[20];
lean_object* v___y_1816_ = _args[21];
lean_object* v___y_1817_ = _args[22];
lean_object* v___y_1818_ = _args[23];
_start:
{
uint8_t v___x_80429__boxed_1819_; lean_object* v_res_1820_; 
v___x_80429__boxed_1819_ = lean_unbox(v___x_1798_);
v_res_1820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(v_upperBound_1795_, v___x_1796_, v___x_1797_, v___x_80429__boxed_1819_, v___x_1799_, v___x_1800_, v___x_1801_, v_inst_1802_, v_R_1803_, v_a_1804_, v_b_1805_, v_c_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v___x_1800_);
lean_dec(v___x_1797_);
lean_dec_ref(v___x_1796_);
lean_dec(v_upperBound_1795_);
return v_res_1820_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_object* v_00_u03b2_1821_, lean_object* v_m_1822_, lean_object* v_a_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_1822_, v_a_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___boxed(lean_object* v_00_u03b2_1825_, lean_object* v_m_1826_, lean_object* v_a_1827_){
_start:
{
uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_res_1828_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(v_00_u03b2_1825_, v_m_1826_, v_a_1827_);
lean_dec_ref(v_a_1827_);
lean_dec_ref(v_m_1826_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(lean_object* v_00_u03b2_1830_, lean_object* v_m_1831_, lean_object* v_a_1832_, lean_object* v_b_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_m_1831_, v_a_1832_, v_b_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(lean_object* v_00_u03b2_1835_, lean_object* v_m_1836_, lean_object* v_a_1837_, lean_object* v_b_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_m_1836_, v_a_1837_, v_b_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_x_1841_, v_x_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(lean_object* v_upperBound_1845_, lean_object* v___x_1846_, lean_object* v_inst_1847_, lean_object* v_R_1848_, lean_object* v_a_1849_, lean_object* v_b_1850_, lean_object* v_c_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1845_, v___x_1846_, v_a_1849_, v_b_1850_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1865_ = _args[0];
lean_object* v___x_1866_ = _args[1];
lean_object* v_inst_1867_ = _args[2];
lean_object* v_R_1868_ = _args[3];
lean_object* v_a_1869_ = _args[4];
lean_object* v_b_1870_ = _args[5];
lean_object* v_c_1871_ = _args[6];
lean_object* v___y_1872_ = _args[7];
lean_object* v___y_1873_ = _args[8];
lean_object* v___y_1874_ = _args[9];
lean_object* v___y_1875_ = _args[10];
lean_object* v___y_1876_ = _args[11];
lean_object* v___y_1877_ = _args[12];
lean_object* v___y_1878_ = _args[13];
lean_object* v___y_1879_ = _args[14];
lean_object* v___y_1880_ = _args[15];
lean_object* v___y_1881_ = _args[16];
lean_object* v___y_1882_ = _args[17];
lean_object* v___y_1883_ = _args[18];
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(v_upperBound_1865_, v___x_1866_, v_inst_1867_, v_R_1868_, v_a_1869_, v_b_1870_, v_c_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec_ref(v___x_1866_);
lean_dec(v_upperBound_1865_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(lean_object* v_00_u03b2_1885_, lean_object* v_a_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1889_, lean_object* v_a_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(v_00_u03b2_1889_, v_a_1890_, v_x_1891_);
lean_dec(v_x_1891_);
lean_dec(v_a_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_object* v_00_u03b2_1893_, lean_object* v_x_1894_, size_t v_x_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_1894_, v_x_1895_, v_x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
size_t v_x_80555__boxed_1902_; lean_object* v_res_1903_; 
v_x_80555__boxed_1902_ = lean_unbox_usize(v_x_1900_);
lean_dec(v_x_1900_);
v_res_1903_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(v_00_u03b2_1898_, v_x_1899_, v_x_80555__boxed_1902_, v_x_1901_);
lean_dec_ref(v_x_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_object* v_00_u03b2_1904_, lean_object* v_a_1905_, lean_object* v_x_1906_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1905_, v_x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1908_, lean_object* v_a_1909_, lean_object* v_x_1910_){
_start:
{
uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_res_1911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(v_00_u03b2_1908_, v_a_1909_, v_x_1910_);
lean_dec(v_x_1910_);
lean_dec_ref(v_a_1909_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(lean_object* v_00_u03b2_1913_, lean_object* v_data_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_data_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_object* v_00_u03b2_1916_, lean_object* v_a_1917_, lean_object* v_x_1918_){
_start:
{
uint8_t v___x_1919_; 
v___x_1919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_1917_, v_x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___boxed(lean_object* v_00_u03b2_1920_, lean_object* v_a_1921_, lean_object* v_x_1922_){
_start:
{
uint8_t v_res_1923_; lean_object* v_r_1924_; 
v_res_1923_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(v_00_u03b2_1920_, v_a_1921_, v_x_1922_);
lean_dec(v_x_1922_);
lean_dec(v_a_1921_);
v_r_1924_ = lean_box(v_res_1923_);
return v_r_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13(lean_object* v_00_u03b2_1925_, lean_object* v_data_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_data_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14(lean_object* v_00_u03b2_1928_, lean_object* v_a_1929_, lean_object* v_b_1930_, lean_object* v_x_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1929_, v_b_1930_, v_x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(lean_object* v_00_u03b2_1933_, lean_object* v_x_1934_, size_t v_x_1935_, size_t v_x_1936_, lean_object* v_x_1937_, lean_object* v_x_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1934_, v_x_1935_, v_x_1936_, v_x_1937_, v_x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
size_t v_x_80584__boxed_1946_; size_t v_x_80585__boxed_1947_; lean_object* v_res_1948_; 
v_x_80584__boxed_1946_ = lean_unbox_usize(v_x_1942_);
lean_dec(v_x_1942_);
v_x_80585__boxed_1947_ = lean_unbox_usize(v_x_1943_);
lean_dec(v_x_1943_);
v_res_1948_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(v_00_u03b2_1940_, v_x_1941_, v_x_80584__boxed_1946_, v_x_80585__boxed_1947_, v_x_1944_, v_x_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_1949_, lean_object* v_i_1950_, lean_object* v_source_1951_, lean_object* v_target_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v_i_1950_, v_source_1951_, v_target_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17(lean_object* v_00_u03b2_1954_, lean_object* v_i_1955_, lean_object* v_source_1956_, lean_object* v_target_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v_i_1955_, v_source_1956_, v_target_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21(lean_object* v_00_u03b2_1959_, lean_object* v_n_1960_, lean_object* v_k_1961_, lean_object* v_v_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v_n_1960_, v_k_1961_, v_v_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(lean_object* v_00_u03b2_1964_, size_t v_depth_1965_, lean_object* v_keys_1966_, lean_object* v_vals_1967_, lean_object* v_heq_1968_, lean_object* v_i_1969_, lean_object* v_entries_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_1965_, v_keys_1966_, v_vals_1967_, v_i_1969_, v_entries_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___boxed(lean_object* v_00_u03b2_1972_, lean_object* v_depth_1973_, lean_object* v_keys_1974_, lean_object* v_vals_1975_, lean_object* v_heq_1976_, lean_object* v_i_1977_, lean_object* v_entries_1978_){
_start:
{
size_t v_depth_boxed_1979_; lean_object* v_res_1980_; 
v_depth_boxed_1979_ = lean_unbox_usize(v_depth_1973_);
lean_dec(v_depth_1973_);
v_res_1980_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(v_00_u03b2_1972_, v_depth_boxed_1979_, v_keys_1974_, v_vals_1975_, v_heq_1976_, v_i_1977_, v_entries_1978_);
lean_dec_ref(v_vals_1975_);
lean_dec_ref(v_keys_1974_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18(lean_object* v_00_u03b2_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_x_1982_, v_x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22(lean_object* v_00_u03b2_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_x_1986_, v_x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26(lean_object* v_00_u03b2_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_x_1990_, v_x_1991_, v_x_1992_, v_x_1993_);
return v___x_1994_;
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

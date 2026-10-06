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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t v___x_78088__boxed_385_; lean_object* v_res_386_; 
v___x_78088__boxed_385_ = lean_unbox(v___x_370_);
v_res_386_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(v___x_78088__boxed_385_, v___f_371_, v_____r_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
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
size_t v_x_78230__boxed_522_; lean_object* v_res_523_; 
v_x_78230__boxed_522_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_523_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_519_, v_x_78230__boxed_522_, v_x_521_);
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
uint8_t v___x_78385__boxed_561_; lean_object* v_res_562_; 
v___x_78385__boxed_561_ = lean_unbox(v___x_549_);
v_res_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(v___x_78385__boxed_561_, v_x_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
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
lean_object* v___x_606_; lean_object* v_env_607_; uint8_t v___x_608_; lean_object* v_env_609_; lean_object* v___x_610_; lean_object* v_toCold_611_; lean_object* v_mctx_612_; lean_object* v_lctx_613_; lean_object* v_options_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_606_ = lean_st_ref_get(v___y_604_);
v_env_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc_ref(v_env_607_);
lean_dec(v___x_606_);
v___x_608_ = 0;
v_env_609_ = l_Lean_Environment_setRecordingDeps(v_env_607_, v___x_608_);
v___x_610_ = lean_st_ref_get(v___y_602_);
v_toCold_611_ = lean_ctor_get(v___y_603_, 0);
v_mctx_612_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_mctx_612_);
lean_dec(v___x_610_);
v_lctx_613_ = lean_ctor_get(v___y_601_, 2);
v_options_614_ = lean_ctor_get(v_toCold_611_, 2);
lean_inc_ref(v_options_614_);
lean_inc_ref(v_lctx_613_);
v___x_615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_615_, 0, v_env_609_);
lean_ctor_set(v___x_615_, 1, v_mctx_612_);
lean_ctor_set(v___x_615_, 2, v_lctx_613_);
lean_ctor_set(v___x_615_, 3, v_options_614_);
v___x_616_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_msgData_600_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1___boxed(lean_object* v_msgData_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msgData_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_624_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_625_; double v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_float_of_nat(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(lean_object* v_cls_630_, lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_ref_637_; lean_object* v___x_638_; lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_684_; 
v_ref_637_ = lean_ctor_get(v___y_634_, 2);
v___x_638_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_684_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_684_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_684_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v_traceState_644_; lean_object* v_env_645_; lean_object* v_nextMacroScope_646_; lean_object* v_ngen_647_; lean_object* v_auxDeclNGen_648_; lean_object* v_cache_649_; lean_object* v_recordedDeps_650_; lean_object* v_messages_651_; lean_object* v_infoState_652_; lean_object* v_snapshotTasks_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_683_; 
v___x_643_ = lean_st_ref_take(v___y_635_);
v_traceState_644_ = lean_ctor_get(v___x_643_, 4);
v_env_645_ = lean_ctor_get(v___x_643_, 0);
v_nextMacroScope_646_ = lean_ctor_get(v___x_643_, 1);
v_ngen_647_ = lean_ctor_get(v___x_643_, 2);
v_auxDeclNGen_648_ = lean_ctor_get(v___x_643_, 3);
v_cache_649_ = lean_ctor_get(v___x_643_, 5);
v_recordedDeps_650_ = lean_ctor_get(v___x_643_, 6);
v_messages_651_ = lean_ctor_get(v___x_643_, 7);
v_infoState_652_ = lean_ctor_get(v___x_643_, 8);
v_snapshotTasks_653_ = lean_ctor_get(v___x_643_, 9);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_683_ == 0)
{
v___x_655_ = v___x_643_;
v_isShared_656_ = v_isSharedCheck_683_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snapshotTasks_653_);
lean_inc(v_infoState_652_);
lean_inc(v_messages_651_);
lean_inc(v_recordedDeps_650_);
lean_inc(v_cache_649_);
lean_inc(v_traceState_644_);
lean_inc(v_auxDeclNGen_648_);
lean_inc(v_ngen_647_);
lean_inc(v_nextMacroScope_646_);
lean_inc(v_env_645_);
lean_dec(v___x_643_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_683_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
uint64_t v_tid_657_; lean_object* v_traces_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_682_; 
v_tid_657_ = lean_ctor_get_uint64(v_traceState_644_, sizeof(void*)*1);
v_traces_658_ = lean_ctor_get(v_traceState_644_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_traceState_644_);
if (v_isSharedCheck_682_ == 0)
{
v___x_660_ = v_traceState_644_;
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_traces_658_);
lean_dec(v_traceState_644_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_682_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; double v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_662_ = lean_box(0);
v___x_663_ = lean_box(0);
v___x_664_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0);
v___x_665_ = 0;
v___x_666_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1));
v___x_667_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_667_, 0, v_cls_630_);
lean_ctor_set(v___x_667_, 1, v___x_663_);
lean_ctor_set(v___x_667_, 2, v___x_666_);
lean_ctor_set_float(v___x_667_, sizeof(void*)*3, v___x_664_);
lean_ctor_set_float(v___x_667_, sizeof(void*)*3 + 8, v___x_664_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*3 + 16, v___x_665_);
v___x_668_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2));
v___x_669_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v_a_639_);
lean_ctor_set(v___x_669_, 2, v___x_668_);
lean_inc(v_ref_637_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_ref_637_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Lean_PersistentArray_push___redArg(v_traces_658_, v___x_670_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_671_);
v___x_673_ = v___x_660_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_671_);
lean_ctor_set_uint64(v_reuseFailAlloc_681_, sizeof(void*)*1, v_tid_657_);
v___x_673_ = v_reuseFailAlloc_681_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v___x_673_);
v___x_675_ = v___x_655_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_env_645_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_nextMacroScope_646_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_ngen_647_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_auxDeclNGen_648_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 5, v_cache_649_);
lean_ctor_set(v_reuseFailAlloc_680_, 6, v_recordedDeps_650_);
lean_ctor_set(v_reuseFailAlloc_680_, 7, v_messages_651_);
lean_ctor_set(v_reuseFailAlloc_680_, 8, v_infoState_652_);
lean_ctor_set(v_reuseFailAlloc_680_, 9, v_snapshotTasks_653_);
v___x_675_ = v_reuseFailAlloc_680_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_st_ref_put(v___y_635_, v___x_675_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_662_);
v___x_678_ = v___x_641_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_662_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___boxed(lean_object* v_cls_685_, lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_685_, v_msg_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_692_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_703_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4));
v___x_704_ = l_Lean_Name_append(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(lean_object* v_upperBound_708_, lean_object* v___x_709_, lean_object* v___x_710_, uint8_t v___x_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_a_715_, lean_object* v_b_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___y_730_; lean_object* v___y_753_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_lt(v_a_715_, v_upperBound_708_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec(v_a_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_b_716_);
return v___x_784_;
}
else
{
lean_object* v_snd_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_855_; 
v_snd_785_ = lean_ctor_get(v_b_716_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_b_716_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v_b_716_, 0);
lean_dec(v_unused_856_);
v___x_787_ = v_b_716_;
v_isShared_788_ = v_isSharedCheck_855_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snd_785_);
lean_dec(v_b_716_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_855_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___y_794_; lean_object* v___x_852_; 
v___x_789_ = lean_box(v___x_711_);
v___f_790_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_790_, 0, v___x_789_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_array_fget_borrowed(v___x_709_, v_a_715_);
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v___x_713_, v_a_715_);
if (lean_obj_tag(v___x_852_) == 1)
{
lean_object* v_val_853_; lean_object* v___x_854_; 
v_val_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v___x_852_, 1);
lean_inc_ref(v___x_714_);
v___x_854_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v___x_714_, v_val_853_);
lean_dec(v_val_853_);
v___y_794_ = v___x_854_;
goto v___jp_793_;
}
else
{
lean_dec(v___x_852_);
lean_inc_ref(v___x_714_);
v___y_794_ = v___x_714_;
goto v___jp_793_;
}
v___jp_793_:
{
lean_object* v_type_795_; uint32_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_type_795_ = lean_ctor_get(v___x_792_, 1);
v___x_796_ = lean_uint32_of_nat(v___x_710_);
v___x_797_ = lean_box_uint32(v___x_796_);
v___x_798_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed), 13, 2);
lean_closure_set(v___x_798_, 0, v___x_797_);
lean_closure_set(v___x_798_, 1, v___y_794_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v___f_790_);
lean_inc_ref(v_type_795_);
v___x_800_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_800_, 0, v_type_795_);
lean_inc_ref(v___x_712_);
v___x_801_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_800_, v___x_799_, v___x_712_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
lean_inc(v___x_792_);
v___x_803_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_792_, v_a_802_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v_type_805_; lean_object* v_value_806_; uint8_t v___x_807_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v_type_805_ = lean_ctor_get(v_a_804_, 1);
v_value_806_ = lean_ctor_get(v_a_804_, 2);
lean_inc_ref(v_type_805_);
v___x_807_ = l_Lean_Expr_isFalse(v_type_805_);
if (v___x_807_ == 0)
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___f_810_; uint8_t v___x_811_; 
lean_del_object(v___x_787_);
lean_inc(v_a_804_);
lean_inc(v_snd_785_);
v___f_808_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_808_, 0, v_snd_785_);
lean_closure_set(v___f_808_, 1, v_a_804_);
lean_closure_set(v___f_808_, 2, v___x_791_);
v___x_809_ = lean_box(v___x_783_);
v___f_810_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed), 15, 2);
lean_closure_set(v___f_810_, 0, v___x_809_);
lean_closure_set(v___f_810_, 1, v___f_808_);
v___x_811_ = lean_expr_eqv(v_type_795_, v_type_805_);
if (v___x_811_ == 0)
{
lean_inc_ref(v_type_805_);
lean_dec(v_a_804_);
lean_dec(v_snd_785_);
lean_inc_ref(v_type_795_);
v___y_757_ = v_type_805_;
v___y_758_ = v_type_795_;
v___y_759_ = v___f_810_;
goto v___jp_756_;
}
else
{
if (v___x_807_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec_ref(v___f_810_);
v___x_812_ = lean_box(0);
v___x_813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_785_, v_a_804_, v___x_791_, v___x_812_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
v___y_730_ = v___x_813_;
goto v___jp_729_;
}
else
{
lean_inc_ref(v_type_805_);
lean_dec(v_a_804_);
lean_dec(v_snd_785_);
lean_inc_ref(v_type_795_);
v___y_757_ = v_type_805_;
v___y_758_ = v_type_795_;
v___y_759_ = v___f_810_;
goto v___jp_756_;
}
}
}
else
{
lean_object* v___x_814_; 
lean_inc_ref(v_value_806_);
lean_dec(v_a_804_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v___x_814_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_806_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_826_; 
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___x_814_, 0);
lean_dec(v_unused_827_);
v___x_816_ = v___x_814_;
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
else
{
lean_dec(v___x_814_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_818_ = lean_box(v___x_783_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_819_);
v___x_821_ = v___x_787_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_snd_785_);
v___x_821_ = v_reuseFailAlloc_825_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_823_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_821_);
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_del_object(v___x_787_);
lean_dec(v_snd_785_);
v_a_828_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_814_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_814_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_787_);
lean_dec(v_snd_785_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v_a_836_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_803_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_803_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_del_object(v___x_787_);
lean_dec(v_snd_785_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v_a_844_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_801_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_801_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
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
}
}
v___jp_729_:
{
if (lean_obj_tag(v___y_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_743_; 
v_a_731_ = lean_ctor_get(v___y_730_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___y_730_);
if (v_isSharedCheck_743_ == 0)
{
v___x_733_ = v___y_730_;
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___y_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; 
lean_dec(v_a_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v_a_735_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v_a_731_, 1);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v_a_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_733_);
v_a_739_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v_a_731_, 1);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_a_715_, v___x_740_);
lean_dec(v_a_715_);
v_a_715_ = v___x_741_;
v_b_716_ = v_a_739_;
goto _start;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v_a_744_ = lean_ctor_get(v___y_730_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___y_730_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___y_730_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___y_730_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_box(0);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
v___x_755_ = lean_apply_13(v___y_753_, v___x_754_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, lean_box(0));
v___y_730_ = v___x_755_;
goto v___jp_729_;
}
v___jp_756_:
{
lean_object* v_toCold_760_; lean_object* v_options_761_; uint8_t v_hasTrace_762_; 
v_toCold_760_ = lean_ctor_get(v___y_726_, 0);
v_options_761_ = lean_ctor_get(v_toCold_760_, 2);
v_hasTrace_762_ = lean_ctor_get_uint8(v_options_761_, sizeof(void*)*1);
if (v_hasTrace_762_ == 0)
{
lean_dec_ref(v___y_758_);
lean_dec_ref(v___y_757_);
v___y_753_ = v___y_759_;
goto v___jp_752_;
}
else
{
lean_object* v_inheritedTraceOptions_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_inheritedTraceOptions_763_ = lean_ctor_get(v_toCold_760_, 11);
v___x_764_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_765_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_763_, v_options_761_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec_ref(v___y_758_);
lean_dec_ref(v___y_757_);
v___y_753_ = v___y_759_;
goto v___jp_752_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_767_ = l_Lean_MessageData_ofExpr(v___y_758_);
v___x_768_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_MessageData_ofExpr(v___y_757_);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_764_, v___x_771_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
lean_inc(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
v___x_774_ = lean_apply_13(v___y_759_, v_a_773_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, lean_box(0));
v___y_730_ = v___x_774_;
goto v___jp_729_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v___y_759_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v_a_775_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_772_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_772_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_857_ = _args[0];
lean_object* v___x_858_ = _args[1];
lean_object* v___x_859_ = _args[2];
lean_object* v___x_860_ = _args[3];
lean_object* v___x_861_ = _args[4];
lean_object* v___x_862_ = _args[5];
lean_object* v___x_863_ = _args[6];
lean_object* v_a_864_ = _args[7];
lean_object* v_b_865_ = _args[8];
lean_object* v___y_866_ = _args[9];
lean_object* v___y_867_ = _args[10];
lean_object* v___y_868_ = _args[11];
lean_object* v___y_869_ = _args[12];
lean_object* v___y_870_ = _args[13];
lean_object* v___y_871_ = _args[14];
lean_object* v___y_872_ = _args[15];
lean_object* v___y_873_ = _args[16];
lean_object* v___y_874_ = _args[17];
lean_object* v___y_875_ = _args[18];
lean_object* v___y_876_ = _args[19];
lean_object* v___y_877_ = _args[20];
_start:
{
uint8_t v___x_78640__boxed_878_; lean_object* v_res_879_; 
v___x_78640__boxed_878_ = lean_unbox(v___x_860_);
v_res_879_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_857_, v___x_858_, v___x_859_, v___x_78640__boxed_878_, v___x_861_, v___x_862_, v___x_863_, v_a_864_, v_b_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v___x_862_);
lean_dec(v___x_859_);
lean_dec_ref(v___x_858_);
lean_dec(v_upperBound_857_);
return v_res_879_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(lean_object* v_a_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
uint8_t v___x_882_; 
v___x_882_ = 0;
return v___x_882_;
}
else
{
lean_object* v_key_883_; lean_object* v_tail_884_; size_t v___x_885_; size_t v___x_886_; uint8_t v___x_887_; 
v_key_883_ = lean_ctor_get(v_x_881_, 0);
v_tail_884_ = lean_ctor_get(v_x_881_, 2);
v___x_885_ = lean_ptr_addr(v_key_883_);
v___x_886_ = lean_ptr_addr(v_a_880_);
v___x_887_ = lean_usize_dec_eq(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
v_x_881_ = v_tail_884_;
goto _start;
}
else
{
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___boxed(lean_object* v_a_889_, lean_object* v_x_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_889_, v_x_890_);
lean_dec(v_x_890_);
lean_dec_ref(v_a_889_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(lean_object* v_m_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_buckets_895_; lean_object* v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v_fold_903_; uint64_t v___x_904_; uint64_t v___x_905_; uint64_t v___x_906_; size_t v___x_907_; size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_buckets_895_ = lean_ctor_get(v_m_893_, 1);
v___x_896_ = lean_array_get_size(v_buckets_895_);
v___x_897_ = lean_ptr_addr(v_a_894_);
v___x_898_ = ((size_t)3ULL);
v___x_899_ = lean_usize_shift_right(v___x_897_, v___x_898_);
v___x_900_ = lean_usize_to_uint64(v___x_899_);
v___x_901_ = 32ULL;
v___x_902_ = lean_uint64_shift_right(v___x_900_, v___x_901_);
v_fold_903_ = lean_uint64_xor(v___x_900_, v___x_902_);
v___x_904_ = 16ULL;
v___x_905_ = lean_uint64_shift_right(v_fold_903_, v___x_904_);
v___x_906_ = lean_uint64_xor(v_fold_903_, v___x_905_);
v___x_907_ = lean_uint64_to_usize(v___x_906_);
v___x_908_ = lean_usize_of_nat(v___x_896_);
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_sub(v___x_908_, v___x_909_);
v___x_911_ = lean_usize_land(v___x_907_, v___x_910_);
v___x_912_ = lean_array_uget_borrowed(v_buckets_895_, v___x_911_);
v___x_913_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_894_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg___boxed(lean_object* v_m_914_, lean_object* v_a_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_914_, v_a_915_);
lean_dec_ref(v_a_915_);
lean_dec_ref(v_m_914_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(lean_object* v_arg_918_, lean_object* v_x_919_){
_start:
{
uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = 0;
v___x_921_ = lean_box(v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_arg_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
return v_x_923_;
}
else
{
lean_object* v_key_925_; lean_object* v_value_926_; lean_object* v_tail_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_950_; 
v_key_925_ = lean_ctor_get(v_x_924_, 0);
v_value_926_ = lean_ctor_get(v_x_924_, 1);
v_tail_927_ = lean_ctor_get(v_x_924_, 2);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_950_ == 0)
{
v___x_929_ = v_x_924_;
v_isShared_930_ = v_isSharedCheck_950_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_tail_927_);
lean_inc(v_value_926_);
lean_inc(v_key_925_);
lean_dec(v_x_924_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_950_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; uint64_t v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v_fold_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; size_t v___x_939_; size_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_931_ = lean_array_get_size(v_x_923_);
v___x_932_ = lean_uint64_of_nat(v_key_925_);
v___x_933_ = 32ULL;
v___x_934_ = lean_uint64_shift_right(v___x_932_, v___x_933_);
v_fold_935_ = lean_uint64_xor(v___x_932_, v___x_934_);
v___x_936_ = 16ULL;
v___x_937_ = lean_uint64_shift_right(v_fold_935_, v___x_936_);
v___x_938_ = lean_uint64_xor(v_fold_935_, v___x_937_);
v___x_939_ = lean_uint64_to_usize(v___x_938_);
v___x_940_ = lean_usize_of_nat(v___x_931_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_sub(v___x_940_, v___x_941_);
v___x_943_ = lean_usize_land(v___x_939_, v___x_942_);
v___x_944_ = lean_array_uget_borrowed(v_x_923_, v___x_943_);
lean_inc(v___x_944_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 2, v___x_944_);
v___x_946_ = v___x_929_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_key_925_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_value_926_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v___x_944_);
v___x_946_ = v_reuseFailAlloc_949_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_array_uset(v_x_923_, v___x_943_, v___x_946_);
v_x_923_ = v___x_947_;
v_x_924_ = v_tail_927_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(lean_object* v_i_951_, lean_object* v_source_952_, lean_object* v_target_953_){
_start:
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_array_get_size(v_source_952_);
v___x_955_ = lean_nat_dec_lt(v_i_951_, v___x_954_);
if (v___x_955_ == 0)
{
lean_dec_ref(v_source_952_);
lean_dec(v_i_951_);
return v_target_953_;
}
else
{
lean_object* v_es_956_; lean_object* v___x_957_; lean_object* v_source_958_; lean_object* v_target_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_es_956_ = lean_array_fget(v_source_952_, v_i_951_);
v___x_957_ = lean_box(0);
v_source_958_ = lean_array_fset(v_source_952_, v_i_951_, v___x_957_);
v_target_959_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_target_953_, v_es_956_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_i_951_, v___x_960_);
lean_dec(v_i_951_);
v_i_951_ = v___x_961_;
v_source_952_ = v_source_958_;
v_target_953_ = v_target_959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(lean_object* v_data_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_nbuckets_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_964_ = lean_array_get_size(v_data_963_);
v___x_965_ = lean_unsigned_to_nat(2u);
v_nbuckets_966_ = lean_nat_mul(v___x_964_, v___x_965_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_box(0);
v___x_969_ = lean_mk_array(v_nbuckets_966_, v___x_968_);
v___x_970_ = lean_array_propagate_mark(v_data_963_, v___x_969_);
v___x_971_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v___x_967_, v_data_963_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(lean_object* v_a_972_, lean_object* v_x_973_){
_start:
{
if (lean_obj_tag(v_x_973_) == 0)
{
uint8_t v___x_974_; 
v___x_974_ = 0;
return v___x_974_;
}
else
{
lean_object* v_key_975_; lean_object* v_tail_976_; uint8_t v___x_977_; 
v_key_975_ = lean_ctor_get(v_x_973_, 0);
v_tail_976_ = lean_ctor_get(v_x_973_, 2);
v___x_977_ = lean_nat_dec_eq(v_key_975_, v_a_972_);
if (v___x_977_ == 0)
{
v_x_973_ = v_tail_976_;
goto _start;
}
else
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg___boxed(lean_object* v_a_979_, lean_object* v_x_980_){
_start:
{
uint8_t v_res_981_; lean_object* v_r_982_; 
v_res_981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_979_, v_x_980_);
lean_dec(v_x_980_);
lean_dec(v_a_979_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(lean_object* v_a_983_, lean_object* v_b_984_, lean_object* v_x_985_){
_start:
{
if (lean_obj_tag(v_x_985_) == 0)
{
lean_dec(v_b_984_);
lean_dec(v_a_983_);
return v_x_985_;
}
else
{
lean_object* v_key_986_; lean_object* v_value_987_; lean_object* v_tail_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1000_; 
v_key_986_ = lean_ctor_get(v_x_985_, 0);
v_value_987_ = lean_ctor_get(v_x_985_, 1);
v_tail_988_ = lean_ctor_get(v_x_985_, 2);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_990_ = v_x_985_;
v_isShared_991_ = v_isSharedCheck_1000_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_tail_988_);
lean_inc(v_value_987_);
lean_inc(v_key_986_);
lean_dec(v_x_985_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1000_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
uint8_t v___x_992_; 
v___x_992_ = lean_nat_dec_eq(v_key_986_, v_a_983_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_983_, v_b_984_, v_tail_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 2, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_key_986_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_value_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
else
{
lean_object* v___x_998_; 
lean_dec(v_value_987_);
lean_dec(v_key_986_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v_b_984_);
lean_ctor_set(v___x_990_, 0, v_a_983_);
v___x_998_ = v___x_990_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_983_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_b_984_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_tail_988_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(lean_object* v_m_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v_size_1004_; lean_object* v_buckets_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1048_; 
v_size_1004_ = lean_ctor_get(v_m_1001_, 0);
v_buckets_1005_ = lean_ctor_get(v_m_1001_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_m_1001_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1007_ = v_m_1001_;
v_isShared_1008_ = v_isSharedCheck_1048_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_buckets_1005_);
lean_inc(v_size_1004_);
lean_dec(v_m_1001_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1048_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; uint64_t v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; uint64_t v_fold_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; lean_object* v_bkt_1022_; uint8_t v___x_1023_; 
v___x_1009_ = lean_array_get_size(v_buckets_1005_);
v___x_1010_ = lean_uint64_of_nat(v_a_1002_);
v___x_1011_ = 32ULL;
v___x_1012_ = lean_uint64_shift_right(v___x_1010_, v___x_1011_);
v_fold_1013_ = lean_uint64_xor(v___x_1010_, v___x_1012_);
v___x_1014_ = 16ULL;
v___x_1015_ = lean_uint64_shift_right(v_fold_1013_, v___x_1014_);
v___x_1016_ = lean_uint64_xor(v_fold_1013_, v___x_1015_);
v___x_1017_ = lean_uint64_to_usize(v___x_1016_);
v___x_1018_ = lean_usize_of_nat(v___x_1009_);
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = lean_usize_sub(v___x_1018_, v___x_1019_);
v___x_1021_ = lean_usize_land(v___x_1017_, v___x_1020_);
v_bkt_1022_ = lean_array_uget_borrowed(v_buckets_1005_, v___x_1021_);
v___x_1023_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_1002_, v_bkt_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v_size_x27_1025_; lean_object* v___x_1026_; lean_object* v_buckets_x27_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1024_ = lean_unsigned_to_nat(1u);
v_size_x27_1025_ = lean_nat_add(v_size_1004_, v___x_1024_);
lean_dec(v_size_1004_);
lean_inc(v_bkt_1022_);
v___x_1026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1026_, 0, v_a_1002_);
lean_ctor_set(v___x_1026_, 1, v_b_1003_);
lean_ctor_set(v___x_1026_, 2, v_bkt_1022_);
v_buckets_x27_1027_ = lean_array_uset(v_buckets_1005_, v___x_1021_, v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(4u);
v___x_1029_ = lean_nat_mul(v_size_x27_1025_, v___x_1028_);
v___x_1030_ = lean_unsigned_to_nat(3u);
v___x_1031_ = lean_nat_div(v___x_1029_, v___x_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_array_get_size(v_buckets_x27_1027_);
v___x_1033_ = lean_nat_dec_le(v___x_1031_, v___x_1032_);
lean_dec(v___x_1031_);
if (v___x_1033_ == 0)
{
lean_object* v_val_1034_; lean_object* v___x_1036_; 
v_val_1034_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_buckets_x27_1027_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v_val_1034_);
lean_ctor_set(v___x_1007_, 0, v_size_x27_1025_);
v___x_1036_ = v___x_1007_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_size_x27_1025_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_val_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
lean_object* v___x_1039_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v_buckets_x27_1027_);
lean_ctor_set(v___x_1007_, 0, v_size_x27_1025_);
v___x_1039_ = v___x_1007_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_size_x27_1025_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_buckets_x27_1027_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v___x_1041_; lean_object* v_buckets_x27_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_inc(v_bkt_1022_);
v___x_1041_ = lean_box(0);
v_buckets_x27_1042_ = lean_array_uset(v_buckets_1005_, v___x_1021_, v___x_1041_);
v___x_1043_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1002_, v_b_1003_, v_bkt_1022_);
v___x_1044_ = lean_array_uset(v_buckets_x27_1042_, v___x_1021_, v___x_1043_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1044_);
v___x_1046_ = v___x_1007_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_size_1004_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 0)
{
return v_x_1049_;
}
else
{
lean_object* v_key_1051_; lean_object* v_value_1052_; lean_object* v_tail_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1079_; 
v_key_1051_ = lean_ctor_get(v_x_1050_, 0);
v_value_1052_ = lean_ctor_get(v_x_1050_, 1);
v_tail_1053_ = lean_ctor_get(v_x_1050_, 2);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_x_1050_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1055_ = v_x_1050_;
v_isShared_1056_ = v_isSharedCheck_1079_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_tail_1053_);
lean_inc(v_value_1052_);
lean_inc(v_key_1051_);
lean_dec(v_x_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1079_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v___x_1063_; uint64_t v_fold_1064_; uint64_t v___x_1065_; uint64_t v___x_1066_; uint64_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1057_ = lean_array_get_size(v_x_1049_);
v___x_1058_ = lean_ptr_addr(v_key_1051_);
v___x_1059_ = ((size_t)3ULL);
v___x_1060_ = lean_usize_shift_right(v___x_1058_, v___x_1059_);
v___x_1061_ = lean_usize_to_uint64(v___x_1060_);
v___x_1062_ = 32ULL;
v___x_1063_ = lean_uint64_shift_right(v___x_1061_, v___x_1062_);
v_fold_1064_ = lean_uint64_xor(v___x_1061_, v___x_1063_);
v___x_1065_ = 16ULL;
v___x_1066_ = lean_uint64_shift_right(v_fold_1064_, v___x_1065_);
v___x_1067_ = lean_uint64_xor(v_fold_1064_, v___x_1066_);
v___x_1068_ = lean_uint64_to_usize(v___x_1067_);
v___x_1069_ = lean_usize_of_nat(v___x_1057_);
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_sub(v___x_1069_, v___x_1070_);
v___x_1072_ = lean_usize_land(v___x_1068_, v___x_1071_);
v___x_1073_ = lean_array_uget_borrowed(v_x_1049_, v___x_1072_);
lean_inc(v___x_1073_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 2, v___x_1073_);
v___x_1075_ = v___x_1055_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_key_1051_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_value_1052_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_array_uset(v_x_1049_, v___x_1072_, v___x_1075_);
v_x_1049_ = v___x_1076_;
v_x_1050_ = v_tail_1053_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(lean_object* v_i_1080_, lean_object* v_source_1081_, lean_object* v_target_1082_){
_start:
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_array_get_size(v_source_1081_);
v___x_1084_ = lean_nat_dec_lt(v_i_1080_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec_ref(v_source_1081_);
lean_dec(v_i_1080_);
return v_target_1082_;
}
else
{
lean_object* v_es_1085_; lean_object* v___x_1086_; lean_object* v_source_1087_; lean_object* v_target_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_es_1085_ = lean_array_fget(v_source_1081_, v_i_1080_);
v___x_1086_ = lean_box(0);
v_source_1087_ = lean_array_fset(v_source_1081_, v_i_1080_, v___x_1086_);
v_target_1088_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_target_1082_, v_es_1085_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_add(v_i_1080_, v___x_1089_);
lean_dec(v_i_1080_);
v_i_1080_ = v___x_1090_;
v_source_1081_ = v_source_1087_;
v_target_1082_ = v_target_1088_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(lean_object* v_data_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_nbuckets_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1093_ = lean_array_get_size(v_data_1092_);
v___x_1094_ = lean_unsigned_to_nat(2u);
v_nbuckets_1095_ = lean_nat_mul(v___x_1093_, v___x_1094_);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_mk_array(v_nbuckets_1095_, v___x_1097_);
v___x_1099_ = lean_array_propagate_mark(v_data_1092_, v___x_1098_);
v___x_1100_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v___x_1096_, v_data_1092_, v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(lean_object* v_m_1101_, lean_object* v_a_1102_, lean_object* v_b_1103_){
_start:
{
lean_object* v_size_1104_; lean_object* v_buckets_1105_; lean_object* v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; uint64_t v___x_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v_fold_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; lean_object* v_bkt_1122_; uint8_t v___x_1123_; 
v_size_1104_ = lean_ctor_get(v_m_1101_, 0);
v_buckets_1105_ = lean_ctor_get(v_m_1101_, 1);
v___x_1106_ = lean_array_get_size(v_buckets_1105_);
v___x_1107_ = lean_ptr_addr(v_a_1102_);
v___x_1108_ = ((size_t)3ULL);
v___x_1109_ = lean_usize_shift_right(v___x_1107_, v___x_1108_);
v___x_1110_ = lean_usize_to_uint64(v___x_1109_);
v___x_1111_ = 32ULL;
v___x_1112_ = lean_uint64_shift_right(v___x_1110_, v___x_1111_);
v_fold_1113_ = lean_uint64_xor(v___x_1110_, v___x_1112_);
v___x_1114_ = 16ULL;
v___x_1115_ = lean_uint64_shift_right(v_fold_1113_, v___x_1114_);
v___x_1116_ = lean_uint64_xor(v_fold_1113_, v___x_1115_);
v___x_1117_ = lean_uint64_to_usize(v___x_1116_);
v___x_1118_ = lean_usize_of_nat(v___x_1106_);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_sub(v___x_1118_, v___x_1119_);
v___x_1121_ = lean_usize_land(v___x_1117_, v___x_1120_);
v_bkt_1122_ = lean_array_uget_borrowed(v_buckets_1105_, v___x_1121_);
v___x_1123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1102_, v_bkt_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1144_; 
lean_inc_ref(v_buckets_1105_);
lean_inc(v_size_1104_);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_m_1101_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; lean_object* v_unused_1146_; 
v_unused_1145_ = lean_ctor_get(v_m_1101_, 1);
lean_dec(v_unused_1145_);
v_unused_1146_ = lean_ctor_get(v_m_1101_, 0);
lean_dec(v_unused_1146_);
v___x_1125_ = v_m_1101_;
v_isShared_1126_ = v_isSharedCheck_1144_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v_m_1101_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1144_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v_size_x27_1128_; lean_object* v___x_1129_; lean_object* v_buckets_x27_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1127_ = lean_unsigned_to_nat(1u);
v_size_x27_1128_ = lean_nat_add(v_size_1104_, v___x_1127_);
lean_dec(v_size_1104_);
lean_inc(v_bkt_1122_);
v___x_1129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1129_, 0, v_a_1102_);
lean_ctor_set(v___x_1129_, 1, v_b_1103_);
lean_ctor_set(v___x_1129_, 2, v_bkt_1122_);
v_buckets_x27_1130_ = lean_array_uset(v_buckets_1105_, v___x_1121_, v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(4u);
v___x_1132_ = lean_nat_mul(v_size_x27_1128_, v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(3u);
v___x_1134_ = lean_nat_div(v___x_1132_, v___x_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_array_get_size(v_buckets_x27_1130_);
v___x_1136_ = lean_nat_dec_le(v___x_1134_, v___x_1135_);
lean_dec(v___x_1134_);
if (v___x_1136_ == 0)
{
lean_object* v_val_1137_; lean_object* v___x_1139_; 
v_val_1137_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_buckets_x27_1130_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_val_1137_);
lean_ctor_set(v___x_1125_, 0, v_size_x27_1128_);
v___x_1139_ = v___x_1125_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_size_x27_1128_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_val_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
else
{
lean_object* v___x_1142_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_buckets_x27_1130_);
lean_ctor_set(v___x_1125_, 0, v_size_x27_1128_);
v___x_1142_ = v___x_1125_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_size_x27_1128_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_buckets_x27_1130_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_dec(v_b_1103_);
lean_dec_ref(v_a_1102_);
return v_m_1101_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(lean_object* v_fst_1147_, lean_object* v_snd_1148_, lean_object* v_fst_1149_, lean_object* v_fst_1150_, lean_object* v_x_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_fst_1147_);
lean_ctor_set(v___x_1164_, 1, v_snd_1148_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_fst_1149_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v_fst_1150_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_1169_ = _args[0];
lean_object* v_snd_1170_ = _args[1];
lean_object* v_fst_1171_ = _args[2];
lean_object* v_fst_1172_ = _args[3];
lean_object* v_x_1173_ = _args[4];
lean_object* v___y_1174_ = _args[5];
lean_object* v___y_1175_ = _args[6];
lean_object* v___y_1176_ = _args[7];
lean_object* v___y_1177_ = _args[8];
lean_object* v___y_1178_ = _args[9];
lean_object* v___y_1179_ = _args[10];
lean_object* v___y_1180_ = _args[11];
lean_object* v___y_1181_ = _args[12];
lean_object* v___y_1182_ = _args[13];
lean_object* v___y_1183_ = _args[14];
lean_object* v___y_1184_ = _args[15];
lean_object* v___y_1185_ = _args[16];
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1169_, v_snd_1170_, v_fst_1171_, v_fst_1172_, v_x_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(lean_object* v_x_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
lean_object* v_ks_1191_; lean_object* v_vs_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1218_; 
v_ks_1191_ = lean_ctor_get(v_x_1187_, 0);
v_vs_1192_ = lean_ctor_get(v_x_1187_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1194_ = v_x_1187_;
v_isShared_1195_ = v_isSharedCheck_1218_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_vs_1192_);
lean_inc(v_ks_1191_);
lean_dec(v_x_1187_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1218_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_array_get_size(v_ks_1191_);
v___x_1197_ = lean_nat_dec_lt(v_x_1188_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_dec(v_x_1188_);
v___x_1198_ = lean_array_push(v_ks_1191_, v_x_1189_);
v___x_1199_ = lean_array_push(v_vs_1192_, v_x_1190_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___x_1199_);
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1201_ = v___x_1194_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v_k_x27_1203_; size_t v___x_1204_; size_t v___x_1205_; uint8_t v___x_1206_; 
v_k_x27_1203_ = lean_array_fget_borrowed(v_ks_1191_, v_x_1188_);
v___x_1204_ = lean_ptr_addr(v_x_1189_);
v___x_1205_ = lean_ptr_addr(v_k_x27_1203_);
v___x_1206_ = lean_usize_dec_eq(v___x_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1208_; 
if (v_isShared_1195_ == 0)
{
v___x_1208_ = v___x_1194_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_ks_1191_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_vs_1192_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_add(v_x_1188_, v___x_1209_);
lean_dec(v_x_1188_);
v_x_1187_ = v___x_1208_;
v_x_1188_ = v___x_1210_;
goto _start;
}
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1213_ = lean_array_fset(v_ks_1191_, v_x_1188_, v_x_1189_);
v___x_1214_ = lean_array_fset(v_vs_1192_, v_x_1188_, v_x_1190_);
lean_dec(v_x_1188_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___x_1214_);
lean_ctor_set(v___x_1194_, 0, v___x_1213_);
v___x_1216_ = v___x_1194_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1214_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(lean_object* v_n_1219_, lean_object* v_k_1220_, lean_object* v_v_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_n_1219_, v___x_1222_, v_k_1220_, v_v_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(lean_object* v_x_1225_, size_t v_x_1226_, size_t v_x_1227_, lean_object* v_x_1228_, lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_object* v_es_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v_j_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_es_1230_ = lean_ctor_get(v_x_1225_, 0);
v___x_1231_ = ((size_t)31ULL);
v___x_1232_ = lean_usize_land(v_x_1226_, v___x_1231_);
v_j_1233_ = lean_usize_to_nat(v___x_1232_);
v___x_1234_ = lean_array_get_size(v_es_1230_);
v___x_1235_ = lean_nat_dec_lt(v_j_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec(v_j_1233_);
lean_dec(v_x_1229_);
lean_dec_ref(v_x_1228_);
return v_x_1225_;
}
else
{
lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1276_; 
lean_inc_ref(v_es_1230_);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_x_1225_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v_x_1225_, 0);
lean_dec(v_unused_1277_);
v___x_1237_ = v_x_1225_;
v_isShared_1238_ = v_isSharedCheck_1276_;
goto v_resetjp_1236_;
}
else
{
lean_dec(v_x_1225_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1276_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_v_1239_; lean_object* v___x_1240_; lean_object* v_xs_x27_1241_; lean_object* v___y_1243_; 
v_v_1239_ = lean_array_fget(v_es_1230_, v_j_1233_);
v___x_1240_ = lean_box(0);
v_xs_x27_1241_ = lean_array_fset(v_es_1230_, v_j_1233_, v___x_1240_);
switch(lean_obj_tag(v_v_1239_))
{
case 0:
{
lean_object* v_key_1248_; lean_object* v_val_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1261_; 
v_key_1248_ = lean_ctor_get(v_v_1239_, 0);
v_val_1249_ = lean_ctor_get(v_v_1239_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_v_1239_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1251_ = v_v_1239_;
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_val_1249_);
lean_inc(v_key_1248_);
lean_dec(v_v_1239_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
size_t v___x_1253_; size_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1253_ = lean_ptr_addr(v_x_1228_);
v___x_1254_ = lean_ptr_addr(v_key_1248_);
v___x_1255_ = lean_usize_dec_eq(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_del_object(v___x_1251_);
v___x_1256_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1248_, v_val_1249_, v_x_1228_, v_x_1229_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
v___y_1243_ = v___x_1257_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1259_; 
lean_dec(v_val_1249_);
lean_dec(v_key_1248_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_x_1229_);
lean_ctor_set(v___x_1251_, 0, v_x_1228_);
v___x_1259_ = v___x_1251_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_x_1228_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_x_1229_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v___y_1243_ = v___x_1259_;
goto v___jp_1242_;
}
}
}
}
case 1:
{
lean_object* v_node_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1274_; 
v_node_1262_ = lean_ctor_get(v_v_1239_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_v_1239_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1264_ = v_v_1239_;
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_node_1262_);
lean_dec(v_v_1239_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
size_t v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1266_ = ((size_t)5ULL);
v___x_1267_ = lean_usize_shift_right(v_x_1226_, v___x_1266_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_add(v_x_1227_, v___x_1268_);
v___x_1270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_node_1262_, v___x_1267_, v___x_1269_, v_x_1228_, v_x_1229_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1270_);
v___x_1272_ = v___x_1264_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
v___y_1243_ = v___x_1272_;
goto v___jp_1242_;
}
}
}
default: 
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_x_1228_);
lean_ctor_set(v___x_1275_, 1, v_x_1229_);
v___y_1243_ = v___x_1275_;
goto v___jp_1242_;
}
}
v___jp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = lean_array_fset(v_xs_x27_1241_, v_j_1233_, v___y_1243_);
lean_dec(v_j_1233_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1244_);
v___x_1246_ = v___x_1237_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
else
{
lean_object* v_ks_1278_; lean_object* v_vs_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1297_; 
v_ks_1278_ = lean_ctor_get(v_x_1225_, 0);
v_vs_1279_ = lean_ctor_get(v_x_1225_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_x_1225_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1281_ = v_x_1225_;
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_vs_1279_);
lean_inc(v_ks_1278_);
lean_dec(v_x_1225_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1297_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_ks_1278_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_vs_1279_);
v___x_1284_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v_newNode_1285_; size_t v___x_1286_; uint8_t v___x_1287_; 
v_newNode_1285_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v___x_1284_, v_x_1228_, v_x_1229_);
v___x_1286_ = ((size_t)7ULL);
v___x_1287_ = lean_usize_dec_le(v___x_1286_, v_x_1227_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1288_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1285_);
v___x_1289_ = lean_unsigned_to_nat(4u);
v___x_1290_ = lean_nat_dec_lt(v___x_1288_, v___x_1289_);
lean_dec(v___x_1288_);
if (v___x_1290_ == 0)
{
lean_object* v_ks_1291_; lean_object* v_vs_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_ks_1291_ = lean_ctor_get(v_newNode_1285_, 0);
lean_inc_ref(v_ks_1291_);
v_vs_1292_ = lean_ctor_get(v_newNode_1285_, 1);
lean_inc_ref(v_vs_1292_);
lean_dec_ref(v_newNode_1285_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0);
v___x_1295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_x_1227_, v_ks_1291_, v_vs_1292_, v___x_1293_, v___x_1294_);
lean_dec_ref(v_vs_1292_);
lean_dec_ref(v_ks_1291_);
return v___x_1295_;
}
else
{
return v_newNode_1285_;
}
}
else
{
return v_newNode_1285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(size_t v_depth_1298_, lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_i_1301_, lean_object* v_entries_1302_){
_start:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = lean_array_get_size(v_keys_1299_);
v___x_1304_ = lean_nat_dec_lt(v_i_1301_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_dec(v_i_1301_);
return v_entries_1302_;
}
else
{
lean_object* v_k_1305_; lean_object* v_v_1306_; size_t v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; uint64_t v___x_1310_; size_t v_h_1311_; size_t v___x_1312_; lean_object* v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; size_t v_h_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_k_1305_ = lean_array_fget_borrowed(v_keys_1299_, v_i_1301_);
v_v_1306_ = lean_array_fget_borrowed(v_vals_1300_, v_i_1301_);
v___x_1307_ = lean_ptr_addr(v_k_1305_);
v___x_1308_ = ((size_t)3ULL);
v___x_1309_ = lean_usize_shift_right(v___x_1307_, v___x_1308_);
v___x_1310_ = lean_usize_to_uint64(v___x_1309_);
v_h_1311_ = lean_uint64_to_usize(v___x_1310_);
v___x_1312_ = ((size_t)5ULL);
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_sub(v_depth_1298_, v___x_1314_);
v___x_1316_ = lean_usize_mul(v___x_1312_, v___x_1315_);
v_h_1317_ = lean_usize_shift_right(v_h_1311_, v___x_1316_);
v___x_1318_ = lean_nat_add(v_i_1301_, v___x_1313_);
lean_dec(v_i_1301_);
lean_inc(v_v_1306_);
lean_inc(v_k_1305_);
v___x_1319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_entries_1302_, v_h_1317_, v_depth_1298_, v_k_1305_, v_v_1306_);
v_i_1301_ = v___x_1318_;
v_entries_1302_ = v___x_1319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg___boxed(lean_object* v_depth_1321_, lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_i_1324_, lean_object* v_entries_1325_){
_start:
{
size_t v_depth_boxed_1326_; lean_object* v_res_1327_; 
v_depth_boxed_1326_ = lean_unbox_usize(v_depth_1321_);
lean_dec(v_depth_1321_);
v_res_1327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_boxed_1326_, v_keys_1322_, v_vals_1323_, v_i_1324_, v_entries_1325_);
lean_dec_ref(v_vals_1323_);
lean_dec_ref(v_keys_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___boxed(lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_){
_start:
{
size_t v_x_79518__boxed_1333_; size_t v_x_79519__boxed_1334_; lean_object* v_res_1335_; 
v_x_79518__boxed_1333_ = lean_unbox_usize(v_x_1329_);
lean_dec(v_x_1329_);
v_x_79519__boxed_1334_ = lean_unbox_usize(v_x_1330_);
lean_dec(v_x_1330_);
v_res_1335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1328_, v_x_79518__boxed_1333_, v_x_79519__boxed_1334_, v_x_1331_, v_x_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; uint64_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1339_ = lean_ptr_addr(v_x_1337_);
v___x_1340_ = ((size_t)3ULL);
v___x_1341_ = lean_usize_shift_right(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_usize_to_uint64(v___x_1341_);
v___x_1343_ = lean_uint64_to_usize(v___x_1342_);
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1336_, v___x_1343_, v___x_1344_, v_x_1337_, v_x_1338_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(lean_object* v_upperBound_1353_, lean_object* v___x_1354_, lean_object* v_a_1355_, lean_object* v_b_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_a_1370_; lean_object* v___y_1375_; uint8_t v___x_1394_; 
v___x_1394_ = lean_nat_dec_lt(v_a_1355_, v_upperBound_1353_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_dec(v_a_1355_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_b_1356_);
return v___x_1395_;
}
else
{
lean_object* v_snd_1396_; lean_object* v_snd_1397_; lean_object* v_fst_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1488_; 
v_snd_1396_ = lean_ctor_get(v_b_1356_, 1);
lean_inc(v_snd_1396_);
v_snd_1397_ = lean_ctor_get(v_snd_1396_, 1);
lean_inc(v_snd_1397_);
v_fst_1398_ = lean_ctor_get(v_b_1356_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_b_1356_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_b_1356_, 1);
lean_dec(v_unused_1489_);
v___x_1400_ = v_b_1356_;
v_isShared_1401_ = v_isSharedCheck_1488_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_fst_1398_);
lean_dec(v_b_1356_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1488_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_fst_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1486_; 
v_fst_1402_ = lean_ctor_get(v_snd_1396_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_snd_1396_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_snd_1396_, 1);
lean_dec(v_unused_1487_);
v___x_1404_ = v_snd_1396_;
v_isShared_1405_ = v_isSharedCheck_1486_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_fst_1402_);
lean_dec(v_snd_1396_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1486_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_fst_1406_; lean_object* v_snd_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1485_; 
v_fst_1406_ = lean_ctor_get(v_snd_1397_, 0);
v_snd_1407_ = lean_ctor_get(v_snd_1397_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_snd_1397_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1409_ = v_snd_1397_;
v_isShared_1410_ = v_isSharedCheck_1485_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_snd_1407_);
lean_inc(v_fst_1406_);
lean_dec(v_snd_1397_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1485_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1421_; lean_object* v_type_1422_; lean_object* v_value_1423_; uint8_t v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1421_ = lean_array_fget_borrowed(v___x_1354_, v_a_1355_);
v_type_1422_ = lean_ctor_get(v___x_1421_, 1);
v_value_1423_ = lean_ctor_get(v___x_1421_, 2);
lean_inc_ref(v_type_1422_);
v___x_1435_ = l_Lean_Expr_cleanupAnnotations(v_type_1422_);
v___x_1436_ = l_Lean_Expr_isApp(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v___x_1435_);
lean_del_object(v___x_1409_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1400_);
v___x_1437_ = lean_box(0);
v___x_1438_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1406_, v_snd_1407_, v_fst_1402_, v_fst_1398_, v___x_1437_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v___y_1375_ = v___x_1438_;
goto v___jp_1374_;
}
else
{
lean_object* v_arg_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_arg_1439_ = lean_ctor_get(v___x_1435_, 1);
lean_inc_ref(v_arg_1439_);
v___x_1440_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1435_);
v___x_1441_ = l_Lean_Expr_isApp(v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec_ref(v___x_1440_);
lean_dec_ref(v_arg_1439_);
lean_del_object(v___x_1409_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1400_);
v___x_1442_ = lean_box(0);
v___x_1443_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1406_, v_snd_1407_, v_fst_1402_, v_fst_1398_, v___x_1442_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v___y_1375_ = v___x_1443_;
goto v___jp_1374_;
}
else
{
lean_object* v_arg_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_arg_1444_ = lean_ctor_get(v___x_1440_, 1);
lean_inc_ref(v_arg_1444_);
v___x_1445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1440_);
v___x_1446_ = l_Lean_Expr_isApp(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v___x_1445_);
lean_dec_ref(v_arg_1444_);
lean_dec_ref(v_arg_1439_);
lean_del_object(v___x_1409_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1400_);
v___x_1447_ = lean_box(0);
v___x_1448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1406_, v_snd_1407_, v_fst_1402_, v_fst_1398_, v___x_1447_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v___y_1375_ = v___x_1448_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1445_);
v___x_1450_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__1));
v___x_1451_ = l_Lean_Expr_isConstOf(v___x_1449_, v___x_1450_);
lean_dec_ref(v___x_1449_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v_arg_1444_);
lean_dec_ref(v_arg_1439_);
lean_del_object(v___x_1409_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1400_);
v___x_1452_ = lean_box(0);
v___x_1453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1406_, v_snd_1407_, v_fst_1402_, v_fst_1398_, v___x_1452_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v___y_1375_ = v___x_1453_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v_fst_1458_; uint8_t v_snd_1459_; lean_object* v___y_1468_; 
v___x_1454_ = l_Lean_Expr_cleanupAnnotations(v_arg_1439_);
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2));
v___x_1456_ = l_Lean_Expr_isConstOf(v___x_1454_, v___x_1455_);
lean_dec_ref(v___x_1454_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v_arg_1444_);
lean_del_object(v___x_1409_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1400_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_fst_1406_);
lean_ctor_set(v___x_1472_, 1, v_snd_1407_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_fst_1402_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_fst_1398_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v_a_1370_ = v___x_1474_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
lean_inc_ref(v_arg_1444_);
v___x_1475_ = l_Lean_Expr_cleanupAnnotations(v_arg_1444_);
v___x_1476_ = l_Lean_Expr_isApp(v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref(v___x_1475_);
v___x_1477_ = lean_box(0);
v___x_1478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1444_, v___x_1477_);
v___y_1468_ = v___x_1478_;
goto v___jp_1467_;
}
else
{
lean_object* v_arg_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v_arg_1479_ = lean_ctor_get(v___x_1475_, 1);
lean_inc_ref(v_arg_1479_);
v___x_1480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1475_);
v___x_1481_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3));
v___x_1482_ = l_Lean_Expr_isConstOf(v___x_1480_, v___x_1481_);
lean_dec_ref(v___x_1480_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref(v_arg_1479_);
v___x_1483_ = lean_box(0);
v___x_1484_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1444_, v___x_1483_);
v___y_1468_ = v___x_1484_;
goto v___jp_1467_;
}
else
{
lean_dec_ref(v_arg_1444_);
v_fst_1458_ = v_arg_1479_;
v_snd_1459_ = v___x_1482_;
goto v___jp_1457_;
}
}
}
v___jp_1457_:
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_fst_1406_, v_fst_1458_);
if (v___x_1460_ == 0)
{
if (v___x_1456_ == 0)
{
lean_dec_ref(v_fst_1458_);
goto v___jp_1411_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint32_t v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
lean_del_object(v___x_1409_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1400_);
v___x_1461_ = lean_box(0);
lean_inc_ref_n(v_fst_1458_, 2);
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_fst_1406_, v_fst_1458_, v___x_1461_);
lean_inc(v_a_1355_);
v___x_1463_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_fst_1402_, v_a_1355_, v_fst_1458_);
v___x_1464_ = l_Lean_Expr_approxDepth(v_fst_1458_);
v___x_1465_ = lean_uint32_to_nat(v___x_1464_);
v___x_1466_ = lean_nat_dec_le(v_snd_1407_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v_snd_1407_);
v___y_1425_ = v_snd_1459_;
v___y_1426_ = v___x_1462_;
v___y_1427_ = v___x_1463_;
v___y_1428_ = v_fst_1458_;
v___y_1429_ = v___x_1465_;
goto v___jp_1424_;
}
else
{
lean_dec(v___x_1465_);
v___y_1425_ = v_snd_1459_;
v___y_1426_ = v___x_1462_;
v___y_1427_ = v___x_1463_;
v___y_1428_ = v_fst_1458_;
v___y_1429_ = v_snd_1407_;
goto v___jp_1424_;
}
}
}
else
{
lean_dec_ref(v_fst_1458_);
goto v___jp_1411_;
}
}
v___jp_1467_:
{
lean_object* v_fst_1469_; lean_object* v_snd_1470_; uint8_t v___x_1471_; 
v_fst_1469_ = lean_ctor_get(v___y_1468_, 0);
lean_inc(v_fst_1469_);
v_snd_1470_ = lean_ctor_get(v___y_1468_, 1);
lean_inc(v_snd_1470_);
lean_dec_ref(v___y_1468_);
v___x_1471_ = lean_unbox(v_snd_1470_);
lean_dec(v_snd_1470_);
v_fst_1458_ = v_fst_1469_;
v_snd_1459_ = v___x_1471_;
goto v___jp_1457_;
}
}
}
}
}
v___jp_1411_:
{
lean_object* v___x_1413_; 
if (v_isShared_1410_ == 0)
{
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_fst_1406_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_snd_1407_);
v___x_1413_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1413_);
v___x_1415_ = v___x_1404_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_fst_1402_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1415_);
v___x_1417_ = v___x_1400_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_fst_1398_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
v_a_1370_ = v___x_1417_;
goto v___jp_1369_;
}
}
}
}
v___jp_1424_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_inc_ref(v_value_1423_);
v___x_1430_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1430_, 0, v_value_1423_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*1, v___y_1425_);
v___x_1431_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_fst_1398_, v___y_1428_, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___y_1426_);
lean_ctor_set(v___x_1432_, 1, v___y_1429_);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1427_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1431_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v_a_1370_ = v___x_1434_;
goto v___jp_1369_;
}
}
}
}
}
v___jp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_a_1355_, v___x_1371_);
lean_dec(v_a_1355_);
v_a_1355_ = v___x_1372_;
v_b_1356_ = v_a_1370_;
goto _start;
}
v___jp_1374_:
{
if (lean_obj_tag(v___y_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1385_; 
v_a_1376_ = lean_ctor_get(v___y_1375_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___y_1375_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1378_ = v___y_1375_;
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___y_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
if (lean_obj_tag(v_a_1376_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; 
lean_dec(v_a_1355_);
v_a_1380_ = lean_ctor_get(v_a_1376_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v_a_1376_, 1);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_a_1380_);
v___x_1382_ = v___x_1378_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
else
{
lean_object* v_a_1384_; 
lean_del_object(v___x_1378_);
v_a_1384_ = lean_ctor_get(v_a_1376_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v_a_1376_, 1);
v_a_1370_ = v_a_1384_;
goto v___jp_1369_;
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_a_1355_);
v_a_1386_ = lean_ctor_get(v___y_1375_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___y_1375_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___y_1375_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___y_1375_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___boxed(lean_object* v_upperBound_1490_, lean_object* v___x_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1490_, v___x_1491_, v_a_1492_, v_b_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec_ref(v___x_1491_);
lean_dec(v_upperBound_1490_);
return v_res_1506_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1508_; lean_object* v_relevantHypsMap_1509_; 
v___x_1508_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0);
v_relevantHypsMap_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_relevantHypsMap_1509_, 0, v___x_1508_);
return v_relevantHypsMap_1509_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_unsigned_to_nat(16u);
v___x_1512_ = lean_mk_array(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_relevantHypsIdxMap_1515_; 
v___x_1513_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2);
v___x_1514_ = lean_unsigned_to_nat(0u);
v_relevantHypsIdxMap_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_relevantHypsIdxMap_1515_, 0, v___x_1514_);
lean_ctor_set(v_relevantHypsIdxMap_1515_, 1, v___x_1513_);
return v_relevantHypsIdxMap_1515_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4(void){
_start:
{
lean_object* v_minDepth_1516_; lean_object* v_relevantHypsIdxMap_1517_; lean_object* v___x_1518_; 
v_minDepth_1516_ = lean_cstr_to_nat("4294967296");
v_relevantHypsIdxMap_1517_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_relevantHypsIdxMap_1517_);
lean_ctor_set(v___x_1518_, 1, v_minDepth_1516_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1519_; lean_object* v_relevantHypsIdxMap_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4);
v_relevantHypsIdxMap_1520_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_relevantHypsIdxMap_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1522_; lean_object* v_relevantHypsMap_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5);
v_relevantHypsMap_1523_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_relevantHypsMap_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1522_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v_hypotheses_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1540_ = lean_st_ref_get(v___y_1529_);
v_hypotheses_1541_ = lean_ctor_get(v___x_1540_, 3);
lean_inc_ref(v_hypotheses_1541_);
lean_dec(v___x_1540_);
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_array_get_size(v_hypotheses_1541_);
v___x_1544_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6);
v___x_1545_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v___x_1543_, v_hypotheses_1541_, v___x_1542_, v___x_1544_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v_hypotheses_1541_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1663_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1663_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1663_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_snd_1550_; lean_object* v_snd_1551_; lean_object* v_fst_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1661_; 
v_snd_1550_ = lean_ctor_get(v_a_1546_, 1);
lean_inc(v_snd_1550_);
v_snd_1551_ = lean_ctor_get(v_snd_1550_, 1);
lean_inc(v_snd_1551_);
v_fst_1552_ = lean_ctor_get(v_a_1546_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_a_1546_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v_a_1546_, 1);
lean_dec(v_unused_1662_);
v___x_1554_ = v_a_1546_;
v_isShared_1555_ = v_isSharedCheck_1661_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_fst_1552_);
lean_dec(v_a_1546_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1661_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_fst_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1659_; 
v_fst_1556_ = lean_ctor_get(v_snd_1550_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_snd_1550_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_snd_1550_, 1);
lean_dec(v_unused_1660_);
v___x_1558_ = v_snd_1550_;
v_isShared_1559_ = v_isSharedCheck_1659_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_fst_1556_);
lean_dec(v_snd_1550_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1659_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_snd_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1657_; 
v_snd_1560_ = lean_ctor_get(v_snd_1551_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_snd_1551_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_snd_1551_, 0);
lean_dec(v_unused_1658_);
v___x_1562_ = v_snd_1551_;
v_isShared_1563_ = v_isSharedCheck_1657_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snd_1560_);
lean_dec(v_snd_1551_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1657_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v_toCold_1634_; lean_object* v_options_1635_; uint8_t v_hasTrace_1636_; 
v_toCold_1634_ = lean_ctor_get(v___y_1537_, 0);
v_options_1635_ = lean_ctor_get(v_toCold_1634_, 2);
v_hasTrace_1636_ = lean_ctor_get_uint8(v_options_1635_, sizeof(void*)*1);
if (v_hasTrace_1636_ == 0)
{
lean_del_object(v___x_1554_);
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
v___y_1571_ = v___y_1534_;
v___y_1572_ = v___y_1535_;
v___y_1573_ = v___y_1536_;
v___y_1574_ = v___y_1537_;
v___y_1575_ = v___y_1538_;
goto v___jp_1564_;
}
else
{
lean_object* v_inheritedTraceOptions_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_inheritedTraceOptions_1637_ = lean_ctor_get(v_toCold_1634_, 11);
v___x_1638_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_1639_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_1640_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1637_, v_options_1635_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_del_object(v___x_1554_);
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
v___y_1571_ = v___y_1534_;
v___y_1572_ = v___y_1535_;
v___y_1573_ = v___y_1536_;
v___y_1574_ = v___y_1537_;
v___y_1575_ = v___y_1538_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1641_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8);
lean_inc(v_snd_1560_);
v___x_1642_ = l_Nat_reprFast(v_snd_1560_);
v___x_1643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
v___x_1644_ = l_Lean_MessageData_ofFormat(v___x_1643_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 7);
lean_ctor_set(v___x_1554_, 1, v___x_1644_);
lean_ctor_set(v___x_1554_, 0, v___x_1641_);
v___x_1646_ = v___x_1554_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_1638_, v___x_1646_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_dec_ref_known(v___x_1647_, 1);
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
v___y_1571_ = v___y_1534_;
v___y_1572_ = v___y_1535_;
v___y_1573_ = v___y_1536_;
v___y_1574_ = v___y_1537_;
v___y_1575_ = v___y_1538_;
goto v___jp_1564_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_del_object(v___x_1562_);
lean_dec(v_snd_1560_);
lean_del_object(v___x_1558_);
lean_dec(v_fst_1556_);
lean_dec(v_fst_1552_);
lean_del_object(v___x_1548_);
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
v___jp_1564_:
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fst_1552_);
if (v___x_1576_ == 0)
{
lean_object* v_config_1577_; lean_object* v_maxSteps_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_del_object(v___x_1548_);
v_config_1577_ = lean_ctor_get(v___y_1565_, 0);
v_maxSteps_1578_ = lean_ctor_get(v_config_1577_, 1);
v___x_1579_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1578_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 1, v___x_1579_);
lean_ctor_set(v___x_1558_, 0, v_maxSteps_1578_);
v___x_1581_ = v___x_1558_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_maxSteps_1578_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; lean_object* v_hypotheses_1583_; lean_object* v___x_1584_; lean_object* v_newHyps_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1582_ = lean_st_ref_get(v___y_1566_);
v_hypotheses_1583_ = lean_ctor_get(v___x_1582_, 3);
lean_inc_ref(v_hypotheses_1583_);
lean_dec(v___x_1582_);
v___x_1584_ = lean_array_get_size(v_hypotheses_1583_);
v_newHyps_1585_ = lean_mk_empty_array_with_capacity(v___x_1584_);
v___x_1586_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v_newHyps_1585_);
lean_ctor_set(v___x_1562_, 0, v___x_1586_);
v___x_1588_ = v___x_1562_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_newHyps_1585_);
v___x_1588_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v___x_1584_, v_hypotheses_1583_, v_snd_1560_, v___x_1576_, v___x_1581_, v_fst_1556_, v_fst_1552_, v___x_1542_, v___x_1588_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v_fst_1556_);
lean_dec(v_snd_1560_);
lean_dec_ref(v_hypotheses_1583_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1618_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1618_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1618_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_fst_1594_; 
v_fst_1594_ = lean_ctor_get(v_a_1590_, 0);
if (lean_obj_tag(v_fst_1594_) == 0)
{
lean_object* v_snd_1595_; lean_object* v___x_1596_; lean_object* v_caches_1597_; lean_object* v_typeAnalysis_1598_; lean_object* v_target_1599_; uint8_t v_didChange_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1612_; 
v_snd_1595_ = lean_ctor_get(v_a_1590_, 1);
lean_inc(v_snd_1595_);
lean_dec(v_a_1590_);
v___x_1596_ = lean_st_ref_take(v___y_1566_);
v_caches_1597_ = lean_ctor_get(v___x_1596_, 0);
v_typeAnalysis_1598_ = lean_ctor_get(v___x_1596_, 1);
v_target_1599_ = lean_ctor_get(v___x_1596_, 2);
v_didChange_1600_ = lean_ctor_get_uint8(v___x_1596_, sizeof(void*)*4);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v___x_1596_, 3);
lean_dec(v_unused_1613_);
v___x_1602_ = v___x_1596_;
v_isShared_1603_ = v_isSharedCheck_1612_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_target_1599_);
lean_inc(v_typeAnalysis_1598_);
lean_inc(v_caches_1597_);
lean_dec(v___x_1596_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1612_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v_snd_1595_);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_caches_1597_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_typeAnalysis_1598_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_target_1599_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_snd_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1611_, sizeof(void*)*4, v_didChange_1600_);
v___x_1605_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = lean_st_ref_put(v___y_1566_, v___x_1605_);
v___x_1607_ = lean_box(v___x_1576_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1607_);
v___x_1609_ = v___x_1592_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1616_; 
lean_inc_ref(v_fst_1594_);
lean_dec(v_a_1590_);
v_val_1614_ = lean_ctor_get(v_fst_1594_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v_fst_1594_, 1);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_val_1614_);
v___x_1616_ = v___x_1592_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_val_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1589_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1589_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
else
{
uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_del_object(v___x_1562_);
lean_dec(v_snd_1560_);
lean_del_object(v___x_1558_);
lean_dec(v_fst_1556_);
lean_dec(v_fst_1552_);
v___x_1629_ = 0;
v___x_1630_ = lean_box(v___x_1629_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1630_);
v___x_1632_ = v___x_1548_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
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
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
v_a_1664_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1545_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1545_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(lean_object* v___f_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v_target_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_st_ref_get(v___y_1687_);
v_target_1699_ = lean_ctor_get(v___x_1698_, 2);
lean_inc_ref(v_target_1699_);
lean_dec(v___x_1698_);
v___x_1700_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1699_);
lean_dec_ref(v_target_1699_);
v___x_1701_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v___x_1700_, v___f_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object* v___f_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(v___f_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(lean_object* v_cls_1726_, lean_object* v_msg_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_1726_, v_msg_1727_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___boxed(lean_object* v_cls_1741_, lean_object* v_msg_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(v_cls_1741_, v_msg_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(lean_object* v_00_u03b2_1756_, lean_object* v_m_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_1757_, v_a_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object* v_00_u03b2_1760_, lean_object* v_m_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(v_00_u03b2_1760_, v_m_1761_, v_a_1762_);
lean_dec(v_a_1762_);
lean_dec_ref(v_m_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(lean_object* v_00_u03b2_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_1765_, v_x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object* v_00_u03b2_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(v_00_u03b2_1768_, v_x_1769_, v_x_1770_);
lean_dec_ref(v_x_1770_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(lean_object* v_upperBound_1772_, lean_object* v___x_1773_, lean_object* v___x_1774_, uint8_t v___x_1775_, lean_object* v___x_1776_, lean_object* v___x_1777_, lean_object* v___x_1778_, lean_object* v_inst_1779_, lean_object* v_R_1780_, lean_object* v_a_1781_, lean_object* v_b_1782_, lean_object* v_c_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_1772_, v___x_1773_, v___x_1774_, v___x_1775_, v___x_1776_, v___x_1777_, v___x_1778_, v_a_1781_, v_b_1782_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_1797_ = _args[0];
lean_object* v___x_1798_ = _args[1];
lean_object* v___x_1799_ = _args[2];
lean_object* v___x_1800_ = _args[3];
lean_object* v___x_1801_ = _args[4];
lean_object* v___x_1802_ = _args[5];
lean_object* v___x_1803_ = _args[6];
lean_object* v_inst_1804_ = _args[7];
lean_object* v_R_1805_ = _args[8];
lean_object* v_a_1806_ = _args[9];
lean_object* v_b_1807_ = _args[10];
lean_object* v_c_1808_ = _args[11];
lean_object* v___y_1809_ = _args[12];
lean_object* v___y_1810_ = _args[13];
lean_object* v___y_1811_ = _args[14];
lean_object* v___y_1812_ = _args[15];
lean_object* v___y_1813_ = _args[16];
lean_object* v___y_1814_ = _args[17];
lean_object* v___y_1815_ = _args[18];
lean_object* v___y_1816_ = _args[19];
lean_object* v___y_1817_ = _args[20];
lean_object* v___y_1818_ = _args[21];
lean_object* v___y_1819_ = _args[22];
lean_object* v___y_1820_ = _args[23];
_start:
{
uint8_t v___x_80437__boxed_1821_; lean_object* v_res_1822_; 
v___x_80437__boxed_1821_ = lean_unbox(v___x_1800_);
v_res_1822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(v_upperBound_1797_, v___x_1798_, v___x_1799_, v___x_80437__boxed_1821_, v___x_1801_, v___x_1802_, v___x_1803_, v_inst_1804_, v_R_1805_, v_a_1806_, v_b_1807_, v_c_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___x_1802_);
lean_dec(v___x_1799_);
lean_dec_ref(v___x_1798_);
lean_dec(v_upperBound_1797_);
return v_res_1822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_object* v_00_u03b2_1823_, lean_object* v_m_1824_, lean_object* v_a_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_1824_, v_a_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___boxed(lean_object* v_00_u03b2_1827_, lean_object* v_m_1828_, lean_object* v_a_1829_){
_start:
{
uint8_t v_res_1830_; lean_object* v_r_1831_; 
v_res_1830_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(v_00_u03b2_1827_, v_m_1828_, v_a_1829_);
lean_dec_ref(v_a_1829_);
lean_dec_ref(v_m_1828_);
v_r_1831_ = lean_box(v_res_1830_);
return v_r_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(lean_object* v_00_u03b2_1832_, lean_object* v_m_1833_, lean_object* v_a_1834_, lean_object* v_b_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_m_1833_, v_a_1834_, v_b_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(lean_object* v_00_u03b2_1837_, lean_object* v_m_1838_, lean_object* v_a_1839_, lean_object* v_b_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_m_1838_, v_a_1839_, v_b_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(lean_object* v_00_u03b2_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_x_1843_, v_x_1844_, v_x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(lean_object* v_upperBound_1847_, lean_object* v___x_1848_, lean_object* v_inst_1849_, lean_object* v_R_1850_, lean_object* v_a_1851_, lean_object* v_b_1852_, lean_object* v_c_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1847_, v___x_1848_, v_a_1851_, v_b_1852_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1867_ = _args[0];
lean_object* v___x_1868_ = _args[1];
lean_object* v_inst_1869_ = _args[2];
lean_object* v_R_1870_ = _args[3];
lean_object* v_a_1871_ = _args[4];
lean_object* v_b_1872_ = _args[5];
lean_object* v_c_1873_ = _args[6];
lean_object* v___y_1874_ = _args[7];
lean_object* v___y_1875_ = _args[8];
lean_object* v___y_1876_ = _args[9];
lean_object* v___y_1877_ = _args[10];
lean_object* v___y_1878_ = _args[11];
lean_object* v___y_1879_ = _args[12];
lean_object* v___y_1880_ = _args[13];
lean_object* v___y_1881_ = _args[14];
lean_object* v___y_1882_ = _args[15];
lean_object* v___y_1883_ = _args[16];
lean_object* v___y_1884_ = _args[17];
lean_object* v___y_1885_ = _args[18];
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(v_upperBound_1867_, v___x_1868_, v_inst_1869_, v_R_1870_, v_a_1871_, v_b_1872_, v_c_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec_ref(v___x_1868_);
lean_dec(v_upperBound_1867_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(lean_object* v_00_u03b2_1887_, lean_object* v_a_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_1888_, v_x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1891_, lean_object* v_a_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(v_00_u03b2_1891_, v_a_1892_, v_x_1893_);
lean_dec(v_x_1893_);
lean_dec(v_a_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_object* v_00_u03b2_1895_, lean_object* v_x_1896_, size_t v_x_1897_, lean_object* v_x_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_1896_, v_x_1897_, v_x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1900_, lean_object* v_x_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
size_t v_x_80563__boxed_1904_; lean_object* v_res_1905_; 
v_x_80563__boxed_1904_ = lean_unbox_usize(v_x_1902_);
lean_dec(v_x_1902_);
v_res_1905_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(v_00_u03b2_1900_, v_x_1901_, v_x_80563__boxed_1904_, v_x_1903_);
lean_dec_ref(v_x_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_object* v_00_u03b2_1906_, lean_object* v_a_1907_, lean_object* v_x_1908_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1907_, v_x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1910_, lean_object* v_a_1911_, lean_object* v_x_1912_){
_start:
{
uint8_t v_res_1913_; lean_object* v_r_1914_; 
v_res_1913_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(v_00_u03b2_1910_, v_a_1911_, v_x_1912_);
lean_dec(v_x_1912_);
lean_dec_ref(v_a_1911_);
v_r_1914_ = lean_box(v_res_1913_);
return v_r_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(lean_object* v_00_u03b2_1915_, lean_object* v_data_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_data_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_object* v_00_u03b2_1918_, lean_object* v_a_1919_, lean_object* v_x_1920_){
_start:
{
uint8_t v___x_1921_; 
v___x_1921_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_1919_, v_x_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___boxed(lean_object* v_00_u03b2_1922_, lean_object* v_a_1923_, lean_object* v_x_1924_){
_start:
{
uint8_t v_res_1925_; lean_object* v_r_1926_; 
v_res_1925_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(v_00_u03b2_1922_, v_a_1923_, v_x_1924_);
lean_dec(v_x_1924_);
lean_dec(v_a_1923_);
v_r_1926_ = lean_box(v_res_1925_);
return v_r_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13(lean_object* v_00_u03b2_1927_, lean_object* v_data_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_data_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14(lean_object* v_00_u03b2_1930_, lean_object* v_a_1931_, lean_object* v_b_1932_, lean_object* v_x_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1931_, v_b_1932_, v_x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(lean_object* v_00_u03b2_1935_, lean_object* v_x_1936_, size_t v_x_1937_, size_t v_x_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1936_, v_x_1937_, v_x_1938_, v_x_1939_, v_x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v_x_1947_){
_start:
{
size_t v_x_80592__boxed_1948_; size_t v_x_80593__boxed_1949_; lean_object* v_res_1950_; 
v_x_80592__boxed_1948_ = lean_unbox_usize(v_x_1944_);
lean_dec(v_x_1944_);
v_x_80593__boxed_1949_ = lean_unbox_usize(v_x_1945_);
lean_dec(v_x_1945_);
v_res_1950_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(v_00_u03b2_1942_, v_x_1943_, v_x_80592__boxed_1948_, v_x_80593__boxed_1949_, v_x_1946_, v_x_1947_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_1951_, lean_object* v_i_1952_, lean_object* v_source_1953_, lean_object* v_target_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v_i_1952_, v_source_1953_, v_target_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17(lean_object* v_00_u03b2_1956_, lean_object* v_i_1957_, lean_object* v_source_1958_, lean_object* v_target_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v_i_1957_, v_source_1958_, v_target_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21(lean_object* v_00_u03b2_1961_, lean_object* v_n_1962_, lean_object* v_k_1963_, lean_object* v_v_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v_n_1962_, v_k_1963_, v_v_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(lean_object* v_00_u03b2_1966_, size_t v_depth_1967_, lean_object* v_keys_1968_, lean_object* v_vals_1969_, lean_object* v_heq_1970_, lean_object* v_i_1971_, lean_object* v_entries_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_1967_, v_keys_1968_, v_vals_1969_, v_i_1971_, v_entries_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___boxed(lean_object* v_00_u03b2_1974_, lean_object* v_depth_1975_, lean_object* v_keys_1976_, lean_object* v_vals_1977_, lean_object* v_heq_1978_, lean_object* v_i_1979_, lean_object* v_entries_1980_){
_start:
{
size_t v_depth_boxed_1981_; lean_object* v_res_1982_; 
v_depth_boxed_1981_ = lean_unbox_usize(v_depth_1975_);
lean_dec(v_depth_1975_);
v_res_1982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(v_00_u03b2_1974_, v_depth_boxed_1981_, v_keys_1976_, v_vals_1977_, v_heq_1978_, v_i_1979_, v_entries_1980_);
lean_dec_ref(v_vals_1977_);
lean_dec_ref(v_keys_1976_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18(lean_object* v_00_u03b2_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_x_1984_, v_x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22(lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_x_1988_, v_x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26(lean_object* v_00_u03b2_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_x_1992_, v_x_1993_, v_x_1994_, v_x_1995_);
return v___x_1996_;
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

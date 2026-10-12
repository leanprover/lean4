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
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(lean_object* v_x_22_, size_t v_x_23_, lean_object* v_x_24_){
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
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_22_ = stack[0].m_obj;
size_t v_x_23_ = stack[1].m_num;
lean_object* v_x_24_ = stack[2].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_22_, v_x_23_, v_x_24_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg___boxed(lean_object* v_x_48_, lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
size_t v_x_2613__boxed_51_; lean_object* v_res_52_; 
v_x_2613__boxed_51_ = lean_unbox_usize(v_x_49_);
lean_dec(v_x_49_);
v_res_52_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_48_, v_x_2613__boxed_51_, v_x_50_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_48_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
size_t v___x_55_; size_t v___x_56_; size_t v___x_57_; uint64_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_55_ = lean_ptr_addr(v_x_54_);
v___x_56_ = ((size_t)3ULL);
v___x_57_ = lean_usize_shift_right(v___x_55_, v___x_56_);
v___x_58_ = lean_usize_to_uint64(v___x_57_);
v___x_59_ = lean_uint64_to_usize(v___x_58_);
v___x_60_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_53_, v___x_59_, v_x_54_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg___boxed(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(v_x_61_, v_x_62_);
lean_dec_ref(v_x_62_);
lean_dec_ref(v_x_61_);
return v_res_63_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_box(0);
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2));
v___x_71_ = l_Lean_mkConst(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_box(0);
v___x_85_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__9));
v___x_86_ = l_Lean_mkConst(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__12));
v___x_93_ = l_Lean_mkConst(v___x_92_, v___x_91_);
return v___x_93_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(uint32_t v_minDepth_94_, lean_object* v_hypMap_95_, lean_object* v_e_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
uint32_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = l_Lean_Expr_approxDepth(v_e_96_);
v___x_105_ = lean_uint32_dec_lt(v___x_104_, v_minDepth_94_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(v_hypMap_95_, v_e_96_);
if (lean_obj_tag(v___x_106_) == 1)
{
lean_object* v_val_107_; lean_object* v_proof_108_; uint8_t v_negated_109_; uint8_t v___x_110_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v___x_106_, 1);
v_proof_108_ = lean_ctor_get(v_val_107_, 0);
lean_inc_ref(v_proof_108_);
v_negated_109_ = lean_ctor_get_uint8(v_val_107_, sizeof(void*)*1);
lean_dec(v_val_107_);
v___x_110_ = 1;
if (v_negated_109_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec_ref(v_e_96_);
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__3);
v___x_112_ = l_Lean_Meta_Sym_shareCommonInc(v___x_111_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_121_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_121_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_117_, 0, v_a_113_);
lean_ctor_set(v___x_117_, 1, v_proof_108_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*2, v___x_110_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*2 + 1, v_negated_109_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_117_);
v___x_119_ = v___x_115_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec_ref(v_proof_108_);
v_a_122_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_112_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_112_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_object* v___x_130_; lean_object* v_proof_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__10);
v_proof_131_ = l_Lean_mkAppB(v___x_130_, v_e_96_, v_proof_108_);
v___x_132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__13);
v___x_133_ = l_Lean_Meta_Sym_shareCommonInc(v___x_132_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_142_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_142_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_142_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_138_, 0, v_a_134_);
lean_ctor_set(v___x_138_, 1, v_proof_131_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*2, v___x_110_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*2 + 1, v___x_105_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v___x_138_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v_proof_131_);
v_a_143_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_133_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v___x_106_);
lean_dec_ref(v_e_96_);
v___x_151_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_151_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_151_, 1, v___x_105_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
else
{
uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref(v_e_96_);
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_154_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_minDepth_94_ = stack[0].m_num;
lean_object* v_hypMap_95_ = stack[1].m_obj;
lean_object* v_e_96_ = stack[2].m_obj;
lean_object* v_a_97_ = stack[3].m_obj;
lean_object* v_a_98_ = stack[4].m_obj;
lean_object* v_a_99_ = stack[5].m_obj;
lean_object* v_a_100_ = stack[6].m_obj;
lean_object* v_a_101_ = stack[7].m_obj;
lean_object* v_a_102_ = stack[8].m_obj;
lean_object* v_res_156_;
v_res_156_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(v_minDepth_94_, v_hypMap_95_, v_e_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___boxed(lean_object* v_minDepth_157_, lean_object* v_hypMap_158_, lean_object* v_e_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
uint32_t v_minDepth_boxed_167_; lean_object* v_res_168_; 
v_minDepth_boxed_167_ = lean_unbox_uint32(v_minDepth_157_);
lean_dec(v_minDepth_157_);
v_res_168_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(v_minDepth_boxed_167_, v_hypMap_158_, v_e_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec_ref(v_hypMap_158_);
return v_res_168_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc(uint32_t v_minDepth_169_, lean_object* v_hypMap_170_, lean_object* v_e_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg(v_minDepth_169_, v_hypMap_170_, v_e_171_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
return v___x_182_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_0interp(lean_interpreter_value* stack)
{
uint32_t v_minDepth_169_ = stack[0].m_num;
lean_object* v_hypMap_170_ = stack[1].m_obj;
lean_object* v_e_171_ = stack[2].m_obj;
lean_object* v_a_172_ = stack[3].m_obj;
lean_object* v_a_173_ = stack[4].m_obj;
lean_object* v_a_174_ = stack[5].m_obj;
lean_object* v_a_175_ = stack[6].m_obj;
lean_object* v_a_176_ = stack[7].m_obj;
lean_object* v_a_177_ = stack[8].m_obj;
lean_object* v_a_178_ = stack[9].m_obj;
lean_object* v_a_179_ = stack[10].m_obj;
lean_object* v_a_180_ = stack[11].m_obj;
lean_object* v_res_183_;
v_res_183_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc(v_minDepth_169_, v_hypMap_170_, v_e_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed(lean_object* v_minDepth_184_, lean_object* v_hypMap_185_, lean_object* v_e_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
uint32_t v_minDepth_boxed_197_; lean_object* v_res_198_; 
v_minDepth_boxed_197_ = lean_unbox_uint32(v_minDepth_184_);
lean_dec(v_minDepth_184_);
v_res_198_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc(v_minDepth_boxed_197_, v_hypMap_185_, v_e_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_hypMap_185_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0(lean_object* v_00_u03b2_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___redArg(v_x_200_, v_x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0___boxed(lean_object* v_00_u03b2_203_, lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0(v_00_u03b2_203_, v_x_204_, v_x_205_);
lean_dec_ref(v_x_205_);
lean_dec_ref(v_x_204_);
return v_res_206_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0(lean_object* v_00_u03b2_207_, lean_object* v_x_208_, size_t v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___redArg(v_x_208_, v_x_209_, v_x_210_);
return v___x_211_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_208_ = stack[1].m_obj;
size_t v_x_209_ = stack[2].m_num;
lean_object* v_x_210_ = stack[3].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0(lean_box(0), v_x_208_, v_x_209_, v_x_210_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_213_, lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
size_t v_x_3019__boxed_217_; lean_object* v_res_218_; 
v_x_3019__boxed_217_ = lean_unbox_usize(v_x_215_);
lean_dec(v_x_215_);
v_res_218_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0(v_00_u03b2_213_, v_x_214_, v_x_3019__boxed_217_, v_x_216_);
lean_dec_ref(v_x_216_);
lean_dec_ref(v_x_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_219_, lean_object* v_keys_220_, lean_object* v_vals_221_, lean_object* v_heq_222_, lean_object* v_i_223_, lean_object* v_k_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___redArg(v_keys_220_, v_vals_221_, v_i_223_, v_k_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_226_, lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_heq_229_, lean_object* v_i_230_, lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc_spec__0_spec__0_spec__1(v_00_u03b2_226_, v_keys_227_, v_vals_228_, v_heq_229_, v_i_230_, v_k_231_);
lean_dec_ref(v_k_231_);
lean_dec_ref(v_vals_228_);
lean_dec_ref(v_keys_227_);
return v_res_232_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(lean_object* v_x_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_233_ = stack[0].m_obj;
uint8_t v_res_235_;
v_res_235_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_x_233_);
stack->m_num = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg___boxed(lean_object* v_x_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___redArg(v_x_236_);
lean_dec_ref(v_x_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(lean_object* v_00_u03b2_239_, lean_object* v_x_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_240_ = stack[1].m_obj;
uint8_t v_res_242_;
v_res_242_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(lean_box(0), v_x_240_);
stack->m_num = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0___boxed(lean_object* v_00_u03b2_243_, lean_object* v_x_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__0(v_00_u03b2_243_, v_x_244_);
lean_dec_ref(v_x_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0(lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
lean_inc(v___y_252_);
lean_inc_ref(v___y_251_);
lean_inc(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
v___x_260_ = lean_apply_12(v_x_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
return v___x_260_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_247_ = stack[0].m_obj;
lean_object* v___y_248_ = stack[1].m_obj;
lean_object* v___y_249_ = stack[2].m_obj;
lean_object* v___y_250_ = stack[3].m_obj;
lean_object* v___y_251_ = stack[4].m_obj;
lean_object* v___y_252_ = stack[5].m_obj;
lean_object* v___y_253_ = stack[6].m_obj;
lean_object* v___y_254_ = stack[7].m_obj;
lean_object* v___y_255_ = stack[8].m_obj;
lean_object* v___y_256_ = stack[9].m_obj;
lean_object* v___y_257_ = stack[10].m_obj;
lean_object* v___y_258_ = stack[11].m_obj;
lean_object* v_res_261_;
v_res_261_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0(v_x_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0___boxed(lean_object* v_x_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0(v_x_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_275_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(lean_object* v_mvarId_276_, lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___f_290_; lean_object* v___x_291_; 
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
v___f_290_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_290_, 0, v_x_277_);
lean_closure_set(v___f_290_, 1, v___y_278_);
lean_closure_set(v___f_290_, 2, v___y_279_);
lean_closure_set(v___f_290_, 3, v___y_280_);
lean_closure_set(v___f_290_, 4, v___y_281_);
lean_closure_set(v___f_290_, 5, v___y_282_);
lean_closure_set(v___f_290_, 6, v___y_283_);
lean_closure_set(v___f_290_, 7, v___y_284_);
v___x_291_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_276_, v___f_290_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_291_) == 0)
{
return v___x_291_;
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_276_ = stack[0].m_obj;
lean_object* v_x_277_ = stack[1].m_obj;
lean_object* v___y_278_ = stack[2].m_obj;
lean_object* v___y_279_ = stack[3].m_obj;
lean_object* v___y_280_ = stack[4].m_obj;
lean_object* v___y_281_ = stack[5].m_obj;
lean_object* v___y_282_ = stack[6].m_obj;
lean_object* v___y_283_ = stack[7].m_obj;
lean_object* v___y_284_ = stack[8].m_obj;
lean_object* v___y_285_ = stack[9].m_obj;
lean_object* v___y_286_ = stack[10].m_obj;
lean_object* v___y_287_ = stack[11].m_obj;
lean_object* v___y_288_ = stack[12].m_obj;
lean_object* v_res_300_;
v_res_300_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_mvarId_276_, v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg___boxed(lean_object* v_mvarId_301_, lean_object* v_x_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_mvarId_301_, v_x_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_315_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(lean_object* v_00_u03b1_316_, lean_object* v_mvarId_317_, lean_object* v_x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v_mvarId_317_, v_x_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_331_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_317_ = stack[1].m_obj;
lean_object* v_x_318_ = stack[2].m_obj;
lean_object* v___y_319_ = stack[3].m_obj;
lean_object* v___y_320_ = stack[4].m_obj;
lean_object* v___y_321_ = stack[5].m_obj;
lean_object* v___y_322_ = stack[6].m_obj;
lean_object* v___y_323_ = stack[7].m_obj;
lean_object* v___y_324_ = stack[8].m_obj;
lean_object* v___y_325_ = stack[9].m_obj;
lean_object* v___y_326_ = stack[10].m_obj;
lean_object* v___y_327_ = stack[11].m_obj;
lean_object* v___y_328_ = stack[12].m_obj;
lean_object* v___y_329_ = stack[13].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(lean_box(0), v_mvarId_317_, v_x_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___boxed(lean_object* v_00_u03b1_333_, lean_object* v_mvarId_334_, lean_object* v_x_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10(v_00_u03b1_333_, v_mvarId_334_, v_x_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_348_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(uint8_t v___x_349_, lean_object* v___f_350_, lean_object* v_____r_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_caches_365_; lean_object* v_typeAnalysis_366_; lean_object* v_target_367_; lean_object* v_hypotheses_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_378_; 
v___x_364_ = lean_st_ref_take(v___y_353_);
v_caches_365_ = lean_ctor_get(v___x_364_, 0);
v_typeAnalysis_366_ = lean_ctor_get(v___x_364_, 1);
v_target_367_ = lean_ctor_get(v___x_364_, 2);
v_hypotheses_368_ = lean_ctor_get(v___x_364_, 3);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_378_ == 0)
{
v___x_370_ = v___x_364_;
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_hypotheses_368_);
lean_inc(v_target_367_);
lean_inc(v_typeAnalysis_366_);
lean_inc(v_caches_365_);
lean_dec(v___x_364_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_box(0);
if (v_isShared_371_ == 0)
{
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_caches_365_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_typeAnalysis_366_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_target_367_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_hypotheses_368_);
v___x_374_ = v_reuseFailAlloc_377_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*4, v___x_349_);
v___x_375_ = lean_st_ref_put(v___y_353_, v___x_374_);
lean_inc(v___y_362_);
lean_inc_ref(v___y_361_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
lean_inc(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_376_ = lean_apply_13(v___f_350_, v___x_372_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, lean_box(0));
return v___x_376_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_349_ = stack[0].m_num;
lean_object* v___f_350_ = stack[1].m_obj;
lean_object* v_____r_351_ = stack[2].m_obj;
lean_object* v___y_352_ = stack[3].m_obj;
lean_object* v___y_353_ = stack[4].m_obj;
lean_object* v___y_354_ = stack[5].m_obj;
lean_object* v___y_355_ = stack[6].m_obj;
lean_object* v___y_356_ = stack[7].m_obj;
lean_object* v___y_357_ = stack[8].m_obj;
lean_object* v___y_358_ = stack[9].m_obj;
lean_object* v___y_359_ = stack[10].m_obj;
lean_object* v___y_360_ = stack[11].m_obj;
lean_object* v___y_361_ = stack[12].m_obj;
lean_object* v___y_362_ = stack[13].m_obj;
lean_object* v_res_379_;
v_res_379_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(v___x_349_, v___f_350_, v_____r_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed(lean_object* v___x_380_, lean_object* v___f_381_, lean_object* v_____r_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___x_78178__boxed_395_; lean_object* v_res_396_; 
v___x_78178__boxed_395_ = lean_unbox(v___x_380_);
v_res_396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(v___x_78178__boxed_395_, v___f_381_, v_____r_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(lean_object* v_a_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
lean_object* v_key_400_; lean_object* v_value_401_; lean_object* v_tail_402_; uint8_t v___x_403_; 
v_key_400_ = lean_ctor_get(v_x_398_, 0);
v_value_401_ = lean_ctor_get(v_x_398_, 1);
v_tail_402_ = lean_ctor_get(v_x_398_, 2);
v___x_403_ = lean_nat_dec_eq(v_key_400_, v_a_397_);
if (v___x_403_ == 0)
{
v_x_398_ = v_tail_402_;
goto _start;
}
else
{
lean_object* v___x_405_; 
lean_inc(v_value_401_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v_value_401_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg___boxed(lean_object* v_a_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_406_, v_x_407_);
lean_dec(v_x_407_);
lean_dec(v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(lean_object* v_m_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_buckets_411_; lean_object* v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v_fold_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_buckets_411_ = lean_ctor_get(v_m_409_, 1);
v___x_412_ = lean_array_get_size(v_buckets_411_);
v___x_413_ = lean_uint64_of_nat(v_a_410_);
v___x_414_ = 32ULL;
v___x_415_ = lean_uint64_shift_right(v___x_413_, v___x_414_);
v_fold_416_ = lean_uint64_xor(v___x_413_, v___x_415_);
v___x_417_ = 16ULL;
v___x_418_ = lean_uint64_shift_right(v_fold_416_, v___x_417_);
v___x_419_ = lean_uint64_xor(v_fold_416_, v___x_418_);
v___x_420_ = lean_uint64_to_usize(v___x_419_);
v___x_421_ = lean_usize_of_nat(v___x_412_);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_sub(v___x_421_, v___x_422_);
v___x_424_ = lean_usize_land(v___x_420_, v___x_423_);
v___x_425_ = lean_array_uget_borrowed(v_buckets_411_, v___x_424_);
v___x_426_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_410_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg___boxed(lean_object* v_m_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_m_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14(lean_object* v_xs_430_, lean_object* v_v_431_, lean_object* v_i_432_){
_start:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_array_get_size(v_xs_430_);
v___x_434_ = lean_nat_dec_lt(v_i_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec(v_i_432_);
v___x_435_ = lean_box(0);
return v___x_435_;
}
else
{
lean_object* v___x_436_; size_t v___x_437_; size_t v___x_438_; uint8_t v___x_439_; 
v___x_436_ = lean_array_fget_borrowed(v_xs_430_, v_i_432_);
v___x_437_ = lean_ptr_addr(v___x_436_);
v___x_438_ = lean_ptr_addr(v_v_431_);
v___x_439_ = lean_usize_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_i_432_, v___x_440_);
lean_dec(v_i_432_);
v_i_432_ = v___x_441_;
goto _start;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_i_432_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14___boxed(lean_object* v_xs_444_, lean_object* v_v_445_, lean_object* v_i_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14(v_xs_444_, v_v_445_, v_i_446_);
lean_dec_ref(v_v_445_);
lean_dec_ref(v_xs_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(lean_object* v_xs_448_, lean_object* v_v_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7_spec__14(v_xs_448_, v_v_449_, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7___boxed(lean_object* v_xs_452_, lean_object* v_v_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(v_xs_452_, v_v_453_);
lean_dec_ref(v_v_453_);
lean_dec_ref(v_xs_452_);
return v_res_454_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(lean_object* v_x_455_, size_t v_x_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v_es_458_; lean_object* v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v_j_462_; lean_object* v_entry_463_; 
v_es_458_ = lean_ctor_get(v_x_455_, 0);
v___x_459_ = lean_box(2);
v___x_460_ = ((size_t)31ULL);
v___x_461_ = lean_usize_land(v_x_456_, v___x_460_);
v_j_462_ = lean_usize_to_nat(v___x_461_);
v_entry_463_ = lean_array_get(v___x_459_, v_es_458_, v_j_462_);
switch(lean_obj_tag(v_entry_463_))
{
case 0:
{
lean_object* v_key_464_; size_t v___x_465_; size_t v___x_466_; uint8_t v___x_467_; 
v_key_464_ = lean_ctor_get(v_entry_463_, 0);
lean_inc(v_key_464_);
lean_dec_ref_known(v_entry_463_, 2);
v___x_465_ = lean_ptr_addr(v_x_457_);
v___x_466_ = lean_ptr_addr(v_key_464_);
lean_dec(v_key_464_);
v___x_467_ = lean_usize_dec_eq(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_dec(v_j_462_);
return v_x_455_;
}
else
{
lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
lean_inc_ref(v_es_458_);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v_x_455_, 0);
lean_dec(v_unused_476_);
v___x_469_ = v_x_455_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_dec(v_x_455_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_array_set(v_es_458_, v_j_462_, v___x_459_);
lean_dec(v_j_462_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
case 1:
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_511_; 
lean_inc_ref(v_es_458_);
v_isSharedCheck_511_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v_x_455_, 0);
lean_dec(v_unused_512_);
v___x_478_ = v_x_455_;
v_isShared_479_ = v_isSharedCheck_511_;
goto v_resetjp_477_;
}
else
{
lean_dec(v_x_455_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_511_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_node_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_510_; 
v_node_480_ = lean_ctor_get(v_entry_463_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_entry_463_);
if (v_isSharedCheck_510_ == 0)
{
v___x_482_ = v_entry_463_;
v_isShared_483_ = v_isSharedCheck_510_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_node_480_);
lean_dec(v_entry_463_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_510_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
size_t v___x_484_; lean_object* v_entries_485_; size_t v___x_486_; lean_object* v_newNode_487_; lean_object* v___x_488_; 
v___x_484_ = ((size_t)5ULL);
v_entries_485_ = lean_array_set(v_es_458_, v_j_462_, v___x_459_);
v___x_486_ = lean_usize_shift_right(v_x_456_, v___x_484_);
v_newNode_487_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_node_480_, v___x_486_, v_x_457_);
lean_inc_ref(v_newNode_487_);
v___x_488_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_490_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v_newNode_487_);
v___x_490_ = v___x_482_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_newNode_487_);
v___x_490_ = v_reuseFailAlloc_495_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_array_set(v_entries_485_, v_j_462_, v___x_490_);
lean_dec(v_j_462_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_491_);
v___x_493_ = v___x_478_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v_val_496_; lean_object* v_fst_497_; lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v_newNode_487_);
lean_del_object(v___x_482_);
v_val_496_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v___x_488_, 1);
v_fst_497_ = lean_ctor_get(v_val_496_, 0);
v_snd_498_ = lean_ctor_get(v_val_496_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_val_496_);
if (v_isSharedCheck_509_ == 0)
{
v___x_500_ = v_val_496_;
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_inc(v_fst_497_);
lean_dec(v_val_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_509_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_fst_497_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_snd_498_);
v___x_503_ = v_reuseFailAlloc_508_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_array_set(v_entries_485_, v_j_462_, v___x_503_);
lean_dec(v_j_462_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_504_);
v___x_506_ = v___x_478_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_462_);
return v_x_455_;
}
}
}
else
{
lean_object* v_ks_513_; lean_object* v_vs_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_528_; 
v_ks_513_ = lean_ctor_get(v_x_455_, 0);
v_vs_514_ = lean_ctor_get(v_x_455_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_528_ == 0)
{
v___x_516_ = v_x_455_;
v_isShared_517_ = v_isSharedCheck_528_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_vs_514_);
lean_inc(v_ks_513_);
lean_dec(v_x_455_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_528_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_spec__7(v_ks_513_, v_x_457_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v___x_520_; 
if (v_isShared_517_ == 0)
{
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_ks_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_vs_514_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_object* v_val_522_; lean_object* v_keys_x27_523_; lean_object* v_vals_x27_524_; lean_object* v___x_526_; 
v_val_522_ = lean_ctor_get(v___x_518_, 0);
lean_inc_n(v_val_522_, 2);
lean_dec_ref_known(v___x_518_, 1);
v_keys_x27_523_ = l_Array_eraseIdx___redArg(v_ks_513_, v_val_522_);
v_vals_x27_524_ = l_Array_eraseIdx___redArg(v_vs_514_, v_val_522_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_vals_x27_524_);
lean_ctor_set(v___x_516_, 0, v_keys_x27_523_);
v___x_526_ = v___x_516_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_keys_x27_523_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_vals_x27_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_455_ = stack[0].m_obj;
size_t v_x_456_ = stack[1].m_num;
lean_object* v_x_457_ = stack[2].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_455_, v_x_456_, v_x_457_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg___boxed(lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
size_t v_x_78398__boxed_533_; lean_object* v_res_534_; 
v_x_78398__boxed_533_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_534_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_530_, v_x_78398__boxed_533_, v_x_532_);
lean_dec_ref(v_x_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; uint64_t v___x_540_; size_t v_h_541_; lean_object* v___x_542_; 
v___x_537_ = lean_ptr_addr(v_x_536_);
v___x_538_ = ((size_t)3ULL);
v___x_539_ = lean_usize_shift_right(v___x_537_, v___x_538_);
v___x_540_ = lean_usize_to_uint64(v___x_539_);
v_h_541_ = lean_uint64_to_usize(v___x_540_);
v___x_542_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_535_, v_h_541_, v_x_536_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg___boxed(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_543_, v_x_544_);
lean_dec_ref(v_x_544_);
return v_res_545_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(uint8_t v___x_546_, lean_object* v_x_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_558_, 0, v___x_546_);
lean_ctor_set_uint8(v___x_558_, 1, v___x_546_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_546_ = stack[0].m_num;
lean_object* v_x_547_ = stack[1].m_obj;
lean_object* v___y_548_ = stack[2].m_obj;
lean_object* v___y_549_ = stack[3].m_obj;
lean_object* v___y_550_ = stack[4].m_obj;
lean_object* v___y_551_ = stack[5].m_obj;
lean_object* v___y_552_ = stack[6].m_obj;
lean_object* v___y_553_ = stack[7].m_obj;
lean_object* v___y_554_ = stack[8].m_obj;
lean_object* v___y_555_ = stack[9].m_obj;
lean_object* v___y_556_ = stack[10].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(v___x_546_, v_x_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed(lean_object* v___x_561_, lean_object* v_x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v___x_78633__boxed_573_; lean_object* v_res_574_; 
v___x_78633__boxed_573_ = lean_unbox(v___x_561_);
v_res_574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(v___x_78633__boxed_573_, v_x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v_x_562_);
return v_res_574_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(lean_object* v_snd_575_, lean_object* v_a_576_, lean_object* v___x_577_, lean_object* v_____r_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_array_push(v_snd_575_, v_a_576_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_577_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_575_ = stack[0].m_obj;
lean_object* v_a_576_ = stack[1].m_obj;
lean_object* v___x_577_ = stack[2].m_obj;
lean_object* v_____r_578_ = stack[3].m_obj;
lean_object* v___y_579_ = stack[4].m_obj;
lean_object* v___y_580_ = stack[5].m_obj;
lean_object* v___y_581_ = stack[6].m_obj;
lean_object* v___y_582_ = stack[7].m_obj;
lean_object* v___y_583_ = stack[8].m_obj;
lean_object* v___y_584_ = stack[9].m_obj;
lean_object* v___y_585_ = stack[10].m_obj;
lean_object* v___y_586_ = stack[11].m_obj;
lean_object* v___y_587_ = stack[12].m_obj;
lean_object* v___y_588_ = stack[13].m_obj;
lean_object* v___y_589_ = stack[14].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_575_, v_a_576_, v___x_577_, v_____r_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed(lean_object* v_snd_596_, lean_object* v_a_597_, lean_object* v___x_598_, lean_object* v_____r_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_596_, v_a_597_, v___x_598_, v_____r_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_612_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(lean_object* v_msgData_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; lean_object* v_env_620_; uint8_t v___x_621_; lean_object* v_env_622_; lean_object* v___x_623_; lean_object* v_toCold_624_; lean_object* v_mctx_625_; lean_object* v_lctx_626_; lean_object* v_options_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_619_ = lean_st_ref_get(v___y_617_);
v_env_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_619_);
v___x_621_ = 0;
v_env_622_ = l_Lean_Environment_setRecordingDeps(v_env_620_, v___x_621_);
v___x_623_ = lean_st_ref_get(v___y_615_);
v_toCold_624_ = lean_ctor_get(v___y_616_, 0);
v_mctx_625_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_mctx_625_);
lean_dec(v___x_623_);
v_lctx_626_ = lean_ctor_get(v___y_614_, 2);
v_options_627_ = lean_ctor_get(v_toCold_624_, 2);
lean_inc_ref(v_options_627_);
lean_inc_ref(v_lctx_626_);
v___x_628_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_628_, 0, v_env_622_);
lean_ctor_set(v___x_628_, 1, v_mctx_625_);
lean_ctor_set(v___x_628_, 2, v_lctx_626_);
lean_ctor_set(v___x_628_, 3, v_options_627_);
v___x_629_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_msgData_613_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_613_ = stack[0].m_obj;
lean_object* v___y_614_ = stack[1].m_obj;
lean_object* v___y_615_ = stack[2].m_obj;
lean_object* v___y_616_ = stack[3].m_obj;
lean_object* v___y_617_ = stack[4].m_obj;
lean_object* v_res_631_;
v_res_631_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msgData_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
stack->m_obj
 = v_res_631_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1___boxed(lean_object* v_msgData_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msgData_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_638_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_639_; double v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_float_of_nat(v___x_639_);
return v___x_640_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(lean_object* v_cls_644_, lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_ref_651_; lean_object* v___x_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_698_; 
v_ref_651_ = lean_ctor_get(v___y_648_, 2);
v___x_652_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_698_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_698_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_698_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v_traceState_658_; lean_object* v_env_659_; lean_object* v_nextMacroScope_660_; lean_object* v_ngen_661_; lean_object* v_auxDeclNGen_662_; lean_object* v_cache_663_; lean_object* v_recordedDeps_664_; lean_object* v_messages_665_; lean_object* v_infoState_666_; lean_object* v_snapshotTasks_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_697_; 
v___x_657_ = lean_st_ref_take(v___y_649_);
v_traceState_658_ = lean_ctor_get(v___x_657_, 4);
v_env_659_ = lean_ctor_get(v___x_657_, 0);
v_nextMacroScope_660_ = lean_ctor_get(v___x_657_, 1);
v_ngen_661_ = lean_ctor_get(v___x_657_, 2);
v_auxDeclNGen_662_ = lean_ctor_get(v___x_657_, 3);
v_cache_663_ = lean_ctor_get(v___x_657_, 5);
v_recordedDeps_664_ = lean_ctor_get(v___x_657_, 6);
v_messages_665_ = lean_ctor_get(v___x_657_, 7);
v_infoState_666_ = lean_ctor_get(v___x_657_, 8);
v_snapshotTasks_667_ = lean_ctor_get(v___x_657_, 9);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_697_ == 0)
{
v___x_669_ = v___x_657_;
v_isShared_670_ = v_isSharedCheck_697_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snapshotTasks_667_);
lean_inc(v_infoState_666_);
lean_inc(v_messages_665_);
lean_inc(v_recordedDeps_664_);
lean_inc(v_cache_663_);
lean_inc(v_traceState_658_);
lean_inc(v_auxDeclNGen_662_);
lean_inc(v_ngen_661_);
lean_inc(v_nextMacroScope_660_);
lean_inc(v_env_659_);
lean_dec(v___x_657_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_697_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
uint64_t v_tid_671_; lean_object* v_traces_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_696_; 
v_tid_671_ = lean_ctor_get_uint64(v_traceState_658_, sizeof(void*)*1);
v_traces_672_ = lean_ctor_get(v_traceState_658_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v_traceState_658_);
if (v_isSharedCheck_696_ == 0)
{
v___x_674_ = v_traceState_658_;
v_isShared_675_ = v_isSharedCheck_696_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_traces_672_);
lean_dec(v_traceState_658_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_696_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; double v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_box(0);
v___x_678_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0);
v___x_679_ = 0;
v___x_680_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1));
v___x_681_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_681_, 0, v_cls_644_);
lean_ctor_set(v___x_681_, 1, v___x_677_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
lean_ctor_set_float(v___x_681_, sizeof(void*)*3, v___x_678_);
lean_ctor_set_float(v___x_681_, sizeof(void*)*3 + 8, v___x_678_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*3 + 16, v___x_679_);
v___x_682_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2));
v___x_683_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v_a_653_);
lean_ctor_set(v___x_683_, 2, v___x_682_);
lean_inc(v_ref_651_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_ref_651_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_PersistentArray_push___redArg(v_traces_672_, v___x_684_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_685_);
v___x_687_ = v___x_674_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_685_);
lean_ctor_set_uint64(v_reuseFailAlloc_695_, sizeof(void*)*1, v_tid_671_);
v___x_687_ = v_reuseFailAlloc_695_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v___x_687_);
v___x_689_ = v___x_669_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_env_659_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_nextMacroScope_660_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_ngen_661_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_auxDeclNGen_662_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v_cache_663_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_recordedDeps_664_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v_messages_665_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_infoState_666_);
lean_ctor_set(v_reuseFailAlloc_694_, 9, v_snapshotTasks_667_);
v___x_689_ = v_reuseFailAlloc_694_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_st_ref_put(v___y_649_, v___x_689_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_676_);
v___x_692_ = v___x_655_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_676_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_644_ = stack[0].m_obj;
lean_object* v_msg_645_ = stack[1].m_obj;
lean_object* v___y_646_ = stack[2].m_obj;
lean_object* v___y_647_ = stack[3].m_obj;
lean_object* v___y_648_ = stack[4].m_obj;
lean_object* v___y_649_ = stack[5].m_obj;
lean_object* v_res_699_;
v_res_699_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_644_, v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___boxed(lean_object* v_cls_700_, lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_700_, v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_718_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4));
v___x_719_ = l_Lean_Name_append(v___x_718_, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6));
v___x_722_ = l_Lean_stringToMessageData(v___x_721_);
return v___x_722_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(lean_object* v_upperBound_723_, lean_object* v___x_724_, lean_object* v___x_725_, uint8_t v___x_726_, lean_object* v___x_727_, lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v_a_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___y_745_; lean_object* v___y_768_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; uint8_t v___x_798_; 
v___x_798_ = lean_nat_dec_lt(v_a_730_, v_upperBound_723_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec(v_a_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_b_731_);
return v___x_799_;
}
else
{
lean_object* v_snd_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_870_; 
v_snd_800_ = lean_ctor_get(v_b_731_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_b_731_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_b_731_, 0);
lean_dec(v_unused_871_);
v___x_802_ = v_b_731_;
v_isShared_803_ = v_isSharedCheck_870_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_snd_800_);
lean_dec(v_b_731_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_870_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___y_809_; lean_object* v___x_867_; 
v___x_804_ = lean_box(v___x_726_);
v___f_805_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_805_, 0, v___x_804_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_array_fget_borrowed(v___x_724_, v_a_730_);
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v___x_728_, v_a_730_);
if (lean_obj_tag(v___x_867_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_869_; 
v_val_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v___x_867_, 1);
lean_inc_ref(v___x_729_);
v___x_869_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v___x_729_, v_val_868_);
lean_dec(v_val_868_);
v___y_809_ = v___x_869_;
goto v___jp_808_;
}
else
{
lean_dec(v___x_867_);
lean_inc_ref(v___x_729_);
v___y_809_ = v___x_729_;
goto v___jp_808_;
}
v___jp_808_:
{
lean_object* v_type_810_; uint32_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_type_810_ = lean_ctor_get(v___x_807_, 1);
v___x_811_ = lean_uint32_of_nat(v___x_725_);
v___x_812_ = lean_box_uint32(v___x_811_);
v___x_813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed), 13, 2);
lean_closure_set(v___x_813_, 0, v___x_812_);
lean_closure_set(v___x_813_, 1, v___y_809_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___f_805_);
lean_inc_ref(v_type_810_);
v___x_815_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_815_, 0, v_type_810_);
lean_inc_ref(v___x_727_);
v___x_816_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_815_, v___x_814_, v___x_727_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
lean_inc(v___x_807_);
v___x_818_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_807_, v_a_817_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_type_820_; lean_object* v_value_821_; uint8_t v___x_822_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v_type_820_ = lean_ctor_get(v_a_819_, 1);
v_value_821_ = lean_ctor_get(v_a_819_, 2);
lean_inc_ref(v_type_820_);
v___x_822_ = l_Lean_Expr_isFalse(v_type_820_);
if (v___x_822_ == 0)
{
lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___f_825_; uint8_t v___x_826_; 
lean_del_object(v___x_802_);
lean_inc(v_a_819_);
lean_inc(v_snd_800_);
v___f_823_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_823_, 0, v_snd_800_);
lean_closure_set(v___f_823_, 1, v_a_819_);
lean_closure_set(v___f_823_, 2, v___x_806_);
v___x_824_ = lean_box(v___x_798_);
v___f_825_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed), 15, 2);
lean_closure_set(v___f_825_, 0, v___x_824_);
lean_closure_set(v___f_825_, 1, v___f_823_);
v___x_826_ = lean_expr_eqv(v_type_810_, v_type_820_);
if (v___x_826_ == 0)
{
lean_inc_ref(v_type_820_);
lean_dec(v_a_819_);
lean_dec(v_snd_800_);
lean_inc_ref(v_type_810_);
v___y_772_ = v___f_825_;
v___y_773_ = v_type_810_;
v___y_774_ = v_type_820_;
goto v___jp_771_;
}
else
{
if (v___x_822_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref(v___f_825_);
v___x_827_ = lean_box(0);
v___x_828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_800_, v_a_819_, v___x_806_, v___x_827_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
v___y_745_ = v___x_828_;
goto v___jp_744_;
}
else
{
lean_inc_ref(v_type_820_);
lean_dec(v_a_819_);
lean_dec(v_snd_800_);
lean_inc_ref(v_type_810_);
v___y_772_ = v___f_825_;
v___y_773_ = v_type_810_;
v___y_774_ = v_type_820_;
goto v___jp_771_;
}
}
}
else
{
lean_object* v___x_829_; 
lean_inc_ref(v_value_821_);
lean_dec(v_a_819_);
lean_dec(v_a_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v___x_829_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_821_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_841_; 
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_829_, 0);
lean_dec(v_unused_842_);
v___x_831_ = v___x_829_;
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___x_829_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_833_ = lean_box(v___x_798_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_834_);
v___x_836_ = v___x_802_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_snd_800_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_838_ = v___x_831_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_del_object(v___x_802_);
lean_dec(v_snd_800_);
v_a_843_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_829_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_829_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_del_object(v___x_802_);
lean_dec(v_snd_800_);
lean_dec(v_a_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v_a_851_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_818_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_818_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
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
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_del_object(v___x_802_);
lean_dec(v_snd_800_);
lean_dec(v_a_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v_a_859_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_816_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_816_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
v___jp_744_:
{
if (lean_obj_tag(v___y_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_758_; 
v_a_746_ = lean_ctor_get(v___y_745_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___y_745_);
if (v_isSharedCheck_758_ == 0)
{
v___x_748_ = v___y_745_;
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___y_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_758_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
if (lean_obj_tag(v_a_746_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; 
lean_dec(v_a_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v_a_750_ = lean_ctor_get(v_a_746_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v_a_746_, 1);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v_a_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_del_object(v___x_748_);
v_a_754_ = lean_ctor_get(v_a_746_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v_a_746_, 1);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_a_730_, v___x_755_);
lean_dec(v_a_730_);
v_a_730_ = v___x_756_;
v_b_731_ = v_a_754_;
goto _start;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v_a_759_ = lean_ctor_get(v___y_745_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___y_745_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___y_745_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___y_745_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_box(0);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
v___x_770_ = lean_apply_13(v___y_768_, v___x_769_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, lean_box(0));
v___y_745_ = v___x_770_;
goto v___jp_744_;
}
v___jp_771_:
{
lean_object* v_toCold_775_; lean_object* v_options_776_; uint8_t v_hasTrace_777_; 
v_toCold_775_ = lean_ctor_get(v___y_741_, 0);
v_options_776_ = lean_ctor_get(v_toCold_775_, 2);
v_hasTrace_777_ = lean_ctor_get_uint8(v_options_776_, sizeof(void*)*1);
if (v_hasTrace_777_ == 0)
{
lean_dec_ref(v___y_774_);
lean_dec_ref(v___y_773_);
v___y_768_ = v___y_772_;
goto v___jp_767_;
}
else
{
lean_object* v_inheritedTraceOptions_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_inheritedTraceOptions_778_ = lean_ctor_get(v_toCold_775_, 11);
v___x_779_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_780_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_778_, v_options_776_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec_ref(v___y_774_);
lean_dec_ref(v___y_773_);
v___y_768_ = v___y_772_;
goto v___jp_767_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = l_Lean_MessageData_ofExpr(v___y_773_);
v___x_783_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_MessageData_ofExpr(v___y_774_);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_779_, v___x_786_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
v___x_789_ = lean_apply_13(v___y_772_, v_a_788_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, lean_box(0));
v___y_745_ = v___x_789_;
goto v___jp_744_;
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v___y_772_);
lean_dec(v_a_730_);
lean_dec_ref(v___x_729_);
lean_dec_ref(v___x_727_);
v_a_790_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_787_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_787_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_723_ = stack[0].m_obj;
lean_object* v___x_724_ = stack[1].m_obj;
lean_object* v___x_725_ = stack[2].m_obj;
uint8_t v___x_726_ = stack[3].m_num;
lean_object* v___x_727_ = stack[4].m_obj;
lean_object* v___x_728_ = stack[5].m_obj;
lean_object* v___x_729_ = stack[6].m_obj;
lean_object* v_a_730_ = stack[7].m_obj;
lean_object* v_b_731_ = stack[8].m_obj;
lean_object* v___y_732_ = stack[9].m_obj;
lean_object* v___y_733_ = stack[10].m_obj;
lean_object* v___y_734_ = stack[11].m_obj;
lean_object* v___y_735_ = stack[12].m_obj;
lean_object* v___y_736_ = stack[13].m_obj;
lean_object* v___y_737_ = stack[14].m_obj;
lean_object* v___y_738_ = stack[15].m_obj;
lean_object* v___y_739_ = stack[16].m_obj;
lean_object* v___y_740_ = stack[17].m_obj;
lean_object* v___y_741_ = stack[18].m_obj;
lean_object* v___y_742_ = stack[19].m_obj;
lean_object* v_res_872_;
v_res_872_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_723_, v___x_724_, v___x_725_, v___x_726_, v___x_727_, v___x_728_, v___x_729_, v_a_730_, v_b_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_873_ = _args[0];
lean_object* v___x_874_ = _args[1];
lean_object* v___x_875_ = _args[2];
lean_object* v___x_876_ = _args[3];
lean_object* v___x_877_ = _args[4];
lean_object* v___x_878_ = _args[5];
lean_object* v___x_879_ = _args[6];
lean_object* v_a_880_ = _args[7];
lean_object* v_b_881_ = _args[8];
lean_object* v___y_882_ = _args[9];
lean_object* v___y_883_ = _args[10];
lean_object* v___y_884_ = _args[11];
lean_object* v___y_885_ = _args[12];
lean_object* v___y_886_ = _args[13];
lean_object* v___y_887_ = _args[14];
lean_object* v___y_888_ = _args[15];
lean_object* v___y_889_ = _args[16];
lean_object* v___y_890_ = _args[17];
lean_object* v___y_891_ = _args[18];
lean_object* v___y_892_ = _args[19];
lean_object* v___y_893_ = _args[20];
_start:
{
uint8_t v___x_79014__boxed_894_; lean_object* v_res_895_; 
v___x_79014__boxed_894_ = lean_unbox(v___x_876_);
v_res_895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_873_, v___x_874_, v___x_875_, v___x_79014__boxed_894_, v___x_877_, v___x_878_, v___x_879_, v_a_880_, v_b_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec_ref(v___x_878_);
lean_dec(v___x_875_);
lean_dec_ref(v___x_874_);
lean_dec(v_upperBound_873_);
return v_res_895_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(lean_object* v_a_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
uint8_t v___x_898_; 
v___x_898_ = 0;
return v___x_898_;
}
else
{
lean_object* v_key_899_; lean_object* v_tail_900_; size_t v___x_901_; size_t v___x_902_; uint8_t v___x_903_; 
v_key_899_ = lean_ctor_get(v_x_897_, 0);
v_tail_900_ = lean_ctor_get(v_x_897_, 2);
v___x_901_ = lean_ptr_addr(v_key_899_);
v___x_902_ = lean_ptr_addr(v_a_896_);
v___x_903_ = lean_usize_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
v_x_897_ = v_tail_900_;
goto _start;
}
else
{
return v___x_903_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_896_ = stack[0].m_obj;
lean_object* v_x_897_ = stack[1].m_obj;
uint8_t v_res_905_;
v_res_905_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_896_, v_x_897_);
stack->m_num = v_res_905_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___boxed(lean_object* v_a_906_, lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_906_, v_x_907_);
lean_dec(v_x_907_);
lean_dec_ref(v_a_906_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(lean_object* v_m_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_buckets_912_; lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; uint64_t v_fold_920_; uint64_t v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_buckets_912_ = lean_ctor_get(v_m_910_, 1);
v___x_913_ = lean_array_get_size(v_buckets_912_);
v___x_914_ = lean_ptr_addr(v_a_911_);
v___x_915_ = ((size_t)3ULL);
v___x_916_ = lean_usize_shift_right(v___x_914_, v___x_915_);
v___x_917_ = lean_usize_to_uint64(v___x_916_);
v___x_918_ = 32ULL;
v___x_919_ = lean_uint64_shift_right(v___x_917_, v___x_918_);
v_fold_920_ = lean_uint64_xor(v___x_917_, v___x_919_);
v___x_921_ = 16ULL;
v___x_922_ = lean_uint64_shift_right(v_fold_920_, v___x_921_);
v___x_923_ = lean_uint64_xor(v_fold_920_, v___x_922_);
v___x_924_ = lean_uint64_to_usize(v___x_923_);
v___x_925_ = lean_usize_of_nat(v___x_913_);
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_sub(v___x_925_, v___x_926_);
v___x_928_ = lean_usize_land(v___x_924_, v___x_927_);
v___x_929_ = lean_array_uget_borrowed(v_buckets_912_, v___x_928_);
v___x_930_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_911_, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_910_ = stack[0].m_obj;
lean_object* v_a_911_ = stack[1].m_obj;
uint8_t v_res_931_;
v_res_931_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_910_, v_a_911_);
stack->m_num = v_res_931_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg___boxed(lean_object* v_m_932_, lean_object* v_a_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_932_, v_a_933_);
lean_dec_ref(v_a_933_);
lean_dec_ref(v_m_932_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(lean_object* v_arg_936_, lean_object* v_x_937_){
_start:
{
uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = 0;
v___x_939_ = lean_box(v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_arg_936_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
return v_x_941_;
}
else
{
lean_object* v_key_943_; lean_object* v_value_944_; lean_object* v_tail_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_968_; 
v_key_943_ = lean_ctor_get(v_x_942_, 0);
v_value_944_ = lean_ctor_get(v_x_942_, 1);
v_tail_945_ = lean_ctor_get(v_x_942_, 2);
v_isSharedCheck_968_ = !lean_is_exclusive(v_x_942_);
if (v_isSharedCheck_968_ == 0)
{
v___x_947_ = v_x_942_;
v_isShared_948_ = v_isSharedCheck_968_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_tail_945_);
lean_inc(v_value_944_);
lean_inc(v_key_943_);
lean_dec(v_x_942_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_968_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v_fold_953_; uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v___x_956_; size_t v___x_957_; size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_949_ = lean_array_get_size(v_x_941_);
v___x_950_ = lean_uint64_of_nat(v_key_943_);
v___x_951_ = 32ULL;
v___x_952_ = lean_uint64_shift_right(v___x_950_, v___x_951_);
v_fold_953_ = lean_uint64_xor(v___x_950_, v___x_952_);
v___x_954_ = 16ULL;
v___x_955_ = lean_uint64_shift_right(v_fold_953_, v___x_954_);
v___x_956_ = lean_uint64_xor(v_fold_953_, v___x_955_);
v___x_957_ = lean_uint64_to_usize(v___x_956_);
v___x_958_ = lean_usize_of_nat(v___x_949_);
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_sub(v___x_958_, v___x_959_);
v___x_961_ = lean_usize_land(v___x_957_, v___x_960_);
v___x_962_ = lean_array_uget_borrowed(v_x_941_, v___x_961_);
lean_inc(v___x_962_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 2, v___x_962_);
v___x_964_ = v___x_947_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_key_943_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_value_944_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v___x_962_);
v___x_964_ = v_reuseFailAlloc_967_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_array_uset(v_x_941_, v___x_961_, v___x_964_);
v_x_941_ = v___x_965_;
v_x_942_ = v_tail_945_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(lean_object* v_i_969_, lean_object* v_source_970_, lean_object* v_target_971_){
_start:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_array_get_size(v_source_970_);
v___x_973_ = lean_nat_dec_lt(v_i_969_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec_ref(v_source_970_);
lean_dec(v_i_969_);
return v_target_971_;
}
else
{
lean_object* v_es_974_; lean_object* v___x_975_; lean_object* v_source_976_; lean_object* v_target_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_es_974_ = lean_array_fget(v_source_970_, v_i_969_);
v___x_975_ = lean_box(0);
v_source_976_ = lean_array_fset(v_source_970_, v_i_969_, v___x_975_);
v_target_977_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_target_971_, v_es_974_);
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = lean_nat_add(v_i_969_, v___x_978_);
lean_dec(v_i_969_);
v_i_969_ = v___x_979_;
v_source_970_ = v_source_976_;
v_target_971_ = v_target_977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(lean_object* v_data_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_nbuckets_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_982_ = lean_array_get_size(v_data_981_);
v___x_983_ = lean_unsigned_to_nat(2u);
v_nbuckets_984_ = lean_nat_mul(v___x_982_, v___x_983_);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_box(0);
v___x_987_ = lean_mk_array(v_nbuckets_984_, v___x_986_);
v___x_988_ = lean_array_propagate_mark(v_data_981_, v___x_987_);
v___x_989_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v___x_985_, v_data_981_, v___x_988_);
return v___x_989_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(lean_object* v_a_990_, lean_object* v_x_991_){
_start:
{
if (lean_obj_tag(v_x_991_) == 0)
{
uint8_t v___x_992_; 
v___x_992_ = 0;
return v___x_992_;
}
else
{
lean_object* v_key_993_; lean_object* v_tail_994_; uint8_t v___x_995_; 
v_key_993_ = lean_ctor_get(v_x_991_, 0);
v_tail_994_ = lean_ctor_get(v_x_991_, 2);
v___x_995_ = lean_nat_dec_eq(v_key_993_, v_a_990_);
if (v___x_995_ == 0)
{
v_x_991_ = v_tail_994_;
goto _start;
}
else
{
return v___x_995_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_990_ = stack[0].m_obj;
lean_object* v_x_991_ = stack[1].m_obj;
uint8_t v_res_997_;
v_res_997_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_990_, v_x_991_);
stack->m_num = v_res_997_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg___boxed(lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_res_1000_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec(v_a_998_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(lean_object* v_a_1002_, lean_object* v_b_1003_, lean_object* v_x_1004_){
_start:
{
if (lean_obj_tag(v_x_1004_) == 0)
{
lean_dec(v_b_1003_);
lean_dec(v_a_1002_);
return v_x_1004_;
}
else
{
lean_object* v_key_1005_; lean_object* v_value_1006_; lean_object* v_tail_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1019_; 
v_key_1005_ = lean_ctor_get(v_x_1004_, 0);
v_value_1006_ = lean_ctor_get(v_x_1004_, 1);
v_tail_1007_ = lean_ctor_get(v_x_1004_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_1004_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1009_ = v_x_1004_;
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_tail_1007_);
lean_inc(v_value_1006_);
lean_inc(v_key_1005_);
lean_dec(v_x_1004_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_nat_dec_eq(v_key_1005_, v_a_1002_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1002_, v_b_1003_, v_tail_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 2, v___x_1012_);
v___x_1014_ = v___x_1009_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_key_1005_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_value_1006_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v___x_1017_; 
lean_dec(v_value_1006_);
lean_dec(v_key_1005_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v_b_1003_);
lean_ctor_set(v___x_1009_, 0, v_a_1002_);
v___x_1017_ = v___x_1009_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1002_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_b_1003_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_tail_1007_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(lean_object* v_m_1020_, lean_object* v_a_1021_, lean_object* v_b_1022_){
_start:
{
lean_object* v_size_1023_; lean_object* v_buckets_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1067_; 
v_size_1023_ = lean_ctor_get(v_m_1020_, 0);
v_buckets_1024_ = lean_ctor_get(v_m_1020_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_m_1020_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1026_ = v_m_1020_;
v_isShared_1027_ = v_isSharedCheck_1067_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_buckets_1024_);
lean_inc(v_size_1023_);
lean_dec(v_m_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1067_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v_fold_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v_bkt_1041_; uint8_t v___x_1042_; 
v___x_1028_ = lean_array_get_size(v_buckets_1024_);
v___x_1029_ = lean_uint64_of_nat(v_a_1021_);
v___x_1030_ = 32ULL;
v___x_1031_ = lean_uint64_shift_right(v___x_1029_, v___x_1030_);
v_fold_1032_ = lean_uint64_xor(v___x_1029_, v___x_1031_);
v___x_1033_ = 16ULL;
v___x_1034_ = lean_uint64_shift_right(v_fold_1032_, v___x_1033_);
v___x_1035_ = lean_uint64_xor(v_fold_1032_, v___x_1034_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_sub(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_usize_land(v___x_1036_, v___x_1039_);
v_bkt_1041_ = lean_array_uget_borrowed(v_buckets_1024_, v___x_1040_);
v___x_1042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_1021_, v_bkt_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v_size_x27_1044_; lean_object* v___x_1045_; lean_object* v_buckets_x27_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v_size_x27_1044_ = lean_nat_add(v_size_1023_, v___x_1043_);
lean_dec(v_size_1023_);
lean_inc(v_bkt_1041_);
v___x_1045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1045_, 0, v_a_1021_);
lean_ctor_set(v___x_1045_, 1, v_b_1022_);
lean_ctor_set(v___x_1045_, 2, v_bkt_1041_);
v_buckets_x27_1046_ = lean_array_uset(v_buckets_1024_, v___x_1040_, v___x_1045_);
v___x_1047_ = lean_unsigned_to_nat(4u);
v___x_1048_ = lean_nat_mul(v_size_x27_1044_, v___x_1047_);
v___x_1049_ = lean_unsigned_to_nat(3u);
v___x_1050_ = lean_nat_div(v___x_1048_, v___x_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_array_get_size(v_buckets_x27_1046_);
v___x_1052_ = lean_nat_dec_le(v___x_1050_, v___x_1051_);
lean_dec(v___x_1050_);
if (v___x_1052_ == 0)
{
lean_object* v_val_1053_; lean_object* v___x_1055_; 
v_val_1053_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_buckets_x27_1046_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v_val_1053_);
lean_ctor_set(v___x_1026_, 0, v_size_x27_1044_);
v___x_1055_ = v___x_1026_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_size_x27_1044_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_val_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v___x_1058_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v_buckets_x27_1046_);
lean_ctor_set(v___x_1026_, 0, v_size_x27_1044_);
v___x_1058_ = v___x_1026_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_size_x27_1044_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_buckets_x27_1046_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v___x_1060_; lean_object* v_buckets_x27_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_inc(v_bkt_1041_);
v___x_1060_ = lean_box(0);
v_buckets_x27_1061_ = lean_array_uset(v_buckets_1024_, v___x_1040_, v___x_1060_);
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1021_, v_b_1022_, v_bkt_1041_);
v___x_1063_ = lean_array_uset(v_buckets_x27_1061_, v___x_1040_, v___x_1062_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v___x_1063_);
v___x_1065_ = v___x_1026_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_size_1023_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 0)
{
return v_x_1068_;
}
else
{
lean_object* v_key_1070_; lean_object* v_value_1071_; lean_object* v_tail_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1098_; 
v_key_1070_ = lean_ctor_get(v_x_1069_, 0);
v_value_1071_ = lean_ctor_get(v_x_1069_, 1);
v_tail_1072_ = lean_ctor_get(v_x_1069_, 2);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_x_1069_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1074_ = v_x_1069_;
v_isShared_1075_ = v_isSharedCheck_1098_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_tail_1072_);
lean_inc(v_value_1071_);
lean_inc(v_key_1070_);
lean_dec(v_x_1069_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1098_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v_fold_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1076_ = lean_array_get_size(v_x_1068_);
v___x_1077_ = lean_ptr_addr(v_key_1070_);
v___x_1078_ = ((size_t)3ULL);
v___x_1079_ = lean_usize_shift_right(v___x_1077_, v___x_1078_);
v___x_1080_ = lean_usize_to_uint64(v___x_1079_);
v___x_1081_ = 32ULL;
v___x_1082_ = lean_uint64_shift_right(v___x_1080_, v___x_1081_);
v_fold_1083_ = lean_uint64_xor(v___x_1080_, v___x_1082_);
v___x_1084_ = 16ULL;
v___x_1085_ = lean_uint64_shift_right(v_fold_1083_, v___x_1084_);
v___x_1086_ = lean_uint64_xor(v_fold_1083_, v___x_1085_);
v___x_1087_ = lean_uint64_to_usize(v___x_1086_);
v___x_1088_ = lean_usize_of_nat(v___x_1076_);
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_sub(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_usize_land(v___x_1087_, v___x_1090_);
v___x_1092_ = lean_array_uget_borrowed(v_x_1068_, v___x_1091_);
lean_inc(v___x_1092_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v___x_1092_);
v___x_1094_ = v___x_1074_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_key_1070_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_value_1071_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_array_uset(v_x_1068_, v___x_1091_, v___x_1094_);
v_x_1068_ = v___x_1095_;
v_x_1069_ = v_tail_1072_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(lean_object* v_i_1099_, lean_object* v_source_1100_, lean_object* v_target_1101_){
_start:
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_array_get_size(v_source_1100_);
v___x_1103_ = lean_nat_dec_lt(v_i_1099_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v_source_1100_);
lean_dec(v_i_1099_);
return v_target_1101_;
}
else
{
lean_object* v_es_1104_; lean_object* v___x_1105_; lean_object* v_source_1106_; lean_object* v_target_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_es_1104_ = lean_array_fget(v_source_1100_, v_i_1099_);
v___x_1105_ = lean_box(0);
v_source_1106_ = lean_array_fset(v_source_1100_, v_i_1099_, v___x_1105_);
v_target_1107_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_target_1101_, v_es_1104_);
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_nat_add(v_i_1099_, v___x_1108_);
lean_dec(v_i_1099_);
v_i_1099_ = v___x_1109_;
v_source_1100_ = v_source_1106_;
v_target_1101_ = v_target_1107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(lean_object* v_data_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_nbuckets_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1112_ = lean_array_get_size(v_data_1111_);
v___x_1113_ = lean_unsigned_to_nat(2u);
v_nbuckets_1114_ = lean_nat_mul(v___x_1112_, v___x_1113_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_mk_array(v_nbuckets_1114_, v___x_1116_);
v___x_1118_ = lean_array_propagate_mark(v_data_1111_, v___x_1117_);
v___x_1119_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v___x_1115_, v_data_1111_, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(lean_object* v_m_1120_, lean_object* v_a_1121_, lean_object* v_b_1122_){
_start:
{
lean_object* v_size_1123_; lean_object* v_buckets_1124_; lean_object* v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; size_t v___x_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v_fold_1132_; uint64_t v___x_1133_; uint64_t v___x_1134_; uint64_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; lean_object* v_bkt_1141_; uint8_t v___x_1142_; 
v_size_1123_ = lean_ctor_get(v_m_1120_, 0);
v_buckets_1124_ = lean_ctor_get(v_m_1120_, 1);
v___x_1125_ = lean_array_get_size(v_buckets_1124_);
v___x_1126_ = lean_ptr_addr(v_a_1121_);
v___x_1127_ = ((size_t)3ULL);
v___x_1128_ = lean_usize_shift_right(v___x_1126_, v___x_1127_);
v___x_1129_ = lean_usize_to_uint64(v___x_1128_);
v___x_1130_ = 32ULL;
v___x_1131_ = lean_uint64_shift_right(v___x_1129_, v___x_1130_);
v_fold_1132_ = lean_uint64_xor(v___x_1129_, v___x_1131_);
v___x_1133_ = 16ULL;
v___x_1134_ = lean_uint64_shift_right(v_fold_1132_, v___x_1133_);
v___x_1135_ = lean_uint64_xor(v_fold_1132_, v___x_1134_);
v___x_1136_ = lean_uint64_to_usize(v___x_1135_);
v___x_1137_ = lean_usize_of_nat(v___x_1125_);
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = lean_usize_sub(v___x_1137_, v___x_1138_);
v___x_1140_ = lean_usize_land(v___x_1136_, v___x_1139_);
v_bkt_1141_ = lean_array_uget_borrowed(v_buckets_1124_, v___x_1140_);
v___x_1142_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1121_, v_bkt_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1163_; 
lean_inc_ref(v_buckets_1124_);
lean_inc(v_size_1123_);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_m_1120_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1164_ = lean_ctor_get(v_m_1120_, 1);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_m_1120_, 0);
lean_dec(v_unused_1165_);
v___x_1144_ = v_m_1120_;
v_isShared_1145_ = v_isSharedCheck_1163_;
goto v_resetjp_1143_;
}
else
{
lean_dec(v_m_1120_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1163_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v_size_x27_1147_; lean_object* v___x_1148_; lean_object* v_buckets_x27_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1146_ = lean_unsigned_to_nat(1u);
v_size_x27_1147_ = lean_nat_add(v_size_1123_, v___x_1146_);
lean_dec(v_size_1123_);
lean_inc(v_bkt_1141_);
v___x_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1148_, 0, v_a_1121_);
lean_ctor_set(v___x_1148_, 1, v_b_1122_);
lean_ctor_set(v___x_1148_, 2, v_bkt_1141_);
v_buckets_x27_1149_ = lean_array_uset(v_buckets_1124_, v___x_1140_, v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(4u);
v___x_1151_ = lean_nat_mul(v_size_x27_1147_, v___x_1150_);
v___x_1152_ = lean_unsigned_to_nat(3u);
v___x_1153_ = lean_nat_div(v___x_1151_, v___x_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_array_get_size(v_buckets_x27_1149_);
v___x_1155_ = lean_nat_dec_le(v___x_1153_, v___x_1154_);
lean_dec(v___x_1153_);
if (v___x_1155_ == 0)
{
lean_object* v_val_1156_; lean_object* v___x_1158_; 
v_val_1156_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_buckets_x27_1149_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_val_1156_);
lean_ctor_set(v___x_1144_, 0, v_size_x27_1147_);
v___x_1158_ = v___x_1144_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_size_x27_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_val_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
lean_object* v___x_1161_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_buckets_x27_1149_);
lean_ctor_set(v___x_1144_, 0, v_size_x27_1147_);
v___x_1161_ = v___x_1144_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_size_x27_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_buckets_x27_1149_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_dec(v_b_1122_);
lean_dec_ref(v_a_1121_);
return v_m_1120_;
}
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(lean_object* v_fst_1166_, lean_object* v_snd_1167_, lean_object* v_fst_1168_, lean_object* v_fst_1169_, lean_object* v_x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_fst_1166_);
lean_ctor_set(v___x_1183_, 1, v_snd_1167_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_fst_1168_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_fst_1169_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1166_ = stack[0].m_obj;
lean_object* v_snd_1167_ = stack[1].m_obj;
lean_object* v_fst_1168_ = stack[2].m_obj;
lean_object* v_fst_1169_ = stack[3].m_obj;
lean_object* v_x_1170_ = stack[4].m_obj;
lean_object* v___y_1171_ = stack[5].m_obj;
lean_object* v___y_1172_ = stack[6].m_obj;
lean_object* v___y_1173_ = stack[7].m_obj;
lean_object* v___y_1174_ = stack[8].m_obj;
lean_object* v___y_1175_ = stack[9].m_obj;
lean_object* v___y_1176_ = stack[10].m_obj;
lean_object* v___y_1177_ = stack[11].m_obj;
lean_object* v___y_1178_ = stack[12].m_obj;
lean_object* v___y_1179_ = stack[13].m_obj;
lean_object* v___y_1180_ = stack[14].m_obj;
lean_object* v___y_1181_ = stack[15].m_obj;
lean_object* v_res_1188_;
v_res_1188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1166_, v_snd_1167_, v_fst_1168_, v_fst_1169_, v_x_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
stack->m_obj
 = v_res_1188_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_1189_ = _args[0];
lean_object* v_snd_1190_ = _args[1];
lean_object* v_fst_1191_ = _args[2];
lean_object* v_fst_1192_ = _args[3];
lean_object* v_x_1193_ = _args[4];
lean_object* v___y_1194_ = _args[5];
lean_object* v___y_1195_ = _args[6];
lean_object* v___y_1196_ = _args[7];
lean_object* v___y_1197_ = _args[8];
lean_object* v___y_1198_ = _args[9];
lean_object* v___y_1199_ = _args[10];
lean_object* v___y_1200_ = _args[11];
lean_object* v___y_1201_ = _args[12];
lean_object* v___y_1202_ = _args[13];
lean_object* v___y_1203_ = _args[14];
lean_object* v___y_1204_ = _args[15];
lean_object* v___y_1205_ = _args[16];
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1189_, v_snd_1190_, v_fst_1191_, v_fst_1192_, v_x_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_ks_1211_; lean_object* v_vs_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1238_; 
v_ks_1211_ = lean_ctor_get(v_x_1207_, 0);
v_vs_1212_ = lean_ctor_get(v_x_1207_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1207_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1214_ = v_x_1207_;
v_isShared_1215_ = v_isSharedCheck_1238_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_vs_1212_);
lean_inc(v_ks_1211_);
lean_dec(v_x_1207_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1238_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_array_get_size(v_ks_1211_);
v___x_1217_ = lean_nat_dec_lt(v_x_1208_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
lean_dec(v_x_1208_);
v___x_1218_ = lean_array_push(v_ks_1211_, v_x_1209_);
v___x_1219_ = lean_array_push(v_vs_1212_, v_x_1210_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1219_);
lean_ctor_set(v___x_1214_, 0, v___x_1218_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
else
{
lean_object* v_k_x27_1223_; size_t v___x_1224_; size_t v___x_1225_; uint8_t v___x_1226_; 
v_k_x27_1223_ = lean_array_fget_borrowed(v_ks_1211_, v_x_1208_);
v___x_1224_ = lean_ptr_addr(v_x_1209_);
v___x_1225_ = lean_ptr_addr(v_k_x27_1223_);
v___x_1226_ = lean_usize_dec_eq(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1228_; 
if (v_isShared_1215_ == 0)
{
v___x_1228_ = v___x_1214_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_ks_1211_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_vs_1212_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = lean_nat_add(v_x_1208_, v___x_1229_);
lean_dec(v_x_1208_);
v_x_1207_ = v___x_1228_;
v_x_1208_ = v___x_1230_;
goto _start;
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1233_ = lean_array_fset(v_ks_1211_, v_x_1208_, v_x_1209_);
v___x_1234_ = lean_array_fset(v_vs_1212_, v_x_1208_, v_x_1210_);
lean_dec(v_x_1208_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1234_);
lean_ctor_set(v___x_1214_, 0, v___x_1233_);
v___x_1236_ = v___x_1214_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(lean_object* v_n_1239_, lean_object* v_k_1240_, lean_object* v_v_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_n_1239_, v___x_1242_, v_k_1240_, v_v_1241_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1244_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(lean_object* v_x_1245_, size_t v_x_1246_, size_t v_x_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
lean_object* v_es_1250_; size_t v___x_1251_; size_t v___x_1252_; lean_object* v_j_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_es_1250_ = lean_ctor_get(v_x_1245_, 0);
v___x_1251_ = ((size_t)31ULL);
v___x_1252_ = lean_usize_land(v_x_1246_, v___x_1251_);
v_j_1253_ = lean_usize_to_nat(v___x_1252_);
v___x_1254_ = lean_array_get_size(v_es_1250_);
v___x_1255_ = lean_nat_dec_lt(v_j_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_j_1253_);
lean_dec(v_x_1249_);
lean_dec_ref(v_x_1248_);
return v_x_1245_;
}
else
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1296_; 
lean_inc_ref(v_es_1250_);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v_x_1245_, 0);
lean_dec(v_unused_1297_);
v___x_1257_ = v_x_1245_;
v_isShared_1258_ = v_isSharedCheck_1296_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v_x_1245_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1296_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_v_1259_; lean_object* v___x_1260_; lean_object* v_xs_x27_1261_; lean_object* v___y_1263_; 
v_v_1259_ = lean_array_fget(v_es_1250_, v_j_1253_);
v___x_1260_ = lean_box(0);
v_xs_x27_1261_ = lean_array_fset(v_es_1250_, v_j_1253_, v___x_1260_);
switch(lean_obj_tag(v_v_1259_))
{
case 0:
{
lean_object* v_key_1268_; lean_object* v_val_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1281_; 
v_key_1268_ = lean_ctor_get(v_v_1259_, 0);
v_val_1269_ = lean_ctor_get(v_v_1259_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_v_1259_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1271_ = v_v_1259_;
v_isShared_1272_ = v_isSharedCheck_1281_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_val_1269_);
lean_inc(v_key_1268_);
lean_dec(v_v_1259_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1281_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
size_t v___x_1273_; size_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = lean_ptr_addr(v_x_1248_);
v___x_1274_ = lean_ptr_addr(v_key_1268_);
v___x_1275_ = lean_usize_dec_eq(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_del_object(v___x_1271_);
v___x_1276_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1268_, v_val_1269_, v_x_1248_, v_x_1249_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
v___y_1263_ = v___x_1277_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1279_; 
lean_dec(v_val_1269_);
lean_dec(v_key_1268_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v_x_1249_);
lean_ctor_set(v___x_1271_, 0, v_x_1248_);
v___x_1279_ = v___x_1271_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_x_1248_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_x_1249_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v___y_1263_ = v___x_1279_;
goto v___jp_1262_;
}
}
}
}
case 1:
{
lean_object* v_node_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1294_; 
v_node_1282_ = lean_ctor_get(v_v_1259_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_v_1259_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1284_ = v_v_1259_;
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_node_1282_);
lean_dec(v_v_1259_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1286_ = ((size_t)5ULL);
v___x_1287_ = lean_usize_shift_right(v_x_1246_, v___x_1286_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_add(v_x_1247_, v___x_1288_);
v___x_1290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_node_1282_, v___x_1287_, v___x_1289_, v_x_1248_, v_x_1249_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1290_);
v___x_1292_ = v___x_1284_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
v___y_1263_ = v___x_1292_;
goto v___jp_1262_;
}
}
}
default: 
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_x_1248_);
lean_ctor_set(v___x_1295_, 1, v_x_1249_);
v___y_1263_ = v___x_1295_;
goto v___jp_1262_;
}
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_array_fset(v_xs_x27_1261_, v_j_1253_, v___y_1263_);
lean_dec(v_j_1253_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1264_);
v___x_1266_ = v___x_1257_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
else
{
lean_object* v_ks_1298_; lean_object* v_vs_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1317_; 
v_ks_1298_ = lean_ctor_get(v_x_1245_, 0);
v_vs_1299_ = lean_ctor_get(v_x_1245_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1301_ = v_x_1245_;
v_isShared_1302_ = v_isSharedCheck_1317_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_vs_1299_);
lean_inc(v_ks_1298_);
lean_dec(v_x_1245_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1317_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_ks_1298_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_vs_1299_);
v___x_1304_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v_newNode_1305_; size_t v___x_1306_; uint8_t v___x_1307_; 
v_newNode_1305_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v___x_1304_, v_x_1248_, v_x_1249_);
v___x_1306_ = ((size_t)7ULL);
v___x_1307_ = lean_usize_dec_le(v___x_1306_, v_x_1247_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1308_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1305_);
v___x_1309_ = lean_unsigned_to_nat(4u);
v___x_1310_ = lean_nat_dec_lt(v___x_1308_, v___x_1309_);
lean_dec(v___x_1308_);
if (v___x_1310_ == 0)
{
lean_object* v_ks_1311_; lean_object* v_vs_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_ks_1311_ = lean_ctor_get(v_newNode_1305_, 0);
lean_inc_ref(v_ks_1311_);
v_vs_1312_ = lean_ctor_get(v_newNode_1305_, 1);
lean_inc_ref(v_vs_1312_);
lean_dec_ref(v_newNode_1305_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0);
v___x_1315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_x_1247_, v_ks_1311_, v_vs_1312_, v___x_1313_, v___x_1314_);
lean_dec_ref(v_vs_1312_);
lean_dec_ref(v_ks_1311_);
return v___x_1315_;
}
else
{
return v_newNode_1305_;
}
}
else
{
return v_newNode_1305_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1245_ = stack[0].m_obj;
size_t v_x_1246_ = stack[1].m_num;
size_t v_x_1247_ = stack[2].m_num;
lean_object* v_x_1248_ = stack[3].m_obj;
lean_object* v_x_1249_ = stack[4].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1245_, v_x_1246_, v_x_1247_, v_x_1248_, v_x_1249_);
stack->m_obj
 = v_res_1318_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(size_t v_depth_1319_, lean_object* v_keys_1320_, lean_object* v_vals_1321_, lean_object* v_i_1322_, lean_object* v_entries_1323_){
_start:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_array_get_size(v_keys_1320_);
v___x_1325_ = lean_nat_dec_lt(v_i_1322_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec(v_i_1322_);
return v_entries_1323_;
}
else
{
lean_object* v_k_1326_; lean_object* v_v_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; uint64_t v___x_1331_; size_t v_h_1332_; size_t v___x_1333_; lean_object* v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v_h_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_k_1326_ = lean_array_fget_borrowed(v_keys_1320_, v_i_1322_);
v_v_1327_ = lean_array_fget_borrowed(v_vals_1321_, v_i_1322_);
v___x_1328_ = lean_ptr_addr(v_k_1326_);
v___x_1329_ = ((size_t)3ULL);
v___x_1330_ = lean_usize_shift_right(v___x_1328_, v___x_1329_);
v___x_1331_ = lean_usize_to_uint64(v___x_1330_);
v_h_1332_ = lean_uint64_to_usize(v___x_1331_);
v___x_1333_ = ((size_t)5ULL);
v___x_1334_ = lean_unsigned_to_nat(1u);
v___x_1335_ = ((size_t)1ULL);
v___x_1336_ = lean_usize_sub(v_depth_1319_, v___x_1335_);
v___x_1337_ = lean_usize_mul(v___x_1333_, v___x_1336_);
v_h_1338_ = lean_usize_shift_right(v_h_1332_, v___x_1337_);
v___x_1339_ = lean_nat_add(v_i_1322_, v___x_1334_);
lean_dec(v_i_1322_);
lean_inc(v_v_1327_);
lean_inc(v_k_1326_);
v___x_1340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_entries_1323_, v_h_1338_, v_depth_1319_, v_k_1326_, v_v_1327_);
v_i_1322_ = v___x_1339_;
v_entries_1323_ = v___x_1340_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1319_ = stack[0].m_num;
lean_object* v_keys_1320_ = stack[1].m_obj;
lean_object* v_vals_1321_ = stack[2].m_obj;
lean_object* v_i_1322_ = stack[3].m_obj;
lean_object* v_entries_1323_ = stack[4].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_1319_, v_keys_1320_, v_vals_1321_, v_i_1322_, v_entries_1323_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg___boxed(lean_object* v_depth_1343_, lean_object* v_keys_1344_, lean_object* v_vals_1345_, lean_object* v_i_1346_, lean_object* v_entries_1347_){
_start:
{
size_t v_depth_boxed_1348_; lean_object* v_res_1349_; 
v_depth_boxed_1348_ = lean_unbox_usize(v_depth_1343_);
lean_dec(v_depth_1343_);
v_res_1349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_boxed_1348_, v_keys_1344_, v_vals_1345_, v_i_1346_, v_entries_1347_);
lean_dec_ref(v_vals_1345_);
lean_dec_ref(v_keys_1344_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___boxed(lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
size_t v_x_80346__boxed_1355_; size_t v_x_80347__boxed_1356_; lean_object* v_res_1357_; 
v_x_80346__boxed_1355_ = lean_unbox_usize(v_x_1351_);
lean_dec(v_x_1351_);
v_x_80347__boxed_1356_ = lean_unbox_usize(v_x_1352_);
lean_dec(v_x_1352_);
v_res_1357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1350_, v_x_80346__boxed_1355_, v_x_80347__boxed_1356_, v_x_1353_, v_x_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
size_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; uint64_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1361_ = lean_ptr_addr(v_x_1359_);
v___x_1362_ = ((size_t)3ULL);
v___x_1363_ = lean_usize_shift_right(v___x_1361_, v___x_1362_);
v___x_1364_ = lean_usize_to_uint64(v___x_1363_);
v___x_1365_ = lean_uint64_to_usize(v___x_1364_);
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1358_, v___x_1365_, v___x_1366_, v_x_1359_, v_x_1360_);
return v___x_1367_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(lean_object* v_upperBound_1375_, lean_object* v___x_1376_, lean_object* v_a_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_a_1392_; lean_object* v___y_1397_; uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_lt(v_a_1377_, v_upperBound_1375_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_a_1377_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v_b_1378_);
return v___x_1417_;
}
else
{
lean_object* v_snd_1418_; lean_object* v_snd_1419_; lean_object* v_fst_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1510_; 
v_snd_1418_ = lean_ctor_get(v_b_1378_, 1);
lean_inc(v_snd_1418_);
v_snd_1419_ = lean_ctor_get(v_snd_1418_, 1);
lean_inc(v_snd_1419_);
v_fst_1420_ = lean_ctor_get(v_b_1378_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_b_1378_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_b_1378_, 1);
lean_dec(v_unused_1511_);
v___x_1422_ = v_b_1378_;
v_isShared_1423_ = v_isSharedCheck_1510_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_fst_1420_);
lean_dec(v_b_1378_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1510_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_fst_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1508_; 
v_fst_1424_ = lean_ctor_get(v_snd_1418_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_snd_1418_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_snd_1418_, 1);
lean_dec(v_unused_1509_);
v___x_1426_ = v_snd_1418_;
v_isShared_1427_ = v_isSharedCheck_1508_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_fst_1424_);
lean_dec(v_snd_1418_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1508_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1507_; 
v_fst_1428_ = lean_ctor_get(v_snd_1419_, 0);
v_snd_1429_ = lean_ctor_get(v_snd_1419_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_snd_1419_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1431_ = v_snd_1419_;
v_isShared_1432_ = v_isSharedCheck_1507_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1429_);
lean_inc(v_fst_1428_);
lean_dec(v_snd_1419_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1507_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1443_; lean_object* v_type_1444_; lean_object* v_value_1445_; uint8_t v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1443_ = lean_array_fget_borrowed(v___x_1376_, v_a_1377_);
v_type_1444_ = lean_ctor_get(v___x_1443_, 1);
v_value_1445_ = lean_ctor_get(v___x_1443_, 2);
lean_inc_ref(v_type_1444_);
v___x_1457_ = l_Lean_Expr_cleanupAnnotations(v_type_1444_);
v___x_1458_ = l_Lean_Expr_isApp(v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1431_);
lean_del_object(v___x_1426_);
lean_del_object(v___x_1422_);
v___x_1459_ = lean_box(0);
v___x_1460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1428_, v_snd_1429_, v_fst_1424_, v_fst_1420_, v___x_1459_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
v___y_1397_ = v___x_1460_;
goto v___jp_1396_;
}
else
{
lean_object* v_arg_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_arg_1461_ = lean_ctor_get(v___x_1457_, 1);
lean_inc_ref(v_arg_1461_);
v___x_1462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1457_);
v___x_1463_ = l_Lean_Expr_isApp(v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec_ref(v___x_1462_);
lean_dec_ref(v_arg_1461_);
lean_del_object(v___x_1431_);
lean_del_object(v___x_1426_);
lean_del_object(v___x_1422_);
v___x_1464_ = lean_box(0);
v___x_1465_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1428_, v_snd_1429_, v_fst_1424_, v_fst_1420_, v___x_1464_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
v___y_1397_ = v___x_1465_;
goto v___jp_1396_;
}
else
{
lean_object* v_arg_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_arg_1466_ = lean_ctor_get(v___x_1462_, 1);
lean_inc_ref(v_arg_1466_);
v___x_1467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1462_);
v___x_1468_ = l_Lean_Expr_isApp(v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref(v___x_1467_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1461_);
lean_del_object(v___x_1431_);
lean_del_object(v___x_1426_);
lean_del_object(v___x_1422_);
v___x_1469_ = lean_box(0);
v___x_1470_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1428_, v_snd_1429_, v_fst_1424_, v_fst_1420_, v___x_1469_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
v___y_1397_ = v___x_1470_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1467_);
v___x_1472_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__1));
v___x_1473_ = l_Lean_Expr_isConstOf(v___x_1471_, v___x_1472_);
lean_dec_ref(v___x_1471_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1461_);
lean_del_object(v___x_1431_);
lean_del_object(v___x_1426_);
lean_del_object(v___x_1422_);
v___x_1474_ = lean_box(0);
v___x_1475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1428_, v_snd_1429_, v_fst_1424_, v_fst_1420_, v___x_1474_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
v___y_1397_ = v___x_1475_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; lean_object* v_fst_1480_; uint8_t v_snd_1481_; lean_object* v___y_1490_; 
v___x_1476_ = l_Lean_Expr_cleanupAnnotations(v_arg_1461_);
v___x_1477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2));
v___x_1478_ = l_Lean_Expr_isConstOf(v___x_1476_, v___x_1477_);
lean_dec_ref(v___x_1476_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v_arg_1466_);
lean_del_object(v___x_1431_);
lean_del_object(v___x_1426_);
lean_del_object(v___x_1422_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_fst_1428_);
lean_ctor_set(v___x_1494_, 1, v_snd_1429_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_fst_1424_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_fst_1420_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v_a_1392_ = v___x_1496_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
lean_inc_ref(v_arg_1466_);
v___x_1497_ = l_Lean_Expr_cleanupAnnotations(v_arg_1466_);
v___x_1498_ = l_Lean_Expr_isApp(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec_ref(v___x_1497_);
v___x_1499_ = lean_box(0);
v___x_1500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1466_, v___x_1499_);
v___y_1490_ = v___x_1500_;
goto v___jp_1489_;
}
else
{
lean_object* v_arg_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v_arg_1501_ = lean_ctor_get(v___x_1497_, 1);
lean_inc_ref(v_arg_1501_);
v___x_1502_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1497_);
v___x_1503_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3));
v___x_1504_ = l_Lean_Expr_isConstOf(v___x_1502_, v___x_1503_);
lean_dec_ref(v___x_1502_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v_arg_1501_);
v___x_1505_ = lean_box(0);
v___x_1506_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1466_, v___x_1505_);
v___y_1490_ = v___x_1506_;
goto v___jp_1489_;
}
else
{
lean_dec_ref(v_arg_1466_);
v_fst_1480_ = v_arg_1501_;
v_snd_1481_ = v___x_1504_;
goto v___jp_1479_;
}
}
}
v___jp_1479_:
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_fst_1428_, v_fst_1480_);
if (v___x_1482_ == 0)
{
if (v___x_1478_ == 0)
{
lean_dec_ref(v_fst_1480_);
goto v___jp_1433_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint32_t v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
lean_del_object(v___x_1431_);
lean_del_object(v___x_1426_);
lean_del_object(v___x_1422_);
v___x_1483_ = lean_box(0);
lean_inc_ref_n(v_fst_1480_, 2);
v___x_1484_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_fst_1428_, v_fst_1480_, v___x_1483_);
lean_inc(v_a_1377_);
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_fst_1424_, v_a_1377_, v_fst_1480_);
v___x_1486_ = l_Lean_Expr_approxDepth(v_fst_1480_);
v___x_1487_ = lean_uint32_to_nat(v___x_1486_);
v___x_1488_ = lean_nat_dec_le(v_snd_1429_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_dec(v_snd_1429_);
v___y_1447_ = v_snd_1481_;
v___y_1448_ = v___x_1485_;
v___y_1449_ = v___x_1484_;
v___y_1450_ = v_fst_1480_;
v___y_1451_ = v___x_1487_;
goto v___jp_1446_;
}
else
{
lean_dec(v___x_1487_);
v___y_1447_ = v_snd_1481_;
v___y_1448_ = v___x_1485_;
v___y_1449_ = v___x_1484_;
v___y_1450_ = v_fst_1480_;
v___y_1451_ = v_snd_1429_;
goto v___jp_1446_;
}
}
}
else
{
lean_dec_ref(v_fst_1480_);
goto v___jp_1433_;
}
}
v___jp_1489_:
{
lean_object* v_fst_1491_; lean_object* v_snd_1492_; uint8_t v___x_1493_; 
v_fst_1491_ = lean_ctor_get(v___y_1490_, 0);
lean_inc(v_fst_1491_);
v_snd_1492_ = lean_ctor_get(v___y_1490_, 1);
lean_inc(v_snd_1492_);
lean_dec_ref(v___y_1490_);
v___x_1493_ = lean_unbox(v_snd_1492_);
lean_dec(v_snd_1492_);
v_fst_1480_ = v_fst_1491_;
v_snd_1481_ = v___x_1493_;
goto v___jp_1479_;
}
}
}
}
}
v___jp_1433_:
{
lean_object* v___x_1435_; 
if (v_isShared_1432_ == 0)
{
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_fst_1428_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1429_);
v___x_1435_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___x_1435_);
v___x_1437_ = v___x_1426_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_fst_1424_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v___x_1437_);
v___x_1439_ = v___x_1422_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_fst_1420_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v_a_1392_ = v___x_1439_;
goto v___jp_1391_;
}
}
}
}
v___jp_1446_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_inc_ref(v_value_1445_);
v___x_1452_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1452_, 0, v_value_1445_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*1, v___y_1447_);
v___x_1453_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_fst_1420_, v___y_1450_, v___x_1452_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___y_1449_);
lean_ctor_set(v___x_1454_, 1, v___y_1451_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___y_1448_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1453_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v_a_1392_ = v___x_1456_;
goto v___jp_1391_;
}
}
}
}
}
v___jp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_add(v_a_1377_, v___x_1393_);
lean_dec(v_a_1377_);
v_a_1377_ = v___x_1394_;
v_b_1378_ = v_a_1392_;
goto _start;
}
v___jp_1396_:
{
if (lean_obj_tag(v___y_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1407_; 
v_a_1398_ = lean_ctor_get(v___y_1397_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___y_1397_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1400_ = v___y_1397_;
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___y_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
if (lean_obj_tag(v_a_1398_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; 
lean_dec(v_a_1377_);
v_a_1402_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v_a_1398_, 1);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_a_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
lean_object* v_a_1406_; 
lean_del_object(v___x_1400_);
v_a_1406_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v_a_1398_, 1);
v_a_1392_ = v_a_1406_;
goto v___jp_1391_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_a_1377_);
v_a_1408_ = lean_ctor_get(v___y_1397_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___y_1397_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___y_1397_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___y_1397_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1375_ = stack[0].m_obj;
lean_object* v___x_1376_ = stack[1].m_obj;
lean_object* v_a_1377_ = stack[2].m_obj;
lean_object* v_b_1378_ = stack[3].m_obj;
lean_object* v___y_1379_ = stack[4].m_obj;
lean_object* v___y_1380_ = stack[5].m_obj;
lean_object* v___y_1381_ = stack[6].m_obj;
lean_object* v___y_1382_ = stack[7].m_obj;
lean_object* v___y_1383_ = stack[8].m_obj;
lean_object* v___y_1384_ = stack[9].m_obj;
lean_object* v___y_1385_ = stack[10].m_obj;
lean_object* v___y_1386_ = stack[11].m_obj;
lean_object* v___y_1387_ = stack[12].m_obj;
lean_object* v___y_1388_ = stack[13].m_obj;
lean_object* v___y_1389_ = stack[14].m_obj;
lean_object* v_res_1512_;
v_res_1512_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1375_, v___x_1376_, v_a_1377_, v_b_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___boxed(lean_object* v_upperBound_1513_, lean_object* v___x_1514_, lean_object* v_a_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1513_, v___x_1514_, v_a_1515_, v_b_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v___x_1514_);
lean_dec(v_upperBound_1513_);
return v_res_1529_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1531_; lean_object* v_relevantHypsMap_1532_; 
v___x_1531_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0);
v_relevantHypsMap_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_relevantHypsMap_1532_, 0, v___x_1531_);
return v_relevantHypsMap_1532_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_unsigned_to_nat(16u);
v___x_1535_ = lean_mk_array(v___x_1534_, v___x_1533_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_relevantHypsIdxMap_1538_; 
v___x_1536_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2);
v___x_1537_ = lean_unsigned_to_nat(0u);
v_relevantHypsIdxMap_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_relevantHypsIdxMap_1538_, 0, v___x_1537_);
lean_ctor_set(v_relevantHypsIdxMap_1538_, 1, v___x_1536_);
return v_relevantHypsIdxMap_1538_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4(void){
_start:
{
lean_object* v_minDepth_1539_; lean_object* v_relevantHypsIdxMap_1540_; lean_object* v___x_1541_; 
v_minDepth_1539_ = lean_cstr_to_nat("4294967296");
v_relevantHypsIdxMap_1540_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_relevantHypsIdxMap_1540_);
lean_ctor_set(v___x_1541_, 1, v_minDepth_1539_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1542_; lean_object* v_relevantHypsIdxMap_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4);
v_relevantHypsIdxMap_1543_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_relevantHypsIdxMap_1543_);
lean_ctor_set(v___x_1544_, 1, v___x_1542_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1545_; lean_object* v_relevantHypsMap_1546_; lean_object* v___x_1547_; 
v___x_1545_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5);
v_relevantHypsMap_1546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_relevantHypsMap_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1545_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7));
v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
return v___x_1550_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v_hypotheses_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1563_ = lean_st_ref_get(v___y_1552_);
v_hypotheses_1564_ = lean_ctor_get(v___x_1563_, 3);
lean_inc_ref(v_hypotheses_1564_);
lean_dec(v___x_1563_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_array_get_size(v_hypotheses_1564_);
v___x_1567_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6);
v___x_1568_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v___x_1566_, v_hypotheses_1564_, v___x_1565_, v___x_1567_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec_ref(v_hypotheses_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1686_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1686_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1686_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v_snd_1573_; lean_object* v_snd_1574_; lean_object* v_fst_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1684_; 
v_snd_1573_ = lean_ctor_get(v_a_1569_, 1);
lean_inc(v_snd_1573_);
v_snd_1574_ = lean_ctor_get(v_snd_1573_, 1);
lean_inc(v_snd_1574_);
v_fst_1575_ = lean_ctor_get(v_a_1569_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_a_1569_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_a_1569_, 1);
lean_dec(v_unused_1685_);
v___x_1577_ = v_a_1569_;
v_isShared_1578_ = v_isSharedCheck_1684_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_fst_1575_);
lean_dec(v_a_1569_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1684_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_fst_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1682_; 
v_fst_1579_ = lean_ctor_get(v_snd_1573_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_snd_1573_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v_snd_1573_, 1);
lean_dec(v_unused_1683_);
v___x_1581_ = v_snd_1573_;
v_isShared_1582_ = v_isSharedCheck_1682_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_fst_1579_);
lean_dec(v_snd_1573_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1682_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_snd_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1680_; 
v_snd_1583_ = lean_ctor_get(v_snd_1574_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_snd_1574_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; 
v_unused_1681_ = lean_ctor_get(v_snd_1574_, 0);
lean_dec(v_unused_1681_);
v___x_1585_ = v_snd_1574_;
v_isShared_1586_ = v_isSharedCheck_1680_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snd_1583_);
lean_dec(v_snd_1574_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1680_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v_toCold_1657_; lean_object* v_options_1658_; uint8_t v_hasTrace_1659_; 
v_toCold_1657_ = lean_ctor_get(v___y_1560_, 0);
v_options_1658_ = lean_ctor_get(v_toCold_1657_, 2);
v_hasTrace_1659_ = lean_ctor_get_uint8(v_options_1658_, sizeof(void*)*1);
if (v_hasTrace_1659_ == 0)
{
lean_del_object(v___x_1577_);
v___y_1588_ = v___y_1551_;
v___y_1589_ = v___y_1552_;
v___y_1590_ = v___y_1553_;
v___y_1591_ = v___y_1554_;
v___y_1592_ = v___y_1555_;
v___y_1593_ = v___y_1556_;
v___y_1594_ = v___y_1557_;
v___y_1595_ = v___y_1558_;
v___y_1596_ = v___y_1559_;
v___y_1597_ = v___y_1560_;
v___y_1598_ = v___y_1561_;
goto v___jp_1587_;
}
else
{
lean_object* v_inheritedTraceOptions_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_inheritedTraceOptions_1660_ = lean_ctor_get(v_toCold_1657_, 11);
v___x_1661_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_1662_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_1663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1660_, v_options_1658_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_del_object(v___x_1577_);
v___y_1588_ = v___y_1551_;
v___y_1589_ = v___y_1552_;
v___y_1590_ = v___y_1553_;
v___y_1591_ = v___y_1554_;
v___y_1592_ = v___y_1555_;
v___y_1593_ = v___y_1556_;
v___y_1594_ = v___y_1557_;
v___y_1595_ = v___y_1558_;
v___y_1596_ = v___y_1559_;
v___y_1597_ = v___y_1560_;
v___y_1598_ = v___y_1561_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1664_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8);
lean_inc(v_snd_1583_);
v___x_1665_ = l_Nat_reprFast(v_snd_1583_);
v___x_1666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
v___x_1667_ = l_Lean_MessageData_ofFormat(v___x_1666_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 7);
lean_ctor_set(v___x_1577_, 1, v___x_1667_);
lean_ctor_set(v___x_1577_, 0, v___x_1664_);
v___x_1669_ = v___x_1577_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_1661_, v___x_1669_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_dec_ref_known(v___x_1670_, 1);
v___y_1588_ = v___y_1551_;
v___y_1589_ = v___y_1552_;
v___y_1590_ = v___y_1553_;
v___y_1591_ = v___y_1554_;
v___y_1592_ = v___y_1555_;
v___y_1593_ = v___y_1556_;
v___y_1594_ = v___y_1557_;
v___y_1595_ = v___y_1558_;
v___y_1596_ = v___y_1559_;
v___y_1597_ = v___y_1560_;
v___y_1598_ = v___y_1561_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_del_object(v___x_1585_);
lean_dec(v_snd_1583_);
lean_del_object(v___x_1581_);
lean_dec(v_fst_1579_);
lean_dec(v_fst_1575_);
lean_del_object(v___x_1571_);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
v___jp_1587_:
{
uint8_t v___x_1599_; 
v___x_1599_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fst_1575_);
if (v___x_1599_ == 0)
{
lean_object* v_config_1600_; lean_object* v_maxSteps_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
lean_del_object(v___x_1571_);
v_config_1600_ = lean_ctor_get(v___y_1588_, 0);
v_maxSteps_1601_ = lean_ctor_get(v_config_1600_, 1);
v___x_1602_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1601_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1602_);
lean_ctor_set(v___x_1581_, 0, v_maxSteps_1601_);
v___x_1604_ = v___x_1581_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_maxSteps_1601_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v_hypotheses_1606_; lean_object* v___x_1607_; lean_object* v_newHyps_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1605_ = lean_st_ref_get(v___y_1589_);
v_hypotheses_1606_ = lean_ctor_get(v___x_1605_, 3);
lean_inc_ref(v_hypotheses_1606_);
lean_dec(v___x_1605_);
v___x_1607_ = lean_array_get_size(v_hypotheses_1606_);
v_newHyps_1608_ = lean_mk_empty_array_with_capacity(v___x_1607_);
v___x_1609_ = lean_box(0);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v_newHyps_1608_);
lean_ctor_set(v___x_1585_, 0, v___x_1609_);
v___x_1611_ = v___x_1585_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_newHyps_1608_);
v___x_1611_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v___x_1607_, v_hypotheses_1606_, v_snd_1583_, v___x_1599_, v___x_1604_, v_fst_1579_, v_fst_1575_, v___x_1565_, v___x_1611_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v_fst_1579_);
lean_dec(v_snd_1583_);
lean_dec_ref(v_hypotheses_1606_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1641_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1641_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1641_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_fst_1617_; 
v_fst_1617_ = lean_ctor_get(v_a_1613_, 0);
if (lean_obj_tag(v_fst_1617_) == 0)
{
lean_object* v_snd_1618_; lean_object* v___x_1619_; lean_object* v_caches_1620_; lean_object* v_typeAnalysis_1621_; lean_object* v_target_1622_; uint8_t v_didChange_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1635_; 
v_snd_1618_ = lean_ctor_get(v_a_1613_, 1);
lean_inc(v_snd_1618_);
lean_dec(v_a_1613_);
v___x_1619_ = lean_st_ref_take(v___y_1589_);
v_caches_1620_ = lean_ctor_get(v___x_1619_, 0);
v_typeAnalysis_1621_ = lean_ctor_get(v___x_1619_, 1);
v_target_1622_ = lean_ctor_get(v___x_1619_, 2);
v_didChange_1623_ = lean_ctor_get_uint8(v___x_1619_, sizeof(void*)*4);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; 
v_unused_1636_ = lean_ctor_get(v___x_1619_, 3);
lean_dec(v_unused_1636_);
v___x_1625_ = v___x_1619_;
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_target_1622_);
lean_inc(v_typeAnalysis_1621_);
lean_inc(v_caches_1620_);
lean_dec(v___x_1619_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 3, v_snd_1618_);
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_caches_1620_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_typeAnalysis_1621_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_target_1622_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_snd_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*4, v_didChange_1623_);
v___x_1628_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1629_ = lean_st_ref_put(v___y_1589_, v___x_1628_);
v___x_1630_ = lean_box(v___x_1599_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1630_);
v___x_1632_ = v___x_1615_;
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
else
{
lean_object* v_val_1637_; lean_object* v___x_1639_; 
lean_inc_ref(v_fst_1617_);
lean_dec(v_a_1613_);
v_val_1637_ = lean_ctor_get(v_fst_1617_, 0);
lean_inc(v_val_1637_);
lean_dec_ref_known(v_fst_1617_, 1);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v_val_1637_);
v___x_1639_ = v___x_1615_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_val_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1612_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1612_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
}
else
{
uint8_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_del_object(v___x_1585_);
lean_dec(v_snd_1583_);
lean_del_object(v___x_1581_);
lean_dec(v_fst_1579_);
lean_dec(v_fst_1575_);
v___x_1652_ = 0;
v___x_1653_ = lean_box(v___x_1652_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1653_);
v___x_1655_ = v___x_1571_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
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
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_a_1687_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1568_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1568_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1551_ = stack[0].m_obj;
lean_object* v___y_1552_ = stack[1].m_obj;
lean_object* v___y_1553_ = stack[2].m_obj;
lean_object* v___y_1554_ = stack[3].m_obj;
lean_object* v___y_1555_ = stack[4].m_obj;
lean_object* v___y_1556_ = stack[5].m_obj;
lean_object* v___y_1557_ = stack[6].m_obj;
lean_object* v___y_1558_ = stack[7].m_obj;
lean_object* v___y_1559_ = stack[8].m_obj;
lean_object* v___y_1560_ = stack[9].m_obj;
lean_object* v___y_1561_ = stack[10].m_obj;
lean_object* v_res_1695_;
v_res_1695_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
stack->m_obj
 = v_res_1695_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1708_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(lean_object* v___f_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; lean_object* v_target_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = lean_st_ref_get(v___y_1711_);
v_target_1723_ = lean_ctor_get(v___x_1722_, 2);
lean_inc_ref(v_target_1723_);
lean_dec(v___x_1722_);
v___x_1724_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1723_);
lean_dec_ref(v_target_1723_);
v___x_1725_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v___x_1724_, v___f_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1725_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1709_ = stack[0].m_obj;
lean_object* v___y_1710_ = stack[1].m_obj;
lean_object* v___y_1711_ = stack[2].m_obj;
lean_object* v___y_1712_ = stack[3].m_obj;
lean_object* v___y_1713_ = stack[4].m_obj;
lean_object* v___y_1714_ = stack[5].m_obj;
lean_object* v___y_1715_ = stack[6].m_obj;
lean_object* v___y_1716_ = stack[7].m_obj;
lean_object* v___y_1717_ = stack[8].m_obj;
lean_object* v___y_1718_ = stack[9].m_obj;
lean_object* v___y_1719_ = stack[10].m_obj;
lean_object* v___y_1720_ = stack[11].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(v___f_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object* v___f_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(v___f_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1740_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(lean_object* v_cls_1751_, lean_object* v_msg_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_1751_, v_msg_1752_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1751_ = stack[0].m_obj;
lean_object* v_msg_1752_ = stack[1].m_obj;
lean_object* v___y_1753_ = stack[2].m_obj;
lean_object* v___y_1754_ = stack[3].m_obj;
lean_object* v___y_1755_ = stack[4].m_obj;
lean_object* v___y_1756_ = stack[5].m_obj;
lean_object* v___y_1757_ = stack[6].m_obj;
lean_object* v___y_1758_ = stack[7].m_obj;
lean_object* v___y_1759_ = stack[8].m_obj;
lean_object* v___y_1760_ = stack[9].m_obj;
lean_object* v___y_1761_ = stack[10].m_obj;
lean_object* v___y_1762_ = stack[11].m_obj;
lean_object* v___y_1763_ = stack[12].m_obj;
lean_object* v_res_1766_;
v_res_1766_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(v_cls_1751_, v_msg_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
stack->m_obj
 = v_res_1766_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___boxed(lean_object* v_cls_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(v_cls_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(lean_object* v_00_u03b2_1782_, lean_object* v_m_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_1783_, v_a_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object* v_00_u03b2_1786_, lean_object* v_m_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(v_00_u03b2_1786_, v_m_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_m_1787_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(lean_object* v_00_u03b2_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_1791_, v_x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object* v_00_u03b2_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(v_00_u03b2_1794_, v_x_1795_, v_x_1796_);
lean_dec_ref(v_x_1796_);
return v_res_1797_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(lean_object* v_upperBound_1798_, lean_object* v___x_1799_, lean_object* v___x_1800_, uint8_t v___x_1801_, lean_object* v___x_1802_, lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v_inst_1805_, lean_object* v_R_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_, lean_object* v_c_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_1798_, v___x_1799_, v___x_1800_, v___x_1801_, v___x_1802_, v___x_1803_, v___x_1804_, v_a_1807_, v_b_1808_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1822_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1798_ = stack[0].m_obj;
lean_object* v___x_1799_ = stack[1].m_obj;
lean_object* v___x_1800_ = stack[2].m_obj;
uint8_t v___x_1801_ = stack[3].m_num;
lean_object* v___x_1802_ = stack[4].m_obj;
lean_object* v___x_1803_ = stack[5].m_obj;
lean_object* v___x_1804_ = stack[6].m_obj;
lean_object* v_a_1807_ = stack[9].m_obj;
lean_object* v_b_1808_ = stack[10].m_obj;
lean_object* v___y_1810_ = stack[12].m_obj;
lean_object* v___y_1811_ = stack[13].m_obj;
lean_object* v___y_1812_ = stack[14].m_obj;
lean_object* v___y_1813_ = stack[15].m_obj;
lean_object* v___y_1814_ = stack[16].m_obj;
lean_object* v___y_1815_ = stack[17].m_obj;
lean_object* v___y_1816_ = stack[18].m_obj;
lean_object* v___y_1817_ = stack[19].m_obj;
lean_object* v___y_1818_ = stack[20].m_obj;
lean_object* v___y_1819_ = stack[21].m_obj;
lean_object* v___y_1820_ = stack[22].m_obj;
lean_object* v_res_1823_;
v_res_1823_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(v_upperBound_1798_, v___x_1799_, v___x_1800_, v___x_1801_, v___x_1802_, v___x_1803_, v___x_1804_, lean_box(0), lean_box(0), v_a_1807_, v_b_1808_, lean_box(0), v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
stack->m_obj
 = v_res_1823_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_1824_ = _args[0];
lean_object* v___x_1825_ = _args[1];
lean_object* v___x_1826_ = _args[2];
lean_object* v___x_1827_ = _args[3];
lean_object* v___x_1828_ = _args[4];
lean_object* v___x_1829_ = _args[5];
lean_object* v___x_1830_ = _args[6];
lean_object* v_inst_1831_ = _args[7];
lean_object* v_R_1832_ = _args[8];
lean_object* v_a_1833_ = _args[9];
lean_object* v_b_1834_ = _args[10];
lean_object* v_c_1835_ = _args[11];
lean_object* v___y_1836_ = _args[12];
lean_object* v___y_1837_ = _args[13];
lean_object* v___y_1838_ = _args[14];
lean_object* v___y_1839_ = _args[15];
lean_object* v___y_1840_ = _args[16];
lean_object* v___y_1841_ = _args[17];
lean_object* v___y_1842_ = _args[18];
lean_object* v___y_1843_ = _args[19];
lean_object* v___y_1844_ = _args[20];
lean_object* v___y_1845_ = _args[21];
lean_object* v___y_1846_ = _args[22];
lean_object* v___y_1847_ = _args[23];
_start:
{
uint8_t v___x_81733__boxed_1848_; lean_object* v_res_1849_; 
v___x_81733__boxed_1848_ = lean_unbox(v___x_1827_);
v_res_1849_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(v_upperBound_1824_, v___x_1825_, v___x_1826_, v___x_81733__boxed_1848_, v___x_1828_, v___x_1829_, v___x_1830_, v_inst_1831_, v_R_1832_, v_a_1833_, v_b_1834_, v_c_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___x_1829_);
lean_dec(v___x_1826_);
lean_dec_ref(v___x_1825_);
lean_dec(v_upperBound_1824_);
return v_res_1849_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_object* v_00_u03b2_1850_, lean_object* v_m_1851_, lean_object* v_a_1852_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_1851_, v_a_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1851_ = stack[1].m_obj;
lean_object* v_a_1852_ = stack[2].m_obj;
uint8_t v_res_1854_;
v_res_1854_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_box(0), v_m_1851_, v_a_1852_);
stack->m_num = v_res_1854_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___boxed(lean_object* v_00_u03b2_1855_, lean_object* v_m_1856_, lean_object* v_a_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(v_00_u03b2_1855_, v_m_1856_, v_a_1857_);
lean_dec_ref(v_a_1857_);
lean_dec_ref(v_m_1856_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(lean_object* v_00_u03b2_1860_, lean_object* v_m_1861_, lean_object* v_a_1862_, lean_object* v_b_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_m_1861_, v_a_1862_, v_b_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(lean_object* v_00_u03b2_1865_, lean_object* v_m_1866_, lean_object* v_a_1867_, lean_object* v_b_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_m_1866_, v_a_1867_, v_b_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_x_1871_, v_x_1872_, v_x_1873_);
return v___x_1874_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(lean_object* v_upperBound_1875_, lean_object* v___x_1876_, lean_object* v_inst_1877_, lean_object* v_R_1878_, lean_object* v_a_1879_, lean_object* v_b_1880_, lean_object* v_c_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1875_, v___x_1876_, v_a_1879_, v_b_1880_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1875_ = stack[0].m_obj;
lean_object* v___x_1876_ = stack[1].m_obj;
lean_object* v_a_1879_ = stack[4].m_obj;
lean_object* v_b_1880_ = stack[5].m_obj;
lean_object* v___y_1882_ = stack[7].m_obj;
lean_object* v___y_1883_ = stack[8].m_obj;
lean_object* v___y_1884_ = stack[9].m_obj;
lean_object* v___y_1885_ = stack[10].m_obj;
lean_object* v___y_1886_ = stack[11].m_obj;
lean_object* v___y_1887_ = stack[12].m_obj;
lean_object* v___y_1888_ = stack[13].m_obj;
lean_object* v___y_1889_ = stack[14].m_obj;
lean_object* v___y_1890_ = stack[15].m_obj;
lean_object* v___y_1891_ = stack[16].m_obj;
lean_object* v___y_1892_ = stack[17].m_obj;
lean_object* v_res_1895_;
v_res_1895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(v_upperBound_1875_, v___x_1876_, lean_box(0), lean_box(0), v_a_1879_, v_b_1880_, lean_box(0), v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
stack->m_obj
 = v_res_1895_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1896_ = _args[0];
lean_object* v___x_1897_ = _args[1];
lean_object* v_inst_1898_ = _args[2];
lean_object* v_R_1899_ = _args[3];
lean_object* v_a_1900_ = _args[4];
lean_object* v_b_1901_ = _args[5];
lean_object* v_c_1902_ = _args[6];
lean_object* v___y_1903_ = _args[7];
lean_object* v___y_1904_ = _args[8];
lean_object* v___y_1905_ = _args[9];
lean_object* v___y_1906_ = _args[10];
lean_object* v___y_1907_ = _args[11];
lean_object* v___y_1908_ = _args[12];
lean_object* v___y_1909_ = _args[13];
lean_object* v___y_1910_ = _args[14];
lean_object* v___y_1911_ = _args[15];
lean_object* v___y_1912_ = _args[16];
lean_object* v___y_1913_ = _args[17];
lean_object* v___y_1914_ = _args[18];
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(v_upperBound_1896_, v___x_1897_, v_inst_1898_, v_R_1899_, v_a_1900_, v_b_1901_, v_c_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec_ref(v___x_1897_);
lean_dec(v_upperBound_1896_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(lean_object* v_00_u03b2_1916_, lean_object* v_a_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_1917_, v_x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1920_, lean_object* v_a_1921_, lean_object* v_x_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(v_00_u03b2_1920_, v_a_1921_, v_x_1922_);
lean_dec(v_x_1922_);
lean_dec(v_a_1921_);
return v_res_1923_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_object* v_00_u03b2_1924_, lean_object* v_x_1925_, size_t v_x_1926_, lean_object* v_x_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_1925_, v_x_1926_, v_x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1925_ = stack[1].m_obj;
size_t v_x_1926_ = stack[2].m_num;
lean_object* v_x_1927_ = stack[3].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_box(0), v_x_1925_, v_x_1926_, v_x_1927_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1930_, lean_object* v_x_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
size_t v_x_81941__boxed_1934_; lean_object* v_res_1935_; 
v_x_81941__boxed_1934_ = lean_unbox_usize(v_x_1932_);
lean_dec(v_x_1932_);
v_res_1935_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(v_00_u03b2_1930_, v_x_1931_, v_x_81941__boxed_1934_, v_x_1933_);
lean_dec_ref(v_x_1933_);
return v_res_1935_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_object* v_00_u03b2_1936_, lean_object* v_a_1937_, lean_object* v_x_1938_){
_start:
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1937_, v_x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1937_ = stack[1].m_obj;
lean_object* v_x_1938_ = stack[2].m_obj;
uint8_t v_res_1940_;
v_res_1940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_box(0), v_a_1937_, v_x_1938_);
stack->m_num = v_res_1940_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1941_, lean_object* v_a_1942_, lean_object* v_x_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(v_00_u03b2_1941_, v_a_1942_, v_x_1943_);
lean_dec(v_x_1943_);
lean_dec_ref(v_a_1942_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(lean_object* v_00_u03b2_1946_, lean_object* v_data_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_data_1947_);
return v___x_1948_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_object* v_00_u03b2_1949_, lean_object* v_a_1950_, lean_object* v_x_1951_){
_start:
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_1950_, v_x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1950_ = stack[1].m_obj;
lean_object* v_x_1951_ = stack[2].m_obj;
uint8_t v_res_1953_;
v_res_1953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_box(0), v_a_1950_, v_x_1951_);
stack->m_num = v_res_1953_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___boxed(lean_object* v_00_u03b2_1954_, lean_object* v_a_1955_, lean_object* v_x_1956_){
_start:
{
uint8_t v_res_1957_; lean_object* v_r_1958_; 
v_res_1957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(v_00_u03b2_1954_, v_a_1955_, v_x_1956_);
lean_dec(v_x_1956_);
lean_dec(v_a_1955_);
v_r_1958_ = lean_box(v_res_1957_);
return v_r_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13(lean_object* v_00_u03b2_1959_, lean_object* v_data_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_data_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14(lean_object* v_00_u03b2_1962_, lean_object* v_a_1963_, lean_object* v_b_1964_, lean_object* v_x_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1963_, v_b_1964_, v_x_1965_);
return v___x_1966_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(lean_object* v_00_u03b2_1967_, lean_object* v_x_1968_, size_t v_x_1969_, size_t v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1968_, v_x_1969_, v_x_1970_, v_x_1971_, v_x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1968_ = stack[1].m_obj;
size_t v_x_1969_ = stack[2].m_num;
size_t v_x_1970_ = stack[3].m_num;
lean_object* v_x_1971_ = stack[4].m_obj;
lean_object* v_x_1972_ = stack[5].m_obj;
lean_object* v_res_1974_;
v_res_1974_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(lean_box(0), v_x_1968_, v_x_1969_, v_x_1970_, v_x_1971_, v_x_1972_);
stack->m_obj
 = v_res_1974_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
size_t v_x_81987__boxed_1981_; size_t v_x_81988__boxed_1982_; lean_object* v_res_1983_; 
v_x_81987__boxed_1981_ = lean_unbox_usize(v_x_1977_);
lean_dec(v_x_1977_);
v_x_81988__boxed_1982_ = lean_unbox_usize(v_x_1978_);
lean_dec(v_x_1978_);
v_res_1983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(v_00_u03b2_1975_, v_x_1976_, v_x_81987__boxed_1981_, v_x_81988__boxed_1982_, v_x_1979_, v_x_1980_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_1984_, lean_object* v_i_1985_, lean_object* v_source_1986_, lean_object* v_target_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v_i_1985_, v_source_1986_, v_target_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17(lean_object* v_00_u03b2_1989_, lean_object* v_i_1990_, lean_object* v_source_1991_, lean_object* v_target_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v_i_1990_, v_source_1991_, v_target_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21(lean_object* v_00_u03b2_1994_, lean_object* v_n_1995_, lean_object* v_k_1996_, lean_object* v_v_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v_n_1995_, v_k_1996_, v_v_1997_);
return v___x_1998_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(lean_object* v_00_u03b2_1999_, size_t v_depth_2000_, lean_object* v_keys_2001_, lean_object* v_vals_2002_, lean_object* v_heq_2003_, lean_object* v_i_2004_, lean_object* v_entries_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_2000_, v_keys_2001_, v_vals_2002_, v_i_2004_, v_entries_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2000_ = stack[1].m_num;
lean_object* v_keys_2001_ = stack[2].m_obj;
lean_object* v_vals_2002_ = stack[3].m_obj;
lean_object* v_i_2004_ = stack[5].m_obj;
lean_object* v_entries_2005_ = stack[6].m_obj;
lean_object* v_res_2007_;
v_res_2007_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(lean_box(0), v_depth_2000_, v_keys_2001_, v_vals_2002_, lean_box(0), v_i_2004_, v_entries_2005_);
stack->m_obj
 = v_res_2007_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___boxed(lean_object* v_00_u03b2_2008_, lean_object* v_depth_2009_, lean_object* v_keys_2010_, lean_object* v_vals_2011_, lean_object* v_heq_2012_, lean_object* v_i_2013_, lean_object* v_entries_2014_){
_start:
{
size_t v_depth_boxed_2015_; lean_object* v_res_2016_; 
v_depth_boxed_2015_ = lean_unbox_usize(v_depth_2009_);
lean_dec(v_depth_2009_);
v_res_2016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(v_00_u03b2_2008_, v_depth_boxed_2015_, v_keys_2010_, v_vals_2011_, v_heq_2012_, v_i_2013_, v_entries_2014_);
lean_dec_ref(v_vals_2011_);
lean_dec_ref(v_keys_2010_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18(lean_object* v_00_u03b2_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_x_2018_, v_x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22(lean_object* v_00_u03b2_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_x_2022_, v_x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26(lean_object* v_00_u03b2_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_x_2026_, v_x_2027_, v_x_2028_, v_x_2029_);
return v___x_2030_;
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

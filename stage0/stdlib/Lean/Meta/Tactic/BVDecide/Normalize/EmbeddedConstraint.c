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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
uint8_t v___x_77890__boxed_385_; lean_object* v_res_386_; 
v___x_77890__boxed_385_ = lean_unbox(v___x_370_);
v_res_386_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2(v___x_77890__boxed_385_, v___f_371_, v_____r_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
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
size_t v_x_78032__boxed_522_; lean_object* v_res_523_; 
v_x_78032__boxed_522_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_523_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_519_, v_x_78032__boxed_522_, v_x_521_);
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
uint8_t v___x_78187__boxed_561_; lean_object* v_res_562_; 
v___x_78187__boxed_561_ = lean_unbox(v___x_549_);
v_res_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0(v___x_78187__boxed_561_, v_x_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
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
lean_object* v_ref_635_; lean_object* v___x_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_681_; 
v_ref_635_ = lean_ctor_get(v___y_632_, 2);
v___x_636_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1_spec__1(v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_681_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_681_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_681_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v_traceState_642_; lean_object* v_env_643_; lean_object* v_nextMacroScope_644_; lean_object* v_ngen_645_; lean_object* v_auxDeclNGen_646_; lean_object* v_cache_647_; lean_object* v_messages_648_; lean_object* v_infoState_649_; lean_object* v_snapshotTasks_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_680_; 
v___x_641_ = lean_st_ref_take(v___y_633_);
v_traceState_642_ = lean_ctor_get(v___x_641_, 4);
v_env_643_ = lean_ctor_get(v___x_641_, 0);
v_nextMacroScope_644_ = lean_ctor_get(v___x_641_, 1);
v_ngen_645_ = lean_ctor_get(v___x_641_, 2);
v_auxDeclNGen_646_ = lean_ctor_get(v___x_641_, 3);
v_cache_647_ = lean_ctor_get(v___x_641_, 5);
v_messages_648_ = lean_ctor_get(v___x_641_, 6);
v_infoState_649_ = lean_ctor_get(v___x_641_, 7);
v_snapshotTasks_650_ = lean_ctor_get(v___x_641_, 8);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_680_ == 0)
{
v___x_652_ = v___x_641_;
v_isShared_653_ = v_isSharedCheck_680_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snapshotTasks_650_);
lean_inc(v_infoState_649_);
lean_inc(v_messages_648_);
lean_inc(v_cache_647_);
lean_inc(v_traceState_642_);
lean_inc(v_auxDeclNGen_646_);
lean_inc(v_ngen_645_);
lean_inc(v_nextMacroScope_644_);
lean_inc(v_env_643_);
lean_dec(v___x_641_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_680_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
uint64_t v_tid_654_; lean_object* v_traces_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_679_; 
v_tid_654_ = lean_ctor_get_uint64(v_traceState_642_, sizeof(void*)*1);
v_traces_655_ = lean_ctor_get(v_traceState_642_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v_traceState_642_);
if (v_isSharedCheck_679_ == 0)
{
v___x_657_ = v_traceState_642_;
v_isShared_658_ = v_isSharedCheck_679_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_traces_655_);
lean_dec(v_traceState_642_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_679_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; double v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_659_ = lean_box(0);
v___x_660_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__0);
v___x_661_ = 0;
v___x_662_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__1));
v___x_663_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_663_, 0, v_cls_628_);
lean_ctor_set(v___x_663_, 1, v___x_659_);
lean_ctor_set(v___x_663_, 2, v___x_662_);
lean_ctor_set_float(v___x_663_, sizeof(void*)*3, v___x_660_);
lean_ctor_set_float(v___x_663_, sizeof(void*)*3 + 8, v___x_660_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*3 + 16, v___x_661_);
v___x_664_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___closed__2));
v___x_665_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v_a_637_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
lean_inc(v_ref_635_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_ref_635_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_PersistentArray_push___redArg(v_traces_655_, v___x_666_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_667_);
v___x_669_ = v___x_657_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_667_);
lean_ctor_set_uint64(v_reuseFailAlloc_678_, sizeof(void*)*1, v_tid_654_);
v___x_669_ = v_reuseFailAlloc_678_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_671_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 4, v___x_669_);
v___x_671_ = v___x_652_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_env_643_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_nextMacroScope_644_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_ngen_645_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_auxDeclNGen_646_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_677_, 5, v_cache_647_);
lean_ctor_set(v_reuseFailAlloc_677_, 6, v_messages_648_);
lean_ctor_set(v_reuseFailAlloc_677_, 7, v_infoState_649_);
lean_ctor_set(v_reuseFailAlloc_677_, 8, v_snapshotTasks_650_);
v___x_671_ = v_reuseFailAlloc_677_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = lean_st_ref_put(v___y_633_, v___x_671_);
v___x_673_ = lean_box(0);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_673_);
v___x_675_ = v___x_639_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg___boxed(lean_object* v_cls_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_682_, v_msg_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v_res_689_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__4));
v___x_701_ = l_Lean_Name_append(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__6));
v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(lean_object* v_upperBound_705_, lean_object* v___x_706_, lean_object* v___x_707_, uint8_t v___x_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_a_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___y_727_; lean_object* v___y_750_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___x_780_; 
v___x_780_ = lean_nat_dec_lt(v_a_712_, v_upperBound_705_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_a_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_709_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v_b_713_);
return v___x_781_;
}
else
{
lean_object* v_snd_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_852_; 
v_snd_782_ = lean_ctor_get(v_b_713_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_b_713_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_b_713_, 0);
lean_dec(v_unused_853_);
v___x_784_ = v_b_713_;
v_isShared_785_ = v_isSharedCheck_852_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_snd_782_);
lean_dec(v_b_713_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_852_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___y_791_; lean_object* v___x_849_; 
v___x_786_ = lean_box(v___x_708_);
v___f_787_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_787_, 0, v___x_786_);
v___x_788_ = lean_box(0);
v___x_789_ = lean_array_fget_borrowed(v___x_706_, v_a_712_);
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v___x_710_, v_a_712_);
if (lean_obj_tag(v___x_849_) == 1)
{
lean_object* v_val_850_; lean_object* v___x_851_; 
v_val_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v___x_849_, 1);
lean_inc_ref(v___x_711_);
v___x_851_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v___x_711_, v_val_850_);
lean_dec(v_val_850_);
v___y_791_ = v___x_851_;
goto v___jp_790_;
}
else
{
lean_dec(v___x_849_);
lean_inc_ref(v___x_711_);
v___y_791_ = v___x_711_;
goto v___jp_790_;
}
v___jp_790_:
{
lean_object* v_type_792_; uint32_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_type_792_ = lean_ctor_get(v___x_789_, 1);
v___x_793_ = lean_uint32_of_nat(v___x_707_);
v___x_794_ = lean_box_uint32(v___x_793_);
v___x_795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___boxed), 13, 2);
lean_closure_set(v___x_795_, 0, v___x_794_);
lean_closure_set(v___x_795_, 1, v___y_791_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___f_787_);
lean_inc_ref(v_type_792_);
v___x_797_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_797_, 0, v_type_792_);
lean_inc_ref(v___x_709_);
v___x_798_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_797_, v___x_796_, v___x_709_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
lean_inc(v___x_789_);
v___x_800_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_789_, v_a_799_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v_type_802_; lean_object* v_value_803_; uint8_t v___x_804_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v_type_802_ = lean_ctor_get(v_a_801_, 1);
v_value_803_ = lean_ctor_get(v_a_801_, 2);
lean_inc_ref(v_type_802_);
v___x_804_ = l_Lean_Expr_isFalse(v_type_802_);
if (v___x_804_ == 0)
{
lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___f_807_; uint8_t v___x_808_; 
lean_del_object(v___x_784_);
lean_inc(v_a_801_);
lean_inc(v_snd_782_);
v___f_805_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_805_, 0, v_snd_782_);
lean_closure_set(v___f_805_, 1, v_a_801_);
lean_closure_set(v___f_805_, 2, v___x_788_);
v___x_806_ = lean_box(v___x_780_);
v___f_807_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__2___boxed), 15, 2);
lean_closure_set(v___f_807_, 0, v___x_806_);
lean_closure_set(v___f_807_, 1, v___f_805_);
v___x_808_ = lean_expr_eqv(v_type_792_, v_type_802_);
if (v___x_808_ == 0)
{
lean_inc_ref(v_type_802_);
lean_dec(v_a_801_);
lean_dec(v_snd_782_);
lean_inc_ref(v_type_792_);
v___y_754_ = v_type_802_;
v___y_755_ = v___f_807_;
v___y_756_ = v_type_792_;
goto v___jp_753_;
}
else
{
if (v___x_804_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v___f_807_);
v___x_809_ = lean_box(0);
v___x_810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___lam__1(v_snd_782_, v_a_801_, v___x_788_, v___x_809_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
v___y_727_ = v___x_810_;
goto v___jp_726_;
}
else
{
lean_inc_ref(v_type_802_);
lean_dec(v_a_801_);
lean_dec(v_snd_782_);
lean_inc_ref(v_type_792_);
v___y_754_ = v_type_802_;
v___y_755_ = v___f_807_;
v___y_756_ = v_type_792_;
goto v___jp_753_;
}
}
}
else
{
lean_object* v___x_811_; 
lean_inc_ref(v_value_803_);
lean_dec(v_a_801_);
lean_dec(v_a_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_709_);
v___x_811_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_803_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_823_; 
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_811_, 0);
lean_dec(v_unused_824_);
v___x_813_ = v___x_811_;
v_isShared_814_ = v_isSharedCheck_823_;
goto v_resetjp_812_;
}
else
{
lean_dec(v___x_811_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_823_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = lean_box(v___x_780_);
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_816_);
v___x_818_ = v___x_784_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_snd_782_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_818_);
v___x_820_ = v___x_813_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_del_object(v___x_784_);
lean_dec(v_snd_782_);
v_a_825_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_811_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_811_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_del_object(v___x_784_);
lean_dec(v_snd_782_);
lean_dec(v_a_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_709_);
v_a_833_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_800_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_800_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
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
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_del_object(v___x_784_);
lean_dec(v_snd_782_);
lean_dec(v_a_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_709_);
v_a_841_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_798_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_798_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
v___jp_726_:
{
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_740_; 
v_a_728_ = lean_ctor_get(v___y_727_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___y_727_);
if (v_isSharedCheck_740_ == 0)
{
v___x_730_ = v___y_727_;
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___y_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
if (lean_obj_tag(v_a_728_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; 
lean_dec(v_a_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_709_);
v_a_732_ = lean_ctor_get(v_a_728_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v_a_728_, 1);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v_a_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_del_object(v___x_730_);
v_a_736_ = lean_ctor_get(v_a_728_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v_a_728_, 1);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_a_712_, v___x_737_);
lean_dec(v_a_712_);
v_a_712_ = v___x_738_;
v_b_713_ = v_a_736_;
goto _start;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_709_);
v_a_741_ = lean_ctor_get(v___y_727_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___y_727_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___y_727_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___y_727_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
v___jp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_box(0);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
v___x_752_ = lean_apply_13(v___y_750_, v___x_751_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, lean_box(0));
v___y_727_ = v___x_752_;
goto v___jp_726_;
}
v___jp_753_:
{
lean_object* v_toCold_757_; lean_object* v_options_758_; uint8_t v_hasTrace_759_; 
v_toCold_757_ = lean_ctor_get(v___y_723_, 0);
v_options_758_ = lean_ctor_get(v_toCold_757_, 2);
v_hasTrace_759_ = lean_ctor_get_uint8(v_options_758_, sizeof(void*)*1);
if (v_hasTrace_759_ == 0)
{
lean_dec_ref(v___y_756_);
lean_dec_ref(v___y_754_);
v___y_750_ = v___y_755_;
goto v___jp_749_;
}
else
{
lean_object* v_inheritedTraceOptions_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_inheritedTraceOptions_760_ = lean_ctor_get(v_toCold_757_, 11);
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_762_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_760_, v_options_758_, v___x_762_);
if (v___x_763_ == 0)
{
lean_dec_ref(v___y_756_);
lean_dec_ref(v___y_754_);
v___y_750_ = v___y_755_;
goto v___jp_749_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_764_ = l_Lean_MessageData_ofExpr(v___y_756_);
v___x_765_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__7);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_MessageData_ofExpr(v___y_754_);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_761_, v___x_768_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
v___x_771_ = lean_apply_13(v___y_755_, v_a_770_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, lean_box(0));
v___y_727_ = v___x_771_;
goto v___jp_726_;
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v___y_755_);
lean_dec(v_a_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_709_);
v_a_772_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_769_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_769_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_854_ = _args[0];
lean_object* v___x_855_ = _args[1];
lean_object* v___x_856_ = _args[2];
lean_object* v___x_857_ = _args[3];
lean_object* v___x_858_ = _args[4];
lean_object* v___x_859_ = _args[5];
lean_object* v___x_860_ = _args[6];
lean_object* v_a_861_ = _args[7];
lean_object* v_b_862_ = _args[8];
lean_object* v___y_863_ = _args[9];
lean_object* v___y_864_ = _args[10];
lean_object* v___y_865_ = _args[11];
lean_object* v___y_866_ = _args[12];
lean_object* v___y_867_ = _args[13];
lean_object* v___y_868_ = _args[14];
lean_object* v___y_869_ = _args[15];
lean_object* v___y_870_ = _args[16];
lean_object* v___y_871_ = _args[17];
lean_object* v___y_872_ = _args[18];
lean_object* v___y_873_ = _args[19];
lean_object* v___y_874_ = _args[20];
_start:
{
uint8_t v___x_78440__boxed_875_; lean_object* v_res_876_; 
v___x_78440__boxed_875_ = lean_unbox(v___x_857_);
v_res_876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_854_, v___x_855_, v___x_856_, v___x_78440__boxed_875_, v___x_858_, v___x_859_, v___x_860_, v_a_861_, v_b_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v___x_859_);
lean_dec(v___x_856_);
lean_dec_ref(v___x_855_);
lean_dec(v_upperBound_854_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(lean_object* v_a_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
uint8_t v___x_879_; 
v___x_879_ = 0;
return v___x_879_;
}
else
{
lean_object* v_key_880_; lean_object* v_tail_881_; size_t v___x_882_; size_t v___x_883_; uint8_t v___x_884_; 
v_key_880_ = lean_ctor_get(v_x_878_, 0);
v_tail_881_ = lean_ctor_get(v_x_878_, 2);
v___x_882_ = lean_ptr_addr(v_key_880_);
v___x_883_ = lean_ptr_addr(v_a_877_);
v___x_884_ = lean_usize_dec_eq(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
v_x_878_ = v_tail_881_;
goto _start;
}
else
{
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg___boxed(lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec_ref(v_a_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(lean_object* v_m_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_buckets_892_; lean_object* v___x_893_; size_t v___x_894_; size_t v___x_895_; size_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v_fold_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; size_t v___x_904_; size_t v___x_905_; size_t v___x_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_buckets_892_ = lean_ctor_get(v_m_890_, 1);
v___x_893_ = lean_array_get_size(v_buckets_892_);
v___x_894_ = lean_ptr_addr(v_a_891_);
v___x_895_ = ((size_t)3ULL);
v___x_896_ = lean_usize_shift_right(v___x_894_, v___x_895_);
v___x_897_ = lean_usize_to_uint64(v___x_896_);
v___x_898_ = 32ULL;
v___x_899_ = lean_uint64_shift_right(v___x_897_, v___x_898_);
v_fold_900_ = lean_uint64_xor(v___x_897_, v___x_899_);
v___x_901_ = 16ULL;
v___x_902_ = lean_uint64_shift_right(v_fold_900_, v___x_901_);
v___x_903_ = lean_uint64_xor(v_fold_900_, v___x_902_);
v___x_904_ = lean_uint64_to_usize(v___x_903_);
v___x_905_ = lean_usize_of_nat(v___x_893_);
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_sub(v___x_905_, v___x_906_);
v___x_908_ = lean_usize_land(v___x_904_, v___x_907_);
v___x_909_ = lean_array_uget_borrowed(v_buckets_892_, v___x_908_);
v___x_910_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_891_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg___boxed(lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_911_, v_a_912_);
lean_dec_ref(v_a_912_);
lean_dec_ref(v_m_911_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(lean_object* v_arg_915_, lean_object* v_x_916_){
_start:
{
uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = 0;
v___x_918_ = lean_box(v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_arg_915_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
return v_x_920_;
}
else
{
lean_object* v_key_922_; lean_object* v_value_923_; lean_object* v_tail_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_947_; 
v_key_922_ = lean_ctor_get(v_x_921_, 0);
v_value_923_ = lean_ctor_get(v_x_921_, 1);
v_tail_924_ = lean_ctor_get(v_x_921_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_921_);
if (v_isSharedCheck_947_ == 0)
{
v___x_926_ = v_x_921_;
v_isShared_927_ = v_isSharedCheck_947_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_tail_924_);
lean_inc(v_value_923_);
lean_inc(v_key_922_);
lean_dec(v_x_921_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_947_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v_fold_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_928_ = lean_array_get_size(v_x_920_);
v___x_929_ = lean_uint64_of_nat(v_key_922_);
v___x_930_ = 32ULL;
v___x_931_ = lean_uint64_shift_right(v___x_929_, v___x_930_);
v_fold_932_ = lean_uint64_xor(v___x_929_, v___x_931_);
v___x_933_ = 16ULL;
v___x_934_ = lean_uint64_shift_right(v_fold_932_, v___x_933_);
v___x_935_ = lean_uint64_xor(v_fold_932_, v___x_934_);
v___x_936_ = lean_uint64_to_usize(v___x_935_);
v___x_937_ = lean_usize_of_nat(v___x_928_);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_sub(v___x_937_, v___x_938_);
v___x_940_ = lean_usize_land(v___x_936_, v___x_939_);
v___x_941_ = lean_array_uget_borrowed(v_x_920_, v___x_940_);
lean_inc(v___x_941_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 2, v___x_941_);
v___x_943_ = v___x_926_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_key_922_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_value_923_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v___x_941_);
v___x_943_ = v_reuseFailAlloc_946_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_array_uset(v_x_920_, v___x_940_, v___x_943_);
v_x_920_ = v___x_944_;
v_x_921_ = v_tail_924_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(lean_object* v_i_948_, lean_object* v_source_949_, lean_object* v_target_950_){
_start:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_array_get_size(v_source_949_);
v___x_952_ = lean_nat_dec_lt(v_i_948_, v___x_951_);
if (v___x_952_ == 0)
{
lean_dec_ref(v_source_949_);
lean_dec(v_i_948_);
return v_target_950_;
}
else
{
lean_object* v_es_953_; lean_object* v___x_954_; lean_object* v_source_955_; lean_object* v_target_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_es_953_ = lean_array_fget(v_source_949_, v_i_948_);
v___x_954_ = lean_box(0);
v_source_955_ = lean_array_fset(v_source_949_, v_i_948_, v___x_954_);
v_target_956_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_target_950_, v_es_953_);
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_add(v_i_948_, v___x_957_);
lean_dec(v_i_948_);
v_i_948_ = v___x_958_;
v_source_949_ = v_source_955_;
v_target_950_ = v_target_956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(lean_object* v_data_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_nbuckets_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_961_ = lean_array_get_size(v_data_960_);
v___x_962_ = lean_unsigned_to_nat(2u);
v_nbuckets_963_ = lean_nat_mul(v___x_961_, v___x_962_);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_box(0);
v___x_966_ = lean_mk_array(v_nbuckets_963_, v___x_965_);
v___x_967_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v___x_964_, v_data_960_, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(lean_object* v_a_968_, lean_object* v_x_969_){
_start:
{
if (lean_obj_tag(v_x_969_) == 0)
{
uint8_t v___x_970_; 
v___x_970_ = 0;
return v___x_970_;
}
else
{
lean_object* v_key_971_; lean_object* v_tail_972_; uint8_t v___x_973_; 
v_key_971_ = lean_ctor_get(v_x_969_, 0);
v_tail_972_ = lean_ctor_get(v_x_969_, 2);
v___x_973_ = lean_nat_dec_eq(v_key_971_, v_a_968_);
if (v___x_973_ == 0)
{
v_x_969_ = v_tail_972_;
goto _start;
}
else
{
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg___boxed(lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_975_, v_x_976_);
lean_dec(v_x_976_);
lean_dec(v_a_975_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(lean_object* v_a_979_, lean_object* v_b_980_, lean_object* v_x_981_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
lean_dec(v_b_980_);
lean_dec(v_a_979_);
return v_x_981_;
}
else
{
lean_object* v_key_982_; lean_object* v_value_983_; lean_object* v_tail_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_996_; 
v_key_982_ = lean_ctor_get(v_x_981_, 0);
v_value_983_ = lean_ctor_get(v_x_981_, 1);
v_tail_984_ = lean_ctor_get(v_x_981_, 2);
v_isSharedCheck_996_ = !lean_is_exclusive(v_x_981_);
if (v_isSharedCheck_996_ == 0)
{
v___x_986_ = v_x_981_;
v_isShared_987_ = v_isSharedCheck_996_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_tail_984_);
lean_inc(v_value_983_);
lean_inc(v_key_982_);
lean_dec(v_x_981_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_996_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v___x_988_; 
v___x_988_ = lean_nat_dec_eq(v_key_982_, v_a_979_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_979_, v_b_980_, v_tail_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 2, v___x_989_);
v___x_991_ = v___x_986_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_key_982_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_value_983_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
lean_object* v___x_994_; 
lean_dec(v_value_983_);
lean_dec(v_key_982_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_b_980_);
lean_ctor_set(v___x_986_, 0, v_a_979_);
v___x_994_ = v___x_986_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_979_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_b_980_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_tail_984_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(lean_object* v_m_997_, lean_object* v_a_998_, lean_object* v_b_999_){
_start:
{
lean_object* v_size_1000_; lean_object* v_buckets_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1044_; 
v_size_1000_ = lean_ctor_get(v_m_997_, 0);
v_buckets_1001_ = lean_ctor_get(v_m_997_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_m_997_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1003_ = v_m_997_;
v_isShared_1004_ = v_isSharedCheck_1044_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_buckets_1001_);
lean_inc(v_size_1000_);
lean_dec(v_m_997_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1044_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; uint64_t v___x_1006_; uint64_t v___x_1007_; uint64_t v___x_1008_; uint64_t v_fold_1009_; uint64_t v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; lean_object* v_bkt_1018_; uint8_t v___x_1019_; 
v___x_1005_ = lean_array_get_size(v_buckets_1001_);
v___x_1006_ = lean_uint64_of_nat(v_a_998_);
v___x_1007_ = 32ULL;
v___x_1008_ = lean_uint64_shift_right(v___x_1006_, v___x_1007_);
v_fold_1009_ = lean_uint64_xor(v___x_1006_, v___x_1008_);
v___x_1010_ = 16ULL;
v___x_1011_ = lean_uint64_shift_right(v_fold_1009_, v___x_1010_);
v___x_1012_ = lean_uint64_xor(v_fold_1009_, v___x_1011_);
v___x_1013_ = lean_uint64_to_usize(v___x_1012_);
v___x_1014_ = lean_usize_of_nat(v___x_1005_);
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_sub(v___x_1014_, v___x_1015_);
v___x_1017_ = lean_usize_land(v___x_1013_, v___x_1016_);
v_bkt_1018_ = lean_array_uget_borrowed(v_buckets_1001_, v___x_1017_);
v___x_1019_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_998_, v_bkt_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v_size_x27_1021_; lean_object* v___x_1022_; lean_object* v_buckets_x27_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v_size_x27_1021_ = lean_nat_add(v_size_1000_, v___x_1020_);
lean_dec(v_size_1000_);
lean_inc(v_bkt_1018_);
v___x_1022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1022_, 0, v_a_998_);
lean_ctor_set(v___x_1022_, 1, v_b_999_);
lean_ctor_set(v___x_1022_, 2, v_bkt_1018_);
v_buckets_x27_1023_ = lean_array_uset(v_buckets_1001_, v___x_1017_, v___x_1022_);
v___x_1024_ = lean_unsigned_to_nat(4u);
v___x_1025_ = lean_nat_mul(v_size_x27_1021_, v___x_1024_);
v___x_1026_ = lean_unsigned_to_nat(3u);
v___x_1027_ = lean_nat_div(v___x_1025_, v___x_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_array_get_size(v_buckets_x27_1023_);
v___x_1029_ = lean_nat_dec_le(v___x_1027_, v___x_1028_);
lean_dec(v___x_1027_);
if (v___x_1029_ == 0)
{
lean_object* v_val_1030_; lean_object* v___x_1032_; 
v_val_1030_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_buckets_x27_1023_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v_val_1030_);
lean_ctor_set(v___x_1003_, 0, v_size_x27_1021_);
v___x_1032_ = v___x_1003_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_size_x27_1021_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_val_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1035_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v_buckets_x27_1023_);
lean_ctor_set(v___x_1003_, 0, v_size_x27_1021_);
v___x_1035_ = v___x_1003_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_size_x27_1021_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_buckets_x27_1023_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v_buckets_x27_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
lean_inc(v_bkt_1018_);
v___x_1037_ = lean_box(0);
v_buckets_x27_1038_ = lean_array_uset(v_buckets_1001_, v___x_1017_, v___x_1037_);
v___x_1039_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_998_, v_b_999_, v_bkt_1018_);
v___x_1040_ = lean_array_uset(v_buckets_x27_1038_, v___x_1017_, v___x_1039_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1040_);
v___x_1042_ = v___x_1003_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_size_1000_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
if (lean_obj_tag(v_x_1046_) == 0)
{
return v_x_1045_;
}
else
{
lean_object* v_key_1047_; lean_object* v_value_1048_; lean_object* v_tail_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1075_; 
v_key_1047_ = lean_ctor_get(v_x_1046_, 0);
v_value_1048_ = lean_ctor_get(v_x_1046_, 1);
v_tail_1049_ = lean_ctor_get(v_x_1046_, 2);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_x_1046_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1051_ = v_x_1046_;
v_isShared_1052_ = v_isSharedCheck_1075_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_tail_1049_);
lean_inc(v_value_1048_);
lean_inc(v_key_1047_);
lean_dec(v_x_1046_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1075_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; uint64_t v___x_1057_; uint64_t v___x_1058_; uint64_t v___x_1059_; uint64_t v_fold_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1053_ = lean_array_get_size(v_x_1045_);
v___x_1054_ = lean_ptr_addr(v_key_1047_);
v___x_1055_ = ((size_t)3ULL);
v___x_1056_ = lean_usize_shift_right(v___x_1054_, v___x_1055_);
v___x_1057_ = lean_usize_to_uint64(v___x_1056_);
v___x_1058_ = 32ULL;
v___x_1059_ = lean_uint64_shift_right(v___x_1057_, v___x_1058_);
v_fold_1060_ = lean_uint64_xor(v___x_1057_, v___x_1059_);
v___x_1061_ = 16ULL;
v___x_1062_ = lean_uint64_shift_right(v_fold_1060_, v___x_1061_);
v___x_1063_ = lean_uint64_xor(v_fold_1060_, v___x_1062_);
v___x_1064_ = lean_uint64_to_usize(v___x_1063_);
v___x_1065_ = lean_usize_of_nat(v___x_1053_);
v___x_1066_ = ((size_t)1ULL);
v___x_1067_ = lean_usize_sub(v___x_1065_, v___x_1066_);
v___x_1068_ = lean_usize_land(v___x_1064_, v___x_1067_);
v___x_1069_ = lean_array_uget_borrowed(v_x_1045_, v___x_1068_);
lean_inc(v___x_1069_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 2, v___x_1069_);
v___x_1071_ = v___x_1051_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_key_1047_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_value_1048_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_array_uset(v_x_1045_, v___x_1068_, v___x_1071_);
v_x_1045_ = v___x_1072_;
v_x_1046_ = v_tail_1049_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(lean_object* v_i_1076_, lean_object* v_source_1077_, lean_object* v_target_1078_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_array_get_size(v_source_1077_);
v___x_1080_ = lean_nat_dec_lt(v_i_1076_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v_source_1077_);
lean_dec(v_i_1076_);
return v_target_1078_;
}
else
{
lean_object* v_es_1081_; lean_object* v___x_1082_; lean_object* v_source_1083_; lean_object* v_target_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_es_1081_ = lean_array_fget(v_source_1077_, v_i_1076_);
v___x_1082_ = lean_box(0);
v_source_1083_ = lean_array_fset(v_source_1077_, v_i_1076_, v___x_1082_);
v_target_1084_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_target_1078_, v_es_1081_);
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_nat_add(v_i_1076_, v___x_1085_);
lean_dec(v_i_1076_);
v_i_1076_ = v___x_1086_;
v_source_1077_ = v_source_1083_;
v_target_1078_ = v_target_1084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(lean_object* v_data_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_nbuckets_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1089_ = lean_array_get_size(v_data_1088_);
v___x_1090_ = lean_unsigned_to_nat(2u);
v_nbuckets_1091_ = lean_nat_mul(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_mk_array(v_nbuckets_1091_, v___x_1093_);
v___x_1095_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v___x_1092_, v_data_1088_, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(lean_object* v_m_1096_, lean_object* v_a_1097_, lean_object* v_b_1098_){
_start:
{
lean_object* v_size_1099_; lean_object* v_buckets_1100_; lean_object* v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v_fold_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; lean_object* v_bkt_1117_; uint8_t v___x_1118_; 
v_size_1099_ = lean_ctor_get(v_m_1096_, 0);
v_buckets_1100_ = lean_ctor_get(v_m_1096_, 1);
v___x_1101_ = lean_array_get_size(v_buckets_1100_);
v___x_1102_ = lean_ptr_addr(v_a_1097_);
v___x_1103_ = ((size_t)3ULL);
v___x_1104_ = lean_usize_shift_right(v___x_1102_, v___x_1103_);
v___x_1105_ = lean_usize_to_uint64(v___x_1104_);
v___x_1106_ = 32ULL;
v___x_1107_ = lean_uint64_shift_right(v___x_1105_, v___x_1106_);
v_fold_1108_ = lean_uint64_xor(v___x_1105_, v___x_1107_);
v___x_1109_ = 16ULL;
v___x_1110_ = lean_uint64_shift_right(v_fold_1108_, v___x_1109_);
v___x_1111_ = lean_uint64_xor(v_fold_1108_, v___x_1110_);
v___x_1112_ = lean_uint64_to_usize(v___x_1111_);
v___x_1113_ = lean_usize_of_nat(v___x_1101_);
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_sub(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_usize_land(v___x_1112_, v___x_1115_);
v_bkt_1117_ = lean_array_uget_borrowed(v_buckets_1100_, v___x_1116_);
v___x_1118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1097_, v_bkt_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1139_; 
lean_inc_ref(v_buckets_1100_);
lean_inc(v_size_1099_);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_m_1096_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; lean_object* v_unused_1141_; 
v_unused_1140_ = lean_ctor_get(v_m_1096_, 1);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_m_1096_, 0);
lean_dec(v_unused_1141_);
v___x_1120_ = v_m_1096_;
v_isShared_1121_ = v_isSharedCheck_1139_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v_m_1096_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1139_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v_size_x27_1123_; lean_object* v___x_1124_; lean_object* v_buckets_x27_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v_size_x27_1123_ = lean_nat_add(v_size_1099_, v___x_1122_);
lean_dec(v_size_1099_);
lean_inc(v_bkt_1117_);
v___x_1124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1097_);
lean_ctor_set(v___x_1124_, 1, v_b_1098_);
lean_ctor_set(v___x_1124_, 2, v_bkt_1117_);
v_buckets_x27_1125_ = lean_array_uset(v_buckets_1100_, v___x_1116_, v___x_1124_);
v___x_1126_ = lean_unsigned_to_nat(4u);
v___x_1127_ = lean_nat_mul(v_size_x27_1123_, v___x_1126_);
v___x_1128_ = lean_unsigned_to_nat(3u);
v___x_1129_ = lean_nat_div(v___x_1127_, v___x_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_array_get_size(v_buckets_x27_1125_);
v___x_1131_ = lean_nat_dec_le(v___x_1129_, v___x_1130_);
lean_dec(v___x_1129_);
if (v___x_1131_ == 0)
{
lean_object* v_val_1132_; lean_object* v___x_1134_; 
v_val_1132_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_buckets_x27_1125_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v_val_1132_);
lean_ctor_set(v___x_1120_, 0, v_size_x27_1123_);
v___x_1134_ = v___x_1120_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_size_x27_1123_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_val_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v___x_1137_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v_buckets_x27_1125_);
lean_ctor_set(v___x_1120_, 0, v_size_x27_1123_);
v___x_1137_ = v___x_1120_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_size_x27_1123_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_buckets_x27_1125_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_dec(v_b_1098_);
lean_dec_ref(v_a_1097_);
return v_m_1096_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(lean_object* v_fst_1142_, lean_object* v_snd_1143_, lean_object* v_fst_1144_, lean_object* v_fst_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_fst_1142_);
lean_ctor_set(v___x_1159_, 1, v_snd_1143_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_fst_1144_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_fst_1145_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_1164_ = _args[0];
lean_object* v_snd_1165_ = _args[1];
lean_object* v_fst_1166_ = _args[2];
lean_object* v_fst_1167_ = _args[3];
lean_object* v_x_1168_ = _args[4];
lean_object* v___y_1169_ = _args[5];
lean_object* v___y_1170_ = _args[6];
lean_object* v___y_1171_ = _args[7];
lean_object* v___y_1172_ = _args[8];
lean_object* v___y_1173_ = _args[9];
lean_object* v___y_1174_ = _args[10];
lean_object* v___y_1175_ = _args[11];
lean_object* v___y_1176_ = _args[12];
lean_object* v___y_1177_ = _args[13];
lean_object* v___y_1178_ = _args[14];
lean_object* v___y_1179_ = _args[15];
lean_object* v___y_1180_ = _args[16];
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1164_, v_snd_1165_, v_fst_1166_, v_fst_1167_, v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v_ks_1186_; lean_object* v_vs_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1213_; 
v_ks_1186_ = lean_ctor_get(v_x_1182_, 0);
v_vs_1187_ = lean_ctor_get(v_x_1182_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1189_ = v_x_1182_;
v_isShared_1190_ = v_isSharedCheck_1213_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_vs_1187_);
lean_inc(v_ks_1186_);
lean_dec(v_x_1182_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1213_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_array_get_size(v_ks_1186_);
v___x_1192_ = lean_nat_dec_lt(v_x_1183_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec(v_x_1183_);
v___x_1193_ = lean_array_push(v_ks_1186_, v_x_1184_);
v___x_1194_ = lean_array_push(v_vs_1187_, v_x_1185_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1194_);
lean_ctor_set(v___x_1189_, 0, v___x_1193_);
v___x_1196_ = v___x_1189_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v_k_x27_1198_; size_t v___x_1199_; size_t v___x_1200_; uint8_t v___x_1201_; 
v_k_x27_1198_ = lean_array_fget_borrowed(v_ks_1186_, v_x_1183_);
v___x_1199_ = lean_ptr_addr(v_x_1184_);
v___x_1200_ = lean_ptr_addr(v_k_x27_1198_);
v___x_1201_ = lean_usize_dec_eq(v___x_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1203_; 
if (v_isShared_1190_ == 0)
{
v___x_1203_ = v___x_1189_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_ks_1186_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_vs_1187_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_add(v_x_1183_, v___x_1204_);
lean_dec(v_x_1183_);
v_x_1182_ = v___x_1203_;
v_x_1183_ = v___x_1205_;
goto _start;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1208_ = lean_array_fset(v_ks_1186_, v_x_1183_, v_x_1184_);
v___x_1209_ = lean_array_fset(v_vs_1187_, v_x_1183_, v_x_1185_);
lean_dec(v_x_1183_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1209_);
lean_ctor_set(v___x_1189_, 0, v___x_1208_);
v___x_1211_ = v___x_1189_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(lean_object* v_n_1214_, lean_object* v_k_1215_, lean_object* v_v_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_n_1214_, v___x_1217_, v_k_1215_, v_v_1216_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(lean_object* v_x_1220_, size_t v_x_1221_, size_t v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
lean_object* v_es_1225_; size_t v___x_1226_; size_t v___x_1227_; lean_object* v_j_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_es_1225_ = lean_ctor_get(v_x_1220_, 0);
v___x_1226_ = ((size_t)31ULL);
v___x_1227_ = lean_usize_land(v_x_1221_, v___x_1226_);
v_j_1228_ = lean_usize_to_nat(v___x_1227_);
v___x_1229_ = lean_array_get_size(v_es_1225_);
v___x_1230_ = lean_nat_dec_lt(v_j_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_dec(v_j_1228_);
lean_dec(v_x_1224_);
lean_dec_ref(v_x_1223_);
return v_x_1220_;
}
else
{
lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1271_; 
lean_inc_ref(v_es_1225_);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_x_1220_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_x_1220_, 0);
lean_dec(v_unused_1272_);
v___x_1232_ = v_x_1220_;
v_isShared_1233_ = v_isSharedCheck_1271_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v_x_1220_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1271_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_v_1234_; lean_object* v___x_1235_; lean_object* v_xs_x27_1236_; lean_object* v___y_1238_; 
v_v_1234_ = lean_array_fget(v_es_1225_, v_j_1228_);
v___x_1235_ = lean_box(0);
v_xs_x27_1236_ = lean_array_fset(v_es_1225_, v_j_1228_, v___x_1235_);
switch(lean_obj_tag(v_v_1234_))
{
case 0:
{
lean_object* v_key_1243_; lean_object* v_val_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1256_; 
v_key_1243_ = lean_ctor_get(v_v_1234_, 0);
v_val_1244_ = lean_ctor_get(v_v_1234_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_v_1234_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1246_ = v_v_1234_;
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_val_1244_);
lean_inc(v_key_1243_);
lean_dec(v_v_1234_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
size_t v___x_1248_; size_t v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = lean_ptr_addr(v_x_1223_);
v___x_1249_ = lean_ptr_addr(v_key_1243_);
v___x_1250_ = lean_usize_dec_eq(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_del_object(v___x_1246_);
v___x_1251_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1243_, v_val_1244_, v_x_1223_, v_x_1224_);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
v___y_1238_ = v___x_1252_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_val_1244_);
lean_dec(v_key_1243_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_x_1224_);
lean_ctor_set(v___x_1246_, 0, v_x_1223_);
v___x_1254_ = v___x_1246_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_x_1223_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_x_1224_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
v___y_1238_ = v___x_1254_;
goto v___jp_1237_;
}
}
}
}
case 1:
{
lean_object* v_node_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v_node_1257_ = lean_ctor_get(v_v_1234_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_v_1234_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1259_ = v_v_1234_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_node_1257_);
lean_dec(v_v_1234_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1261_ = ((size_t)5ULL);
v___x_1262_ = lean_usize_shift_right(v_x_1221_, v___x_1261_);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_x_1222_, v___x_1263_);
v___x_1265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_node_1257_, v___x_1262_, v___x_1264_, v_x_1223_, v_x_1224_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1265_);
v___x_1267_ = v___x_1259_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v___y_1238_ = v___x_1267_;
goto v___jp_1237_;
}
}
}
default: 
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_x_1223_);
lean_ctor_set(v___x_1270_, 1, v_x_1224_);
v___y_1238_ = v___x_1270_;
goto v___jp_1237_;
}
}
v___jp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_array_fset(v_xs_x27_1236_, v_j_1228_, v___y_1238_);
lean_dec(v_j_1228_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1239_);
v___x_1241_ = v___x_1232_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
else
{
lean_object* v_ks_1273_; lean_object* v_vs_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1292_; 
v_ks_1273_ = lean_ctor_get(v_x_1220_, 0);
v_vs_1274_ = lean_ctor_get(v_x_1220_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1220_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1276_ = v_x_1220_;
v_isShared_1277_ = v_isSharedCheck_1292_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_vs_1274_);
lean_inc(v_ks_1273_);
lean_dec(v_x_1220_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1292_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_ks_1273_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_vs_1274_);
v___x_1279_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v_newNode_1280_; size_t v___x_1281_; uint8_t v___x_1282_; 
v_newNode_1280_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v___x_1279_, v_x_1223_, v_x_1224_);
v___x_1281_ = ((size_t)7ULL);
v___x_1282_ = lean_usize_dec_le(v___x_1281_, v_x_1222_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1283_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1280_);
v___x_1284_ = lean_unsigned_to_nat(4u);
v___x_1285_ = lean_nat_dec_lt(v___x_1283_, v___x_1284_);
lean_dec(v___x_1283_);
if (v___x_1285_ == 0)
{
lean_object* v_ks_1286_; lean_object* v_vs_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_ks_1286_ = lean_ctor_get(v_newNode_1280_, 0);
lean_inc_ref(v_ks_1286_);
v_vs_1287_ = lean_ctor_get(v_newNode_1280_, 1);
lean_inc_ref(v_vs_1287_);
lean_dec_ref(v_newNode_1280_);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___closed__0);
v___x_1290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_x_1222_, v_ks_1286_, v_vs_1287_, v___x_1288_, v___x_1289_);
lean_dec_ref(v_vs_1287_);
lean_dec_ref(v_ks_1286_);
return v___x_1290_;
}
else
{
return v_newNode_1280_;
}
}
else
{
return v_newNode_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(size_t v_depth_1293_, lean_object* v_keys_1294_, lean_object* v_vals_1295_, lean_object* v_i_1296_, lean_object* v_entries_1297_){
_start:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_array_get_size(v_keys_1294_);
v___x_1299_ = lean_nat_dec_lt(v_i_1296_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec(v_i_1296_);
return v_entries_1297_;
}
else
{
lean_object* v_k_1300_; lean_object* v_v_1301_; size_t v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; uint64_t v___x_1305_; size_t v_h_1306_; size_t v___x_1307_; lean_object* v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; size_t v_h_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_k_1300_ = lean_array_fget_borrowed(v_keys_1294_, v_i_1296_);
v_v_1301_ = lean_array_fget_borrowed(v_vals_1295_, v_i_1296_);
v___x_1302_ = lean_ptr_addr(v_k_1300_);
v___x_1303_ = ((size_t)3ULL);
v___x_1304_ = lean_usize_shift_right(v___x_1302_, v___x_1303_);
v___x_1305_ = lean_usize_to_uint64(v___x_1304_);
v_h_1306_ = lean_uint64_to_usize(v___x_1305_);
v___x_1307_ = ((size_t)5ULL);
v___x_1308_ = lean_unsigned_to_nat(1u);
v___x_1309_ = ((size_t)1ULL);
v___x_1310_ = lean_usize_sub(v_depth_1293_, v___x_1309_);
v___x_1311_ = lean_usize_mul(v___x_1307_, v___x_1310_);
v_h_1312_ = lean_usize_shift_right(v_h_1306_, v___x_1311_);
v___x_1313_ = lean_nat_add(v_i_1296_, v___x_1308_);
lean_dec(v_i_1296_);
lean_inc(v_v_1301_);
lean_inc(v_k_1300_);
v___x_1314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_entries_1297_, v_h_1312_, v_depth_1293_, v_k_1300_, v_v_1301_);
v_i_1296_ = v___x_1313_;
v_entries_1297_ = v___x_1314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg___boxed(lean_object* v_depth_1316_, lean_object* v_keys_1317_, lean_object* v_vals_1318_, lean_object* v_i_1319_, lean_object* v_entries_1320_){
_start:
{
size_t v_depth_boxed_1321_; lean_object* v_res_1322_; 
v_depth_boxed_1321_ = lean_unbox_usize(v_depth_1316_);
lean_dec(v_depth_1316_);
v_res_1322_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_boxed_1321_, v_keys_1317_, v_vals_1318_, v_i_1319_, v_entries_1320_);
lean_dec_ref(v_vals_1318_);
lean_dec_ref(v_keys_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg___boxed(lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
size_t v_x_79314__boxed_1328_; size_t v_x_79315__boxed_1329_; lean_object* v_res_1330_; 
v_x_79314__boxed_1328_ = lean_unbox_usize(v_x_1324_);
lean_dec(v_x_1324_);
v_x_79315__boxed_1329_ = lean_unbox_usize(v_x_1325_);
lean_dec(v_x_1325_);
v_res_1330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1323_, v_x_79314__boxed_1328_, v_x_79315__boxed_1329_, v_x_1326_, v_x_1327_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; uint64_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; 
v___x_1334_ = lean_ptr_addr(v_x_1332_);
v___x_1335_ = ((size_t)3ULL);
v___x_1336_ = lean_usize_shift_right(v___x_1334_, v___x_1335_);
v___x_1337_ = lean_usize_to_uint64(v___x_1336_);
v___x_1338_ = lean_uint64_to_usize(v___x_1337_);
v___x_1339_ = ((size_t)1ULL);
v___x_1340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1331_, v___x_1338_, v___x_1339_, v_x_1332_, v_x_1333_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(lean_object* v_upperBound_1348_, lean_object* v___x_1349_, lean_object* v_a_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_a_1365_; lean_object* v___y_1370_; uint8_t v___x_1389_; 
v___x_1389_ = lean_nat_dec_lt(v_a_1350_, v_upperBound_1348_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_a_1350_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_b_1351_);
return v___x_1390_;
}
else
{
lean_object* v_snd_1391_; lean_object* v_snd_1392_; lean_object* v_fst_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1483_; 
v_snd_1391_ = lean_ctor_get(v_b_1351_, 1);
lean_inc(v_snd_1391_);
v_snd_1392_ = lean_ctor_get(v_snd_1391_, 1);
lean_inc(v_snd_1392_);
v_fst_1393_ = lean_ctor_get(v_b_1351_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_b_1351_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v_b_1351_, 1);
lean_dec(v_unused_1484_);
v___x_1395_ = v_b_1351_;
v_isShared_1396_ = v_isSharedCheck_1483_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_fst_1393_);
lean_dec(v_b_1351_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1483_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_fst_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1481_; 
v_fst_1397_ = lean_ctor_get(v_snd_1391_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_snd_1391_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_snd_1391_, 1);
lean_dec(v_unused_1482_);
v___x_1399_ = v_snd_1391_;
v_isShared_1400_ = v_isSharedCheck_1481_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_fst_1397_);
lean_dec(v_snd_1391_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1481_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1480_; 
v_fst_1401_ = lean_ctor_get(v_snd_1392_, 0);
v_snd_1402_ = lean_ctor_get(v_snd_1392_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_snd_1392_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1404_ = v_snd_1392_;
v_isShared_1405_ = v_isSharedCheck_1480_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1401_);
lean_dec(v_snd_1392_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1480_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1416_; lean_object* v_type_1417_; lean_object* v_value_1418_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1416_ = lean_array_fget_borrowed(v___x_1349_, v_a_1350_);
v_type_1417_ = lean_ctor_get(v___x_1416_, 1);
v_value_1418_ = lean_ctor_get(v___x_1416_, 2);
lean_inc_ref(v_type_1417_);
v___x_1430_ = l_Lean_Expr_cleanupAnnotations(v_type_1417_);
v___x_1431_ = l_Lean_Expr_isApp(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v___x_1430_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1399_);
lean_del_object(v___x_1395_);
v___x_1432_ = lean_box(0);
v___x_1433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1401_, v_snd_1402_, v_fst_1397_, v_fst_1393_, v___x_1432_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
v___y_1370_ = v___x_1433_;
goto v___jp_1369_;
}
else
{
lean_object* v_arg_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v_arg_1434_ = lean_ctor_get(v___x_1430_, 1);
lean_inc_ref(v_arg_1434_);
v___x_1435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1430_);
v___x_1436_ = l_Lean_Expr_isApp(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v___x_1435_);
lean_dec_ref(v_arg_1434_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1399_);
lean_del_object(v___x_1395_);
v___x_1437_ = lean_box(0);
v___x_1438_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1401_, v_snd_1402_, v_fst_1397_, v_fst_1393_, v___x_1437_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
v___y_1370_ = v___x_1438_;
goto v___jp_1369_;
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
lean_dec_ref(v_arg_1434_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1399_);
lean_del_object(v___x_1395_);
v___x_1442_ = lean_box(0);
v___x_1443_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1401_, v_snd_1402_, v_fst_1397_, v_fst_1393_, v___x_1442_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
v___y_1370_ = v___x_1443_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1440_);
v___x_1445_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__1));
v___x_1446_ = l_Lean_Expr_isConstOf(v___x_1444_, v___x_1445_);
lean_dec_ref(v___x_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v_arg_1439_);
lean_dec_ref(v_arg_1434_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1399_);
lean_del_object(v___x_1395_);
v___x_1447_ = lean_box(0);
v___x_1448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__0(v_fst_1401_, v_snd_1402_, v_fst_1397_, v_fst_1393_, v___x_1447_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
v___y_1370_ = v___x_1448_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; lean_object* v_fst_1453_; uint8_t v_snd_1454_; lean_object* v___y_1463_; 
v___x_1449_ = l_Lean_Expr_cleanupAnnotations(v_arg_1434_);
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint_0__Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintProc___redArg___closed__2));
v___x_1451_ = l_Lean_Expr_isConstOf(v___x_1449_, v___x_1450_);
lean_dec_ref(v___x_1449_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref(v_arg_1439_);
lean_del_object(v___x_1404_);
lean_del_object(v___x_1399_);
lean_del_object(v___x_1395_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_fst_1401_);
lean_ctor_set(v___x_1467_, 1, v_snd_1402_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_fst_1397_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_fst_1393_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v_a_1365_ = v___x_1469_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
lean_inc_ref(v_arg_1439_);
v___x_1470_ = l_Lean_Expr_cleanupAnnotations(v_arg_1439_);
v___x_1471_ = l_Lean_Expr_isApp(v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec_ref(v___x_1470_);
v___x_1472_ = lean_box(0);
v___x_1473_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1439_, v___x_1472_);
v___y_1463_ = v___x_1473_;
goto v___jp_1462_;
}
else
{
lean_object* v_arg_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v_arg_1474_ = lean_ctor_get(v___x_1470_, 1);
lean_inc_ref(v_arg_1474_);
v___x_1475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1470_);
v___x_1476_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___closed__3));
v___x_1477_ = l_Lean_Expr_isConstOf(v___x_1475_, v___x_1476_);
lean_dec_ref(v___x_1475_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v_arg_1474_);
v___x_1478_ = lean_box(0);
v___x_1479_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___lam__1(v_arg_1439_, v___x_1478_);
v___y_1463_ = v___x_1479_;
goto v___jp_1462_;
}
else
{
lean_dec_ref(v_arg_1439_);
v_fst_1453_ = v_arg_1474_;
v_snd_1454_ = v___x_1477_;
goto v___jp_1452_;
}
}
}
v___jp_1452_:
{
uint8_t v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_fst_1401_, v_fst_1453_);
if (v___x_1455_ == 0)
{
if (v___x_1451_ == 0)
{
lean_dec_ref(v_fst_1453_);
goto v___jp_1406_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint32_t v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
lean_del_object(v___x_1404_);
lean_del_object(v___x_1399_);
lean_del_object(v___x_1395_);
v___x_1456_ = lean_box(0);
lean_inc_ref_n(v_fst_1453_, 2);
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_fst_1401_, v_fst_1453_, v___x_1456_);
lean_inc(v_a_1350_);
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_fst_1397_, v_a_1350_, v_fst_1453_);
v___x_1459_ = l_Lean_Expr_approxDepth(v_fst_1453_);
v___x_1460_ = lean_uint32_to_nat(v___x_1459_);
v___x_1461_ = lean_nat_dec_le(v_snd_1402_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_dec(v_snd_1402_);
v___y_1420_ = v___x_1458_;
v___y_1421_ = v_fst_1453_;
v___y_1422_ = v_snd_1454_;
v___y_1423_ = v___x_1457_;
v___y_1424_ = v___x_1460_;
goto v___jp_1419_;
}
else
{
lean_dec(v___x_1460_);
v___y_1420_ = v___x_1458_;
v___y_1421_ = v_fst_1453_;
v___y_1422_ = v_snd_1454_;
v___y_1423_ = v___x_1457_;
v___y_1424_ = v_snd_1402_;
goto v___jp_1419_;
}
}
}
else
{
lean_dec_ref(v_fst_1453_);
goto v___jp_1406_;
}
}
v___jp_1462_:
{
lean_object* v_fst_1464_; lean_object* v_snd_1465_; uint8_t v___x_1466_; 
v_fst_1464_ = lean_ctor_get(v___y_1463_, 0);
lean_inc(v_fst_1464_);
v_snd_1465_ = lean_ctor_get(v___y_1463_, 1);
lean_inc(v_snd_1465_);
lean_dec_ref(v___y_1463_);
v___x_1466_ = lean_unbox(v_snd_1465_);
lean_dec(v_snd_1465_);
v_fst_1453_ = v_fst_1464_;
v_snd_1454_ = v___x_1466_;
goto v___jp_1452_;
}
}
}
}
}
v___jp_1406_:
{
lean_object* v___x_1408_; 
if (v_isShared_1405_ == 0)
{
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_fst_1401_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_snd_1402_);
v___x_1408_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v___x_1408_);
v___x_1410_ = v___x_1399_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_fst_1397_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___x_1410_);
v___x_1412_ = v___x_1395_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_fst_1393_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
v_a_1365_ = v___x_1412_;
goto v___jp_1364_;
}
}
}
}
v___jp_1419_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_inc_ref(v_value_1418_);
v___x_1425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1425_, 0, v_value_1418_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*1, v___y_1422_);
v___x_1426_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_fst_1393_, v___y_1421_, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1423_);
lean_ctor_set(v___x_1427_, 1, v___y_1424_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1420_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1426_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v_a_1365_ = v___x_1429_;
goto v___jp_1364_;
}
}
}
}
}
v___jp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v_a_1350_, v___x_1366_);
lean_dec(v_a_1350_);
v_a_1350_ = v___x_1367_;
v_b_1351_ = v_a_1365_;
goto _start;
}
v___jp_1369_:
{
if (lean_obj_tag(v___y_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1380_; 
v_a_1371_ = lean_ctor_get(v___y_1370_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___y_1370_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1373_ = v___y_1370_;
v_isShared_1374_ = v_isSharedCheck_1380_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___y_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1380_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
if (lean_obj_tag(v_a_1371_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; 
lean_dec(v_a_1350_);
v_a_1375_ = lean_ctor_get(v_a_1371_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v_a_1371_, 1);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v_a_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v_a_1379_; 
lean_del_object(v___x_1373_);
v_a_1379_ = lean_ctor_get(v_a_1371_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v_a_1371_, 1);
v_a_1365_ = v_a_1379_;
goto v___jp_1364_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_a_1350_);
v_a_1381_ = lean_ctor_get(v___y_1370_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___y_1370_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___y_1370_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___y_1370_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg___boxed(lean_object* v_upperBound_1485_, lean_object* v___x_1486_, lean_object* v_a_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1485_, v___x_1486_, v_a_1487_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v___x_1486_);
lean_dec(v_upperBound_1485_);
return v_res_1501_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v_relevantHypsMap_1504_; 
v___x_1503_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__0);
v_relevantHypsMap_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_relevantHypsMap_1504_, 0, v___x_1503_);
return v_relevantHypsMap_1504_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_unsigned_to_nat(16u);
v___x_1507_ = lean_mk_array(v___x_1506_, v___x_1505_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_relevantHypsIdxMap_1510_; 
v___x_1508_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__2);
v___x_1509_ = lean_unsigned_to_nat(0u);
v_relevantHypsIdxMap_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_relevantHypsIdxMap_1510_, 0, v___x_1509_);
lean_ctor_set(v_relevantHypsIdxMap_1510_, 1, v___x_1508_);
return v_relevantHypsIdxMap_1510_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4(void){
_start:
{
lean_object* v_minDepth_1511_; lean_object* v_relevantHypsIdxMap_1512_; lean_object* v___x_1513_; 
v_minDepth_1511_ = lean_cstr_to_nat("4294967296");
v_relevantHypsIdxMap_1512_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_relevantHypsIdxMap_1512_);
lean_ctor_set(v___x_1513_, 1, v_minDepth_1511_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1514_; lean_object* v_relevantHypsIdxMap_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__4);
v_relevantHypsIdxMap_1515_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__3);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_relevantHypsIdxMap_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1514_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1517_; lean_object* v_relevantHypsMap_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__5);
v_relevantHypsMap_1518_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__1);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_relevantHypsMap_1518_);
lean_ctor_set(v___x_1519_, 1, v___x_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__7));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_hypotheses_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1535_ = lean_st_ref_get(v___y_1524_);
v_hypotheses_1536_ = lean_ctor_get(v___x_1535_, 3);
lean_inc_ref(v_hypotheses_1536_);
lean_dec(v___x_1535_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = lean_array_get_size(v_hypotheses_1536_);
v___x_1539_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__6);
v___x_1540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v___x_1538_, v_hypotheses_1536_, v___x_1537_, v___x_1539_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec_ref(v_hypotheses_1536_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1658_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1658_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1658_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_snd_1545_; lean_object* v_snd_1546_; lean_object* v_fst_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1656_; 
v_snd_1545_ = lean_ctor_get(v_a_1541_, 1);
lean_inc(v_snd_1545_);
v_snd_1546_ = lean_ctor_get(v_snd_1545_, 1);
lean_inc(v_snd_1546_);
v_fst_1547_ = lean_ctor_get(v_a_1541_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_a_1541_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v_a_1541_, 1);
lean_dec(v_unused_1657_);
v___x_1549_ = v_a_1541_;
v_isShared_1550_ = v_isSharedCheck_1656_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_fst_1547_);
lean_dec(v_a_1541_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1656_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_fst_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1654_; 
v_fst_1551_ = lean_ctor_get(v_snd_1545_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_snd_1545_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v_snd_1545_, 1);
lean_dec(v_unused_1655_);
v___x_1553_ = v_snd_1545_;
v_isShared_1554_ = v_isSharedCheck_1654_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_fst_1551_);
lean_dec(v_snd_1545_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1654_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_snd_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1652_; 
v_snd_1555_ = lean_ctor_get(v_snd_1546_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_snd_1546_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; 
v_unused_1653_ = lean_ctor_get(v_snd_1546_, 0);
lean_dec(v_unused_1653_);
v___x_1557_ = v_snd_1546_;
v_isShared_1558_ = v_isSharedCheck_1652_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_snd_1555_);
lean_dec(v_snd_1546_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1652_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v_toCold_1629_; lean_object* v_options_1630_; uint8_t v_hasTrace_1631_; 
v_toCold_1629_ = lean_ctor_get(v___y_1532_, 0);
v_options_1630_ = lean_ctor_get(v_toCold_1629_, 2);
v_hasTrace_1631_ = lean_ctor_get_uint8(v_options_1630_, sizeof(void*)*1);
if (v_hasTrace_1631_ == 0)
{
lean_del_object(v___x_1549_);
v___y_1560_ = v___y_1523_;
v___y_1561_ = v___y_1524_;
v___y_1562_ = v___y_1525_;
v___y_1563_ = v___y_1526_;
v___y_1564_ = v___y_1527_;
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
goto v___jp_1559_;
}
else
{
lean_object* v_inheritedTraceOptions_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_inheritedTraceOptions_1632_ = lean_ctor_get(v_toCold_1629_, 11);
v___x_1633_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__2));
v___x_1634_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg___closed__5);
v___x_1635_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1632_, v_options_1630_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_del_object(v___x_1549_);
v___y_1560_ = v___y_1523_;
v___y_1561_ = v___y_1524_;
v___y_1562_ = v___y_1525_;
v___y_1563_ = v___y_1526_;
v___y_1564_ = v___y_1527_;
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1636_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___closed__8);
lean_inc(v_snd_1555_);
v___x_1637_ = l_Nat_reprFast(v_snd_1555_);
v___x_1638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___x_1639_ = l_Lean_MessageData_ofFormat(v___x_1638_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 7);
lean_ctor_set(v___x_1549_, 1, v___x_1639_);
lean_ctor_set(v___x_1549_, 0, v___x_1636_);
v___x_1641_ = v___x_1549_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v___x_1633_, v___x_1641_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec_ref_known(v___x_1642_, 1);
v___y_1560_ = v___y_1523_;
v___y_1561_ = v___y_1524_;
v___y_1562_ = v___y_1525_;
v___y_1563_ = v___y_1526_;
v___y_1564_ = v___y_1527_;
v___y_1565_ = v___y_1528_;
v___y_1566_ = v___y_1529_;
v___y_1567_ = v___y_1530_;
v___y_1568_ = v___y_1531_;
v___y_1569_ = v___y_1532_;
v___y_1570_ = v___y_1533_;
goto v___jp_1559_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_del_object(v___x_1557_);
lean_dec(v_snd_1555_);
lean_del_object(v___x_1553_);
lean_dec(v_fst_1551_);
lean_dec(v_fst_1547_);
lean_del_object(v___x_1543_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
}
v___jp_1559_:
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fst_1547_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v_config_1573_; lean_object* v_hypotheses_1574_; lean_object* v_maxSteps_1575_; lean_object* v___x_1576_; lean_object* v_newHyps_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_del_object(v___x_1543_);
v___x_1572_ = lean_st_ref_get(v___y_1561_);
v_config_1573_ = lean_ctor_get(v___y_1560_, 0);
v_hypotheses_1574_ = lean_ctor_get(v___x_1572_, 3);
lean_inc_ref(v_hypotheses_1574_);
lean_dec(v___x_1572_);
v_maxSteps_1575_ = lean_ctor_get(v_config_1573_, 1);
v___x_1576_ = lean_array_get_size(v_hypotheses_1574_);
v_newHyps_1577_ = lean_mk_empty_array_with_capacity(v___x_1576_);
v___x_1578_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_1575_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v___x_1578_);
lean_ctor_set(v___x_1553_, 0, v_maxSteps_1575_);
v___x_1580_ = v___x_1553_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_maxSteps_1575_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_box(0);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v_newHyps_1577_);
lean_ctor_set(v___x_1557_, 0, v___x_1581_);
v___x_1583_ = v___x_1557_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_newHyps_1577_);
v___x_1583_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v___x_1576_, v_hypotheses_1574_, v_snd_1555_, v___x_1571_, v___x_1580_, v_fst_1551_, v_fst_1547_, v___x_1537_, v___x_1583_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v_fst_1551_);
lean_dec(v_snd_1555_);
lean_dec_ref(v_hypotheses_1574_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1613_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1613_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1613_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_fst_1589_; 
v_fst_1589_ = lean_ctor_get(v_a_1585_, 0);
if (lean_obj_tag(v_fst_1589_) == 0)
{
lean_object* v_snd_1590_; lean_object* v___x_1591_; lean_object* v_caches_1592_; lean_object* v_typeAnalysis_1593_; lean_object* v_target_1594_; uint8_t v_didChange_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1607_; 
v_snd_1590_ = lean_ctor_get(v_a_1585_, 1);
lean_inc(v_snd_1590_);
lean_dec(v_a_1585_);
v___x_1591_ = lean_st_ref_take(v___y_1561_);
v_caches_1592_ = lean_ctor_get(v___x_1591_, 0);
v_typeAnalysis_1593_ = lean_ctor_get(v___x_1591_, 1);
v_target_1594_ = lean_ctor_get(v___x_1591_, 2);
v_didChange_1595_ = lean_ctor_get_uint8(v___x_1591_, sizeof(void*)*4);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1591_, 3);
lean_dec(v_unused_1608_);
v___x_1597_ = v___x_1591_;
v_isShared_1598_ = v_isSharedCheck_1607_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_target_1594_);
lean_inc(v_typeAnalysis_1593_);
lean_inc(v_caches_1592_);
lean_dec(v___x_1591_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1607_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 3, v_snd_1590_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_caches_1592_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_typeAnalysis_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_target_1594_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_snd_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*4, v_didChange_1595_);
v___x_1600_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = lean_st_ref_put(v___y_1561_, v___x_1600_);
v___x_1602_ = lean_box(v___x_1571_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1602_);
v___x_1604_ = v___x_1587_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v_val_1609_; lean_object* v___x_1611_; 
lean_inc_ref(v_fst_1589_);
lean_dec(v_a_1585_);
v_val_1609_ = lean_ctor_get(v_fst_1589_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v_fst_1589_, 1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_val_1609_);
v___x_1611_ = v___x_1587_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_val_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1614_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1584_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1584_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
else
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_del_object(v___x_1557_);
lean_dec(v_snd_1555_);
lean_del_object(v___x_1553_);
lean_dec(v_fst_1551_);
lean_dec(v_fst_1547_);
v___x_1624_ = 0;
v___x_1625_ = lean_box(v___x_1624_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1625_);
v___x_1627_ = v___x_1543_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
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
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1540_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1540_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0___boxed(lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__0(v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(lean_object* v___f_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; lean_object* v_target_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = lean_st_ref_get(v___y_1682_);
v_target_1694_ = lean_ctor_get(v___x_1693_, 2);
lean_inc_ref(v_target_1694_);
lean_dec(v___x_1693_);
v___x_1695_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1694_);
lean_dec_ref(v_target_1694_);
v___x_1696_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__10___redArg(v___x_1695_, v___f_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1___boxed(lean_object* v___f_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass___lam__1(v___f_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(lean_object* v_cls_1721_, lean_object* v_msg_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___redArg(v_cls_1721_, v_msg_1722_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1___boxed(lean_object* v_cls_1736_, lean_object* v_msg_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__1(v_cls_1736_, v_msg_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(lean_object* v_00_u03b2_1751_, lean_object* v_m_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___redArg(v_m_1752_, v_a_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2(v_00_u03b2_1755_, v_m_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_m_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(lean_object* v_00_u03b2_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___redArg(v_x_1760_, v_x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3___boxed(lean_object* v_00_u03b2_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3(v_00_u03b2_1763_, v_x_1764_, v_x_1765_);
lean_dec_ref(v_x_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(lean_object* v_upperBound_1767_, lean_object* v___x_1768_, lean_object* v___x_1769_, uint8_t v___x_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, lean_object* v___x_1773_, lean_object* v_inst_1774_, lean_object* v_R_1775_, lean_object* v_a_1776_, lean_object* v_b_1777_, lean_object* v_c_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___redArg(v_upperBound_1767_, v___x_1768_, v___x_1769_, v___x_1770_, v___x_1771_, v___x_1772_, v___x_1773_, v_a_1776_, v_b_1777_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_1792_ = _args[0];
lean_object* v___x_1793_ = _args[1];
lean_object* v___x_1794_ = _args[2];
lean_object* v___x_1795_ = _args[3];
lean_object* v___x_1796_ = _args[4];
lean_object* v___x_1797_ = _args[5];
lean_object* v___x_1798_ = _args[6];
lean_object* v_inst_1799_ = _args[7];
lean_object* v_R_1800_ = _args[8];
lean_object* v_a_1801_ = _args[9];
lean_object* v_b_1802_ = _args[10];
lean_object* v_c_1803_ = _args[11];
lean_object* v___y_1804_ = _args[12];
lean_object* v___y_1805_ = _args[13];
lean_object* v___y_1806_ = _args[14];
lean_object* v___y_1807_ = _args[15];
lean_object* v___y_1808_ = _args[16];
lean_object* v___y_1809_ = _args[17];
lean_object* v___y_1810_ = _args[18];
lean_object* v___y_1811_ = _args[19];
lean_object* v___y_1812_ = _args[20];
lean_object* v___y_1813_ = _args[21];
lean_object* v___y_1814_ = _args[22];
lean_object* v___y_1815_ = _args[23];
_start:
{
uint8_t v___x_80233__boxed_1816_; lean_object* v_res_1817_; 
v___x_80233__boxed_1816_ = lean_unbox(v___x_1795_);
v_res_1817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__4(v_upperBound_1792_, v___x_1793_, v___x_1794_, v___x_80233__boxed_1816_, v___x_1796_, v___x_1797_, v___x_1798_, v_inst_1799_, v_R_1800_, v_a_1801_, v_b_1802_, v_c_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec_ref(v___x_1797_);
lean_dec(v___x_1794_);
lean_dec_ref(v___x_1793_);
lean_dec(v_upperBound_1792_);
return v_res_1817_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(lean_object* v_00_u03b2_1818_, lean_object* v_m_1819_, lean_object* v_a_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___redArg(v_m_1819_, v_a_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5___boxed(lean_object* v_00_u03b2_1822_, lean_object* v_m_1823_, lean_object* v_a_1824_){
_start:
{
uint8_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5(v_00_u03b2_1822_, v_m_1823_, v_a_1824_);
lean_dec_ref(v_a_1824_);
lean_dec_ref(v_m_1823_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6(lean_object* v_00_u03b2_1827_, lean_object* v_m_1828_, lean_object* v_a_1829_, lean_object* v_b_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6___redArg(v_m_1828_, v_a_1829_, v_b_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7(lean_object* v_00_u03b2_1832_, lean_object* v_m_1833_, lean_object* v_a_1834_, lean_object* v_b_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7___redArg(v_m_1833_, v_a_1834_, v_b_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8(lean_object* v_00_u03b2_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8___redArg(v_x_1838_, v_x_1839_, v_x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(lean_object* v_upperBound_1842_, lean_object* v___x_1843_, lean_object* v_inst_1844_, lean_object* v_R_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_, lean_object* v_c_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___redArg(v_upperBound_1842_, v___x_1843_, v_a_1846_, v_b_1847_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1862_ = _args[0];
lean_object* v___x_1863_ = _args[1];
lean_object* v_inst_1864_ = _args[2];
lean_object* v_R_1865_ = _args[3];
lean_object* v_a_1866_ = _args[4];
lean_object* v_b_1867_ = _args[5];
lean_object* v_c_1868_ = _args[6];
lean_object* v___y_1869_ = _args[7];
lean_object* v___y_1870_ = _args[8];
lean_object* v___y_1871_ = _args[9];
lean_object* v___y_1872_ = _args[10];
lean_object* v___y_1873_ = _args[11];
lean_object* v___y_1874_ = _args[12];
lean_object* v___y_1875_ = _args[13];
lean_object* v___y_1876_ = _args[14];
lean_object* v___y_1877_ = _args[15];
lean_object* v___y_1878_ = _args[16];
lean_object* v___y_1879_ = _args[17];
lean_object* v___y_1880_ = _args[18];
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__9(v_upperBound_1862_, v___x_1863_, v_inst_1864_, v_R_1865_, v_a_1866_, v_b_1867_, v_c_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___x_1863_);
lean_dec(v_upperBound_1862_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(lean_object* v_00_u03b2_1882_, lean_object* v_a_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___redArg(v_a_1883_, v_x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1886_, lean_object* v_a_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__2_spec__3(v_00_u03b2_1886_, v_a_1887_, v_x_1888_);
lean_dec(v_x_1888_);
lean_dec(v_a_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(lean_object* v_00_u03b2_1890_, lean_object* v_x_1891_, size_t v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___redArg(v_x_1891_, v_x_1892_, v_x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
size_t v_x_80359__boxed_1899_; lean_object* v_res_1900_; 
v_x_80359__boxed_1899_ = lean_unbox_usize(v_x_1897_);
lean_dec(v_x_1897_);
v_res_1900_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__3_spec__5(v_00_u03b2_1895_, v_x_1896_, v_x_80359__boxed_1899_, v_x_1898_);
lean_dec_ref(v_x_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(lean_object* v_00_u03b2_1901_, lean_object* v_a_1902_, lean_object* v_x_1903_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___redArg(v_a_1902_, v_x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1905_, lean_object* v_a_1906_, lean_object* v_x_1907_){
_start:
{
uint8_t v_res_1908_; lean_object* v_r_1909_; 
v_res_1908_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__5_spec__8(v_00_u03b2_1905_, v_a_1906_, v_x_1907_);
lean_dec(v_x_1907_);
lean_dec_ref(v_a_1906_);
v_r_1909_ = lean_box(v_res_1908_);
return v_r_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10(lean_object* v_00_u03b2_1910_, lean_object* v_data_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10___redArg(v_data_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(lean_object* v_00_u03b2_1913_, lean_object* v_a_1914_, lean_object* v_x_1915_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___redArg(v_a_1914_, v_x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12___boxed(lean_object* v_00_u03b2_1917_, lean_object* v_a_1918_, lean_object* v_x_1919_){
_start:
{
uint8_t v_res_1920_; lean_object* v_r_1921_; 
v_res_1920_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__12(v_00_u03b2_1917_, v_a_1918_, v_x_1919_);
lean_dec(v_x_1919_);
lean_dec(v_a_1918_);
v_r_1921_ = lean_box(v_res_1920_);
return v_r_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13(lean_object* v_00_u03b2_1922_, lean_object* v_data_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13___redArg(v_data_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14(lean_object* v_00_u03b2_1925_, lean_object* v_a_1926_, lean_object* v_b_1927_, lean_object* v_x_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__14___redArg(v_a_1926_, v_b_1927_, v_x_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(lean_object* v_00_u03b2_1930_, lean_object* v_x_1931_, size_t v_x_1932_, size_t v_x_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___redArg(v_x_1931_, v_x_1932_, v_x_1933_, v_x_1934_, v_x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
size_t v_x_80388__boxed_1943_; size_t v_x_80389__boxed_1944_; lean_object* v_res_1945_; 
v_x_80388__boxed_1943_ = lean_unbox_usize(v_x_1939_);
lean_dec(v_x_1939_);
v_x_80389__boxed_1944_ = lean_unbox_usize(v_x_1940_);
lean_dec(v_x_1940_);
v_res_1945_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16(v_00_u03b2_1937_, v_x_1938_, v_x_80388__boxed_1943_, v_x_80389__boxed_1944_, v_x_1941_, v_x_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_1946_, lean_object* v_i_1947_, lean_object* v_source_1948_, lean_object* v_target_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13___redArg(v_i_1947_, v_source_1948_, v_target_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17(lean_object* v_00_u03b2_1951_, lean_object* v_i_1952_, lean_object* v_source_1953_, lean_object* v_target_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17___redArg(v_i_1952_, v_source_1953_, v_target_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21(lean_object* v_00_u03b2_1956_, lean_object* v_n_1957_, lean_object* v_k_1958_, lean_object* v_v_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21___redArg(v_n_1957_, v_k_1958_, v_v_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(lean_object* v_00_u03b2_1961_, size_t v_depth_1962_, lean_object* v_keys_1963_, lean_object* v_vals_1964_, lean_object* v_heq_1965_, lean_object* v_i_1966_, lean_object* v_entries_1967_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___redArg(v_depth_1962_, v_keys_1963_, v_vals_1964_, v_i_1966_, v_entries_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22___boxed(lean_object* v_00_u03b2_1969_, lean_object* v_depth_1970_, lean_object* v_keys_1971_, lean_object* v_vals_1972_, lean_object* v_heq_1973_, lean_object* v_i_1974_, lean_object* v_entries_1975_){
_start:
{
size_t v_depth_boxed_1976_; lean_object* v_res_1977_; 
v_depth_boxed_1976_ = lean_unbox_usize(v_depth_1970_);
lean_dec(v_depth_1970_);
v_res_1977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__22(v_00_u03b2_1969_, v_depth_boxed_1976_, v_keys_1971_, v_vals_1972_, v_heq_1973_, v_i_1974_, v_entries_1975_);
lean_dec_ref(v_vals_1972_);
lean_dec_ref(v_keys_1971_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18(lean_object* v_00_u03b2_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__6_spec__10_spec__13_spec__18___redArg(v_x_1979_, v_x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22(lean_object* v_00_u03b2_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__7_spec__13_spec__17_spec__22___redArg(v_x_1983_, v_x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26(lean_object* v_00_u03b2_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass_spec__8_spec__16_spec__21_spec__26___redArg(v_x_1987_, v_x_1988_, v_x_1989_, v_x_1990_);
return v___x_1991_;
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

// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.ModelUtil
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedRat;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Grind.Arith.Cutsat.Model"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 103, .m_capacity = 103, .m_length = 102, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Cutsat.Model.0.Lean.Meta.Grind.Arith.Cutsat.getCutsatAssignment\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: isSameExpr node.self node.root\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 57, 122, 235, 182, 82, 28, 168)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 57, 165, 14, 135, 135, 191)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 54, 185, 195, 30, 183, 107, 8)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(44, 210, 78, 221, 232, 52, 28, 161)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(144, 114, 73, 21, 161, 185, 192, 185)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(156, 179, 78, 164, 17, 99, 115, 128)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 144, 45, 221, 65, 48, 204, 242)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 106, 42, 185, 61, 138, 17, 12)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(83, 21, 175, 117, 0, 32, 88, 5)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 247, 174, 117, 226, 108, 136, 114)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(36, 9, 44, 71, 206, 78, 188, 190)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(142, 44, 53, 46, 180, 233, 253, 99)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(165, 91, 87, 132, 175, 103, 206, 109)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value),LEAN_SCALAR_PTR_LITERAL(172, 153, 248, 110, 186, 235, 101, 152)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(lean_object* v_n_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_self_7_; lean_object* v_keyedConfig_8_; uint8_t v_trackZetaDelta_9_; lean_object* v_zetaDeltaSet_10_; lean_object* v_lctx_11_; lean_object* v_localInstances_12_; lean_object* v_defEqCtx_x3f_13_; lean_object* v_synthPendingDepth_14_; lean_object* v_customCanUnfoldPredicate_x3f_15_; uint8_t v_univApprox_16_; uint8_t v_inTypeClassResolution_17_; uint8_t v_cacheInferType_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_self_7_ = lean_ctor_get(v_n_1_, 0);
lean_inc_ref(v_self_7_);
lean_dec_ref(v_n_1_);
v_keyedConfig_8_ = lean_ctor_get(v_a_2_, 0);
v_trackZetaDelta_9_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7);
v_zetaDeltaSet_10_ = lean_ctor_get(v_a_2_, 1);
v_lctx_11_ = lean_ctor_get(v_a_2_, 2);
v_localInstances_12_ = lean_ctor_get(v_a_2_, 3);
v_defEqCtx_x3f_13_ = lean_ctor_get(v_a_2_, 4);
v_synthPendingDepth_14_ = lean_ctor_get(v_a_2_, 5);
v_customCanUnfoldPredicate_x3f_15_ = lean_ctor_get(v_a_2_, 6);
v_univApprox_16_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_17_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7 + 2);
v_cacheInferType_18_ = lean_ctor_get_uint8(v_a_2_, sizeof(void*)*7 + 3);
v___x_19_ = 1;
lean_inc_ref(v_keyedConfig_8_);
v___x_20_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_19_, v_keyedConfig_8_);
lean_inc(v_customCanUnfoldPredicate_x3f_15_);
lean_inc(v_synthPendingDepth_14_);
lean_inc(v_defEqCtx_x3f_13_);
lean_inc_ref(v_localInstances_12_);
lean_inc_ref(v_lctx_11_);
lean_inc(v_zetaDeltaSet_10_);
v___x_21_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v_zetaDeltaSet_10_);
lean_ctor_set(v___x_21_, 2, v_lctx_11_);
lean_ctor_set(v___x_21_, 3, v_localInstances_12_);
lean_ctor_set(v___x_21_, 4, v_defEqCtx_x3f_13_);
lean_ctor_set(v___x_21_, 5, v_synthPendingDepth_14_);
lean_ctor_set(v___x_21_, 6, v_customCanUnfoldPredicate_x3f_15_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*7, v_trackZetaDelta_9_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*7 + 1, v_univApprox_16_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*7 + 2, v_inTypeClassResolution_17_);
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*7 + 3, v_cacheInferType_18_);
lean_inc(v_a_5_);
lean_inc_ref(v_a_4_);
lean_inc(v_a_3_);
lean_inc_ref(v___x_21_);
v___x_22_ = lean_infer_type(v_self_7_, v___x_21_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_n(v_a_23_, 2);
lean_dec_ref_known(v___x_22_, 1);
v___x_24_ = l_Lean_Int_mkType;
v___x_25_ = l_Lean_Meta_isExprDefEq(v_a_23_, v___x_24_, v___x_21_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; uint8_t v___x_27_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_a_26_);
v___x_27_ = lean_unbox(v_a_26_);
lean_dec(v_a_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec_ref_known(v___x_25_, 1);
v___x_28_ = l_Lean_Nat_mkType;
v___x_29_ = l_Lean_Meta_isExprDefEq(v_a_23_, v___x_28_, v___x_21_, v_a_3_, v_a_4_, v_a_5_);
lean_dec_ref_known(v___x_21_, 7);
return v___x_29_;
}
else
{
lean_dec(v_a_23_);
lean_dec_ref_known(v___x_21_, 7);
return v___x_25_;
}
}
else
{
lean_dec(v_a_23_);
lean_dec_ref_known(v___x_21_, 7);
return v___x_25_;
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
lean_dec_ref_known(v___x_21_, 7);
v_a_30_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_22_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_22_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(lean_object* v_n_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_n_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
return v_res_44_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = l_instInhabitedError;
v___x_46_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_46_, 0, lean_box(0));
lean_closure_set(v___x_46_, 1, lean_box(0));
lean_closure_set(v___x_46_, 2, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(lean_object* v_msg_47_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_484__overap_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0);
v___x_484__overap_50_ = lean_panic_fn_borrowed(v___x_49_, v_msg_47_);
v___x_51_ = lean_apply_1(v___x_484__overap_50_, lean_box(0));
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(lean_object* v_msg_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v_msg_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_55_, lean_object* v_vals_56_, lean_object* v_i_57_, lean_object* v_k_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_keys_55_);
v___x_60_ = lean_nat_dec_lt(v_i_57_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec(v_i_57_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
lean_object* v_k_x27_62_; size_t v___x_63_; size_t v___x_64_; uint8_t v___x_65_; 
v_k_x27_62_ = lean_array_fget_borrowed(v_keys_55_, v_i_57_);
v___x_63_ = lean_ptr_addr(v_k_58_);
v___x_64_ = lean_ptr_addr(v_k_x27_62_);
v___x_65_ = lean_usize_dec_eq(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_i_57_, v___x_66_);
lean_dec(v_i_57_);
v_i_57_ = v___x_67_;
goto _start;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_array_fget_borrowed(v_vals_56_, v_i_57_);
lean_dec(v_i_57_);
lean_inc(v___x_69_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_71_, lean_object* v_vals_72_, lean_object* v_i_73_, lean_object* v_k_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_71_, v_vals_72_, v_i_73_, v_k_74_);
lean_dec_ref(v_k_74_);
lean_dec_ref(v_vals_72_);
lean_dec_ref(v_keys_71_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(lean_object* v_x_76_, size_t v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_es_79_; lean_object* v___x_80_; size_t v___x_81_; size_t v___x_82_; lean_object* v_j_83_; lean_object* v___x_84_; 
v_es_79_ = lean_ctor_get(v_x_76_, 0);
v___x_80_ = lean_box(2);
v___x_81_ = ((size_t)31ULL);
v___x_82_ = lean_usize_land(v_x_77_, v___x_81_);
v_j_83_ = lean_usize_to_nat(v___x_82_);
v___x_84_ = lean_array_get_borrowed(v___x_80_, v_es_79_, v_j_83_);
lean_dec(v_j_83_);
switch(lean_obj_tag(v___x_84_))
{
case 0:
{
lean_object* v_key_85_; lean_object* v_val_86_; size_t v___x_87_; size_t v___x_88_; uint8_t v___x_89_; 
v_key_85_ = lean_ctor_get(v___x_84_, 0);
v_val_86_ = lean_ctor_get(v___x_84_, 1);
v___x_87_ = lean_ptr_addr(v_x_78_);
v___x_88_ = lean_ptr_addr(v_key_85_);
v___x_89_ = lean_usize_dec_eq(v___x_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_inc(v_val_86_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_val_86_);
return v___x_91_;
}
}
case 1:
{
lean_object* v_node_92_; size_t v___x_93_; size_t v___x_94_; 
v_node_92_ = lean_ctor_get(v___x_84_, 0);
v___x_93_ = ((size_t)5ULL);
v___x_94_ = lean_usize_shift_right(v_x_77_, v___x_93_);
v_x_76_ = v_node_92_;
v_x_77_ = v___x_94_;
goto _start;
}
default: 
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
}
else
{
lean_object* v_ks_97_; lean_object* v_vs_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_ks_97_ = lean_ctor_get(v_x_76_, 0);
v_vs_98_ = lean_ctor_get(v_x_76_, 1);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_ks_97_, v_vs_98_, v___x_99_, v_x_78_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
size_t v_x_667__boxed_104_; lean_object* v_res_105_; 
v_x_667__boxed_104_ = lean_unbox_usize(v_x_102_);
lean_dec(v_x_102_);
v_res_105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_101_, v_x_667__boxed_104_, v_x_103_);
lean_dec_ref(v_x_103_);
lean_dec_ref(v_x_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
size_t v___x_108_; size_t v___x_109_; size_t v___x_110_; uint64_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_108_ = lean_ptr_addr(v_x_107_);
v___x_109_ = ((size_t)3ULL);
v___x_110_ = lean_usize_shift_right(v___x_108_, v___x_109_);
v___x_111_ = lean_usize_to_uint64(v___x_110_);
v___x_112_ = lean_uint64_to_usize(v___x_111_);
v___x_113_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_106_, v___x_112_, v_x_107_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_114_, v_x_115_);
lean_dec_ref(v_x_115_);
lean_dec_ref(v_x_114_);
return v_res_116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2));
v___x_121_ = lean_unsigned_to_nat(2u);
v___x_122_ = lean_unsigned_to_nat(21u);
v___x_123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1));
v___x_124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0));
v___x_125_ = l_mkPanicMessageWithDecl(v___x_124_, v___x_123_, v___x_122_, v___x_121_, v___x_120_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(lean_object* v_goal_126_, lean_object* v_node_127_){
_start:
{
lean_object* v_self_129_; lean_object* v_root_130_; size_t v___x_131_; size_t v___x_132_; uint8_t v___x_133_; 
v_self_129_ = lean_ctor_get(v_node_127_, 0);
v_root_130_ = lean_ctor_get(v_node_127_, 2);
v___x_131_ = lean_ptr_addr(v_self_129_);
v___x_132_ = lean_ptr_addr(v_root_130_);
v___x_133_ = lean_usize_dec_eq(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3);
v___x_135_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v___x_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_137_ = l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(v___x_136_, v_node_127_);
if (lean_obj_tag(v___x_137_) == 1)
{
lean_object* v_val_138_; lean_object* v___x_139_; 
v_val_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_136_, v_goal_126_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_170_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_170_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_170_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_170_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_varMap_144_; lean_object* v_assignment_145_; lean_object* v___x_146_; 
v_varMap_144_ = lean_ctor_get(v_a_140_, 1);
lean_inc_ref(v_varMap_144_);
v_assignment_145_ = lean_ctor_get(v_a_140_, 13);
lean_inc_ref(v_assignment_145_);
lean_dec(v_a_140_);
v___x_146_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_varMap_144_, v_val_138_);
lean_dec(v_val_138_);
lean_dec_ref(v_varMap_144_);
if (lean_obj_tag(v___x_146_) == 1)
{
lean_object* v_val_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_165_; 
v_val_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_165_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_165_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_val_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_165_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_size_151_; uint8_t v___x_152_; 
v_size_151_ = lean_ctor_get(v_assignment_145_, 2);
v___x_152_ = lean_nat_dec_lt(v_val_147_, v_size_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_155_; 
lean_del_object(v___x_149_);
lean_dec(v_val_147_);
lean_dec_ref(v_assignment_145_);
v___x_153_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_153_);
v___x_155_ = v___x_142_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_157_ = l_instInhabitedRat;
v___x_158_ = l_Lean_PersistentArray_get_x21___redArg(v___x_157_, v_assignment_145_, v_val_147_);
lean_dec(v_val_147_);
lean_dec_ref(v_assignment_145_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_158_);
v___x_160_ = v___x_149_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_164_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_160_);
v___x_162_ = v___x_142_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v___x_146_);
lean_dec_ref(v_assignment_145_);
v___x_166_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_166_);
v___x_168_ = v___x_142_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_val_138_);
v_a_171_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_139_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_139_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v___x_137_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object* v_goal_181_, lean_object* v_node_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_181_, v_node_182_);
lean_dec_ref(v_node_182_);
lean_dec_ref(v_goal_181_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object* v_00_u03b2_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object* v_00_u03b2_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(v_00_u03b2_189_, v_x_190_, v_x_191_);
lean_dec_ref(v_x_191_);
lean_dec_ref(v_x_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object* v_00_u03b2_193_, lean_object* v_x_194_, size_t v_x_195_, lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_194_, v_x_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
size_t v_x_868__boxed_202_; lean_object* v_res_203_; 
v_x_868__boxed_202_ = lean_unbox_usize(v_x_200_);
lean_dec(v_x_200_);
v_res_203_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(v_00_u03b2_198_, v_x_199_, v_x_868__boxed_202_, v_x_201_);
lean_dec_ref(v_x_201_);
lean_dec_ref(v_x_199_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_204_, lean_object* v_keys_205_, lean_object* v_vals_206_, lean_object* v_heq_207_, lean_object* v_i_208_, lean_object* v_k_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_205_, v_vals_206_, v_i_208_, v_k_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_211_, lean_object* v_keys_212_, lean_object* v_vals_213_, lean_object* v_heq_214_, lean_object* v_i_215_, lean_object* v_k_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(v_00_u03b2_211_, v_keys_212_, v_vals_213_, v_heq_214_, v_i_215_, v_k_216_);
lean_dec_ref(v_k_216_);
lean_dec_ref(v_vals_213_);
lean_dec_ref(v_keys_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(lean_object* v_e_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = l_Lean_Expr_cleanupAnnotations(v_e_273_);
v___x_275_ = l_Lean_Expr_isApp(v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v___x_274_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
else
{
lean_object* v_arg_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_arg_277_ = lean_ctor_get(v___x_274_, 1);
lean_inc_ref(v_arg_277_);
v___x_278_ = l_Lean_Expr_appFnCleanup___redArg(v___x_274_);
v___x_279_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2));
v___x_280_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4));
v___x_282_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6));
v___x_284_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8));
v___x_286_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10));
v___x_288_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12));
v___x_290_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14));
v___x_292_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16));
v___x_294_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18));
v___x_296_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20));
v___x_298_ = l_Lean_Expr_isConstOf(v___x_278_, v___x_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_Expr_isApp(v___x_278_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v___x_278_);
lean_dec_ref(v_arg_277_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_278_);
v___x_302_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23));
v___x_303_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25));
v___x_305_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28));
v___x_307_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_306_);
lean_dec_ref(v___x_301_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec_ref(v_arg_277_);
v___x_308_ = lean_box(0);
return v___x_308_;
}
else
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v_arg_277_);
return v___x_309_;
}
}
else
{
lean_object* v___x_310_; 
lean_dec_ref(v___x_301_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_arg_277_);
return v___x_310_;
}
}
else
{
lean_object* v___x_311_; 
lean_dec_ref(v___x_301_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v_arg_277_);
return v___x_311_;
}
}
}
else
{
lean_object* v___x_312_; 
lean_dec_ref(v___x_278_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_arg_277_);
return v___x_312_;
}
}
else
{
lean_object* v___x_313_; 
lean_dec_ref(v___x_278_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_arg_277_);
return v___x_313_;
}
}
else
{
lean_object* v___x_314_; 
lean_dec_ref(v___x_278_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_arg_277_);
return v___x_314_;
}
}
else
{
lean_object* v___x_315_; 
lean_dec_ref(v___x_278_);
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v_arg_277_);
return v___x_315_;
}
}
else
{
lean_object* v___x_316_; 
lean_dec_ref(v___x_278_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v_arg_277_);
return v___x_316_;
}
}
else
{
lean_object* v___x_317_; 
lean_dec_ref(v___x_278_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_arg_277_);
return v___x_317_;
}
}
else
{
lean_object* v___x_318_; 
lean_dec_ref(v___x_278_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v_arg_277_);
return v___x_318_;
}
}
else
{
lean_object* v___x_319_; 
lean_dec_ref(v___x_278_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v_arg_277_);
return v___x_319_;
}
}
else
{
lean_object* v___x_320_; 
lean_dec_ref(v___x_278_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_arg_277_);
return v___x_320_;
}
}
else
{
lean_object* v___x_321_; 
lean_dec_ref(v___x_278_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v_arg_277_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object* v_e_330_){
_start:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
lean_inc_ref(v_e_330_);
v___x_331_ = l_Lean_Expr_cleanupAnnotations(v_e_330_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v___x_331_);
v___x_333_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_330_);
return v___x_333_;
}
else
{
lean_object* v_arg_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_arg_334_ = lean_ctor_get(v___x_331_, 1);
lean_inc_ref(v_arg_334_);
v___x_335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v___x_335_);
lean_dec_ref(v_arg_334_);
v___x_337_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_330_);
return v___x_337_;
}
else
{
lean_object* v_arg_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_arg_338_ = lean_ctor_get(v___x_335_, 1);
lean_inc_ref(v_arg_338_);
v___x_339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_340_ = l_Lean_Expr_isApp(v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v___x_339_);
lean_dec_ref(v_arg_338_);
lean_dec_ref(v_arg_334_);
v___x_341_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_330_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_339_);
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_343_);
lean_dec_ref(v___x_342_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v_arg_338_);
lean_dec_ref(v_arg_334_);
v___x_345_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_330_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
lean_dec_ref(v_e_330_);
v___x_346_ = l_Lean_Expr_cleanupAnnotations(v_arg_338_);
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4));
v___x_348_ = l_Lean_Expr_isConstOf(v___x_346_, v___x_347_);
lean_dec_ref(v___x_346_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec_ref(v_arg_334_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_arg_334_);
return v___x_350_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Rat_ofInt(v_a_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object* v_goal_353_, lean_object* v_e_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Grind_Goal_getRoot(v_goal_353_, v_e_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_362_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
v___x_362_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_353_, v_a_361_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_353_, v_a_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_430_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_430_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_430_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_430_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
if (lean_obj_tag(v_a_365_) == 1)
{
lean_object* v___x_370_; 
lean_dec(v_a_363_);
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
else
{
lean_object* v_self_372_; lean_object* v___x_373_; 
lean_del_object(v___x_367_);
lean_dec(v_a_365_);
v_self_372_ = lean_ctor_get(v_a_363_, 0);
lean_inc_ref_n(v_self_372_, 2);
lean_dec(v_a_363_);
v___x_373_ = l_Lean_Meta_getIntValue_x3f(v_self_372_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_421_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_421_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_421_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_421_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
if (lean_obj_tag(v_a_374_) == 1)
{
lean_object* v_val_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_389_; 
lean_dec_ref(v_self_372_);
v_val_378_ = lean_ctor_get(v_a_374_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_a_374_);
if (v_isSharedCheck_389_ == 0)
{
v___x_380_ = v_a_374_;
v_isShared_381_ = v_isSharedCheck_389_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_val_378_);
lean_dec(v_a_374_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_389_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = l_Rat_ofInt(v_val_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_384_);
v___x_386_ = v___x_376_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v___x_390_; 
lean_del_object(v___x_376_);
lean_dec(v_a_374_);
v___x_390_ = l_Lean_Meta_getNatValue_x3f(v_self_372_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec_ref(v_self_372_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_412_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_412_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_412_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_412_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
if (lean_obj_tag(v_a_391_) == 1)
{
lean_object* v_val_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_407_; 
v_val_395_ = lean_ctor_get(v_a_391_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_a_391_);
if (v_isSharedCheck_407_ == 0)
{
v___x_397_ = v_a_391_;
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_val_395_);
lean_dec(v_a_391_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_nat_to_int(v_val_395_);
v___x_400_ = l_Rat_ofInt(v___x_399_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_404_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_402_);
v___x_404_ = v___x_393_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_410_; 
lean_dec(v_a_391_);
v___x_408_ = lean_box(0);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_408_);
v___x_410_ = v___x_393_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_a_413_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_390_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_390_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_self_372_);
v_a_422_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_373_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_373_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_a_363_);
v_a_431_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_443_ == 0)
{
v___x_433_ = v___x_364_;
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_364_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_ref_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v_ref_435_ = lean_ctor_get(v_a_357_, 5);
v___x_436_ = lean_io_error_to_string(v_a_431_);
v___x_437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
v___x_438_ = l_Lean_MessageData_ofFormat(v___x_437_);
lean_inc(v_ref_435_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_ref_435_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_439_);
v___x_441_ = v___x_433_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
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
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_362_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_362_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_360_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_360_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object* v_goal_460_, lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_460_, v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec_ref(v_goal_460_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object* v_goal_468_, lean_object* v_as_469_, size_t v_sz_470_, size_t v_i_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_lt(v_i_471_, v_sz_470_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_b_472_);
return v___x_479_;
}
else
{
lean_object* v_snd_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_529_; 
v_snd_480_ = lean_ctor_get(v_b_472_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_b_472_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_b_472_, 0);
lean_dec(v_unused_530_);
v___x_482_ = v_b_472_;
v_isShared_483_ = v_isSharedCheck_529_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snd_480_);
lean_dec(v_b_472_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_529_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_array_uget_borrowed(v_as_469_, v_i_471_);
lean_inc(v_a_484_);
v___x_485_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_468_, v_a_484_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; lean_object* v_a_489_; uint8_t v___x_496_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = lean_box(0);
v___x_496_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_486_);
if (v___x_496_ == 0)
{
lean_dec(v_a_486_);
v_a_489_ = v_snd_480_;
goto v___jp_488_;
}
else
{
lean_object* v___x_497_; 
lean_inc(v_a_486_);
v___x_497_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_486_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; uint8_t v___x_499_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = lean_unbox(v_a_498_);
lean_dec(v_a_498_);
if (v___x_499_ == 0)
{
lean_dec(v_a_486_);
v_a_489_ = v_snd_480_;
goto v___jp_488_;
}
else
{
lean_object* v_self_500_; lean_object* v___x_501_; 
v_self_500_ = lean_ctor_get(v_a_486_, 0);
lean_inc_ref_n(v_self_500_, 2);
lean_dec(v_a_486_);
v___x_501_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_468_, v_self_500_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
if (lean_obj_tag(v_a_502_) == 1)
{
lean_object* v_val_503_; lean_object* v___x_504_; 
v_val_503_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_a_502_, 1);
v___x_504_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_468_, v_self_500_, v_val_503_, v_snd_480_);
v_a_489_ = v___x_504_;
goto v___jp_488_;
}
else
{
lean_dec(v_a_502_);
lean_dec_ref(v_self_500_);
v_a_489_ = v_snd_480_;
goto v___jp_488_;
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v_self_500_);
lean_del_object(v___x_482_);
lean_dec(v_snd_480_);
v_a_505_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_501_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_501_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_a_486_);
lean_del_object(v___x_482_);
lean_dec(v_snd_480_);
v_a_513_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_497_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_497_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
v___jp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v_a_489_);
lean_ctor_set(v___x_482_, 0, v___x_487_);
v___x_491_ = v___x_482_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_471_, v___x_492_);
v_i_471_ = v___x_493_;
v_b_472_ = v___x_491_;
goto _start;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_del_object(v___x_482_);
lean_dec(v_snd_480_);
v_a_521_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_485_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_485_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_goal_531_, lean_object* v_as_532_, lean_object* v_sz_533_, lean_object* v_i_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
size_t v_sz_boxed_541_; size_t v_i_boxed_542_; lean_object* v_res_543_; 
v_sz_boxed_541_ = lean_unbox_usize(v_sz_533_);
lean_dec(v_sz_533_);
v_i_boxed_542_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_531_, v_as_532_, v_sz_boxed_541_, v_i_boxed_542_, v_b_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec_ref(v_as_532_);
lean_dec_ref(v_goal_531_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object* v_goal_544_, lean_object* v_as_545_, size_t v_sz_546_, size_t v_i_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = lean_usize_dec_lt(v_i_547_, v_sz_546_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v_b_548_);
return v___x_555_;
}
else
{
lean_object* v_snd_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_605_; 
v_snd_556_ = lean_ctor_get(v_b_548_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_b_548_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v_b_548_, 0);
lean_dec(v_unused_606_);
v___x_558_ = v_b_548_;
v_isShared_559_ = v_isSharedCheck_605_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_556_);
lean_dec(v_b_548_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_605_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_a_560_; lean_object* v___x_561_; 
v_a_560_ = lean_array_uget_borrowed(v_as_545_, v_i_547_);
lean_inc(v_a_560_);
v___x_561_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_544_, v_a_560_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v_a_565_; uint8_t v___x_572_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = lean_box(0);
v___x_572_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_562_);
if (v___x_572_ == 0)
{
lean_dec(v_a_562_);
v_a_565_ = v_snd_556_;
goto v___jp_564_;
}
else
{
lean_object* v___x_573_; 
lean_inc(v_a_562_);
v___x_573_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_562_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; uint8_t v___x_575_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = lean_unbox(v_a_574_);
lean_dec(v_a_574_);
if (v___x_575_ == 0)
{
lean_dec(v_a_562_);
v_a_565_ = v_snd_556_;
goto v___jp_564_;
}
else
{
lean_object* v_self_576_; lean_object* v___x_577_; 
v_self_576_ = lean_ctor_get(v_a_562_, 0);
lean_inc_ref_n(v_self_576_, 2);
lean_dec(v_a_562_);
v___x_577_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_544_, v_self_576_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
if (lean_obj_tag(v_a_578_) == 1)
{
lean_object* v_val_579_; lean_object* v___x_580_; 
v_val_579_ = lean_ctor_get(v_a_578_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v_a_578_, 1);
v___x_580_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_544_, v_self_576_, v_val_579_, v_snd_556_);
v_a_565_ = v___x_580_;
goto v___jp_564_;
}
else
{
lean_dec(v_a_578_);
lean_dec_ref(v_self_576_);
v_a_565_ = v_snd_556_;
goto v___jp_564_;
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_self_576_);
lean_del_object(v___x_558_);
lean_dec(v_snd_556_);
v_a_581_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_577_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_577_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_a_562_);
lean_del_object(v___x_558_);
lean_dec(v_snd_556_);
v_a_589_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_573_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_573_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
v___jp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v_a_565_);
lean_ctor_set(v___x_558_, 0, v___x_563_);
v___x_567_ = v___x_558_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_a_565_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_547_, v___x_568_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_544_, v_as_545_, v_sz_546_, v___x_569_, v___x_567_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_570_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_del_object(v___x_558_);
lean_dec(v_snd_556_);
v_a_597_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_561_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_561_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object* v_goal_607_, lean_object* v_as_608_, lean_object* v_sz_609_, lean_object* v_i_610_, lean_object* v_b_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
size_t v_sz_boxed_617_; size_t v_i_boxed_618_; lean_object* v_res_619_; 
v_sz_boxed_617_ = lean_unbox_usize(v_sz_609_);
lean_dec(v_sz_609_);
v_i_boxed_618_ = lean_unbox_usize(v_i_610_);
lean_dec(v_i_610_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_607_, v_as_608_, v_sz_boxed_617_, v_i_boxed_618_, v_b_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec_ref(v_as_608_);
lean_dec_ref(v_goal_607_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object* v_init_620_, lean_object* v_goal_621_, lean_object* v_n_622_, lean_object* v_b_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
if (lean_obj_tag(v_n_622_) == 0)
{
lean_object* v_cs_629_; lean_object* v___x_630_; lean_object* v___x_631_; size_t v_sz_632_; size_t v___x_633_; lean_object* v___x_634_; 
v_cs_629_ = lean_ctor_get(v_n_622_, 0);
v___x_630_ = lean_box(0);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v_b_623_);
v_sz_632_ = lean_array_size(v_cs_629_);
v___x_633_ = ((size_t)0ULL);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_620_, v_goal_621_, v_cs_629_, v_sz_632_, v___x_633_, v___x_631_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_649_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_649_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_fst_639_; 
v_fst_639_ = lean_ctor_get(v_a_635_, 0);
if (lean_obj_tag(v_fst_639_) == 0)
{
lean_object* v_snd_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v_snd_640_ = lean_ctor_get(v_a_635_, 1);
lean_inc(v_snd_640_);
lean_dec(v_a_635_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v_snd_640_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_641_);
v___x_643_ = v___x_637_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v_val_645_; lean_object* v___x_647_; 
lean_inc_ref(v_fst_639_);
lean_dec(v_a_635_);
v_val_645_ = lean_ctor_get(v_fst_639_, 0);
lean_inc(v_val_645_);
lean_dec_ref_known(v_fst_639_, 1);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v_val_645_);
v___x_647_ = v___x_637_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_val_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_a_650_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_634_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_634_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v_vs_658_; lean_object* v___x_659_; lean_object* v___x_660_; size_t v_sz_661_; size_t v___x_662_; lean_object* v___x_663_; 
v_vs_658_ = lean_ctor_get(v_n_622_, 0);
v___x_659_ = lean_box(0);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_b_623_);
v_sz_661_ = lean_array_size(v_vs_658_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_621_, v_vs_658_, v_sz_661_, v___x_662_, v___x_660_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_678_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_678_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_fst_668_; 
v_fst_668_ = lean_ctor_get(v_a_664_, 0);
if (lean_obj_tag(v_fst_668_) == 0)
{
lean_object* v_snd_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v_snd_669_ = lean_ctor_get(v_a_664_, 1);
lean_inc(v_snd_669_);
lean_dec(v_a_664_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v_snd_669_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_670_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v_val_674_; lean_object* v___x_676_; 
lean_inc_ref(v_fst_668_);
lean_dec(v_a_664_);
v_val_674_ = lean_ctor_get(v_fst_668_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_fst_668_, 1);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v_val_674_);
v___x_676_ = v___x_666_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_val_674_);
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
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_679_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_663_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_663_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object* v_init_687_, lean_object* v_goal_688_, lean_object* v_as_689_, size_t v_sz_690_, size_t v_i_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = lean_usize_dec_lt(v_i_691_, v_sz_690_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v_b_692_);
return v___x_699_;
}
else
{
lean_object* v_snd_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_734_; 
v_snd_700_ = lean_ctor_get(v_b_692_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_b_692_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_b_692_, 0);
lean_dec(v_unused_735_);
v___x_702_ = v_b_692_;
v_isShared_703_ = v_isSharedCheck_734_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_snd_700_);
lean_dec(v_b_692_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_734_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_704_ = lean_array_uget_borrowed(v_as_689_, v_i_691_);
lean_inc(v_snd_700_);
v___x_705_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_687_, v_goal_688_, v_a_704_, v_snd_700_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_725_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_725_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_725_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_725_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
if (lean_obj_tag(v_a_706_) == 0)
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_a_706_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_710_);
v___x_712_ = v___x_702_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_snd_700_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_712_);
v___x_714_ = v___x_708_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_del_object(v___x_708_);
lean_dec(v_snd_700_);
v_a_717_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v_a_706_, 1);
v___x_718_ = lean_box(0);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_a_717_);
lean_ctor_set(v___x_702_, 0, v___x_718_);
v___x_720_ = v___x_702_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_a_717_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
size_t v___x_721_; size_t v___x_722_; 
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_691_, v___x_721_);
v_i_691_ = v___x_722_;
v_b_692_ = v___x_720_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_del_object(v___x_702_);
lean_dec(v_snd_700_);
v_a_726_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_705_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_705_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object* v_init_736_, lean_object* v_goal_737_, lean_object* v_as_738_, lean_object* v_sz_739_, lean_object* v_i_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
size_t v_sz_boxed_747_; size_t v_i_boxed_748_; lean_object* v_res_749_; 
v_sz_boxed_747_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_748_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_736_, v_goal_737_, v_as_738_, v_sz_boxed_747_, v_i_boxed_748_, v_b_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v_as_738_);
lean_dec_ref(v_goal_737_);
lean_dec_ref(v_init_736_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object* v_init_750_, lean_object* v_goal_751_, lean_object* v_n_752_, lean_object* v_b_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_750_, v_goal_751_, v_n_752_, v_b_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec_ref(v_n_752_);
lean_dec_ref(v_goal_751_);
lean_dec_ref(v_init_750_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object* v_goal_760_, lean_object* v_as_761_, size_t v_sz_762_, size_t v_i_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_lt(v_i_763_, v_sz_762_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_b_764_);
return v___x_771_;
}
else
{
lean_object* v_snd_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_821_; 
v_snd_772_ = lean_ctor_get(v_b_764_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_b_764_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_b_764_, 0);
lean_dec(v_unused_822_);
v___x_774_ = v_b_764_;
v_isShared_775_ = v_isSharedCheck_821_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_snd_772_);
lean_dec(v_b_764_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_821_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_array_uget_borrowed(v_as_761_, v_i_763_);
lean_inc(v_a_776_);
v___x_777_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_760_, v_a_776_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; lean_object* v_a_781_; uint8_t v___x_788_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = lean_box(0);
v___x_788_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_778_);
if (v___x_788_ == 0)
{
lean_dec(v_a_778_);
v_a_781_ = v_snd_772_;
goto v___jp_780_;
}
else
{
lean_object* v___x_789_; 
lean_inc(v_a_778_);
v___x_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_778_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; uint8_t v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_unbox(v_a_790_);
lean_dec(v_a_790_);
if (v___x_791_ == 0)
{
lean_dec(v_a_778_);
v_a_781_ = v_snd_772_;
goto v___jp_780_;
}
else
{
lean_object* v_self_792_; lean_object* v___x_793_; 
v_self_792_ = lean_ctor_get(v_a_778_, 0);
lean_inc_ref_n(v_self_792_, 2);
lean_dec(v_a_778_);
v___x_793_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_760_, v_self_792_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
if (lean_obj_tag(v_a_794_) == 1)
{
lean_object* v_val_795_; lean_object* v___x_796_; 
v_val_795_ = lean_ctor_get(v_a_794_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v_a_794_, 1);
v___x_796_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_760_, v_self_792_, v_val_795_, v_snd_772_);
v_a_781_ = v___x_796_;
goto v___jp_780_;
}
else
{
lean_dec(v_a_794_);
lean_dec_ref(v_self_792_);
v_a_781_ = v_snd_772_;
goto v___jp_780_;
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_self_792_);
lean_del_object(v___x_774_);
lean_dec(v_snd_772_);
v_a_797_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_793_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_793_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_a_778_);
lean_del_object(v___x_774_);
lean_dec(v_snd_772_);
v_a_805_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_789_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_789_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
v___jp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_a_781_);
lean_ctor_set(v___x_774_, 0, v___x_779_);
v___x_783_ = v___x_774_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_a_781_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
size_t v___x_784_; size_t v___x_785_; 
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_763_, v___x_784_);
v_i_763_ = v___x_785_;
v_b_764_ = v___x_783_;
goto _start;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_del_object(v___x_774_);
lean_dec(v_snd_772_);
v_a_813_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_777_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_777_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object* v_goal_823_, lean_object* v_as_824_, lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
size_t v_sz_boxed_833_; size_t v_i_boxed_834_; lean_object* v_res_835_; 
v_sz_boxed_833_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_834_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_823_, v_as_824_, v_sz_boxed_833_, v_i_boxed_834_, v_b_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec_ref(v_as_824_);
lean_dec_ref(v_goal_823_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object* v_goal_836_, lean_object* v_as_837_, size_t v_sz_838_, size_t v_i_839_, lean_object* v_b_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_lt(v_i_839_, v_sz_838_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_b_840_);
return v___x_847_;
}
else
{
lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_897_; 
v_snd_848_ = lean_ctor_get(v_b_840_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_b_840_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v_b_840_, 0);
lean_dec(v_unused_898_);
v___x_850_ = v_b_840_;
v_isShared_851_ = v_isSharedCheck_897_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_dec(v_b_840_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_897_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_array_uget_borrowed(v_as_837_, v_i_839_);
lean_inc(v_a_852_);
v___x_853_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_836_, v_a_852_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v_a_857_; uint8_t v___x_864_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = lean_box(0);
v___x_864_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_854_);
if (v___x_864_ == 0)
{
lean_dec(v_a_854_);
v_a_857_ = v_snd_848_;
goto v___jp_856_;
}
else
{
lean_object* v___x_865_; 
lean_inc(v_a_854_);
v___x_865_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_854_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; uint8_t v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_867_ == 0)
{
lean_dec(v_a_854_);
v_a_857_ = v_snd_848_;
goto v___jp_856_;
}
else
{
lean_object* v_self_868_; lean_object* v___x_869_; 
v_self_868_ = lean_ctor_get(v_a_854_, 0);
lean_inc_ref_n(v_self_868_, 2);
lean_dec(v_a_854_);
v___x_869_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_836_, v_self_868_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
if (lean_obj_tag(v_a_870_) == 1)
{
lean_object* v_val_871_; lean_object* v___x_872_; 
v_val_871_ = lean_ctor_get(v_a_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_a_870_, 1);
v___x_872_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_836_, v_self_868_, v_val_871_, v_snd_848_);
v_a_857_ = v___x_872_;
goto v___jp_856_;
}
else
{
lean_dec(v_a_870_);
lean_dec_ref(v_self_868_);
v_a_857_ = v_snd_848_;
goto v___jp_856_;
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v_self_868_);
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_873_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_869_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_869_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_854_);
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_881_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_865_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_865_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
v___jp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_857_);
lean_ctor_set(v___x_850_, 0, v___x_855_);
v___x_859_ = v___x_850_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_a_857_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_add(v_i_839_, v___x_860_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_836_, v_as_837_, v_sz_838_, v___x_861_, v___x_859_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
return v___x_862_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_889_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_853_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_853_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object* v_goal_899_, lean_object* v_as_900_, lean_object* v_sz_901_, lean_object* v_i_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
size_t v_sz_boxed_909_; size_t v_i_boxed_910_; lean_object* v_res_911_; 
v_sz_boxed_909_ = lean_unbox_usize(v_sz_901_);
lean_dec(v_sz_901_);
v_i_boxed_910_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_res_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_899_, v_as_900_, v_sz_boxed_909_, v_i_boxed_910_, v_b_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v_as_900_);
lean_dec_ref(v_goal_899_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object* v_goal_912_, lean_object* v_t_913_, lean_object* v_init_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_root_920_; lean_object* v_tail_921_; lean_object* v___x_922_; 
v_root_920_ = lean_ctor_get(v_t_913_, 0);
v_tail_921_ = lean_ctor_get(v_t_913_, 1);
lean_inc_ref(v_init_914_);
v___x_922_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_914_, v_goal_912_, v_root_920_, v_init_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec_ref(v_init_914_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_959_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_959_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_959_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_959_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_a_923_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; 
v_a_927_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v_a_923_, 1);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_a_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_932_; lean_object* v___x_933_; size_t v_sz_934_; size_t v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_925_);
v_a_931_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v_a_923_, 1);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v_a_931_);
v_sz_934_ = lean_array_size(v_tail_921_);
v___x_935_ = ((size_t)0ULL);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_912_, v_tail_921_, v_sz_934_, v___x_935_, v___x_933_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_950_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_fst_941_; 
v_fst_941_ = lean_ctor_get(v_a_937_, 0);
if (lean_obj_tag(v_fst_941_) == 0)
{
lean_object* v_snd_942_; lean_object* v___x_944_; 
v_snd_942_ = lean_ctor_get(v_a_937_, 1);
lean_inc(v_snd_942_);
lean_dec(v_a_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_snd_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_snd_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
else
{
lean_object* v_val_946_; lean_object* v___x_948_; 
lean_inc_ref(v_fst_941_);
lean_dec(v_a_937_);
v_val_946_ = lean_ctor_get(v_fst_941_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v_fst_941_, 1);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_val_946_);
v___x_948_ = v___x_939_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_val_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_936_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_936_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_922_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_922_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object* v_goal_968_, lean_object* v_t_969_, lean_object* v_init_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_968_, v_t_969_, v_init_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec_ref(v_t_969_);
lean_dec_ref(v_goal_968_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object* v_a_977_, lean_object* v_x_978_){
_start:
{
if (lean_obj_tag(v_x_978_) == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_box(0);
return v___x_979_;
}
else
{
lean_object* v_key_980_; lean_object* v_value_981_; lean_object* v_tail_982_; uint8_t v___x_983_; 
v_key_980_ = lean_ctor_get(v_x_978_, 0);
v_value_981_ = lean_ctor_get(v_x_978_, 1);
v_tail_982_ = lean_ctor_get(v_x_978_, 2);
v___x_983_ = lean_expr_eqv(v_key_980_, v_a_977_);
if (v___x_983_ == 0)
{
v_x_978_ = v_tail_982_;
goto _start;
}
else
{
lean_object* v___x_985_; 
lean_inc(v_value_981_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_value_981_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_986_, v_x_987_);
lean_dec(v_x_987_);
lean_dec_ref(v_a_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object* v_m_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_buckets_991_; lean_object* v___x_992_; uint64_t v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; uint64_t v_fold_996_; uint64_t v___x_997_; uint64_t v___x_998_; uint64_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_buckets_991_ = lean_ctor_get(v_m_989_, 1);
v___x_992_ = lean_array_get_size(v_buckets_991_);
v___x_993_ = l_Lean_Expr_hash(v_a_990_);
v___x_994_ = 32ULL;
v___x_995_ = lean_uint64_shift_right(v___x_993_, v___x_994_);
v_fold_996_ = lean_uint64_xor(v___x_993_, v___x_995_);
v___x_997_ = 16ULL;
v___x_998_ = lean_uint64_shift_right(v_fold_996_, v___x_997_);
v___x_999_ = lean_uint64_xor(v_fold_996_, v___x_998_);
v___x_1000_ = lean_uint64_to_usize(v___x_999_);
v___x_1001_ = lean_usize_of_nat(v___x_992_);
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_sub(v___x_1001_, v___x_1002_);
v___x_1004_ = lean_usize_land(v___x_1000_, v___x_1003_);
v___x_1005_ = lean_array_uget_borrowed(v_buckets_991_, v___x_1004_);
v___x_1006_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_990_, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object* v_m_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1007_, v_a_1008_);
lean_dec_ref(v_a_1008_);
lean_dec_ref(v_m_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object* v_goal_1010_, lean_object* v_as_1011_, size_t v_sz_1012_, size_t v_i_1013_, lean_object* v_b_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_a_1021_; uint8_t v___x_1025_; 
v___x_1025_ = lean_usize_dec_lt(v_i_1013_, v_sz_1012_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_b_1014_);
return v___x_1026_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_array_uget_borrowed(v_as_1011_, v_i_1013_);
lean_inc(v_a_1027_);
v___x_1028_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1010_, v_a_1027_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_self_1030_; lean_object* v___x_1031_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v_self_1030_ = lean_ctor_get(v_a_1029_, 0);
lean_inc_ref_n(v_self_1030_, 2);
lean_dec(v_a_1029_);
v___x_1031_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1030_);
if (lean_obj_tag(v___x_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1033_; 
v_val_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1014_, v_val_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1014_, v_self_1030_);
lean_dec_ref(v_self_1030_);
if (lean_obj_tag(v___x_1034_) == 1)
{
lean_object* v_val_1035_; lean_object* v___x_1036_; 
v_val_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1010_, v_val_1032_, v_val_1035_, v_b_1014_);
v_a_1021_ = v___x_1036_;
goto v___jp_1020_;
}
else
{
lean_dec(v___x_1034_);
lean_dec(v_val_1032_);
v_a_1021_ = v_b_1014_;
goto v___jp_1020_;
}
}
else
{
lean_dec_ref_known(v___x_1033_, 1);
lean_dec(v_val_1032_);
lean_dec_ref(v_self_1030_);
v_a_1021_ = v_b_1014_;
goto v___jp_1020_;
}
}
else
{
lean_dec(v___x_1031_);
lean_dec_ref(v_self_1030_);
v_a_1021_ = v_b_1014_;
goto v___jp_1020_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_b_1014_);
v_a_1037_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1028_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1028_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
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
v___jp_1020_:
{
size_t v___x_1022_; size_t v___x_1023_; 
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1013_, v___x_1022_);
v_i_1013_ = v___x_1023_;
v_b_1014_ = v_a_1021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object* v_goal_1045_, lean_object* v_as_1046_, lean_object* v_sz_1047_, lean_object* v_i_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1047_);
lean_dec(v_sz_1047_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1048_);
lean_dec(v_i_1048_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1045_, v_as_1046_, v_sz_boxed_1055_, v_i_boxed_1056_, v_b_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v_as_1046_);
lean_dec_ref(v_goal_1045_);
return v_res_1057_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_unsigned_to_nat(16u);
v___x_1060_ = lean_mk_array(v___x_1059_, v___x_1058_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_model_1063_; 
v___x_1061_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0);
v___x_1062_ = lean_unsigned_to_nat(0u);
v_model_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_1063_, 0, v___x_1062_);
lean_ctor_set(v_model_1063_, 1, v___x_1061_);
return v_model_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object* v_goal_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_toGoalState_1078_; lean_object* v_exprs_1079_; lean_object* v_model_1080_; lean_object* v___x_1081_; 
v_toGoalState_1078_ = lean_ctor_get(v_goal_1072_, 0);
v_exprs_1079_ = lean_ctor_get(v_toGoalState_1078_, 2);
v_model_1080_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1);
v___x_1081_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1072_, v_exprs_1079_, v_model_1080_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = l_Lean_PersistentArray_toArray___redArg(v_exprs_1079_);
v___x_1084_ = l_Array_reverse___redArg(v___x_1083_);
v_sz_1085_ = lean_array_size(v___x_1084_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1072_, v___x_1084_, v_sz_1085_, v___x_1086_, v_a_1082_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec_ref(v___x_1084_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2));
v___x_1090_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1072_, v___x_1089_, v_a_1088_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6));
v___x_1093_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_1092_, v_a_1091_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1093_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___x_1093_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_a_1091_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1091_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_a_1091_);
v_a_1102_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1093_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1093_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
return v___x_1090_;
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1087_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1087_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1081_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1081_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object* v_goal_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec_ref(v_goal_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object* v_00_u03b2_1133_, lean_object* v_m_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1134_, v_a_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object* v_00_u03b2_1137_, lean_object* v_m_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(v_00_u03b2_1137_, v_m_1138_, v_a_1139_);
lean_dec_ref(v_a_1139_);
lean_dec_ref(v_m_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object* v_00_u03b2_1141_, lean_object* v_a_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1142_, v_x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1145_, lean_object* v_a_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(v_00_u03b2_1145_, v_a_1146_, v_x_1147_);
lean_dec(v_x_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1148_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
}
#ifdef __cplusplus
}
#endif

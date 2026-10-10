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
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
extern lean_object* l_instInhabitedRat;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(lean_object* v_self_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; 
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_7_ = lean_infer_type(v_self_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_n(v_a_8_, 2);
lean_dec_ref_known(v___x_7_, 1);
v___x_9_ = l_Lean_Int_mkType;
v___x_10_ = l_Lean_Meta_isExprDefEq(v_a_8_, v___x_9_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; uint8_t v___x_12_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
v___x_12_ = lean_unbox(v_a_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec_ref_known(v___x_10_, 1);
v___x_13_ = l_Lean_Nat_mkType;
v___x_14_ = l_Lean_Meta_isExprDefEq(v_a_8_, v___x_13_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
lean_dec(v___y_5_);
lean_dec_ref(v___y_4_);
lean_dec(v___y_3_);
lean_dec_ref(v___y_2_);
return v___x_14_;
}
else
{
lean_dec(v_a_8_);
lean_dec(v___y_5_);
lean_dec_ref(v___y_4_);
lean_dec(v___y_3_);
lean_dec_ref(v___y_2_);
return v___x_10_;
}
}
else
{
lean_dec(v_a_8_);
lean_dec(v___y_5_);
lean_dec_ref(v___y_4_);
lean_dec(v___y_3_);
lean_dec_ref(v___y_2_);
return v___x_10_;
}
}
else
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_22_; 
lean_dec(v___y_5_);
lean_dec_ref(v___y_4_);
lean_dec(v___y_3_);
lean_dec_ref(v___y_2_);
v_a_15_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_22_ == 0)
{
v___x_17_ = v___x_7_;
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_7_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_a_15_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_23_;
v_res_23_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(v_self_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0___boxed(lean_object* v_self_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(v_self_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
return v_res_30_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(lean_object* v_n_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___y_38_; lean_object* v_self_55_; lean_object* v___x_56_; uint8_t v_transparency_57_; uint8_t v___x_58_; uint8_t v___x_59_; 
v_self_55_ = lean_ctor_get(v_n_31_, 0);
lean_inc_ref(v_self_55_);
lean_dec_ref(v_n_31_);
v___x_56_ = l_Lean_Meta_Context_config(v_a_32_);
v_transparency_57_ = lean_ctor_get_uint8(v___x_56_, 9);
lean_dec_ref(v___x_56_);
v___x_58_ = 1;
v___x_59_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v_keyedConfig_60_; uint8_t v_trackZetaDelta_61_; lean_object* v_zetaDeltaSet_62_; lean_object* v_lctx_63_; lean_object* v_localInstances_64_; lean_object* v_defEqCtx_x3f_65_; lean_object* v_synthPendingDepth_66_; lean_object* v_customCanUnfoldPredicate_x3f_67_; uint8_t v_univApprox_68_; uint8_t v_inTypeClassResolution_69_; uint8_t v_cacheInferType_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_keyedConfig_60_ = lean_ctor_get(v_a_32_, 0);
v_trackZetaDelta_61_ = lean_ctor_get_uint8(v_a_32_, sizeof(void*)*7);
v_zetaDeltaSet_62_ = lean_ctor_get(v_a_32_, 1);
v_lctx_63_ = lean_ctor_get(v_a_32_, 2);
v_localInstances_64_ = lean_ctor_get(v_a_32_, 3);
v_defEqCtx_x3f_65_ = lean_ctor_get(v_a_32_, 4);
v_synthPendingDepth_66_ = lean_ctor_get(v_a_32_, 5);
v_customCanUnfoldPredicate_x3f_67_ = lean_ctor_get(v_a_32_, 6);
v_univApprox_68_ = lean_ctor_get_uint8(v_a_32_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_69_ = lean_ctor_get_uint8(v_a_32_, sizeof(void*)*7 + 2);
v_cacheInferType_70_ = lean_ctor_get_uint8(v_a_32_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_60_);
v___x_71_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_58_, v_keyedConfig_60_);
lean_inc(v_customCanUnfoldPredicate_x3f_67_);
lean_inc(v_synthPendingDepth_66_);
lean_inc(v_defEqCtx_x3f_65_);
lean_inc_ref(v_localInstances_64_);
lean_inc_ref(v_lctx_63_);
lean_inc(v_zetaDeltaSet_62_);
v___x_72_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_zetaDeltaSet_62_);
lean_ctor_set(v___x_72_, 2, v_lctx_63_);
lean_ctor_set(v___x_72_, 3, v_localInstances_64_);
lean_ctor_set(v___x_72_, 4, v_defEqCtx_x3f_65_);
lean_ctor_set(v___x_72_, 5, v_synthPendingDepth_66_);
lean_ctor_set(v___x_72_, 6, v_customCanUnfoldPredicate_x3f_67_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*7, v_trackZetaDelta_61_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*7 + 1, v_univApprox_68_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*7 + 2, v_inTypeClassResolution_69_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*7 + 3, v_cacheInferType_70_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
v___x_73_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(v_self_55_, v___x_72_, v_a_33_, v_a_34_, v_a_35_);
v___y_38_ = v___x_73_;
goto v___jp_37_;
}
else
{
lean_object* v___x_74_; 
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
v___x_74_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(v_self_55_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
v___y_38_ = v___x_74_;
goto v___jp_37_;
}
v___jp_37_:
{
if (lean_obj_tag(v___y_38_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___y_38_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___y_38_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___y_38_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___y_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
else
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_54_; 
v_a_47_ = lean_ctor_get(v___y_38_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___y_38_);
if (v_isSharedCheck_54_ == 0)
{
v___x_49_ = v___y_38_;
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___y_38_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_31_ = stack[0].m_obj;
lean_object* v_a_32_ = stack[1].m_obj;
lean_object* v_a_33_ = stack[2].m_obj;
lean_object* v_a_34_ = stack[3].m_obj;
lean_object* v_a_35_ = stack[4].m_obj;
lean_object* v_res_75_;
v_res_75_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_n_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(lean_object* v_n_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_n_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_82_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = l_instInhabitedError;
v___x_84_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_84_, 0, lean_box(0));
lean_closure_set(v___x_84_, 1, lean_box(0));
lean_closure_set(v___x_84_, 2, v___x_83_);
return v___x_84_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(lean_object* v_msg_85_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_347__overap_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0);
v___x_347__overap_88_ = lean_panic_fn_borrowed(v___x_87_, v_msg_85_);
v___x_89_ = lean_apply_1(v___x_347__overap_88_, lean_box(0));
return v___x_89_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_85_ = stack[0].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v_msg_85_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(lean_object* v_msg_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v_msg_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_94_, lean_object* v_vals_95_, lean_object* v_i_96_, lean_object* v_k_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_array_get_size(v_keys_94_);
v___x_99_ = lean_nat_dec_lt(v_i_96_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec(v_i_96_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v_k_x27_101_; size_t v___x_102_; size_t v___x_103_; uint8_t v___x_104_; 
v_k_x27_101_ = lean_array_fget_borrowed(v_keys_94_, v_i_96_);
v___x_102_ = lean_ptr_addr(v_k_97_);
v___x_103_ = lean_ptr_addr(v_k_x27_101_);
v___x_104_ = lean_usize_dec_eq(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_i_96_, v___x_105_);
lean_dec(v_i_96_);
v_i_96_ = v___x_106_;
goto _start;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_array_fget_borrowed(v_vals_95_, v_i_96_);
lean_dec(v_i_96_);
lean_inc(v___x_108_);
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_110_, lean_object* v_vals_111_, lean_object* v_i_112_, lean_object* v_k_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_110_, v_vals_111_, v_i_112_, v_k_113_);
lean_dec_ref(v_k_113_);
lean_dec_ref(v_vals_111_);
lean_dec_ref(v_keys_110_);
return v_res_114_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(lean_object* v_x_115_, size_t v_x_116_, lean_object* v_x_117_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v_es_118_; lean_object* v___x_119_; size_t v___x_120_; size_t v___x_121_; lean_object* v_j_122_; lean_object* v___x_123_; 
v_es_118_ = lean_ctor_get(v_x_115_, 0);
v___x_119_ = lean_box(2);
v___x_120_ = ((size_t)31ULL);
v___x_121_ = lean_usize_land(v_x_116_, v___x_120_);
v_j_122_ = lean_usize_to_nat(v___x_121_);
v___x_123_ = lean_array_get_borrowed(v___x_119_, v_es_118_, v_j_122_);
lean_dec(v_j_122_);
switch(lean_obj_tag(v___x_123_))
{
case 0:
{
lean_object* v_key_124_; lean_object* v_val_125_; size_t v___x_126_; size_t v___x_127_; uint8_t v___x_128_; 
v_key_124_ = lean_ctor_get(v___x_123_, 0);
v_val_125_ = lean_ctor_get(v___x_123_, 1);
v___x_126_ = lean_ptr_addr(v_x_117_);
v___x_127_ = lean_ptr_addr(v_key_124_);
v___x_128_ = lean_usize_dec_eq(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
lean_inc(v_val_125_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v_val_125_);
return v___x_130_;
}
}
case 1:
{
lean_object* v_node_131_; size_t v___x_132_; size_t v___x_133_; 
v_node_131_ = lean_ctor_get(v___x_123_, 0);
v___x_132_ = ((size_t)5ULL);
v___x_133_ = lean_usize_shift_right(v_x_116_, v___x_132_);
v_x_115_ = v_node_131_;
v_x_116_ = v___x_133_;
goto _start;
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
}
else
{
lean_object* v_ks_136_; lean_object* v_vs_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_ks_136_ = lean_ctor_get(v_x_115_, 0);
v_vs_137_ = lean_ctor_get(v_x_115_, 1);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_ks_136_, v_vs_137_, v___x_138_, v_x_117_);
return v___x_139_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_115_ = stack[0].m_obj;
size_t v_x_116_ = stack[1].m_num;
lean_object* v_x_117_ = stack[2].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_115_, v_x_116_, v_x_117_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
size_t v_x_567__boxed_144_; lean_object* v_res_145_; 
v_x_567__boxed_144_ = lean_unbox_usize(v_x_142_);
lean_dec(v_x_142_);
v_res_145_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_141_, v_x_567__boxed_144_, v_x_143_);
lean_dec_ref(v_x_143_);
lean_dec_ref(v_x_141_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; uint64_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; 
v___x_148_ = lean_ptr_addr(v_x_147_);
v___x_149_ = ((size_t)3ULL);
v___x_150_ = lean_usize_shift_right(v___x_148_, v___x_149_);
v___x_151_ = lean_usize_to_uint64(v___x_150_);
v___x_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_146_, v___x_152_, v_x_147_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_154_, v_x_155_);
lean_dec_ref(v_x_155_);
lean_dec_ref(v_x_154_);
return v_res_156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2));
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_unsigned_to_nat(21u);
v___x_163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1));
v___x_164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0));
v___x_165_ = l_mkPanicMessageWithDecl(v___x_164_, v___x_163_, v___x_162_, v___x_161_, v___x_160_);
return v___x_165_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(lean_object* v_goal_166_, lean_object* v_node_167_){
_start:
{
lean_object* v_self_169_; lean_object* v_root_170_; size_t v___x_171_; size_t v___x_172_; uint8_t v___x_173_; 
v_self_169_ = lean_ctor_get(v_node_167_, 0);
v_root_170_ = lean_ctor_get(v_node_167_, 2);
v___x_171_ = lean_ptr_addr(v_self_169_);
v___x_172_ = lean_ptr_addr(v_root_170_);
v___x_173_ = lean_usize_dec_eq(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3);
v___x_175_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v___x_174_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_177_ = l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(v___x_176_, v_node_167_);
if (lean_obj_tag(v___x_177_) == 1)
{
lean_object* v_val_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_val_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_val_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = l_instInhabitedRat;
v___x_180_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_176_, v_goal_166_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_210_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_210_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_210_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_210_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_varMap_185_; lean_object* v_assignment_186_; lean_object* v___x_187_; 
v_varMap_185_ = lean_ctor_get(v_a_181_, 1);
lean_inc_ref(v_varMap_185_);
v_assignment_186_ = lean_ctor_get(v_a_181_, 12);
lean_inc_ref(v_assignment_186_);
lean_dec(v_a_181_);
v___x_187_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_varMap_185_, v_val_178_);
lean_dec(v_val_178_);
lean_dec_ref(v_varMap_185_);
if (lean_obj_tag(v___x_187_) == 1)
{
lean_object* v_val_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_205_; 
v_val_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_205_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_205_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_val_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_205_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_size_192_; uint8_t v___x_193_; 
v_size_192_ = lean_ctor_get(v_assignment_186_, 2);
v___x_193_ = lean_nat_dec_lt(v_val_188_, v_size_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_del_object(v___x_190_);
lean_dec(v_val_188_);
lean_dec_ref(v_assignment_186_);
v___x_194_ = lean_box(0);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_194_);
v___x_196_ = v___x_183_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = l_Lean_PersistentArray_get_x21___redArg(v___x_179_, v_assignment_186_, v_val_188_);
lean_dec(v_val_188_);
lean_dec_ref(v_assignment_186_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_198_);
v___x_200_ = v___x_190_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_200_);
v___x_202_ = v___x_183_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec(v___x_187_);
lean_dec_ref(v_assignment_186_);
v___x_206_ = lean_box(0);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_206_);
v___x_208_ = v___x_183_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_val_178_);
v_a_211_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_180_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_180_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v___x_177_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_166_ = stack[0].m_obj;
lean_object* v_node_167_ = stack[1].m_obj;
lean_object* v_res_221_;
v_res_221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_166_, v_node_167_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object* v_goal_222_, lean_object* v_node_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_222_, v_node_223_);
lean_dec_ref(v_node_223_);
lean_dec_ref(v_goal_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object* v_00_u03b2_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_227_, v_x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object* v_00_u03b2_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(v_00_u03b2_230_, v_x_231_, v_x_232_);
lean_dec_ref(v_x_232_);
lean_dec_ref(v_x_231_);
return v_res_233_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object* v_00_u03b2_234_, lean_object* v_x_235_, size_t v_x_236_, lean_object* v_x_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_235_, v_x_236_, v_x_237_);
return v___x_238_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_235_ = stack[1].m_obj;
size_t v_x_236_ = stack[2].m_num;
lean_object* v_x_237_ = stack[3].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_box(0), v_x_235_, v_x_236_, v_x_237_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
size_t v_x_868__boxed_244_; lean_object* v_res_245_; 
v_x_868__boxed_244_ = lean_unbox_usize(v_x_242_);
lean_dec(v_x_242_);
v_res_245_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(v_00_u03b2_240_, v_x_241_, v_x_868__boxed_244_, v_x_243_);
lean_dec_ref(v_x_243_);
lean_dec_ref(v_x_241_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_246_, lean_object* v_keys_247_, lean_object* v_vals_248_, lean_object* v_heq_249_, lean_object* v_i_250_, lean_object* v_k_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_247_, v_vals_248_, v_i_250_, v_k_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_253_, lean_object* v_keys_254_, lean_object* v_vals_255_, lean_object* v_heq_256_, lean_object* v_i_257_, lean_object* v_k_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(v_00_u03b2_253_, v_keys_254_, v_vals_255_, v_heq_256_, v_i_257_, v_k_258_);
lean_dec_ref(v_k_258_);
lean_dec_ref(v_vals_255_);
lean_dec_ref(v_keys_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(lean_object* v_e_315_){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = l_Lean_Expr_cleanupAnnotations(v_e_315_);
v___x_317_ = l_Lean_Expr_isApp(v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
lean_dec_ref(v___x_316_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
else
{
lean_object* v_arg_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_arg_319_ = lean_ctor_get(v___x_316_, 1);
lean_inc_ref(v_arg_319_);
v___x_320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_316_);
v___x_321_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2));
v___x_322_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4));
v___x_324_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6));
v___x_326_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8));
v___x_328_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10));
v___x_330_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12));
v___x_332_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16));
v___x_336_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18));
v___x_338_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20));
v___x_340_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_339_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = l_Lean_Expr_isApp(v___x_320_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_dec_ref(v___x_320_);
lean_dec_ref(v_arg_319_);
v___x_342_ = lean_box(0);
return v___x_342_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_320_);
v___x_344_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23));
v___x_345_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25));
v___x_347_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_343_, v___x_348_);
lean_dec_ref(v___x_343_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec_ref(v_arg_319_);
v___x_350_ = lean_box(0);
return v___x_350_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_arg_319_);
return v___x_351_;
}
}
else
{
lean_object* v___x_352_; 
lean_dec_ref(v___x_343_);
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v_arg_319_);
return v___x_352_;
}
}
else
{
lean_object* v___x_353_; 
lean_dec_ref(v___x_343_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_arg_319_);
return v___x_353_;
}
}
}
else
{
lean_object* v___x_354_; 
lean_dec_ref(v___x_320_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v_arg_319_);
return v___x_354_;
}
}
else
{
lean_object* v___x_355_; 
lean_dec_ref(v___x_320_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_arg_319_);
return v___x_355_;
}
}
else
{
lean_object* v___x_356_; 
lean_dec_ref(v___x_320_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_arg_319_);
return v___x_356_;
}
}
else
{
lean_object* v___x_357_; 
lean_dec_ref(v___x_320_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_arg_319_);
return v___x_357_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec_ref(v___x_320_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_arg_319_);
return v___x_358_;
}
}
else
{
lean_object* v___x_359_; 
lean_dec_ref(v___x_320_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v_arg_319_);
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; 
lean_dec_ref(v___x_320_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v_arg_319_);
return v___x_360_;
}
}
else
{
lean_object* v___x_361_; 
lean_dec_ref(v___x_320_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v_arg_319_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; 
lean_dec_ref(v___x_320_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v_arg_319_);
return v___x_362_;
}
}
else
{
lean_object* v___x_363_; 
lean_dec_ref(v___x_320_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v_arg_319_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object* v_e_372_){
_start:
{
lean_object* v___x_373_; uint8_t v___x_374_; 
lean_inc_ref(v_e_372_);
v___x_373_ = l_Lean_Expr_cleanupAnnotations(v_e_372_);
v___x_374_ = l_Lean_Expr_isApp(v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec_ref(v___x_373_);
v___x_375_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_372_);
return v___x_375_;
}
else
{
lean_object* v_arg_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_arg_376_ = lean_ctor_get(v___x_373_, 1);
lean_inc_ref(v_arg_376_);
v___x_377_ = l_Lean_Expr_appFnCleanup___redArg(v___x_373_);
v___x_378_ = l_Lean_Expr_isApp(v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec_ref(v___x_377_);
lean_dec_ref(v_arg_376_);
v___x_379_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_372_);
return v___x_379_;
}
else
{
lean_object* v_arg_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_arg_380_ = lean_ctor_get(v___x_377_, 1);
lean_inc_ref(v_arg_380_);
v___x_381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_377_);
v___x_382_ = l_Lean_Expr_isApp(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v___x_381_);
lean_dec_ref(v_arg_380_);
lean_dec_ref(v_arg_376_);
v___x_383_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_372_);
return v___x_383_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_384_ = l_Lean_Expr_appFnCleanup___redArg(v___x_381_);
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2));
v___x_386_ = l_Lean_Expr_isConstOf(v___x_384_, v___x_385_);
lean_dec_ref(v___x_384_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec_ref(v_arg_380_);
lean_dec_ref(v_arg_376_);
v___x_387_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_372_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
lean_dec_ref(v_e_372_);
v___x_388_ = l_Lean_Expr_cleanupAnnotations(v_arg_380_);
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4));
v___x_390_ = l_Lean_Expr_isConstOf(v___x_388_, v___x_389_);
lean_dec_ref(v___x_388_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec_ref(v_arg_376_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v_arg_376_);
return v___x_392_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object* v_a_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Rat_ofInt(v_a_393_);
return v___x_394_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object* v_goal_395_, lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Grind_Goal_getRoot(v_goal_395_, v_e_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_395_, v_a_403_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v_ref_406_; lean_object* v___x_407_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
v_ref_406_ = lean_ctor_get(v_a_399_, 2);
v___x_407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_395_, v_a_405_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_473_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_473_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_473_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_473_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
if (lean_obj_tag(v_a_408_) == 1)
{
lean_object* v___x_413_; 
lean_dec(v_a_405_);
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
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
lean_object* v_self_415_; lean_object* v___x_416_; 
lean_del_object(v___x_410_);
lean_dec(v_a_408_);
v_self_415_ = lean_ctor_get(v_a_405_, 0);
lean_inc_ref_n(v_self_415_, 2);
lean_dec(v_a_405_);
v___x_416_ = l_Lean_Meta_getIntValue_x3f(v_self_415_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_464_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_464_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_464_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_464_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
if (lean_obj_tag(v_a_417_) == 1)
{
lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_self_415_);
v_val_421_ = lean_ctor_get(v_a_417_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_432_ == 0)
{
v___x_423_ = v_a_417_;
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_val_421_);
lean_dec(v_a_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = l_Rat_ofInt(v_val_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_427_);
v___x_429_ = v___x_419_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v___x_433_; 
lean_del_object(v___x_419_);
lean_dec(v_a_417_);
v___x_433_ = l_Lean_Meta_getNatValue_x3f(v_self_415_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec_ref(v_self_415_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_455_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_455_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_455_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_455_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
if (lean_obj_tag(v_a_434_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_450_; 
v_val_438_ = lean_ctor_get(v_a_434_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_450_ == 0)
{
v___x_440_ = v_a_434_;
v_isShared_441_ = v_isSharedCheck_450_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_val_438_);
lean_dec(v_a_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_450_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_442_ = lean_nat_to_int(v_val_438_);
v___x_443_ = l_Rat_ofInt(v___x_442_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_443_);
v___x_445_ = v___x_440_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_449_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_445_);
v___x_447_ = v___x_436_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_dec(v_a_434_);
v___x_451_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_451_);
v___x_453_ = v___x_436_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_433_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_433_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_self_415_);
v_a_465_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_416_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_416_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_485_; 
lean_dec(v_a_405_);
v_a_474_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_485_ == 0)
{
v___x_476_ = v___x_407_;
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_407_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_478_ = lean_io_error_to_string(v_a_474_);
v___x_479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
v___x_480_ = l_Lean_MessageData_ofFormat(v___x_479_);
lean_inc(v_ref_406_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_ref_406_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_481_);
v___x_483_ = v___x_476_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_486_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_404_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_404_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_402_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_402_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_395_ = stack[0].m_obj;
lean_object* v_e_396_ = stack[1].m_obj;
lean_object* v_a_397_ = stack[2].m_obj;
lean_object* v_a_398_ = stack[3].m_obj;
lean_object* v_a_399_ = stack[4].m_obj;
lean_object* v_a_400_ = stack[5].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_395_, v_e_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object* v_goal_503_, lean_object* v_e_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_503_, v_e_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec_ref(v_goal_503_);
return v_res_510_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object* v_goal_511_, lean_object* v_as_512_, size_t v_sz_513_, size_t v_i_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_b_515_);
return v___x_522_;
}
else
{
lean_object* v_snd_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_572_; 
v_snd_523_ = lean_ctor_get(v_b_515_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_b_515_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v_b_515_, 0);
lean_dec(v_unused_573_);
v___x_525_ = v_b_515_;
v_isShared_526_ = v_isSharedCheck_572_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_snd_523_);
lean_dec(v_b_515_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_572_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v_a_529_; lean_object* v_a_536_; lean_object* v___x_537_; 
v___x_527_ = lean_box(0);
v_a_536_ = lean_array_uget_borrowed(v_as_512_, v_i_514_);
lean_inc(v_a_536_);
v___x_537_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_511_, v_a_536_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; uint8_t v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_538_);
if (v___x_539_ == 0)
{
lean_dec(v_a_538_);
v_a_529_ = v_snd_523_;
goto v___jp_528_;
}
else
{
lean_object* v___x_540_; 
lean_inc(v_a_538_);
v___x_540_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_538_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; uint8_t v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = lean_unbox(v_a_541_);
lean_dec(v_a_541_);
if (v___x_542_ == 0)
{
lean_dec(v_a_538_);
v_a_529_ = v_snd_523_;
goto v___jp_528_;
}
else
{
lean_object* v_self_543_; lean_object* v___x_544_; 
v_self_543_ = lean_ctor_get(v_a_538_, 0);
lean_inc_ref_n(v_self_543_, 2);
lean_dec(v_a_538_);
v___x_544_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_511_, v_self_543_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
if (lean_obj_tag(v_a_545_) == 1)
{
lean_object* v_val_546_; lean_object* v___x_547_; 
v_val_546_ = lean_ctor_get(v_a_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v_a_545_, 1);
v___x_547_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_511_, v_self_543_, v_val_546_, v_snd_523_);
v_a_529_ = v___x_547_;
goto v___jp_528_;
}
else
{
lean_dec(v_a_545_);
lean_dec_ref(v_self_543_);
v_a_529_ = v_snd_523_;
goto v___jp_528_;
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v_self_543_);
lean_del_object(v___x_525_);
lean_dec(v_snd_523_);
v_a_548_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_544_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_a_538_);
lean_del_object(v___x_525_);
lean_dec(v_snd_523_);
v_a_556_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_540_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_540_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_del_object(v___x_525_);
lean_dec(v_snd_523_);
v_a_564_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_537_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_537_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
v___jp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_a_529_);
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_531_ = v___x_525_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_529_);
v___x_531_ = v_reuseFailAlloc_535_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
size_t v___x_532_; size_t v___x_533_; 
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_514_, v___x_532_);
v_i_514_ = v___x_533_;
v_b_515_ = v___x_531_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_511_ = stack[0].m_obj;
lean_object* v_as_512_ = stack[1].m_obj;
size_t v_sz_513_ = stack[2].m_num;
size_t v_i_514_ = stack[3].m_num;
lean_object* v_b_515_ = stack[4].m_obj;
lean_object* v___y_516_ = stack[5].m_obj;
lean_object* v___y_517_ = stack[6].m_obj;
lean_object* v___y_518_ = stack[7].m_obj;
lean_object* v___y_519_ = stack[8].m_obj;
lean_object* v_res_574_;
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_511_, v_as_512_, v_sz_513_, v_i_514_, v_b_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_goal_575_, lean_object* v_as_576_, lean_object* v_sz_577_, lean_object* v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_577_);
lean_dec(v_sz_577_);
v_i_boxed_586_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_575_, v_as_576_, v_sz_boxed_585_, v_i_boxed_586_, v_b_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_as_576_);
lean_dec_ref(v_goal_575_);
return v_res_587_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object* v_goal_588_, lean_object* v_as_589_, size_t v_sz_590_, size_t v_i_591_, lean_object* v_b_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = lean_usize_dec_lt(v_i_591_, v_sz_590_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v_b_592_);
return v___x_599_;
}
else
{
lean_object* v_snd_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_649_; 
v_snd_600_ = lean_ctor_get(v_b_592_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_b_592_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_b_592_, 0);
lean_dec(v_unused_650_);
v___x_602_ = v_b_592_;
v_isShared_603_ = v_isSharedCheck_649_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snd_600_);
lean_dec(v_b_592_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_649_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v_a_606_; lean_object* v_a_613_; lean_object* v___x_614_; 
v___x_604_ = lean_box(0);
v_a_613_ = lean_array_uget_borrowed(v_as_589_, v_i_591_);
lean_inc(v_a_613_);
v___x_614_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_588_, v_a_613_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; uint8_t v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_615_);
if (v___x_616_ == 0)
{
lean_dec(v_a_615_);
v_a_606_ = v_snd_600_;
goto v___jp_605_;
}
else
{
lean_object* v___x_617_; 
lean_inc(v_a_615_);
v___x_617_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_615_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; uint8_t v___x_619_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = lean_unbox(v_a_618_);
lean_dec(v_a_618_);
if (v___x_619_ == 0)
{
lean_dec(v_a_615_);
v_a_606_ = v_snd_600_;
goto v___jp_605_;
}
else
{
lean_object* v_self_620_; lean_object* v___x_621_; 
v_self_620_ = lean_ctor_get(v_a_615_, 0);
lean_inc_ref_n(v_self_620_, 2);
lean_dec(v_a_615_);
v___x_621_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_588_, v_self_620_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
if (lean_obj_tag(v_a_622_) == 1)
{
lean_object* v_val_623_; lean_object* v___x_624_; 
v_val_623_ = lean_ctor_get(v_a_622_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v_a_622_, 1);
v___x_624_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_588_, v_self_620_, v_val_623_, v_snd_600_);
v_a_606_ = v___x_624_;
goto v___jp_605_;
}
else
{
lean_dec(v_a_622_);
lean_dec_ref(v_self_620_);
v_a_606_ = v_snd_600_;
goto v___jp_605_;
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_self_620_);
lean_del_object(v___x_602_);
lean_dec(v_snd_600_);
v_a_625_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_621_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_621_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_615_);
lean_del_object(v___x_602_);
lean_dec(v_snd_600_);
v_a_633_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_617_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_617_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_del_object(v___x_602_);
lean_dec(v_snd_600_);
v_a_641_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_614_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_614_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
v___jp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_a_606_);
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_608_ = v___x_602_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_a_606_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
size_t v___x_609_; size_t v___x_610_; lean_object* v___x_611_; 
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_591_, v___x_609_);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_588_, v_as_589_, v_sz_590_, v___x_610_, v___x_608_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
return v___x_611_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_588_ = stack[0].m_obj;
lean_object* v_as_589_ = stack[1].m_obj;
size_t v_sz_590_ = stack[2].m_num;
size_t v_i_591_ = stack[3].m_num;
lean_object* v_b_592_ = stack[4].m_obj;
lean_object* v___y_593_ = stack[5].m_obj;
lean_object* v___y_594_ = stack[6].m_obj;
lean_object* v___y_595_ = stack[7].m_obj;
lean_object* v___y_596_ = stack[8].m_obj;
lean_object* v_res_651_;
v_res_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_588_, v_as_589_, v_sz_590_, v_i_591_, v_b_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object* v_goal_652_, lean_object* v_as_653_, lean_object* v_sz_654_, lean_object* v_i_655_, lean_object* v_b_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_654_);
lean_dec(v_sz_654_);
v_i_boxed_663_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_652_, v_as_653_, v_sz_boxed_662_, v_i_boxed_663_, v_b_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v_as_653_);
lean_dec_ref(v_goal_652_);
return v_res_664_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object* v_init_665_, lean_object* v_goal_666_, lean_object* v_n_667_, lean_object* v_b_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
if (lean_obj_tag(v_n_667_) == 0)
{
lean_object* v_cs_674_; lean_object* v___x_675_; lean_object* v___x_676_; size_t v_sz_677_; size_t v___x_678_; lean_object* v___x_679_; 
v_cs_674_ = lean_ctor_get(v_n_667_, 0);
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_b_668_);
v_sz_677_ = lean_array_size(v_cs_674_);
v___x_678_ = ((size_t)0ULL);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_665_, v_goal_666_, v_cs_674_, v_sz_677_, v___x_678_, v___x_676_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_694_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_694_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_694_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_694_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_fst_684_; 
v_fst_684_ = lean_ctor_get(v_a_680_, 0);
if (lean_obj_tag(v_fst_684_) == 0)
{
lean_object* v_snd_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v_snd_685_ = lean_ctor_get(v_a_680_, 1);
lean_inc(v_snd_685_);
lean_dec(v_a_680_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_snd_685_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_686_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
lean_object* v_val_690_; lean_object* v___x_692_; 
lean_inc_ref(v_fst_684_);
lean_dec(v_a_680_);
v_val_690_ = lean_ctor_get(v_fst_684_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v_fst_684_, 1);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v_val_690_);
v___x_692_ = v___x_682_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_val_690_);
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
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
v_a_695_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_679_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_679_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_vs_703_; lean_object* v___x_704_; lean_object* v___x_705_; size_t v_sz_706_; size_t v___x_707_; lean_object* v___x_708_; 
v_vs_703_ = lean_ctor_get(v_n_667_, 0);
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_b_668_);
v_sz_706_ = lean_array_size(v_vs_703_);
v___x_707_ = ((size_t)0ULL);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_666_, v_vs_703_, v_sz_706_, v___x_707_, v___x_705_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_723_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_fst_713_; 
v_fst_713_ = lean_ctor_get(v_a_709_, 0);
if (lean_obj_tag(v_fst_713_) == 0)
{
lean_object* v_snd_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v_snd_714_ = lean_ctor_get(v_a_709_, 1);
lean_inc(v_snd_714_);
lean_dec(v_a_709_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v_snd_714_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_715_);
v___x_717_ = v___x_711_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v_val_719_; lean_object* v___x_721_; 
lean_inc_ref(v_fst_713_);
lean_dec(v_a_709_);
v_val_719_ = lean_ctor_get(v_fst_713_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v_fst_713_, 1);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_val_719_);
v___x_721_ = v___x_711_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_val_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v_a_724_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_708_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_708_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_665_ = stack[0].m_obj;
lean_object* v_goal_666_ = stack[1].m_obj;
lean_object* v_n_667_ = stack[2].m_obj;
lean_object* v_b_668_ = stack[3].m_obj;
lean_object* v___y_669_ = stack[4].m_obj;
lean_object* v___y_670_ = stack[5].m_obj;
lean_object* v___y_671_ = stack[6].m_obj;
lean_object* v___y_672_ = stack[7].m_obj;
lean_object* v_res_732_;
v_res_732_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_665_, v_goal_666_, v_n_667_, v_b_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
stack->m_obj
 = v_res_732_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object* v_init_733_, lean_object* v_goal_734_, lean_object* v_as_735_, size_t v_sz_736_, size_t v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_lt(v_i_737_, v_sz_736_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_b_738_);
return v___x_745_;
}
else
{
lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_780_; 
v_snd_746_ = lean_ctor_get(v_b_738_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_b_738_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_b_738_, 0);
lean_dec(v_unused_781_);
v___x_748_ = v_b_738_;
v_isShared_749_ = v_isSharedCheck_780_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_dec(v_b_738_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_780_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v_a_751_; lean_object* v___x_752_; 
v___x_750_ = lean_box(0);
v_a_751_ = lean_array_uget_borrowed(v_as_735_, v_i_737_);
lean_inc(v_snd_746_);
v___x_752_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_733_, v_goal_734_, v_a_751_, v_snd_746_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_771_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_771_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_771_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_771_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
if (lean_obj_tag(v_a_753_) == 0)
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v_a_753_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_757_);
v___x_759_ = v___x_748_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_snd_746_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_759_);
v___x_761_ = v___x_755_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; 
lean_del_object(v___x_755_);
lean_dec(v_snd_746_);
v_a_764_ = lean_ctor_get(v_a_753_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v_a_753_, 1);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v_a_764_);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_766_ = v___x_748_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_764_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
size_t v___x_767_; size_t v___x_768_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_737_, v___x_767_);
v_i_737_ = v___x_768_;
v_b_738_ = v___x_766_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_del_object(v___x_748_);
lean_dec(v_snd_746_);
v_a_772_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_752_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_752_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_733_ = stack[0].m_obj;
lean_object* v_goal_734_ = stack[1].m_obj;
lean_object* v_as_735_ = stack[2].m_obj;
size_t v_sz_736_ = stack[3].m_num;
size_t v_i_737_ = stack[4].m_num;
lean_object* v_b_738_ = stack[5].m_obj;
lean_object* v___y_739_ = stack[6].m_obj;
lean_object* v___y_740_ = stack[7].m_obj;
lean_object* v___y_741_ = stack[8].m_obj;
lean_object* v___y_742_ = stack[9].m_obj;
lean_object* v_res_782_;
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_733_, v_goal_734_, v_as_735_, v_sz_736_, v_i_737_, v_b_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object* v_init_783_, lean_object* v_goal_784_, lean_object* v_as_785_, lean_object* v_sz_786_, lean_object* v_i_787_, lean_object* v_b_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
size_t v_sz_boxed_794_; size_t v_i_boxed_795_; lean_object* v_res_796_; 
v_sz_boxed_794_ = lean_unbox_usize(v_sz_786_);
lean_dec(v_sz_786_);
v_i_boxed_795_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_783_, v_goal_784_, v_as_785_, v_sz_boxed_794_, v_i_boxed_795_, v_b_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_as_785_);
lean_dec_ref(v_goal_784_);
lean_dec_ref(v_init_783_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object* v_init_797_, lean_object* v_goal_798_, lean_object* v_n_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_797_, v_goal_798_, v_n_799_, v_b_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_n_799_);
lean_dec_ref(v_goal_798_);
lean_dec_ref(v_init_797_);
return v_res_806_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object* v_goal_807_, lean_object* v_as_808_, size_t v_sz_809_, size_t v_i_810_, lean_object* v_b_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_usize_dec_lt(v_i_810_, v_sz_809_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v_b_811_);
return v___x_818_;
}
else
{
lean_object* v_snd_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_868_; 
v_snd_819_ = lean_ctor_get(v_b_811_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_b_811_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_b_811_, 0);
lean_dec(v_unused_869_);
v___x_821_ = v_b_811_;
v_isShared_822_ = v_isSharedCheck_868_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_snd_819_);
lean_dec(v_b_811_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_868_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v_a_825_; lean_object* v_a_832_; lean_object* v___x_833_; 
v___x_823_ = lean_box(0);
v_a_832_ = lean_array_uget_borrowed(v_as_808_, v_i_810_);
lean_inc(v_a_832_);
v___x_833_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_807_, v_a_832_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; uint8_t v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_834_);
if (v___x_835_ == 0)
{
lean_dec(v_a_834_);
v_a_825_ = v_snd_819_;
goto v___jp_824_;
}
else
{
lean_object* v___x_836_; 
lean_inc(v_a_834_);
v___x_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_834_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; uint8_t v___x_838_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
v___x_838_ = lean_unbox(v_a_837_);
lean_dec(v_a_837_);
if (v___x_838_ == 0)
{
lean_dec(v_a_834_);
v_a_825_ = v_snd_819_;
goto v___jp_824_;
}
else
{
lean_object* v_self_839_; lean_object* v___x_840_; 
v_self_839_ = lean_ctor_get(v_a_834_, 0);
lean_inc_ref_n(v_self_839_, 2);
lean_dec(v_a_834_);
v___x_840_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_807_, v_self_839_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
if (lean_obj_tag(v_a_841_) == 1)
{
lean_object* v_val_842_; lean_object* v___x_843_; 
v_val_842_ = lean_ctor_get(v_a_841_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v_a_841_, 1);
v___x_843_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_807_, v_self_839_, v_val_842_, v_snd_819_);
v_a_825_ = v___x_843_;
goto v___jp_824_;
}
else
{
lean_dec(v_a_841_);
lean_dec_ref(v_self_839_);
v_a_825_ = v_snd_819_;
goto v___jp_824_;
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_self_839_);
lean_del_object(v___x_821_);
lean_dec(v_snd_819_);
v_a_844_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_840_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_840_);
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
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_a_834_);
lean_del_object(v___x_821_);
lean_dec(v_snd_819_);
v_a_852_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_836_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_836_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_del_object(v___x_821_);
lean_dec(v_snd_819_);
v_a_860_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_833_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_833_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
v___jp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v_a_825_);
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_827_ = v___x_821_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_a_825_);
v___x_827_ = v_reuseFailAlloc_831_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
size_t v___x_828_; size_t v___x_829_; 
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_add(v_i_810_, v___x_828_);
v_i_810_ = v___x_829_;
v_b_811_ = v___x_827_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_807_ = stack[0].m_obj;
lean_object* v_as_808_ = stack[1].m_obj;
size_t v_sz_809_ = stack[2].m_num;
size_t v_i_810_ = stack[3].m_num;
lean_object* v_b_811_ = stack[4].m_obj;
lean_object* v___y_812_ = stack[5].m_obj;
lean_object* v___y_813_ = stack[6].m_obj;
lean_object* v___y_814_ = stack[7].m_obj;
lean_object* v___y_815_ = stack[8].m_obj;
lean_object* v_res_870_;
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_807_, v_as_808_, v_sz_809_, v_i_810_, v_b_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object* v_goal_871_, lean_object* v_as_872_, lean_object* v_sz_873_, lean_object* v_i_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
size_t v_sz_boxed_881_; size_t v_i_boxed_882_; lean_object* v_res_883_; 
v_sz_boxed_881_ = lean_unbox_usize(v_sz_873_);
lean_dec(v_sz_873_);
v_i_boxed_882_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_871_, v_as_872_, v_sz_boxed_881_, v_i_boxed_882_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_as_872_);
lean_dec_ref(v_goal_871_);
return v_res_883_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object* v_goal_884_, lean_object* v_as_885_, size_t v_sz_886_, size_t v_i_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
uint8_t v___x_894_; 
v___x_894_ = lean_usize_dec_lt(v_i_887_, v_sz_886_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_b_888_);
return v___x_895_;
}
else
{
lean_object* v_snd_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_945_; 
v_snd_896_ = lean_ctor_get(v_b_888_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_b_888_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_b_888_, 0);
lean_dec(v_unused_946_);
v___x_898_ = v_b_888_;
v_isShared_899_ = v_isSharedCheck_945_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_snd_896_);
lean_dec(v_b_888_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_945_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v_a_902_; lean_object* v_a_909_; lean_object* v___x_910_; 
v___x_900_ = lean_box(0);
v_a_909_ = lean_array_uget_borrowed(v_as_885_, v_i_887_);
lean_inc(v_a_909_);
v___x_910_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_884_, v_a_909_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; uint8_t v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_911_);
if (v___x_912_ == 0)
{
lean_dec(v_a_911_);
v_a_902_ = v_snd_896_;
goto v___jp_901_;
}
else
{
lean_object* v___x_913_; 
lean_inc(v_a_911_);
v___x_913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_911_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; uint8_t v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_unbox(v_a_914_);
lean_dec(v_a_914_);
if (v___x_915_ == 0)
{
lean_dec(v_a_911_);
v_a_902_ = v_snd_896_;
goto v___jp_901_;
}
else
{
lean_object* v_self_916_; lean_object* v___x_917_; 
v_self_916_ = lean_ctor_get(v_a_911_, 0);
lean_inc_ref_n(v_self_916_, 2);
lean_dec(v_a_911_);
v___x_917_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_884_, v_self_916_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
if (lean_obj_tag(v_a_918_) == 1)
{
lean_object* v_val_919_; lean_object* v___x_920_; 
v_val_919_ = lean_ctor_get(v_a_918_, 0);
lean_inc(v_val_919_);
lean_dec_ref_known(v_a_918_, 1);
v___x_920_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_884_, v_self_916_, v_val_919_, v_snd_896_);
v_a_902_ = v___x_920_;
goto v___jp_901_;
}
else
{
lean_dec(v_a_918_);
lean_dec_ref(v_self_916_);
v_a_902_ = v_snd_896_;
goto v___jp_901_;
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_self_916_);
lean_del_object(v___x_898_);
lean_dec(v_snd_896_);
v_a_921_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_917_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_917_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_911_);
lean_del_object(v___x_898_);
lean_dec(v_snd_896_);
v_a_929_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_913_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_913_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_del_object(v___x_898_);
lean_dec(v_snd_896_);
v_a_937_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_910_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_910_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
v___jp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_a_902_);
lean_ctor_set(v___x_898_, 0, v___x_900_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_a_902_);
v___x_904_ = v_reuseFailAlloc_908_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
v___x_905_ = ((size_t)1ULL);
v___x_906_ = lean_usize_add(v_i_887_, v___x_905_);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_884_, v_as_885_, v_sz_886_, v___x_906_, v___x_904_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_907_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_884_ = stack[0].m_obj;
lean_object* v_as_885_ = stack[1].m_obj;
size_t v_sz_886_ = stack[2].m_num;
size_t v_i_887_ = stack[3].m_num;
lean_object* v_b_888_ = stack[4].m_obj;
lean_object* v___y_889_ = stack[5].m_obj;
lean_object* v___y_890_ = stack[6].m_obj;
lean_object* v___y_891_ = stack[7].m_obj;
lean_object* v___y_892_ = stack[8].m_obj;
lean_object* v_res_947_;
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_884_, v_as_885_, v_sz_886_, v_i_887_, v_b_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object* v_goal_948_, lean_object* v_as_949_, lean_object* v_sz_950_, lean_object* v_i_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
size_t v_sz_boxed_958_; size_t v_i_boxed_959_; lean_object* v_res_960_; 
v_sz_boxed_958_ = lean_unbox_usize(v_sz_950_);
lean_dec(v_sz_950_);
v_i_boxed_959_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_948_, v_as_949_, v_sz_boxed_958_, v_i_boxed_959_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_as_949_);
lean_dec_ref(v_goal_948_);
return v_res_960_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object* v_goal_961_, lean_object* v_t_962_, lean_object* v_init_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_root_969_; lean_object* v_tail_970_; lean_object* v___x_971_; 
v_root_969_ = lean_ctor_get(v_t_962_, 0);
v_tail_970_ = lean_ctor_get(v_t_962_, 1);
lean_inc_ref(v_init_963_);
v___x_971_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_963_, v_goal_961_, v_root_969_, v_init_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec_ref(v_init_963_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1008_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_1008_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1008_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
if (lean_obj_tag(v_a_972_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v_a_972_, 1);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v_a_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; size_t v_sz_983_; size_t v___x_984_; lean_object* v___x_985_; 
lean_del_object(v___x_974_);
v_a_980_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v_a_972_, 1);
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_a_980_);
v_sz_983_ = lean_array_size(v_tail_970_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_961_, v_tail_970_, v_sz_983_, v___x_984_, v___x_982_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_999_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_999_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_999_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_999_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_fst_990_; 
v_fst_990_ = lean_ctor_get(v_a_986_, 0);
if (lean_obj_tag(v_fst_990_) == 0)
{
lean_object* v_snd_991_; lean_object* v___x_993_; 
v_snd_991_ = lean_ctor_get(v_a_986_, 1);
lean_inc(v_snd_991_);
lean_dec(v_a_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v_snd_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_snd_991_);
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
lean_object* v_val_995_; lean_object* v___x_997_; 
lean_inc_ref(v_fst_990_);
lean_dec(v_a_986_);
v_val_995_ = lean_ctor_get(v_fst_990_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v_fst_990_, 1);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v_val_995_);
v___x_997_ = v___x_988_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_val_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_985_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_985_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_971_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_971_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_961_ = stack[0].m_obj;
lean_object* v_t_962_ = stack[1].m_obj;
lean_object* v_init_963_ = stack[2].m_obj;
lean_object* v___y_964_ = stack[3].m_obj;
lean_object* v___y_965_ = stack[4].m_obj;
lean_object* v___y_966_ = stack[5].m_obj;
lean_object* v___y_967_ = stack[6].m_obj;
lean_object* v_res_1017_;
v_res_1017_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_961_, v_t_962_, v_init_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
stack->m_obj
 = v_res_1017_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object* v_goal_1018_, lean_object* v_t_1019_, lean_object* v_init_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1018_, v_t_1019_, v_init_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_t_1019_);
lean_dec_ref(v_goal_1018_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object* v_a_1027_, lean_object* v_x_1028_){
_start:
{
if (lean_obj_tag(v_x_1028_) == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_box(0);
return v___x_1029_;
}
else
{
lean_object* v_key_1030_; lean_object* v_value_1031_; lean_object* v_tail_1032_; uint8_t v___x_1033_; 
v_key_1030_ = lean_ctor_get(v_x_1028_, 0);
v_value_1031_ = lean_ctor_get(v_x_1028_, 1);
v_tail_1032_ = lean_ctor_get(v_x_1028_, 2);
v___x_1033_ = lean_expr_eqv(v_key_1030_, v_a_1027_);
if (v___x_1033_ == 0)
{
v_x_1028_ = v_tail_1032_;
goto _start;
}
else
{
lean_object* v___x_1035_; 
lean_inc(v_value_1031_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_value_1031_);
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1036_, v_x_1037_);
lean_dec(v_x_1037_);
lean_dec_ref(v_a_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object* v_m_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_buckets_1041_; lean_object* v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; uint64_t v___x_1045_; uint64_t v_fold_1046_; uint64_t v___x_1047_; uint64_t v___x_1048_; uint64_t v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_buckets_1041_ = lean_ctor_get(v_m_1039_, 1);
v___x_1042_ = lean_array_get_size(v_buckets_1041_);
v___x_1043_ = l_Lean_Expr_hash(v_a_1040_);
v___x_1044_ = 32ULL;
v___x_1045_ = lean_uint64_shift_right(v___x_1043_, v___x_1044_);
v_fold_1046_ = lean_uint64_xor(v___x_1043_, v___x_1045_);
v___x_1047_ = 16ULL;
v___x_1048_ = lean_uint64_shift_right(v_fold_1046_, v___x_1047_);
v___x_1049_ = lean_uint64_xor(v_fold_1046_, v___x_1048_);
v___x_1050_ = lean_uint64_to_usize(v___x_1049_);
v___x_1051_ = lean_usize_of_nat(v___x_1042_);
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_sub(v___x_1051_, v___x_1052_);
v___x_1054_ = lean_usize_land(v___x_1050_, v___x_1053_);
v___x_1055_ = lean_array_uget_borrowed(v_buckets_1041_, v___x_1054_);
v___x_1056_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1040_, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object* v_m_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1057_, v_a_1058_);
lean_dec_ref(v_a_1058_);
lean_dec_ref(v_m_1057_);
return v_res_1059_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object* v_goal_1060_, lean_object* v_as_1061_, size_t v_sz_1062_, size_t v_i_1063_, lean_object* v_b_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_a_1071_; uint8_t v___x_1075_; 
v___x_1075_ = lean_usize_dec_lt(v_i_1063_, v_sz_1062_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_b_1064_);
return v___x_1076_;
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_array_uget_borrowed(v_as_1061_, v_i_1063_);
lean_inc(v_a_1077_);
v___x_1078_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1060_, v_a_1077_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v_self_1080_; lean_object* v___x_1081_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_self_1080_ = lean_ctor_get(v_a_1079_, 0);
lean_inc_ref_n(v_self_1080_, 2);
lean_dec(v_a_1079_);
v___x_1081_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1080_);
if (lean_obj_tag(v___x_1081_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1083_; 
v_val_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1064_, v_val_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1064_, v_self_1080_);
lean_dec_ref(v_self_1080_);
if (lean_obj_tag(v___x_1084_) == 1)
{
lean_object* v_val_1085_; lean_object* v___x_1086_; 
v_val_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_val_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1060_, v_val_1082_, v_val_1085_, v_b_1064_);
v_a_1071_ = v___x_1086_;
goto v___jp_1070_;
}
else
{
lean_dec(v___x_1084_);
lean_dec(v_val_1082_);
v_a_1071_ = v_b_1064_;
goto v___jp_1070_;
}
}
else
{
lean_dec_ref_known(v___x_1083_, 1);
lean_dec(v_val_1082_);
lean_dec_ref(v_self_1080_);
v_a_1071_ = v_b_1064_;
goto v___jp_1070_;
}
}
else
{
lean_dec(v___x_1081_);
lean_dec_ref(v_self_1080_);
v_a_1071_ = v_b_1064_;
goto v___jp_1070_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_b_1064_);
v_a_1087_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1078_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1078_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
v___jp_1070_:
{
size_t v___x_1072_; size_t v___x_1073_; 
v___x_1072_ = ((size_t)1ULL);
v___x_1073_ = lean_usize_add(v_i_1063_, v___x_1072_);
v_i_1063_ = v___x_1073_;
v_b_1064_ = v_a_1071_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1060_ = stack[0].m_obj;
lean_object* v_as_1061_ = stack[1].m_obj;
size_t v_sz_1062_ = stack[2].m_num;
size_t v_i_1063_ = stack[3].m_num;
lean_object* v_b_1064_ = stack[4].m_obj;
lean_object* v___y_1065_ = stack[5].m_obj;
lean_object* v___y_1066_ = stack[6].m_obj;
lean_object* v___y_1067_ = stack[7].m_obj;
lean_object* v___y_1068_ = stack[8].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1060_, v_as_1061_, v_sz_1062_, v_i_1063_, v_b_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object* v_goal_1096_, lean_object* v_as_1097_, lean_object* v_sz_1098_, lean_object* v_i_1099_, lean_object* v_b_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
size_t v_sz_boxed_1106_; size_t v_i_boxed_1107_; lean_object* v_res_1108_; 
v_sz_boxed_1106_ = lean_unbox_usize(v_sz_1098_);
lean_dec(v_sz_1098_);
v_i_boxed_1107_ = lean_unbox_usize(v_i_1099_);
lean_dec(v_i_1099_);
v_res_1108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1096_, v_as_1097_, v_sz_boxed_1106_, v_i_boxed_1107_, v_b_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec_ref(v_as_1097_);
lean_dec_ref(v_goal_1096_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_unsigned_to_nat(16u);
v___x_1111_ = lean_mk_array(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_model_1114_; 
v___x_1112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0);
v___x_1113_ = lean_unsigned_to_nat(0u);
v_model_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_1114_, 0, v___x_1113_);
lean_ctor_set(v_model_1114_, 1, v___x_1112_);
return v_model_1114_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object* v_goal_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_toGoalState_1129_; lean_object* v_exprs_1130_; lean_object* v_model_1131_; lean_object* v___x_1132_; 
v_toGoalState_1129_ = lean_ctor_get(v_goal_1123_, 0);
v_exprs_1130_ = lean_ctor_get(v_toGoalState_1129_, 2);
v_model_1131_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1);
v___x_1132_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1123_, v_exprs_1130_, v_model_1131_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = l_Lean_PersistentArray_toArray___redArg(v_exprs_1130_);
v___x_1135_ = l_Array_reverse___redArg(v___x_1134_);
v_sz_1136_ = lean_array_size(v___x_1135_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1123_, v___x_1135_, v_sz_1136_, v___x_1137_, v_a_1133_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec_ref(v___x_1135_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2));
v___x_1141_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1123_, v___x_1140_, v_a_1139_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6));
v___x_1144_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_1143_, v_a_1142_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___x_1144_, 0);
lean_dec(v_unused_1152_);
v___x_1146_ = v___x_1144_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v___x_1144_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_a_1142_);
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1142_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_a_1142_);
v_a_1153_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1144_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1144_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
return v___x_1141_;
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1138_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1138_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
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
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1169_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1132_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1132_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_mkModel_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1123_ = stack[0].m_obj;
lean_object* v_a_1124_ = stack[1].m_obj;
lean_object* v_a_1125_ = stack[2].m_obj;
lean_object* v_a_1126_ = stack[3].m_obj;
lean_object* v_a_1127_ = stack[4].m_obj;
lean_object* v_res_1177_;
v_res_1177_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
stack->m_obj
 = v_res_1177_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object* v_goal_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_goal_1178_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object* v_00_u03b2_1185_, lean_object* v_m_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1186_, v_a_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object* v_00_u03b2_1189_, lean_object* v_m_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(v_00_u03b2_1189_, v_m_1190_, v_a_1191_);
lean_dec_ref(v_a_1191_);
lean_dec_ref(v_m_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object* v_00_u03b2_1193_, lean_object* v_a_1194_, lean_object* v_x_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1194_, v_x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1197_, lean_object* v_a_1198_, lean_object* v_x_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(v_00_u03b2_1197_, v_a_1198_, v_x_1199_);
lean_dec(v_x_1199_);
lean_dec_ref(v_a_1198_);
return v_res_1200_;
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

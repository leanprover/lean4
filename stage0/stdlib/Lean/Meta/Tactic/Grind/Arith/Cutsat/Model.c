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
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(lean_object* v_self_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0___boxed(lean_object* v_self_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(v_self_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(lean_object* v_n_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v___y_37_; lean_object* v_self_54_; lean_object* v___x_55_; uint8_t v_transparency_56_; uint8_t v___x_57_; uint8_t v___x_58_; 
v_self_54_ = lean_ctor_get(v_n_30_, 0);
lean_inc_ref(v_self_54_);
lean_dec_ref(v_n_30_);
v___x_55_ = l_Lean_Meta_Context_config(v_a_31_);
v_transparency_56_ = lean_ctor_get_uint8(v___x_55_, 9);
lean_dec_ref(v___x_55_);
v___x_57_ = 1;
v___x_58_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_56_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v_keyedConfig_59_; uint8_t v_trackZetaDelta_60_; lean_object* v_zetaDeltaSet_61_; lean_object* v_lctx_62_; lean_object* v_localInstances_63_; lean_object* v_defEqCtx_x3f_64_; lean_object* v_synthPendingDepth_65_; lean_object* v_customCanUnfoldPredicate_x3f_66_; uint8_t v_univApprox_67_; uint8_t v_inTypeClassResolution_68_; uint8_t v_cacheInferType_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_keyedConfig_59_ = lean_ctor_get(v_a_31_, 0);
v_trackZetaDelta_60_ = lean_ctor_get_uint8(v_a_31_, sizeof(void*)*7);
v_zetaDeltaSet_61_ = lean_ctor_get(v_a_31_, 1);
v_lctx_62_ = lean_ctor_get(v_a_31_, 2);
v_localInstances_63_ = lean_ctor_get(v_a_31_, 3);
v_defEqCtx_x3f_64_ = lean_ctor_get(v_a_31_, 4);
v_synthPendingDepth_65_ = lean_ctor_get(v_a_31_, 5);
v_customCanUnfoldPredicate_x3f_66_ = lean_ctor_get(v_a_31_, 6);
v_univApprox_67_ = lean_ctor_get_uint8(v_a_31_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_68_ = lean_ctor_get_uint8(v_a_31_, sizeof(void*)*7 + 2);
v_cacheInferType_69_ = lean_ctor_get_uint8(v_a_31_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_59_);
v___x_70_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_57_, v_keyedConfig_59_);
lean_inc(v_customCanUnfoldPredicate_x3f_66_);
lean_inc(v_synthPendingDepth_65_);
lean_inc(v_defEqCtx_x3f_64_);
lean_inc_ref(v_localInstances_63_);
lean_inc_ref(v_lctx_62_);
lean_inc(v_zetaDeltaSet_61_);
v___x_71_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_zetaDeltaSet_61_);
lean_ctor_set(v___x_71_, 2, v_lctx_62_);
lean_ctor_set(v___x_71_, 3, v_localInstances_63_);
lean_ctor_set(v___x_71_, 4, v_defEqCtx_x3f_64_);
lean_ctor_set(v___x_71_, 5, v_synthPendingDepth_65_);
lean_ctor_set(v___x_71_, 6, v_customCanUnfoldPredicate_x3f_66_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*7, v_trackZetaDelta_60_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*7 + 1, v_univApprox_67_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*7 + 2, v_inTypeClassResolution_68_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*7 + 3, v_cacheInferType_69_);
lean_inc(v_a_34_);
lean_inc_ref(v_a_33_);
lean_inc(v_a_32_);
v___x_72_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(v_self_54_, v___x_71_, v_a_32_, v_a_33_, v_a_34_);
v___y_37_ = v___x_72_;
goto v___jp_36_;
}
else
{
lean_object* v___x_73_; 
lean_inc(v_a_34_);
lean_inc_ref(v_a_33_);
lean_inc(v_a_32_);
lean_inc_ref(v_a_31_);
v___x_73_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___lam__0(v_self_54_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
v___y_37_ = v___x_73_;
goto v___jp_36_;
}
v___jp_36_:
{
if (lean_obj_tag(v___y_37_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___y_37_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___y_37_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___y_37_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___y_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___y_37_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___y_37_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___y_37_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___y_37_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(lean_object* v_n_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_n_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
return v_res_80_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = l_instInhabitedError;
v___x_82_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_82_, 0, lean_box(0));
lean_closure_set(v___x_82_, 1, lean_box(0));
lean_closure_set(v___x_82_, 2, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(lean_object* v_msg_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_500__overap_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0);
v___x_500__overap_86_ = lean_panic_fn_borrowed(v___x_85_, v_msg_83_);
v___x_87_ = lean_apply_1(v___x_500__overap_86_, lean_box(0));
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(lean_object* v_msg_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v_msg_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_91_, lean_object* v_vals_92_, lean_object* v_i_93_, lean_object* v_k_94_){
_start:
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_array_get_size(v_keys_91_);
v___x_96_ = lean_nat_dec_lt(v_i_93_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec(v_i_93_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v_k_x27_98_; size_t v___x_99_; size_t v___x_100_; uint8_t v___x_101_; 
v_k_x27_98_ = lean_array_fget_borrowed(v_keys_91_, v_i_93_);
v___x_99_ = lean_ptr_addr(v_k_94_);
v___x_100_ = lean_ptr_addr(v_k_x27_98_);
v___x_101_ = lean_usize_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_add(v_i_93_, v___x_102_);
lean_dec(v_i_93_);
v_i_93_ = v___x_103_;
goto _start;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_array_fget_borrowed(v_vals_92_, v_i_93_);
lean_dec(v_i_93_);
lean_inc(v___x_105_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_107_, lean_object* v_vals_108_, lean_object* v_i_109_, lean_object* v_k_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_107_, v_vals_108_, v_i_109_, v_k_110_);
lean_dec_ref(v_k_110_);
lean_dec_ref(v_vals_108_);
lean_dec_ref(v_keys_107_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(lean_object* v_x_112_, size_t v_x_113_, lean_object* v_x_114_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v_es_115_; lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; lean_object* v_j_119_; lean_object* v___x_120_; 
v_es_115_ = lean_ctor_get(v_x_112_, 0);
v___x_116_ = lean_box(2);
v___x_117_ = ((size_t)31ULL);
v___x_118_ = lean_usize_land(v_x_113_, v___x_117_);
v_j_119_ = lean_usize_to_nat(v___x_118_);
v___x_120_ = lean_array_get_borrowed(v___x_116_, v_es_115_, v_j_119_);
lean_dec(v_j_119_);
switch(lean_obj_tag(v___x_120_))
{
case 0:
{
lean_object* v_key_121_; lean_object* v_val_122_; size_t v___x_123_; size_t v___x_124_; uint8_t v___x_125_; 
v_key_121_ = lean_ctor_get(v___x_120_, 0);
v_val_122_ = lean_ctor_get(v___x_120_, 1);
v___x_123_ = lean_ptr_addr(v_x_114_);
v___x_124_ = lean_ptr_addr(v_key_121_);
v___x_125_ = lean_usize_dec_eq(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
lean_inc(v_val_122_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_val_122_);
return v___x_127_;
}
}
case 1:
{
lean_object* v_node_128_; size_t v___x_129_; size_t v___x_130_; 
v_node_128_ = lean_ctor_get(v___x_120_, 0);
v___x_129_ = ((size_t)5ULL);
v___x_130_ = lean_usize_shift_right(v_x_113_, v___x_129_);
v_x_112_ = v_node_128_;
v_x_113_ = v___x_130_;
goto _start;
}
default: 
{
lean_object* v___x_132_; 
v___x_132_ = lean_box(0);
return v___x_132_;
}
}
}
else
{
lean_object* v_ks_133_; lean_object* v_vs_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_ks_133_ = lean_ctor_get(v_x_112_, 0);
v_vs_134_ = lean_ctor_get(v_x_112_, 1);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_ks_133_, v_vs_134_, v___x_135_, v_x_114_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
size_t v_x_706__boxed_140_; lean_object* v_res_141_; 
v_x_706__boxed_140_ = lean_unbox_usize(v_x_138_);
lean_dec(v_x_138_);
v_res_141_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_137_, v_x_706__boxed_140_, v_x_139_);
lean_dec_ref(v_x_139_);
lean_dec_ref(v_x_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; uint64_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v___x_144_ = lean_ptr_addr(v_x_143_);
v___x_145_ = ((size_t)3ULL);
v___x_146_ = lean_usize_shift_right(v___x_144_, v___x_145_);
v___x_147_ = lean_usize_to_uint64(v___x_146_);
v___x_148_ = lean_uint64_to_usize(v___x_147_);
v___x_149_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_142_, v___x_148_, v_x_143_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_150_, v_x_151_);
lean_dec_ref(v_x_151_);
lean_dec_ref(v_x_150_);
return v_res_152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2));
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_unsigned_to_nat(21u);
v___x_159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1));
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0));
v___x_161_ = l_mkPanicMessageWithDecl(v___x_160_, v___x_159_, v___x_158_, v___x_157_, v___x_156_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(lean_object* v_goal_162_, lean_object* v_node_163_){
_start:
{
lean_object* v_self_168_; lean_object* v_root_169_; size_t v___x_170_; size_t v___x_171_; uint8_t v___x_172_; 
v_self_168_ = lean_ctor_get(v_node_163_, 0);
v_root_169_ = lean_ctor_get(v_node_163_, 2);
v___x_170_ = lean_ptr_addr(v_self_168_);
v___x_171_ = lean_ptr_addr(v_root_169_);
v___x_172_ = lean_usize_dec_eq(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3);
v___x_174_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v___x_173_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_176_ = l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(v___x_175_, v_node_163_);
if (lean_obj_tag(v___x_176_) == 1)
{
lean_object* v_val_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_val_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_176_, 1);
v___x_178_ = 0;
v___x_179_ = l_instInhabitedRat;
v___x_180_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_175_, v_goal_162_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_217_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_217_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_217_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_217_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_varMap_185_; lean_object* v_active_186_; lean_object* v_assignment_187_; lean_object* v___x_188_; 
v_varMap_185_ = lean_ctor_get(v_a_181_, 1);
lean_inc_ref(v_varMap_185_);
v_active_186_ = lean_ctor_get(v_a_181_, 10);
lean_inc_ref(v_active_186_);
v_assignment_187_ = lean_ctor_get(v_a_181_, 13);
lean_inc_ref(v_assignment_187_);
lean_dec(v_a_181_);
v___x_188_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_varMap_185_, v_val_177_);
lean_dec(v_val_177_);
lean_dec_ref(v_varMap_185_);
if (lean_obj_tag(v___x_188_) == 1)
{
lean_object* v_val_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_212_; 
v_val_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_212_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_212_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_val_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_212_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___y_194_; lean_object* v_size_204_; uint8_t v___x_205_; 
v_size_204_ = lean_ctor_get(v_active_186_, 2);
v___x_205_ = lean_nat_dec_lt(v_val_189_, v_size_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
lean_dec_ref(v_active_186_);
v___x_206_ = lean_box(v___x_178_);
v___x_207_ = l_outOfBounds___redArg(v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = lean_unbox(v___x_207_);
lean_dec(v___x_207_);
v___y_194_ = v___x_208_;
goto v___jp_193_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_box(v___x_178_);
v___x_210_ = l_Lean_PersistentArray_get_x21___redArg(v___x_209_, v_active_186_, v_val_189_);
lean_dec_ref(v_active_186_);
lean_dec(v___x_209_);
v___x_211_ = lean_unbox(v___x_210_);
lean_dec(v___x_210_);
v___y_194_ = v___x_211_;
goto v___jp_193_;
}
v___jp_193_:
{
if (v___y_194_ == 0)
{
lean_del_object(v___x_191_);
lean_dec(v_val_189_);
lean_dec_ref(v_assignment_187_);
lean_del_object(v___x_183_);
goto v___jp_165_;
}
else
{
lean_object* v_size_195_; uint8_t v___x_196_; 
v_size_195_ = lean_ctor_get(v_assignment_187_, 2);
v___x_196_ = lean_nat_dec_lt(v_val_189_, v_size_195_);
if (v___x_196_ == 0)
{
lean_del_object(v___x_191_);
lean_dec(v_val_189_);
lean_dec_ref(v_assignment_187_);
lean_del_object(v___x_183_);
goto v___jp_165_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = l_Lean_PersistentArray_get_x21___redArg(v___x_179_, v_assignment_187_, v_val_189_);
lean_dec(v_val_189_);
lean_dec_ref(v_assignment_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_197_);
v___x_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_203_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_199_);
v___x_201_ = v___x_183_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec(v___x_188_);
lean_dec_ref(v_assignment_187_);
lean_dec_ref(v_active_186_);
v___x_213_ = lean_box(0);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_213_);
v___x_215_ = v___x_183_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_val_177_);
v_a_218_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_180_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_180_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v___x_176_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
v___jp_165_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object* v_goal_228_, lean_object* v_node_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_228_, v_node_229_);
lean_dec_ref(v_node_229_);
lean_dec_ref(v_goal_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object* v_00_u03b2_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_233_, v_x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object* v_00_u03b2_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(v_00_u03b2_236_, v_x_237_, v_x_238_);
lean_dec_ref(v_x_238_);
lean_dec_ref(v_x_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object* v_00_u03b2_240_, lean_object* v_x_241_, size_t v_x_242_, lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_241_, v_x_242_, v_x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
size_t v_x_925__boxed_249_; lean_object* v_res_250_; 
v_x_925__boxed_249_ = lean_unbox_usize(v_x_247_);
lean_dec(v_x_247_);
v_res_250_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(v_00_u03b2_245_, v_x_246_, v_x_925__boxed_249_, v_x_248_);
lean_dec_ref(v_x_248_);
lean_dec_ref(v_x_246_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_251_, lean_object* v_keys_252_, lean_object* v_vals_253_, lean_object* v_heq_254_, lean_object* v_i_255_, lean_object* v_k_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_252_, v_vals_253_, v_i_255_, v_k_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_258_, lean_object* v_keys_259_, lean_object* v_vals_260_, lean_object* v_heq_261_, lean_object* v_i_262_, lean_object* v_k_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(v_00_u03b2_258_, v_keys_259_, v_vals_260_, v_heq_261_, v_i_262_, v_k_263_);
lean_dec_ref(v_k_263_);
lean_dec_ref(v_vals_260_);
lean_dec_ref(v_keys_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(lean_object* v_e_320_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Expr_cleanupAnnotations(v_e_320_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v___x_321_);
v___x_323_ = lean_box(0);
return v___x_323_;
}
else
{
lean_object* v_arg_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_arg_324_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_arg_324_);
v___x_325_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
lean_dec_ref(v___x_321_);
v___x_326_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2));
v___x_327_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4));
v___x_329_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6));
v___x_331_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8));
v___x_333_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10));
v___x_335_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12));
v___x_337_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16));
v___x_341_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20));
v___x_345_ = l_Lean_Expr_isConstOf(v___x_325_, v___x_344_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = l_Lean_Expr_isApp(v___x_325_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec_ref(v___x_325_);
lean_dec_ref(v_arg_324_);
v___x_347_ = lean_box(0);
return v___x_347_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_325_);
lean_dec_ref(v___x_325_);
v___x_349_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25));
v___x_352_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28));
v___x_354_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_353_);
lean_dec_ref(v___x_348_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec_ref(v_arg_324_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_arg_324_);
return v___x_356_;
}
}
else
{
lean_object* v___x_357_; 
lean_dec_ref(v___x_348_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_arg_324_);
return v___x_357_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec_ref(v___x_348_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_arg_324_);
return v___x_358_;
}
}
}
else
{
lean_object* v___x_359_; 
lean_dec_ref(v___x_325_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v_arg_324_);
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; 
lean_dec_ref(v___x_325_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v_arg_324_);
return v___x_360_;
}
}
else
{
lean_object* v___x_361_; 
lean_dec_ref(v___x_325_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v_arg_324_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; 
lean_dec_ref(v___x_325_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v_arg_324_);
return v___x_362_;
}
}
else
{
lean_object* v___x_363_; 
lean_dec_ref(v___x_325_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v_arg_324_);
return v___x_363_;
}
}
else
{
lean_object* v___x_364_; 
lean_dec_ref(v___x_325_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_arg_324_);
return v___x_364_;
}
}
else
{
lean_object* v___x_365_; 
lean_dec_ref(v___x_325_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_arg_324_);
return v___x_365_;
}
}
else
{
lean_object* v___x_366_; 
lean_dec_ref(v___x_325_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v_arg_324_);
return v___x_366_;
}
}
else
{
lean_object* v___x_367_; 
lean_dec_ref(v___x_325_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v_arg_324_);
return v___x_367_;
}
}
else
{
lean_object* v___x_368_; 
lean_dec_ref(v___x_325_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v_arg_324_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___boxed(lean_object* v_e_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_369_);
lean_dec_ref(v_e_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object* v_e_379_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = l_Lean_Expr_cleanupAnnotations(v_e_379_);
v___x_381_ = l_Lean_Expr_isApp(v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec_ref(v___x_380_);
v___x_382_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_379_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_380_);
v___x_384_ = l_Lean_Expr_isApp(v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_380_);
v___x_385_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_379_);
return v___x_385_;
}
else
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = l_Lean_Expr_appFnCleanup___redArg(v___x_383_);
v___x_387_ = l_Lean_Expr_isApp(v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec_ref(v___x_386_);
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_380_);
v___x_388_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_379_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_386_);
lean_dec_ref(v___x_386_);
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2));
v___x_391_ = l_Lean_Expr_isConstOf(v___x_389_, v___x_390_);
lean_dec_ref(v___x_389_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_380_);
v___x_392_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_379_);
return v___x_392_;
}
else
{
lean_object* v_arg_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_arg_393_ = lean_ctor_get(v___x_383_, 1);
lean_inc_ref(v_arg_393_);
lean_dec_ref(v___x_383_);
v___x_394_ = l_Lean_Expr_cleanupAnnotations(v_arg_393_);
lean_dec_ref(v_arg_393_);
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4));
v___x_396_ = l_Lean_Expr_isConstOf(v___x_394_, v___x_395_);
lean_dec_ref(v___x_394_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v___x_380_);
v___x_397_ = lean_box(0);
return v___x_397_;
}
else
{
lean_object* v_arg_398_; lean_object* v___x_399_; 
v_arg_398_ = lean_ctor_get(v___x_380_, 1);
lean_inc_ref(v_arg_398_);
lean_dec_ref(v___x_380_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_arg_398_);
return v___x_399_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___boxed(lean_object* v_e_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_e_400_);
lean_dec_ref(v_e_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Rat_ofInt(v_a_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object* v_goal_404_, lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Grind_Goal_getRoot(v_goal_404_, v_e_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_404_, v_a_412_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v_ref_415_; lean_object* v___x_416_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v_ref_415_ = lean_ctor_get(v_a_408_, 2);
v___x_416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_404_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_482_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_482_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_482_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_482_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
if (lean_obj_tag(v_a_417_) == 1)
{
lean_object* v___x_422_; 
lean_dec(v_a_414_);
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_object* v_self_424_; lean_object* v___x_425_; 
lean_del_object(v___x_419_);
lean_dec(v_a_417_);
v_self_424_ = lean_ctor_get(v_a_414_, 0);
lean_inc_ref_n(v_self_424_, 2);
lean_dec(v_a_414_);
v___x_425_ = l_Lean_Meta_getIntValue_x3f(v_self_424_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_473_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_473_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_473_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_473_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
if (lean_obj_tag(v_a_426_) == 1)
{
lean_object* v_val_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_self_424_);
v_val_430_ = lean_ctor_get(v_a_426_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_a_426_);
if (v_isSharedCheck_441_ == 0)
{
v___x_432_ = v_a_426_;
v_isShared_433_ = v_isSharedCheck_441_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_val_430_);
lean_dec(v_a_426_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_441_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = l_Rat_ofInt(v_val_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_436_);
v___x_438_ = v___x_428_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v___x_442_; 
lean_del_object(v___x_428_);
lean_dec(v_a_426_);
v___x_442_ = l_Lean_Meta_getNatValue_x3f(v_self_424_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec_ref(v_self_424_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_464_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_464_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_464_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_464_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
if (lean_obj_tag(v_a_443_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_459_; 
v_val_447_ = lean_ctor_get(v_a_443_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_459_ == 0)
{
v___x_449_ = v_a_443_;
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v_a_443_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_451_ = lean_nat_to_int(v_val_447_);
v___x_452_ = l_Rat_ofInt(v___x_451_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_454_);
v___x_456_ = v___x_445_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v_a_443_);
v___x_460_ = lean_box(0);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_460_);
v___x_462_ = v___x_445_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_442_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_442_);
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
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_self_424_);
v_a_474_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_425_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_425_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_a_414_);
v_a_483_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_494_ == 0)
{
v___x_485_ = v___x_416_;
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_416_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_487_ = lean_io_error_to_string(v_a_483_);
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = l_Lean_MessageData_ofFormat(v___x_488_);
lean_inc(v_ref_415_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_ref_415_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_490_);
v___x_492_ = v___x_485_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_413_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_413_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_a_503_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_411_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_411_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object* v_goal_511_, lean_object* v_e_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_511_, v_e_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec_ref(v_goal_511_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object* v_goal_519_, lean_object* v_as_520_, size_t v_sz_521_, size_t v_i_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = lean_usize_dec_lt(v_i_522_, v_sz_521_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v_b_523_);
return v___x_530_;
}
else
{
lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_580_; 
v_snd_531_ = lean_ctor_get(v_b_523_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_b_523_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_b_523_, 0);
lean_dec(v_unused_581_);
v___x_533_ = v_b_523_;
v_isShared_534_ = v_isSharedCheck_580_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_dec(v_b_523_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_580_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v_a_537_; lean_object* v_a_544_; lean_object* v___x_545_; 
v___x_535_ = lean_box(0);
v_a_544_ = lean_array_uget_borrowed(v_as_520_, v_i_522_);
lean_inc(v_a_544_);
v___x_545_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_519_, v_a_544_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; uint8_t v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_546_);
if (v___x_547_ == 0)
{
lean_dec(v_a_546_);
v_a_537_ = v_snd_531_;
goto v___jp_536_;
}
else
{
lean_object* v___x_548_; 
lean_inc(v_a_546_);
v___x_548_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_546_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; uint8_t v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = lean_unbox(v_a_549_);
lean_dec(v_a_549_);
if (v___x_550_ == 0)
{
lean_dec(v_a_546_);
v_a_537_ = v_snd_531_;
goto v___jp_536_;
}
else
{
lean_object* v_self_551_; lean_object* v___x_552_; 
v_self_551_ = lean_ctor_get(v_a_546_, 0);
lean_inc_ref_n(v_self_551_, 2);
lean_dec(v_a_546_);
v___x_552_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_519_, v_self_551_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
if (lean_obj_tag(v_a_553_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_555_; 
v_val_554_ = lean_ctor_get(v_a_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v_a_553_, 1);
v___x_555_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_519_, v_self_551_, v_val_554_, v_snd_531_);
v_a_537_ = v___x_555_;
goto v___jp_536_;
}
else
{
lean_dec(v_a_553_);
lean_dec_ref(v_self_551_);
v_a_537_ = v_snd_531_;
goto v___jp_536_;
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v_self_551_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
v_a_556_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_552_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_552_);
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
lean_dec(v_a_546_);
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
v_a_564_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_548_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_548_);
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
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_del_object(v___x_533_);
lean_dec(v_snd_531_);
v_a_572_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_545_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_545_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
v___jp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v_a_537_);
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_539_ = v___x_533_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_a_537_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
size_t v___x_540_; size_t v___x_541_; 
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_add(v_i_522_, v___x_540_);
v_i_522_ = v___x_541_;
v_b_523_ = v___x_539_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_goal_582_, lean_object* v_as_583_, lean_object* v_sz_584_, lean_object* v_i_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_584_);
lean_dec(v_sz_584_);
v_i_boxed_593_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_582_, v_as_583_, v_sz_boxed_592_, v_i_boxed_593_, v_b_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec_ref(v_as_583_);
lean_dec_ref(v_goal_582_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object* v_goal_595_, lean_object* v_as_596_, size_t v_sz_597_, size_t v_i_598_, lean_object* v_b_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_lt(v_i_598_, v_sz_597_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_b_599_);
return v___x_606_;
}
else
{
lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_656_; 
v_snd_607_ = lean_ctor_get(v_b_599_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_b_599_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v_b_599_, 0);
lean_dec(v_unused_657_);
v___x_609_ = v_b_599_;
v_isShared_610_ = v_isSharedCheck_656_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_dec(v_b_599_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_656_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v_a_613_; lean_object* v_a_620_; lean_object* v___x_621_; 
v___x_611_ = lean_box(0);
v_a_620_ = lean_array_uget_borrowed(v_as_596_, v_i_598_);
lean_inc(v_a_620_);
v___x_621_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_595_, v_a_620_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; uint8_t v___x_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_622_);
if (v___x_623_ == 0)
{
lean_dec(v_a_622_);
v_a_613_ = v_snd_607_;
goto v___jp_612_;
}
else
{
lean_object* v___x_624_; 
lean_inc(v_a_622_);
v___x_624_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_622_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; uint8_t v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_unbox(v_a_625_);
lean_dec(v_a_625_);
if (v___x_626_ == 0)
{
lean_dec(v_a_622_);
v_a_613_ = v_snd_607_;
goto v___jp_612_;
}
else
{
lean_object* v_self_627_; lean_object* v___x_628_; 
v_self_627_ = lean_ctor_get(v_a_622_, 0);
lean_inc_ref_n(v_self_627_, 2);
lean_dec(v_a_622_);
v___x_628_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_595_, v_self_627_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
if (lean_obj_tag(v_a_629_) == 1)
{
lean_object* v_val_630_; lean_object* v___x_631_; 
v_val_630_ = lean_ctor_get(v_a_629_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_a_629_, 1);
v___x_631_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_595_, v_self_627_, v_val_630_, v_snd_607_);
v_a_613_ = v___x_631_;
goto v___jp_612_;
}
else
{
lean_dec(v_a_629_);
lean_dec_ref(v_self_627_);
v_a_613_ = v_snd_607_;
goto v___jp_612_;
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v_self_627_);
lean_del_object(v___x_609_);
lean_dec(v_snd_607_);
v_a_632_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_628_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_622_);
lean_del_object(v___x_609_);
lean_dec(v_snd_607_);
v_a_640_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_624_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_624_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_del_object(v___x_609_);
lean_dec(v_snd_607_);
v_a_648_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_621_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_621_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
v___jp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_a_613_);
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_a_613_);
v___x_615_ = v_reuseFailAlloc_619_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_598_, v___x_616_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_595_, v_as_596_, v_sz_597_, v___x_617_, v___x_615_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object* v_goal_658_, lean_object* v_as_659_, lean_object* v_sz_660_, lean_object* v_i_661_, lean_object* v_b_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
size_t v_sz_boxed_668_; size_t v_i_boxed_669_; lean_object* v_res_670_; 
v_sz_boxed_668_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_669_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_658_, v_as_659_, v_sz_boxed_668_, v_i_boxed_669_, v_b_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v_as_659_);
lean_dec_ref(v_goal_658_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object* v_init_671_, lean_object* v_goal_672_, lean_object* v_n_673_, lean_object* v_b_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
if (lean_obj_tag(v_n_673_) == 0)
{
lean_object* v_cs_680_; lean_object* v___x_681_; lean_object* v___x_682_; size_t v_sz_683_; size_t v___x_684_; lean_object* v___x_685_; 
v_cs_680_ = lean_ctor_get(v_n_673_, 0);
v___x_681_ = lean_box(0);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_b_674_);
v_sz_683_ = lean_array_size(v_cs_680_);
v___x_684_ = ((size_t)0ULL);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_671_, v_goal_672_, v_cs_680_, v_sz_683_, v___x_684_, v___x_682_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_700_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_700_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_700_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_700_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; 
v_fst_690_ = lean_ctor_get(v_a_686_, 0);
if (lean_obj_tag(v_fst_690_) == 0)
{
lean_object* v_snd_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v_snd_691_ = lean_ctor_get(v_a_686_, 1);
lean_inc(v_snd_691_);
lean_dec(v_a_686_);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v_snd_691_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_692_);
v___x_694_ = v___x_688_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
else
{
lean_object* v_val_696_; lean_object* v___x_698_; 
lean_inc_ref(v_fst_690_);
lean_dec(v_a_686_);
v_val_696_ = lean_ctor_get(v_fst_690_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_fst_690_, 1);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v_val_696_);
v___x_698_ = v___x_688_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_val_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_685_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_685_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_vs_709_; lean_object* v___x_710_; lean_object* v___x_711_; size_t v_sz_712_; size_t v___x_713_; lean_object* v___x_714_; 
v_vs_709_ = lean_ctor_get(v_n_673_, 0);
v___x_710_ = lean_box(0);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_b_674_);
v_sz_712_ = lean_array_size(v_vs_709_);
v___x_713_ = ((size_t)0ULL);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_672_, v_vs_709_, v_sz_712_, v___x_713_, v___x_711_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_729_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_729_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_fst_719_; 
v_fst_719_ = lean_ctor_get(v_a_715_, 0);
if (lean_obj_tag(v_fst_719_) == 0)
{
lean_object* v_snd_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_snd_720_ = lean_ctor_get(v_a_715_, 1);
lean_inc(v_snd_720_);
lean_dec(v_a_715_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v_snd_720_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_721_);
v___x_723_ = v___x_717_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v_val_725_; lean_object* v___x_727_; 
lean_inc_ref(v_fst_719_);
lean_dec(v_a_715_);
v_val_725_ = lean_ctor_get(v_fst_719_, 0);
lean_inc(v_val_725_);
lean_dec_ref_known(v_fst_719_, 1);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_val_725_);
v___x_727_ = v___x_717_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_val_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_714_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_714_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object* v_init_738_, lean_object* v_goal_739_, lean_object* v_as_740_, size_t v_sz_741_, size_t v_i_742_, lean_object* v_b_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_lt(v_i_742_, v_sz_741_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_b_743_);
return v___x_750_;
}
else
{
lean_object* v_snd_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_785_; 
v_snd_751_ = lean_ctor_get(v_b_743_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_b_743_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_b_743_, 0);
lean_dec(v_unused_786_);
v___x_753_ = v_b_743_;
v_isShared_754_ = v_isSharedCheck_785_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_snd_751_);
lean_dec(v_b_743_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_785_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v_a_756_; lean_object* v___x_757_; 
v___x_755_ = lean_box(0);
v_a_756_ = lean_array_uget_borrowed(v_as_740_, v_i_742_);
lean_inc(v_snd_751_);
v___x_757_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_738_, v_goal_739_, v_a_756_, v_snd_751_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_776_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_776_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_776_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_776_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
if (lean_obj_tag(v_a_758_) == 0)
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_a_758_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_762_);
v___x_764_ = v___x_753_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_snd_751_);
v___x_764_ = v_reuseFailAlloc_768_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_764_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; 
lean_del_object(v___x_760_);
lean_dec(v_snd_751_);
v_a_769_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v_a_758_, 1);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v_a_769_);
lean_ctor_set(v___x_753_, 0, v___x_755_);
v___x_771_ = v___x_753_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_769_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_742_, v___x_772_);
v_i_742_ = v___x_773_;
v_b_743_ = v___x_771_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_753_);
lean_dec(v_snd_751_);
v_a_777_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_757_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_757_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object* v_init_787_, lean_object* v_goal_788_, lean_object* v_as_789_, lean_object* v_sz_790_, lean_object* v_i_791_, lean_object* v_b_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
size_t v_sz_boxed_798_; size_t v_i_boxed_799_; lean_object* v_res_800_; 
v_sz_boxed_798_ = lean_unbox_usize(v_sz_790_);
lean_dec(v_sz_790_);
v_i_boxed_799_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_787_, v_goal_788_, v_as_789_, v_sz_boxed_798_, v_i_boxed_799_, v_b_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_as_789_);
lean_dec_ref(v_goal_788_);
lean_dec_ref(v_init_787_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object* v_init_801_, lean_object* v_goal_802_, lean_object* v_n_803_, lean_object* v_b_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_801_, v_goal_802_, v_n_803_, v_b_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_n_803_);
lean_dec_ref(v_goal_802_);
lean_dec_ref(v_init_801_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object* v_goal_811_, lean_object* v_as_812_, size_t v_sz_813_, size_t v_i_814_, lean_object* v_b_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = lean_usize_dec_lt(v_i_814_, v_sz_813_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_b_815_);
return v___x_822_;
}
else
{
lean_object* v_snd_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_872_; 
v_snd_823_ = lean_ctor_get(v_b_815_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_b_815_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_b_815_, 0);
lean_dec(v_unused_873_);
v___x_825_ = v_b_815_;
v_isShared_826_ = v_isSharedCheck_872_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_snd_823_);
lean_dec(v_b_815_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_872_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v_a_829_; lean_object* v_a_836_; lean_object* v___x_837_; 
v___x_827_ = lean_box(0);
v_a_836_ = lean_array_uget_borrowed(v_as_812_, v_i_814_);
lean_inc(v_a_836_);
v___x_837_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_811_, v_a_836_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_838_);
if (v___x_839_ == 0)
{
lean_dec(v_a_838_);
v_a_829_ = v_snd_823_;
goto v___jp_828_;
}
else
{
lean_object* v___x_840_; 
lean_inc(v_a_838_);
v___x_840_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_838_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_842_ == 0)
{
lean_dec(v_a_838_);
v_a_829_ = v_snd_823_;
goto v___jp_828_;
}
else
{
lean_object* v_self_843_; lean_object* v___x_844_; 
v_self_843_ = lean_ctor_get(v_a_838_, 0);
lean_inc_ref_n(v_self_843_, 2);
lean_dec(v_a_838_);
v___x_844_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_811_, v_self_843_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
if (lean_obj_tag(v_a_845_) == 1)
{
lean_object* v_val_846_; lean_object* v___x_847_; 
v_val_846_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v_a_845_, 1);
v___x_847_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_811_, v_self_843_, v_val_846_, v_snd_823_);
v_a_829_ = v___x_847_;
goto v___jp_828_;
}
else
{
lean_dec(v_a_845_);
lean_dec_ref(v_self_843_);
v_a_829_ = v_snd_823_;
goto v___jp_828_;
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_self_843_);
lean_del_object(v___x_825_);
lean_dec(v_snd_823_);
v_a_848_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_844_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_844_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_838_);
lean_del_object(v___x_825_);
lean_dec(v_snd_823_);
v_a_856_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_840_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_840_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_825_);
lean_dec(v_snd_823_);
v_a_864_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_837_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_837_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
v___jp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_a_829_);
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_831_ = v___x_825_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_a_829_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
size_t v___x_832_; size_t v___x_833_; 
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_add(v_i_814_, v___x_832_);
v_i_814_ = v___x_833_;
v_b_815_ = v___x_831_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object* v_goal_874_, lean_object* v_as_875_, lean_object* v_sz_876_, lean_object* v_i_877_, lean_object* v_b_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
size_t v_sz_boxed_884_; size_t v_i_boxed_885_; lean_object* v_res_886_; 
v_sz_boxed_884_ = lean_unbox_usize(v_sz_876_);
lean_dec(v_sz_876_);
v_i_boxed_885_ = lean_unbox_usize(v_i_877_);
lean_dec(v_i_877_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_874_, v_as_875_, v_sz_boxed_884_, v_i_boxed_885_, v_b_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v_as_875_);
lean_dec_ref(v_goal_874_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object* v_goal_887_, lean_object* v_as_888_, size_t v_sz_889_, size_t v_i_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_lt(v_i_890_, v_sz_889_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_b_891_);
return v___x_898_;
}
else
{
lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_948_; 
v_snd_899_ = lean_ctor_get(v_b_891_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_b_891_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_b_891_, 0);
lean_dec(v_unused_949_);
v___x_901_ = v_b_891_;
v_isShared_902_ = v_isSharedCheck_948_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_dec(v_b_891_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_948_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v_a_905_; lean_object* v_a_912_; lean_object* v___x_913_; 
v___x_903_ = lean_box(0);
v_a_912_ = lean_array_uget_borrowed(v_as_888_, v_i_890_);
lean_inc(v_a_912_);
v___x_913_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_887_, v_a_912_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; uint8_t v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_914_);
if (v___x_915_ == 0)
{
lean_dec(v_a_914_);
v_a_905_ = v_snd_899_;
goto v___jp_904_;
}
else
{
lean_object* v___x_916_; 
lean_inc(v_a_914_);
v___x_916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_914_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; uint8_t v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = lean_unbox(v_a_917_);
lean_dec(v_a_917_);
if (v___x_918_ == 0)
{
lean_dec(v_a_914_);
v_a_905_ = v_snd_899_;
goto v___jp_904_;
}
else
{
lean_object* v_self_919_; lean_object* v___x_920_; 
v_self_919_ = lean_ctor_get(v_a_914_, 0);
lean_inc_ref_n(v_self_919_, 2);
lean_dec(v_a_914_);
v___x_920_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_887_, v_self_919_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
if (lean_obj_tag(v_a_921_) == 1)
{
lean_object* v_val_922_; lean_object* v___x_923_; 
v_val_922_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v_a_921_, 1);
v___x_923_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_887_, v_self_919_, v_val_922_, v_snd_899_);
v_a_905_ = v___x_923_;
goto v___jp_904_;
}
else
{
lean_dec(v_a_921_);
lean_dec_ref(v_self_919_);
v_a_905_ = v_snd_899_;
goto v___jp_904_;
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_self_919_);
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v_a_924_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_920_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_920_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_a_914_);
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v_a_932_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_916_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_916_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v_a_940_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_913_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_913_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
v___jp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v_a_905_);
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_907_ = v___x_901_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_a_905_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
size_t v___x_908_; size_t v___x_909_; lean_object* v___x_910_; 
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_add(v_i_890_, v___x_908_);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_887_, v_as_888_, v_sz_889_, v___x_909_, v___x_907_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
return v___x_910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object* v_goal_950_, lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_961_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_950_, v_as_951_, v_sz_boxed_960_, v_i_boxed_961_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_as_951_);
lean_dec_ref(v_goal_950_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object* v_goal_963_, lean_object* v_t_964_, lean_object* v_init_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_root_971_; lean_object* v_tail_972_; lean_object* v___x_973_; 
v_root_971_ = lean_ctor_get(v_t_964_, 0);
v_tail_972_ = lean_ctor_get(v_t_964_, 1);
lean_inc_ref(v_init_965_);
v___x_973_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_965_, v_goal_963_, v_root_971_, v_init_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec_ref(v_init_965_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1010_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_1010_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1010_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
if (lean_obj_tag(v_a_974_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; 
v_a_978_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v_a_974_, 1);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v_a_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; size_t v_sz_985_; size_t v___x_986_; lean_object* v___x_987_; 
lean_del_object(v___x_976_);
v_a_982_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v_a_974_, 1);
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_a_982_);
v_sz_985_ = lean_array_size(v_tail_972_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_963_, v_tail_972_, v_sz_985_, v___x_986_, v___x_984_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1001_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1001_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1001_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_fst_992_; 
v_fst_992_ = lean_ctor_get(v_a_988_, 0);
if (lean_obj_tag(v_fst_992_) == 0)
{
lean_object* v_snd_993_; lean_object* v___x_995_; 
v_snd_993_ = lean_ctor_get(v_a_988_, 1);
lean_inc(v_snd_993_);
lean_dec(v_a_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_snd_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_snd_993_);
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
lean_object* v_val_997_; lean_object* v___x_999_; 
lean_inc_ref(v_fst_992_);
lean_dec(v_a_988_);
v_val_997_ = lean_ctor_get(v_fst_992_, 0);
lean_inc(v_val_997_);
lean_dec_ref_known(v_fst_992_, 1);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_val_997_);
v___x_999_ = v___x_990_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_val_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_987_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_987_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_973_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_973_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object* v_goal_1019_, lean_object* v_t_1020_, lean_object* v_init_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1019_, v_t_1020_, v_init_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec_ref(v_t_1020_);
lean_dec_ref(v_goal_1019_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object* v_a_1028_, lean_object* v_x_1029_){
_start:
{
if (lean_obj_tag(v_x_1029_) == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_box(0);
return v___x_1030_;
}
else
{
lean_object* v_key_1031_; lean_object* v_value_1032_; lean_object* v_tail_1033_; uint8_t v___x_1034_; 
v_key_1031_ = lean_ctor_get(v_x_1029_, 0);
v_value_1032_ = lean_ctor_get(v_x_1029_, 1);
v_tail_1033_ = lean_ctor_get(v_x_1029_, 2);
v___x_1034_ = lean_expr_eqv(v_key_1031_, v_a_1028_);
if (v___x_1034_ == 0)
{
v_x_1029_ = v_tail_1033_;
goto _start;
}
else
{
lean_object* v___x_1036_; 
lean_inc(v_value_1032_);
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_value_1032_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1037_, v_x_1038_);
lean_dec(v_x_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object* v_m_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_buckets_1042_; lean_object* v___x_1043_; uint64_t v___x_1044_; uint64_t v___x_1045_; uint64_t v___x_1046_; uint64_t v_fold_1047_; uint64_t v___x_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_buckets_1042_ = lean_ctor_get(v_m_1040_, 1);
v___x_1043_ = lean_array_get_size(v_buckets_1042_);
v___x_1044_ = l_Lean_Expr_hash(v_a_1041_);
v___x_1045_ = 32ULL;
v___x_1046_ = lean_uint64_shift_right(v___x_1044_, v___x_1045_);
v_fold_1047_ = lean_uint64_xor(v___x_1044_, v___x_1046_);
v___x_1048_ = 16ULL;
v___x_1049_ = lean_uint64_shift_right(v_fold_1047_, v___x_1048_);
v___x_1050_ = lean_uint64_xor(v_fold_1047_, v___x_1049_);
v___x_1051_ = lean_uint64_to_usize(v___x_1050_);
v___x_1052_ = lean_usize_of_nat(v___x_1043_);
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_sub(v___x_1052_, v___x_1053_);
v___x_1055_ = lean_usize_land(v___x_1051_, v___x_1054_);
v___x_1056_ = lean_array_uget_borrowed(v_buckets_1042_, v___x_1055_);
v___x_1057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1041_, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object* v_m_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1058_, v_a_1059_);
lean_dec_ref(v_a_1059_);
lean_dec_ref(v_m_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object* v_goal_1061_, lean_object* v_as_1062_, size_t v_sz_1063_, size_t v_i_1064_, lean_object* v_b_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_a_1072_; uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_lt(v_i_1064_, v_sz_1063_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_b_1065_);
return v___x_1077_;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_array_uget_borrowed(v_as_1062_, v_i_1064_);
lean_inc(v_a_1078_);
v___x_1079_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1061_, v_a_1078_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v_self_1081_; lean_object* v___x_1082_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_self_1081_ = lean_ctor_get(v_a_1080_, 0);
lean_inc_ref(v_self_1081_);
lean_dec(v_a_1080_);
v___x_1082_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1081_);
if (lean_obj_tag(v___x_1082_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; 
v_val_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1065_, v_val_1083_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1065_, v_self_1081_);
lean_dec_ref(v_self_1081_);
if (lean_obj_tag(v___x_1085_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; 
v_val_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1061_, v_val_1083_, v_val_1086_, v_b_1065_);
v_a_1072_ = v___x_1087_;
goto v___jp_1071_;
}
else
{
lean_dec(v___x_1085_);
lean_dec(v_val_1083_);
v_a_1072_ = v_b_1065_;
goto v___jp_1071_;
}
}
else
{
lean_dec_ref_known(v___x_1084_, 1);
lean_dec(v_val_1083_);
lean_dec_ref(v_self_1081_);
v_a_1072_ = v_b_1065_;
goto v___jp_1071_;
}
}
else
{
lean_dec(v___x_1082_);
lean_dec_ref(v_self_1081_);
v_a_1072_ = v_b_1065_;
goto v___jp_1071_;
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v_b_1065_);
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1079_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1079_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
v___jp_1071_:
{
size_t v___x_1073_; size_t v___x_1074_; 
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = lean_usize_add(v_i_1064_, v___x_1073_);
v_i_1064_ = v___x_1074_;
v_b_1065_ = v_a_1072_;
goto _start;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object* v_goal_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object* v_goal_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec_ref(v_goal_1177_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object* v_00_u03b2_1184_, lean_object* v_m_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1185_, v_a_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object* v_00_u03b2_1188_, lean_object* v_m_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(v_00_u03b2_1188_, v_m_1189_, v_a_1190_);
lean_dec_ref(v_a_1190_);
lean_dec_ref(v_m_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object* v_00_u03b2_1192_, lean_object* v_a_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1193_, v_x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1196_, lean_object* v_a_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(v_00_u03b2_1196_, v_a_1197_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec_ref(v_a_1197_);
return v_res_1199_;
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

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
lean_object* v___x_85_; lean_object* v___x_347__overap_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0);
v___x_347__overap_86_ = lean_panic_fn_borrowed(v___x_85_, v_msg_83_);
v___x_87_ = lean_apply_1(v___x_347__overap_86_, lean_box(0));
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
size_t v_x_550__boxed_140_; lean_object* v_res_141_; 
v_x_550__boxed_140_ = lean_unbox_usize(v_x_138_);
lean_dec(v_x_138_);
v_res_141_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_137_, v_x_550__boxed_140_, v_x_139_);
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
lean_object* v_self_165_; lean_object* v_root_166_; size_t v___x_167_; size_t v___x_168_; uint8_t v___x_169_; 
v_self_165_ = lean_ctor_get(v_node_163_, 0);
v_root_166_ = lean_ctor_get(v_node_163_, 2);
v___x_167_ = lean_ptr_addr(v_self_165_);
v___x_168_ = lean_ptr_addr(v_root_166_);
v___x_169_ = lean_usize_dec_eq(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3);
v___x_171_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_173_ = l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(v___x_172_, v_node_163_);
if (lean_obj_tag(v___x_173_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_val_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = l_instInhabitedRat;
v___x_176_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_172_, v_goal_162_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_206_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_206_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_206_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_206_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_varMap_181_; lean_object* v_assignment_182_; lean_object* v___x_183_; 
v_varMap_181_ = lean_ctor_get(v_a_177_, 1);
lean_inc_ref(v_varMap_181_);
v_assignment_182_ = lean_ctor_get(v_a_177_, 12);
lean_inc_ref(v_assignment_182_);
lean_dec(v_a_177_);
v___x_183_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_varMap_181_, v_val_174_);
lean_dec(v_val_174_);
lean_dec_ref(v_varMap_181_);
if (lean_obj_tag(v___x_183_) == 1)
{
lean_object* v_val_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_201_; 
v_val_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_201_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_201_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_val_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_201_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_size_188_; uint8_t v___x_189_; 
v_size_188_ = lean_ctor_get(v_assignment_182_, 2);
v___x_189_ = lean_nat_dec_lt(v_val_184_, v_size_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_del_object(v___x_186_);
lean_dec(v_val_184_);
lean_dec_ref(v_assignment_182_);
v___x_190_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_190_);
v___x_192_ = v___x_179_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_PersistentArray_get_x21___redArg(v___x_175_, v_assignment_182_, v_val_184_);
lean_dec(v_val_184_);
lean_dec_ref(v_assignment_182_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_194_);
v___x_196_ = v___x_186_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_196_);
v___x_198_ = v___x_179_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec(v___x_183_);
lean_dec_ref(v_assignment_182_);
v___x_202_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_202_);
v___x_204_ = v___x_179_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_val_174_);
v_a_207_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_176_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_176_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v___x_173_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object* v_goal_217_, lean_object* v_node_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_217_, v_node_218_);
lean_dec_ref(v_node_218_);
lean_dec_ref(v_goal_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object* v_00_u03b2_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_222_, v_x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object* v_00_u03b2_225_, lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(v_00_u03b2_225_, v_x_226_, v_x_227_);
lean_dec_ref(v_x_227_);
lean_dec_ref(v_x_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object* v_00_u03b2_229_, lean_object* v_x_230_, size_t v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_230_, v_x_231_, v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
size_t v_x_751__boxed_238_; lean_object* v_res_239_; 
v_x_751__boxed_238_ = lean_unbox_usize(v_x_236_);
lean_dec(v_x_236_);
v_res_239_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(v_00_u03b2_234_, v_x_235_, v_x_751__boxed_238_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_240_, lean_object* v_keys_241_, lean_object* v_vals_242_, lean_object* v_heq_243_, lean_object* v_i_244_, lean_object* v_k_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_241_, v_vals_242_, v_i_244_, v_k_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_247_, lean_object* v_keys_248_, lean_object* v_vals_249_, lean_object* v_heq_250_, lean_object* v_i_251_, lean_object* v_k_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(v_00_u03b2_247_, v_keys_248_, v_vals_249_, v_heq_250_, v_i_251_, v_k_252_);
lean_dec_ref(v_k_252_);
lean_dec_ref(v_vals_249_);
lean_dec_ref(v_keys_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(lean_object* v_e_309_){
_start:
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = l_Lean_Expr_cleanupAnnotations(v_e_309_);
v___x_311_ = l_Lean_Expr_isApp(v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v___x_310_);
v___x_312_ = lean_box(0);
return v___x_312_;
}
else
{
lean_object* v_arg_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_arg_313_ = lean_ctor_get(v___x_310_, 1);
lean_inc_ref(v_arg_313_);
v___x_314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_310_);
lean_dec_ref(v___x_310_);
v___x_315_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__2));
v___x_316_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__4));
v___x_318_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__6));
v___x_320_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__8));
v___x_322_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__10));
v___x_324_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__12));
v___x_326_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__14));
v___x_328_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__16));
v___x_330_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__18));
v___x_332_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__20));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_314_, v___x_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = l_Lean_Expr_isApp(v___x_314_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v___x_314_);
lean_dec_ref(v_arg_313_);
v___x_336_ = lean_box(0);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_314_);
lean_dec_ref(v___x_314_);
v___x_338_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__23));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__25));
v___x_341_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___closed__28));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_342_);
lean_dec_ref(v___x_337_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec_ref(v_arg_313_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v_arg_313_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec_ref(v___x_337_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v_arg_313_);
return v___x_346_;
}
}
else
{
lean_object* v___x_347_; 
lean_dec_ref(v___x_337_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v_arg_313_);
return v___x_347_;
}
}
}
else
{
lean_object* v___x_348_; 
lean_dec_ref(v___x_314_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v_arg_313_);
return v___x_348_;
}
}
else
{
lean_object* v___x_349_; 
lean_dec_ref(v___x_314_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_arg_313_);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; 
lean_dec_ref(v___x_314_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_arg_313_);
return v___x_350_;
}
}
else
{
lean_object* v___x_351_; 
lean_dec_ref(v___x_314_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_arg_313_);
return v___x_351_;
}
}
else
{
lean_object* v___x_352_; 
lean_dec_ref(v___x_314_);
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v_arg_313_);
return v___x_352_;
}
}
else
{
lean_object* v___x_353_; 
lean_dec_ref(v___x_314_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_arg_313_);
return v___x_353_;
}
}
else
{
lean_object* v___x_354_; 
lean_dec_ref(v___x_314_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v_arg_313_);
return v___x_354_;
}
}
else
{
lean_object* v___x_355_; 
lean_dec_ref(v___x_314_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_arg_313_);
return v___x_355_;
}
}
else
{
lean_object* v___x_356_; 
lean_dec_ref(v___x_314_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_arg_313_);
return v___x_356_;
}
}
else
{
lean_object* v___x_357_; 
lean_dec_ref(v___x_314_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_arg_313_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f___boxed(lean_object* v_e_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_358_);
lean_dec_ref(v_e_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object* v_e_368_){
_start:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = l_Lean_Expr_cleanupAnnotations(v_e_368_);
v___x_370_ = l_Lean_Expr_isApp(v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec_ref(v___x_369_);
v___x_371_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_368_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_369_);
v___x_373_ = l_Lean_Expr_isApp(v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v___x_369_);
v___x_374_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_368_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_372_);
v___x_376_ = l_Lean_Expr_isApp(v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec_ref(v___x_375_);
lean_dec_ref(v___x_372_);
lean_dec_ref(v___x_369_);
v___x_377_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_368_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_375_);
lean_dec_ref(v___x_375_);
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2));
v___x_380_ = l_Lean_Expr_isConstOf(v___x_378_, v___x_379_);
lean_dec_ref(v___x_378_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec_ref(v___x_372_);
lean_dec_ref(v___x_369_);
v___x_381_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_e_368_);
return v___x_381_;
}
else
{
lean_object* v_arg_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_arg_382_ = lean_ctor_get(v___x_372_, 1);
lean_inc_ref(v_arg_382_);
lean_dec_ref(v___x_372_);
v___x_383_ = l_Lean_Expr_cleanupAnnotations(v_arg_382_);
lean_dec_ref(v_arg_382_);
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4));
v___x_385_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_384_);
lean_dec_ref(v___x_383_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec_ref(v___x_369_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v_arg_387_; lean_object* v___x_388_; 
v_arg_387_ = lean_ctor_get(v___x_369_, 1);
lean_inc_ref(v_arg_387_);
lean_dec_ref(v___x_369_);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v_arg_387_);
return v___x_388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___boxed(lean_object* v_e_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_e_389_);
lean_dec_ref(v_e_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Rat_ofInt(v_a_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object* v_goal_393_, lean_object* v_e_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Grind_Goal_getRoot(v_goal_393_, v_e_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v___x_402_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_393_, v_a_401_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v_ref_404_; lean_object* v___x_405_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v_ref_404_ = lean_ctor_get(v_a_397_, 2);
v___x_405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_393_, v_a_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_471_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_471_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_471_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_471_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
if (lean_obj_tag(v_a_406_) == 1)
{
lean_object* v___x_411_; 
lean_dec(v_a_403_);
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
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
lean_object* v_self_413_; lean_object* v___x_414_; 
lean_del_object(v___x_408_);
lean_dec(v_a_406_);
v_self_413_ = lean_ctor_get(v_a_403_, 0);
lean_inc_ref_n(v_self_413_, 2);
lean_dec(v_a_403_);
v___x_414_ = l_Lean_Meta_getIntValue_x3f(v_self_413_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_462_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_462_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_462_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_462_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
if (lean_obj_tag(v_a_415_) == 1)
{
lean_object* v_val_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_self_413_);
v_val_419_ = lean_ctor_get(v_a_415_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_a_415_);
if (v_isSharedCheck_430_ == 0)
{
v___x_421_ = v_a_415_;
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_val_419_);
lean_dec(v_a_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = l_Rat_ofInt(v_val_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_425_);
v___x_427_ = v___x_417_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
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
else
{
lean_object* v___x_431_; 
lean_del_object(v___x_417_);
lean_dec(v_a_415_);
v___x_431_ = l_Lean_Meta_getNatValue_x3f(v_self_413_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec_ref(v_self_413_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_453_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_453_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_453_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_453_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
if (lean_obj_tag(v_a_432_) == 1)
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_448_; 
v_val_436_ = lean_ctor_get(v_a_432_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_a_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_438_ = v_a_432_;
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v_a_432_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_448_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_nat_to_int(v_val_436_);
v___x_441_ = l_Rat_ofInt(v___x_440_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_443_);
v___x_445_ = v___x_434_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec(v_a_432_);
v___x_449_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_449_);
v___x_451_ = v___x_434_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_431_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_431_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_self_413_);
v_a_463_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_414_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_414_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_a_403_);
v_a_472_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_483_ == 0)
{
v___x_474_ = v___x_405_;
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_405_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_483_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_476_ = lean_io_error_to_string(v_a_472_);
v___x_477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
v___x_478_ = l_Lean_MessageData_ofFormat(v___x_477_);
lean_inc(v_ref_404_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_ref_404_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_479_);
v___x_481_ = v___x_474_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_402_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_402_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_400_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_400_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object* v_goal_500_, lean_object* v_e_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_500_, v_e_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_goal_500_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object* v_goal_508_, lean_object* v_as_509_, size_t v_sz_510_, size_t v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_b_512_);
return v___x_519_;
}
else
{
lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_569_; 
v_snd_520_ = lean_ctor_get(v_b_512_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_b_512_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_b_512_, 0);
lean_dec(v_unused_570_);
v___x_522_ = v_b_512_;
v_isShared_523_ = v_isSharedCheck_569_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_dec(v_b_512_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_569_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v_a_526_; lean_object* v_a_533_; lean_object* v___x_534_; 
v___x_524_ = lean_box(0);
v_a_533_ = lean_array_uget_borrowed(v_as_509_, v_i_511_);
lean_inc(v_a_533_);
v___x_534_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_508_, v_a_533_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; uint8_t v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_535_);
if (v___x_536_ == 0)
{
lean_dec(v_a_535_);
v_a_526_ = v_snd_520_;
goto v___jp_525_;
}
else
{
lean_object* v___x_537_; 
lean_inc(v_a_535_);
v___x_537_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_535_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; uint8_t v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = lean_unbox(v_a_538_);
lean_dec(v_a_538_);
if (v___x_539_ == 0)
{
lean_dec(v_a_535_);
v_a_526_ = v_snd_520_;
goto v___jp_525_;
}
else
{
lean_object* v_self_540_; lean_object* v___x_541_; 
v_self_540_ = lean_ctor_get(v_a_535_, 0);
lean_inc_ref_n(v_self_540_, 2);
lean_dec(v_a_535_);
v___x_541_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_508_, v_self_540_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
if (lean_obj_tag(v_a_542_) == 1)
{
lean_object* v_val_543_; lean_object* v___x_544_; 
v_val_543_ = lean_ctor_get(v_a_542_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_a_542_, 1);
v___x_544_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_508_, v_self_540_, v_val_543_, v_snd_520_);
v_a_526_ = v___x_544_;
goto v___jp_525_;
}
else
{
lean_dec(v_a_542_);
lean_dec_ref(v_self_540_);
v_a_526_ = v_snd_520_;
goto v___jp_525_;
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_self_540_);
lean_del_object(v___x_522_);
lean_dec(v_snd_520_);
v_a_545_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_541_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_541_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_535_);
lean_del_object(v___x_522_);
lean_dec(v_snd_520_);
v_a_553_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_537_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_537_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_del_object(v___x_522_);
lean_dec(v_snd_520_);
v_a_561_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_534_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_534_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
v___jp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v_a_526_);
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_a_526_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
size_t v___x_529_; size_t v___x_530_; 
v___x_529_ = ((size_t)1ULL);
v___x_530_ = lean_usize_add(v_i_511_, v___x_529_);
v_i_511_ = v___x_530_;
v_b_512_ = v___x_528_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_goal_571_, lean_object* v_as_572_, lean_object* v_sz_573_, lean_object* v_i_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
size_t v_sz_boxed_581_; size_t v_i_boxed_582_; lean_object* v_res_583_; 
v_sz_boxed_581_ = lean_unbox_usize(v_sz_573_);
lean_dec(v_sz_573_);
v_i_boxed_582_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_571_, v_as_572_, v_sz_boxed_581_, v_i_boxed_582_, v_b_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v_as_572_);
lean_dec_ref(v_goal_571_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object* v_goal_584_, lean_object* v_as_585_, size_t v_sz_586_, size_t v_i_587_, lean_object* v_b_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_usize_dec_lt(v_i_587_, v_sz_586_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_b_588_);
return v___x_595_;
}
else
{
lean_object* v_snd_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_645_; 
v_snd_596_ = lean_ctor_get(v_b_588_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_b_588_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_b_588_, 0);
lean_dec(v_unused_646_);
v___x_598_ = v_b_588_;
v_isShared_599_ = v_isSharedCheck_645_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snd_596_);
lean_dec(v_b_588_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_645_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v_a_602_; lean_object* v_a_609_; lean_object* v___x_610_; 
v___x_600_ = lean_box(0);
v_a_609_ = lean_array_uget_borrowed(v_as_585_, v_i_587_);
lean_inc(v_a_609_);
v___x_610_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_584_, v_a_609_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; uint8_t v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_611_);
if (v___x_612_ == 0)
{
lean_dec(v_a_611_);
v_a_602_ = v_snd_596_;
goto v___jp_601_;
}
else
{
lean_object* v___x_613_; 
lean_inc(v_a_611_);
v___x_613_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_611_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; uint8_t v___x_615_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v___x_615_ = lean_unbox(v_a_614_);
lean_dec(v_a_614_);
if (v___x_615_ == 0)
{
lean_dec(v_a_611_);
v_a_602_ = v_snd_596_;
goto v___jp_601_;
}
else
{
lean_object* v_self_616_; lean_object* v___x_617_; 
v_self_616_ = lean_ctor_get(v_a_611_, 0);
lean_inc_ref_n(v_self_616_, 2);
lean_dec(v_a_611_);
v___x_617_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_584_, v_self_616_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
if (lean_obj_tag(v_a_618_) == 1)
{
lean_object* v_val_619_; lean_object* v___x_620_; 
v_val_619_ = lean_ctor_get(v_a_618_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v_a_618_, 1);
v___x_620_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_584_, v_self_616_, v_val_619_, v_snd_596_);
v_a_602_ = v___x_620_;
goto v___jp_601_;
}
else
{
lean_dec(v_a_618_);
lean_dec_ref(v_self_616_);
v_a_602_ = v_snd_596_;
goto v___jp_601_;
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_self_616_);
lean_del_object(v___x_598_);
lean_dec(v_snd_596_);
v_a_621_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_617_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_617_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_a_611_);
lean_del_object(v___x_598_);
lean_dec(v_snd_596_);
v_a_629_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_613_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_613_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_del_object(v___x_598_);
lean_dec(v_snd_596_);
v_a_637_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_610_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_610_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
v___jp_601_:
{
lean_object* v___x_604_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_a_602_);
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_604_ = v___x_598_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_602_);
v___x_604_ = v_reuseFailAlloc_608_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_587_, v___x_605_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_584_, v_as_585_, v_sz_586_, v___x_606_, v___x_604_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object* v_goal_647_, lean_object* v_as_648_, lean_object* v_sz_649_, lean_object* v_i_650_, lean_object* v_b_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_sz_boxed_657_ = lean_unbox_usize(v_sz_649_);
lean_dec(v_sz_649_);
v_i_boxed_658_ = lean_unbox_usize(v_i_650_);
lean_dec(v_i_650_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_647_, v_as_648_, v_sz_boxed_657_, v_i_boxed_658_, v_b_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v_as_648_);
lean_dec_ref(v_goal_647_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object* v_init_660_, lean_object* v_goal_661_, lean_object* v_n_662_, lean_object* v_b_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
if (lean_obj_tag(v_n_662_) == 0)
{
lean_object* v_cs_669_; lean_object* v___x_670_; lean_object* v___x_671_; size_t v_sz_672_; size_t v___x_673_; lean_object* v___x_674_; 
v_cs_669_ = lean_ctor_get(v_n_662_, 0);
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_b_663_);
v_sz_672_ = lean_array_size(v_cs_669_);
v___x_673_ = ((size_t)0ULL);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_660_, v_goal_661_, v_cs_669_, v_sz_672_, v___x_673_, v___x_671_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_689_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_689_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_689_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_689_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_fst_679_; 
v_fst_679_ = lean_ctor_get(v_a_675_, 0);
if (lean_obj_tag(v_fst_679_) == 0)
{
lean_object* v_snd_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v_snd_680_ = lean_ctor_get(v_a_675_, 1);
lean_inc(v_snd_680_);
lean_dec(v_a_675_);
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_snd_680_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_681_);
v___x_683_ = v___x_677_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
lean_object* v_val_685_; lean_object* v___x_687_; 
lean_inc_ref(v_fst_679_);
lean_dec(v_a_675_);
v_val_685_ = lean_ctor_get(v_fst_679_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v_fst_679_, 1);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_val_685_);
v___x_687_ = v___x_677_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_val_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_674_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_674_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_vs_698_; lean_object* v___x_699_; lean_object* v___x_700_; size_t v_sz_701_; size_t v___x_702_; lean_object* v___x_703_; 
v_vs_698_ = lean_ctor_get(v_n_662_, 0);
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_b_663_);
v_sz_701_ = lean_array_size(v_vs_698_);
v___x_702_ = ((size_t)0ULL);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_661_, v_vs_698_, v_sz_701_, v___x_702_, v___x_700_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_718_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_718_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_718_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_718_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_fst_708_; 
v_fst_708_ = lean_ctor_get(v_a_704_, 0);
if (lean_obj_tag(v_fst_708_) == 0)
{
lean_object* v_snd_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v_snd_709_ = lean_ctor_get(v_a_704_, 1);
lean_inc(v_snd_709_);
lean_dec(v_a_704_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_snd_709_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_710_);
v___x_712_ = v___x_706_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v_val_714_; lean_object* v___x_716_; 
lean_inc_ref(v_fst_708_);
lean_dec(v_a_704_);
v_val_714_ = lean_ctor_get(v_fst_708_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v_fst_708_, 1);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v_val_714_);
v___x_716_ = v___x_706_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_val_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_703_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_703_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object* v_init_727_, lean_object* v_goal_728_, lean_object* v_as_729_, size_t v_sz_730_, size_t v_i_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_lt(v_i_731_, v_sz_730_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v_b_732_);
return v___x_739_;
}
else
{
lean_object* v_snd_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_774_; 
v_snd_740_ = lean_ctor_get(v_b_732_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_b_732_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_b_732_, 0);
lean_dec(v_unused_775_);
v___x_742_ = v_b_732_;
v_isShared_743_ = v_isSharedCheck_774_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_snd_740_);
lean_dec(v_b_732_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_774_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_746_; 
v___x_744_ = lean_box(0);
v_a_745_ = lean_array_uget_borrowed(v_as_729_, v_i_731_);
lean_inc(v_snd_740_);
v___x_746_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_727_, v_goal_728_, v_a_745_, v_snd_740_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_765_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_765_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_765_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
if (lean_obj_tag(v_a_747_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v_a_747_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_751_);
v___x_753_ = v___x_742_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_snd_740_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_753_);
v___x_755_ = v___x_749_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; 
lean_del_object(v___x_749_);
lean_dec(v_snd_740_);
v_a_758_ = lean_ctor_get(v_a_747_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v_a_747_, 1);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v_a_758_);
lean_ctor_set(v___x_742_, 0, v___x_744_);
v___x_760_ = v___x_742_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_758_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
size_t v___x_761_; size_t v___x_762_; 
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_731_, v___x_761_);
v_i_731_ = v___x_762_;
v_b_732_ = v___x_760_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_del_object(v___x_742_);
lean_dec(v_snd_740_);
v_a_766_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_746_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_746_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object* v_init_776_, lean_object* v_goal_777_, lean_object* v_as_778_, lean_object* v_sz_779_, lean_object* v_i_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
size_t v_sz_boxed_787_; size_t v_i_boxed_788_; lean_object* v_res_789_; 
v_sz_boxed_787_ = lean_unbox_usize(v_sz_779_);
lean_dec(v_sz_779_);
v_i_boxed_788_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_776_, v_goal_777_, v_as_778_, v_sz_boxed_787_, v_i_boxed_788_, v_b_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v_as_778_);
lean_dec_ref(v_goal_777_);
lean_dec_ref(v_init_776_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object* v_init_790_, lean_object* v_goal_791_, lean_object* v_n_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_790_, v_goal_791_, v_n_792_, v_b_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec_ref(v_n_792_);
lean_dec_ref(v_goal_791_);
lean_dec_ref(v_init_790_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object* v_goal_800_, lean_object* v_as_801_, size_t v_sz_802_, size_t v_i_803_, lean_object* v_b_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
uint8_t v___x_810_; 
v___x_810_ = lean_usize_dec_lt(v_i_803_, v_sz_802_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_b_804_);
return v___x_811_;
}
else
{
lean_object* v_snd_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_861_; 
v_snd_812_ = lean_ctor_get(v_b_804_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_b_804_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_b_804_, 0);
lean_dec(v_unused_862_);
v___x_814_ = v_b_804_;
v_isShared_815_ = v_isSharedCheck_861_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_snd_812_);
lean_dec(v_b_804_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_861_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v_a_818_; lean_object* v_a_825_; lean_object* v___x_826_; 
v___x_816_ = lean_box(0);
v_a_825_ = lean_array_uget_borrowed(v_as_801_, v_i_803_);
lean_inc(v_a_825_);
v___x_826_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_800_, v_a_825_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; uint8_t v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v___x_828_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_827_);
if (v___x_828_ == 0)
{
lean_dec(v_a_827_);
v_a_818_ = v_snd_812_;
goto v___jp_817_;
}
else
{
lean_object* v___x_829_; 
lean_inc(v_a_827_);
v___x_829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_827_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; uint8_t v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = lean_unbox(v_a_830_);
lean_dec(v_a_830_);
if (v___x_831_ == 0)
{
lean_dec(v_a_827_);
v_a_818_ = v_snd_812_;
goto v___jp_817_;
}
else
{
lean_object* v_self_832_; lean_object* v___x_833_; 
v_self_832_ = lean_ctor_get(v_a_827_, 0);
lean_inc_ref_n(v_self_832_, 2);
lean_dec(v_a_827_);
v___x_833_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_800_, v_self_832_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
if (lean_obj_tag(v_a_834_) == 1)
{
lean_object* v_val_835_; lean_object* v___x_836_; 
v_val_835_ = lean_ctor_get(v_a_834_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_a_834_, 1);
v___x_836_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_800_, v_self_832_, v_val_835_, v_snd_812_);
v_a_818_ = v___x_836_;
goto v___jp_817_;
}
else
{
lean_dec(v_a_834_);
lean_dec_ref(v_self_832_);
v_a_818_ = v_snd_812_;
goto v___jp_817_;
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_self_832_);
lean_del_object(v___x_814_);
lean_dec(v_snd_812_);
v_a_837_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_833_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_833_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_a_827_);
lean_del_object(v___x_814_);
lean_dec(v_snd_812_);
v_a_845_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_829_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_829_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_del_object(v___x_814_);
lean_dec(v_snd_812_);
v_a_853_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_826_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_826_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
v___jp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_a_818_);
lean_ctor_set(v___x_814_, 0, v___x_816_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_a_818_);
v___x_820_ = v_reuseFailAlloc_824_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
size_t v___x_821_; size_t v___x_822_; 
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_803_, v___x_821_);
v_i_803_ = v___x_822_;
v_b_804_ = v___x_820_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object* v_goal_863_, lean_object* v_as_864_, lean_object* v_sz_865_, lean_object* v_i_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
size_t v_sz_boxed_873_; size_t v_i_boxed_874_; lean_object* v_res_875_; 
v_sz_boxed_873_ = lean_unbox_usize(v_sz_865_);
lean_dec(v_sz_865_);
v_i_boxed_874_ = lean_unbox_usize(v_i_866_);
lean_dec(v_i_866_);
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_863_, v_as_864_, v_sz_boxed_873_, v_i_boxed_874_, v_b_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v_as_864_);
lean_dec_ref(v_goal_863_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object* v_goal_876_, lean_object* v_as_877_, size_t v_sz_878_, size_t v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_b_880_);
return v___x_887_;
}
else
{
lean_object* v_snd_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_937_; 
v_snd_888_ = lean_ctor_get(v_b_880_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_b_880_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_b_880_, 0);
lean_dec(v_unused_938_);
v___x_890_ = v_b_880_;
v_isShared_891_ = v_isSharedCheck_937_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_snd_888_);
lean_dec(v_b_880_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_937_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v_a_894_; lean_object* v_a_901_; lean_object* v___x_902_; 
v___x_892_ = lean_box(0);
v_a_901_ = lean_array_uget_borrowed(v_as_877_, v_i_879_);
lean_inc(v_a_901_);
v___x_902_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_876_, v_a_901_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; uint8_t v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_903_);
if (v___x_904_ == 0)
{
lean_dec(v_a_903_);
v_a_894_ = v_snd_888_;
goto v___jp_893_;
}
else
{
lean_object* v___x_905_; 
lean_inc(v_a_903_);
v___x_905_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_903_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; uint8_t v___x_907_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = lean_unbox(v_a_906_);
lean_dec(v_a_906_);
if (v___x_907_ == 0)
{
lean_dec(v_a_903_);
v_a_894_ = v_snd_888_;
goto v___jp_893_;
}
else
{
lean_object* v_self_908_; lean_object* v___x_909_; 
v_self_908_ = lean_ctor_get(v_a_903_, 0);
lean_inc_ref_n(v_self_908_, 2);
lean_dec(v_a_903_);
v___x_909_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_876_, v_self_908_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
if (lean_obj_tag(v_a_910_) == 1)
{
lean_object* v_val_911_; lean_object* v___x_912_; 
v_val_911_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v_a_910_, 1);
v___x_912_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_876_, v_self_908_, v_val_911_, v_snd_888_);
v_a_894_ = v___x_912_;
goto v___jp_893_;
}
else
{
lean_dec(v_a_910_);
lean_dec_ref(v_self_908_);
v_a_894_ = v_snd_888_;
goto v___jp_893_;
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_self_908_);
lean_del_object(v___x_890_);
lean_dec(v_snd_888_);
v_a_913_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_909_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_909_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_a_903_);
lean_del_object(v___x_890_);
lean_dec(v_snd_888_);
v_a_921_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_905_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_905_);
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
lean_del_object(v___x_890_);
lean_dec(v_snd_888_);
v_a_929_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_902_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_902_);
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
v___jp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_a_894_);
lean_ctor_set(v___x_890_, 0, v___x_892_);
v___x_896_ = v___x_890_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_a_894_);
v___x_896_ = v_reuseFailAlloc_900_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_add(v_i_879_, v___x_897_);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_876_, v_as_877_, v_sz_878_, v___x_898_, v___x_896_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object* v_goal_939_, lean_object* v_as_940_, lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
size_t v_sz_boxed_949_; size_t v_i_boxed_950_; lean_object* v_res_951_; 
v_sz_boxed_949_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_950_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_939_, v_as_940_, v_sz_boxed_949_, v_i_boxed_950_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_as_940_);
lean_dec_ref(v_goal_939_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object* v_goal_952_, lean_object* v_t_953_, lean_object* v_init_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_root_960_; lean_object* v_tail_961_; lean_object* v___x_962_; 
v_root_960_ = lean_ctor_get(v_t_953_, 0);
v_tail_961_ = lean_ctor_get(v_t_953_, 1);
lean_inc_ref(v_init_954_);
v___x_962_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_954_, v_goal_952_, v_root_960_, v_init_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec_ref(v_init_954_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_999_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_999_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_999_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_999_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
if (lean_obj_tag(v_a_963_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v_a_963_, 1);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v_a_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; size_t v_sz_974_; size_t v___x_975_; lean_object* v___x_976_; 
lean_del_object(v___x_965_);
v_a_971_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v_a_963_, 1);
v___x_972_ = lean_box(0);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v_a_971_);
v_sz_974_ = lean_array_size(v_tail_961_);
v___x_975_ = ((size_t)0ULL);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_952_, v_tail_961_, v_sz_974_, v___x_975_, v___x_973_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_990_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_990_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_990_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_990_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_fst_981_; 
v_fst_981_ = lean_ctor_get(v_a_977_, 0);
if (lean_obj_tag(v_fst_981_) == 0)
{
lean_object* v_snd_982_; lean_object* v___x_984_; 
v_snd_982_ = lean_ctor_get(v_a_977_, 1);
lean_inc(v_snd_982_);
lean_dec(v_a_977_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v_snd_982_);
v___x_984_ = v___x_979_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_snd_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; 
lean_inc_ref(v_fst_981_);
lean_dec(v_a_977_);
v_val_986_ = lean_ctor_get(v_fst_981_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v_fst_981_, 1);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v_val_986_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_976_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_976_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
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
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_962_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_962_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object* v_goal_1008_, lean_object* v_t_1009_, lean_object* v_init_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1008_, v_t_1009_, v_init_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec_ref(v_t_1009_);
lean_dec_ref(v_goal_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object* v_a_1017_, lean_object* v_x_1018_){
_start:
{
if (lean_obj_tag(v_x_1018_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_box(0);
return v___x_1019_;
}
else
{
lean_object* v_key_1020_; lean_object* v_value_1021_; lean_object* v_tail_1022_; uint8_t v___x_1023_; 
v_key_1020_ = lean_ctor_get(v_x_1018_, 0);
v_value_1021_ = lean_ctor_get(v_x_1018_, 1);
v_tail_1022_ = lean_ctor_get(v_x_1018_, 2);
v___x_1023_ = lean_expr_eqv(v_key_1020_, v_a_1017_);
if (v___x_1023_ == 0)
{
v_x_1018_ = v_tail_1022_;
goto _start;
}
else
{
lean_object* v___x_1025_; 
lean_inc(v_value_1021_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_value_1021_);
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1026_, v_x_1027_);
lean_dec(v_x_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object* v_m_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_buckets_1031_; lean_object* v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; uint64_t v_fold_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_buckets_1031_ = lean_ctor_get(v_m_1029_, 1);
v___x_1032_ = lean_array_get_size(v_buckets_1031_);
v___x_1033_ = l_Lean_Expr_hash(v_a_1030_);
v___x_1034_ = 32ULL;
v___x_1035_ = lean_uint64_shift_right(v___x_1033_, v___x_1034_);
v_fold_1036_ = lean_uint64_xor(v___x_1033_, v___x_1035_);
v___x_1037_ = 16ULL;
v___x_1038_ = lean_uint64_shift_right(v_fold_1036_, v___x_1037_);
v___x_1039_ = lean_uint64_xor(v_fold_1036_, v___x_1038_);
v___x_1040_ = lean_uint64_to_usize(v___x_1039_);
v___x_1041_ = lean_usize_of_nat(v___x_1032_);
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_sub(v___x_1041_, v___x_1042_);
v___x_1044_ = lean_usize_land(v___x_1040_, v___x_1043_);
v___x_1045_ = lean_array_uget_borrowed(v_buckets_1031_, v___x_1044_);
v___x_1046_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1030_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object* v_m_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1047_, v_a_1048_);
lean_dec_ref(v_a_1048_);
lean_dec_ref(v_m_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object* v_goal_1050_, lean_object* v_as_1051_, size_t v_sz_1052_, size_t v_i_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_a_1061_; uint8_t v___x_1065_; 
v___x_1065_ = lean_usize_dec_lt(v_i_1053_, v_sz_1052_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_b_1054_);
return v___x_1066_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_array_uget_borrowed(v_as_1051_, v_i_1053_);
lean_inc(v_a_1067_);
v___x_1068_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1050_, v_a_1067_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v_self_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v_self_1070_ = lean_ctor_get(v_a_1069_, 0);
lean_inc_ref(v_self_1070_);
lean_dec(v_a_1069_);
v___x_1071_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1070_);
if (lean_obj_tag(v___x_1071_) == 1)
{
lean_object* v_val_1072_; lean_object* v___x_1073_; 
v_val_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1054_, v_val_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_b_1054_, v_self_1070_);
lean_dec_ref(v_self_1070_);
if (lean_obj_tag(v___x_1074_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1076_; 
v_val_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1050_, v_val_1072_, v_val_1075_, v_b_1054_);
v_a_1061_ = v___x_1076_;
goto v___jp_1060_;
}
else
{
lean_dec(v___x_1074_);
lean_dec(v_val_1072_);
v_a_1061_ = v_b_1054_;
goto v___jp_1060_;
}
}
else
{
lean_dec_ref_known(v___x_1073_, 1);
lean_dec(v_val_1072_);
lean_dec_ref(v_self_1070_);
v_a_1061_ = v_b_1054_;
goto v___jp_1060_;
}
}
else
{
lean_dec(v___x_1071_);
lean_dec_ref(v_self_1070_);
v_a_1061_ = v_b_1054_;
goto v___jp_1060_;
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v_b_1054_);
v_a_1077_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1068_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1068_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
v___jp_1060_:
{
size_t v___x_1062_; size_t v___x_1063_; 
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1053_, v___x_1062_);
v_i_1053_ = v___x_1063_;
v_b_1054_ = v_a_1061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object* v_goal_1085_, lean_object* v_as_1086_, lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
size_t v_sz_boxed_1095_; size_t v_i_boxed_1096_; lean_object* v_res_1097_; 
v_sz_boxed_1095_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1096_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1085_, v_as_1086_, v_sz_boxed_1095_, v_i_boxed_1096_, v_b_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_as_1086_);
lean_dec_ref(v_goal_1085_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_unsigned_to_nat(16u);
v___x_1100_ = lean_mk_array(v___x_1099_, v___x_1098_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_model_1103_; 
v___x_1101_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0);
v___x_1102_ = lean_unsigned_to_nat(0u);
v_model_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_1103_, 0, v___x_1102_);
lean_ctor_set(v_model_1103_, 1, v___x_1101_);
return v_model_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object* v_goal_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_toGoalState_1118_; lean_object* v_exprs_1119_; lean_object* v_model_1120_; lean_object* v___x_1121_; 
v_toGoalState_1118_ = lean_ctor_get(v_goal_1112_, 0);
v_exprs_1119_ = lean_ctor_get(v_toGoalState_1118_, 2);
v_model_1120_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1);
v___x_1121_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1112_, v_exprs_1119_, v_model_1120_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; size_t v_sz_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = l_Lean_PersistentArray_toArray___redArg(v_exprs_1119_);
v___x_1124_ = l_Array_reverse___redArg(v___x_1123_);
v_sz_1125_ = lean_array_size(v___x_1124_);
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1112_, v___x_1124_, v_sz_1125_, v___x_1126_, v_a_1122_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec_ref(v___x_1124_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2));
v___x_1130_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1112_, v___x_1129_, v_a_1128_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6));
v___x_1133_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_1132_, v_a_1131_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v___x_1133_, 0);
lean_dec(v_unused_1141_);
v___x_1135_ = v___x_1133_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v___x_1133_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_a_1131_);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1131_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_a_1131_);
v_a_1142_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1133_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1133_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
return v___x_1130_;
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1127_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1127_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1121_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1121_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object* v_goal_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec_ref(v_goal_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object* v_00_u03b2_1173_, lean_object* v_m_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1174_, v_a_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object* v_00_u03b2_1177_, lean_object* v_m_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(v_00_u03b2_1177_, v_m_1178_, v_a_1179_);
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_m_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object* v_00_u03b2_1181_, lean_object* v_a_1182_, lean_object* v_x_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1182_, v_x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1185_, lean_object* v_a_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(v_00_u03b2_1185_, v_a_1186_, v_x_1187_);
lean_dec(v_x_1187_);
lean_dec_ref(v_a_1186_);
return v_res_1188_;
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

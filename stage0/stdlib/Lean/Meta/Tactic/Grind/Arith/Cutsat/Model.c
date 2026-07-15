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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(251, 249, 151, 171, 150, 156, 160, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0(void){
_start:
{
uint8_t v___x_1_; uint64_t v___x_2_; 
v___x_1_ = 1;
v___x_2_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(lean_object* v_n_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_self_9_; lean_object* v___x_10_; uint8_t v_foApprox_11_; uint8_t v_ctxApprox_12_; uint8_t v_quasiPatternApprox_13_; uint8_t v_constApprox_14_; uint8_t v_isDefEqStuckEx_15_; uint8_t v_unificationHints_16_; uint8_t v_proofIrrelevance_17_; uint8_t v_assignSyntheticOpaque_18_; uint8_t v_offsetCnstrs_19_; uint8_t v_etaStruct_20_; uint8_t v_univApprox_21_; uint8_t v_iota_22_; uint8_t v_beta_23_; uint8_t v_proj_24_; uint8_t v_zeta_25_; uint8_t v_zetaDelta_26_; uint8_t v_zetaUnused_27_; uint8_t v_zetaHave_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_70_; 
v_self_9_ = lean_ctor_get(v_n_3_, 0);
lean_inc_ref(v_self_9_);
lean_dec_ref(v_n_3_);
v___x_10_ = l_Lean_Meta_Context_config(v_a_4_);
v_foApprox_11_ = lean_ctor_get_uint8(v___x_10_, 0);
v_ctxApprox_12_ = lean_ctor_get_uint8(v___x_10_, 1);
v_quasiPatternApprox_13_ = lean_ctor_get_uint8(v___x_10_, 2);
v_constApprox_14_ = lean_ctor_get_uint8(v___x_10_, 3);
v_isDefEqStuckEx_15_ = lean_ctor_get_uint8(v___x_10_, 4);
v_unificationHints_16_ = lean_ctor_get_uint8(v___x_10_, 5);
v_proofIrrelevance_17_ = lean_ctor_get_uint8(v___x_10_, 6);
v_assignSyntheticOpaque_18_ = lean_ctor_get_uint8(v___x_10_, 7);
v_offsetCnstrs_19_ = lean_ctor_get_uint8(v___x_10_, 8);
v_etaStruct_20_ = lean_ctor_get_uint8(v___x_10_, 10);
v_univApprox_21_ = lean_ctor_get_uint8(v___x_10_, 11);
v_iota_22_ = lean_ctor_get_uint8(v___x_10_, 12);
v_beta_23_ = lean_ctor_get_uint8(v___x_10_, 13);
v_proj_24_ = lean_ctor_get_uint8(v___x_10_, 14);
v_zeta_25_ = lean_ctor_get_uint8(v___x_10_, 15);
v_zetaDelta_26_ = lean_ctor_get_uint8(v___x_10_, 16);
v_zetaUnused_27_ = lean_ctor_get_uint8(v___x_10_, 17);
v_zetaHave_28_ = lean_ctor_get_uint8(v___x_10_, 18);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_70_ == 0)
{
v___x_30_ = v___x_10_;
v_isShared_31_ = v_isSharedCheck_70_;
goto v_resetjp_29_;
}
else
{
lean_dec(v___x_10_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_70_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v_trackZetaDelta_32_; lean_object* v_zetaDeltaSet_33_; lean_object* v_lctx_34_; lean_object* v_localInstances_35_; lean_object* v_defEqCtx_x3f_36_; lean_object* v_synthPendingDepth_37_; lean_object* v_canUnfold_x3f_38_; uint8_t v_univApprox_39_; uint8_t v_inTypeClassResolution_40_; uint8_t v_cacheInferType_41_; uint8_t v___x_42_; lean_object* v_config_44_; 
v_trackZetaDelta_32_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7);
v_zetaDeltaSet_33_ = lean_ctor_get(v_a_4_, 1);
v_lctx_34_ = lean_ctor_get(v_a_4_, 2);
v_localInstances_35_ = lean_ctor_get(v_a_4_, 3);
v_defEqCtx_x3f_36_ = lean_ctor_get(v_a_4_, 4);
v_synthPendingDepth_37_ = lean_ctor_get(v_a_4_, 5);
v_canUnfold_x3f_38_ = lean_ctor_get(v_a_4_, 6);
v_univApprox_39_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_40_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7 + 2);
v_cacheInferType_41_ = lean_ctor_get_uint8(v_a_4_, sizeof(void*)*7 + 3);
v___x_42_ = 1;
if (v_isShared_31_ == 0)
{
v_config_44_ = v___x_30_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 0, v_foApprox_11_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 1, v_ctxApprox_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 2, v_quasiPatternApprox_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 3, v_constApprox_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 4, v_isDefEqStuckEx_15_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 5, v_unificationHints_16_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 6, v_proofIrrelevance_17_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 7, v_assignSyntheticOpaque_18_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 8, v_offsetCnstrs_19_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 10, v_etaStruct_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 11, v_univApprox_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 12, v_iota_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 13, v_beta_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 14, v_proj_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 15, v_zeta_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 16, v_zetaDelta_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 17, v_zetaUnused_27_);
lean_ctor_set_uint8(v_reuseFailAlloc_69_, 18, v_zetaHave_28_);
v_config_44_ = v_reuseFailAlloc_69_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; uint64_t v___x_48_; uint64_t v___x_49_; uint64_t v_key_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_ctor_set_uint8(v_config_44_, 9, v___x_42_);
v___x_45_ = l_Lean_Meta_Context_configKey(v_a_4_);
v___x_46_ = 3ULL;
v___x_47_ = lean_uint64_shift_right(v___x_45_, v___x_46_);
v___x_48_ = lean_uint64_shift_left(v___x_47_, v___x_46_);
v___x_49_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0);
v_key_50_ = lean_uint64_lor(v___x_48_, v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_51_, 0, v_config_44_);
lean_ctor_set_uint64(v___x_51_, sizeof(void*)*1, v_key_50_);
lean_inc(v_canUnfold_x3f_38_);
lean_inc(v_synthPendingDepth_37_);
lean_inc(v_defEqCtx_x3f_36_);
lean_inc_ref(v_localInstances_35_);
lean_inc_ref(v_lctx_34_);
lean_inc(v_zetaDeltaSet_33_);
v___x_52_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v_zetaDeltaSet_33_);
lean_ctor_set(v___x_52_, 2, v_lctx_34_);
lean_ctor_set(v___x_52_, 3, v_localInstances_35_);
lean_ctor_set(v___x_52_, 4, v_defEqCtx_x3f_36_);
lean_ctor_set(v___x_52_, 5, v_synthPendingDepth_37_);
lean_ctor_set(v___x_52_, 6, v_canUnfold_x3f_38_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*7, v_trackZetaDelta_32_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*7 + 1, v_univApprox_39_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*7 + 2, v_inTypeClassResolution_40_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*7 + 3, v_cacheInferType_41_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc_ref(v___x_52_);
v___x_53_ = lean_infer_type(v_self_9_, v___x_52_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_n(v_a_54_, 2);
lean_dec_ref_known(v___x_53_, 1);
v___x_55_ = l_Lean_Int_mkType;
v___x_56_ = l_Lean_Meta_isExprDefEq(v_a_54_, v___x_55_, v___x_52_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; uint8_t v___x_58_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
v___x_58_ = lean_unbox(v_a_57_);
lean_dec(v_a_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec_ref_known(v___x_56_, 1);
v___x_59_ = l_Lean_Nat_mkType;
v___x_60_ = l_Lean_Meta_isExprDefEq(v_a_54_, v___x_59_, v___x_52_, v_a_5_, v_a_6_, v_a_7_);
lean_dec_ref_known(v___x_52_, 7);
return v___x_60_;
}
else
{
lean_dec(v_a_54_);
lean_dec_ref_known(v___x_52_, 7);
return v___x_56_;
}
}
else
{
lean_dec(v_a_54_);
lean_dec_ref_known(v___x_52_, 7);
return v___x_56_;
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec_ref_known(v___x_52_, 7);
v_a_61_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_53_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_53_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(lean_object* v_n_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_n_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_77_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = l_instInhabitedError;
v___x_79_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_79_, 0, lean_box(0));
lean_closure_set(v___x_79_, 1, lean_box(0));
lean_closure_set(v___x_79_, 2, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(lean_object* v_msg_80_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_484__overap_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0);
v___x_484__overap_83_ = lean_panic_fn_borrowed(v___x_82_, v_msg_80_);
v___x_84_ = lean_apply_1(v___x_484__overap_83_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(lean_object* v_msg_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v_msg_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_88_, lean_object* v_vals_89_, lean_object* v_i_90_, lean_object* v_k_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = lean_array_get_size(v_keys_88_);
v___x_93_ = lean_nat_dec_lt(v_i_90_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec(v_i_90_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v_k_x27_95_; size_t v___x_96_; size_t v___x_97_; uint8_t v___x_98_; 
v_k_x27_95_ = lean_array_fget_borrowed(v_keys_88_, v_i_90_);
v___x_96_ = lean_ptr_addr(v_k_91_);
v___x_97_ = lean_ptr_addr(v_k_x27_95_);
v___x_98_ = lean_usize_dec_eq(v___x_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_i_90_, v___x_99_);
lean_dec(v_i_90_);
v_i_90_ = v___x_100_;
goto _start;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_array_fget_borrowed(v_vals_89_, v_i_90_);
lean_dec(v_i_90_);
lean_inc(v___x_102_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_104_, lean_object* v_vals_105_, lean_object* v_i_106_, lean_object* v_k_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_104_, v_vals_105_, v_i_106_, v_k_107_);
lean_dec_ref(v_k_107_);
lean_dec_ref(v_vals_105_);
lean_dec_ref(v_keys_104_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(lean_object* v_x_109_, size_t v_x_110_, lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_object* v_es_112_; lean_object* v___x_113_; size_t v___x_114_; size_t v___x_115_; lean_object* v_j_116_; lean_object* v___x_117_; 
v_es_112_ = lean_ctor_get(v_x_109_, 0);
v___x_113_ = lean_box(2);
v___x_114_ = ((size_t)31ULL);
v___x_115_ = lean_usize_land(v_x_110_, v___x_114_);
v_j_116_ = lean_usize_to_nat(v___x_115_);
v___x_117_ = lean_array_get_borrowed(v___x_113_, v_es_112_, v_j_116_);
lean_dec(v_j_116_);
switch(lean_obj_tag(v___x_117_))
{
case 0:
{
lean_object* v_key_118_; lean_object* v_val_119_; size_t v___x_120_; size_t v___x_121_; uint8_t v___x_122_; 
v_key_118_ = lean_ctor_get(v___x_117_, 0);
v_val_119_ = lean_ctor_get(v___x_117_, 1);
v___x_120_ = lean_ptr_addr(v_x_111_);
v___x_121_ = lean_ptr_addr(v_key_118_);
v___x_122_ = lean_usize_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
lean_inc(v_val_119_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v_val_119_);
return v___x_124_;
}
}
case 1:
{
lean_object* v_node_125_; size_t v___x_126_; size_t v___x_127_; 
v_node_125_ = lean_ctor_get(v___x_117_, 0);
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_usize_shift_right(v_x_110_, v___x_126_);
v_x_109_ = v_node_125_;
v_x_110_ = v___x_127_;
goto _start;
}
default: 
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
}
else
{
lean_object* v_ks_130_; lean_object* v_vs_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_ks_130_ = lean_ctor_get(v_x_109_, 0);
v_vs_131_ = lean_ctor_get(v_x_109_, 1);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_ks_130_, v_vs_131_, v___x_132_, v_x_111_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
size_t v_x_667__boxed_137_; lean_object* v_res_138_; 
v_x_667__boxed_137_ = lean_unbox_usize(v_x_135_);
lean_dec(v_x_135_);
v_res_138_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_134_, v_x_667__boxed_137_, v_x_136_);
lean_dec_ref(v_x_136_);
lean_dec_ref(v_x_134_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; 
v___x_141_ = lean_ptr_addr(v_x_140_);
v___x_142_ = ((size_t)3ULL);
v___x_143_ = lean_usize_shift_right(v___x_141_, v___x_142_);
v___x_144_ = lean_usize_to_uint64(v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_139_, v___x_145_, v_x_140_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_147_, v_x_148_);
lean_dec_ref(v_x_148_);
lean_dec_ref(v_x_147_);
return v_res_149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2));
v___x_154_ = lean_unsigned_to_nat(2u);
v___x_155_ = lean_unsigned_to_nat(21u);
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1));
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0));
v___x_158_ = l_mkPanicMessageWithDecl(v___x_157_, v___x_156_, v___x_155_, v___x_154_, v___x_153_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(lean_object* v_goal_159_, lean_object* v_node_160_){
_start:
{
lean_object* v_self_162_; lean_object* v_root_163_; size_t v___x_164_; size_t v___x_165_; uint8_t v___x_166_; 
v_self_162_ = lean_ctor_get(v_node_160_, 0);
v_root_163_ = lean_ctor_get(v_node_160_, 2);
v___x_164_ = lean_ptr_addr(v_self_162_);
v___x_165_ = lean_ptr_addr(v_root_163_);
v___x_166_ = lean_usize_dec_eq(v___x_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3);
v___x_168_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v___x_167_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_170_ = l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(v___x_169_, v_node_160_);
if (lean_obj_tag(v___x_170_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_172_; 
v_val_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v___x_170_, 1);
v___x_172_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_169_, v_goal_159_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_203_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_203_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_203_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_203_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_varMap_177_; lean_object* v_assignment_178_; lean_object* v___x_179_; 
v_varMap_177_ = lean_ctor_get(v_a_173_, 1);
lean_inc_ref(v_varMap_177_);
v_assignment_178_ = lean_ctor_get(v_a_173_, 13);
lean_inc_ref(v_assignment_178_);
lean_dec(v_a_173_);
v___x_179_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_varMap_177_, v_val_171_);
lean_dec(v_val_171_);
lean_dec_ref(v_varMap_177_);
if (lean_obj_tag(v___x_179_) == 1)
{
lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_198_; 
v_val_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_198_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_198_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_198_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_size_184_; uint8_t v___x_185_; 
v_size_184_ = lean_ctor_get(v_assignment_178_, 2);
v___x_185_ = lean_nat_dec_lt(v_val_180_, v_size_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_188_; 
lean_del_object(v___x_182_);
lean_dec(v_val_180_);
lean_dec_ref(v_assignment_178_);
v___x_186_ = lean_box(0);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_186_);
v___x_188_ = v___x_175_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = l_instInhabitedRat;
v___x_191_ = l_Lean_PersistentArray_get_x21___redArg(v___x_190_, v_assignment_178_, v_val_180_);
lean_dec(v_val_180_);
lean_dec_ref(v_assignment_178_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_191_);
v___x_193_ = v___x_182_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_193_);
v___x_195_ = v___x_175_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_dec(v___x_179_);
lean_dec_ref(v_assignment_178_);
v___x_199_ = lean_box(0);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_199_);
v___x_201_ = v___x_175_;
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
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_val_171_);
v_a_204_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_172_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_172_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v___x_170_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(lean_object* v_goal_214_, lean_object* v_node_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_214_, v_node_215_);
lean_dec_ref(v_node_215_);
lean_dec_ref(v_goal_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(lean_object* v_00_u03b2_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_219_, v_x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(lean_object* v_00_u03b2_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(v_00_u03b2_222_, v_x_223_, v_x_224_);
lean_dec_ref(v_x_224_);
lean_dec_ref(v_x_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(lean_object* v_00_u03b2_226_, lean_object* v_x_227_, size_t v_x_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_227_, v_x_228_, v_x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
size_t v_x_868__boxed_235_; lean_object* v_res_236_; 
v_x_868__boxed_235_ = lean_unbox_usize(v_x_233_);
lean_dec(v_x_233_);
v_res_236_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(v_00_u03b2_231_, v_x_232_, v_x_868__boxed_235_, v_x_234_);
lean_dec_ref(v_x_234_);
lean_dec_ref(v_x_232_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_237_, lean_object* v_keys_238_, lean_object* v_vals_239_, lean_object* v_heq_240_, lean_object* v_i_241_, lean_object* v_k_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_238_, v_vals_239_, v_i_241_, v_k_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_244_, lean_object* v_keys_245_, lean_object* v_vals_246_, lean_object* v_heq_247_, lean_object* v_i_248_, lean_object* v_k_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(v_00_u03b2_244_, v_keys_245_, v_vals_246_, v_heq_247_, v_i_248_, v_k_249_);
lean_dec_ref(v_k_249_);
lean_dec_ref(v_vals_246_);
lean_dec_ref(v_keys_245_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(lean_object* v_e_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = l_Lean_Expr_cleanupAnnotations(v_e_268_);
v___x_270_ = l_Lean_Expr_isApp(v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec_ref(v___x_269_);
v___x_271_ = lean_box(0);
return v___x_271_;
}
else
{
lean_object* v_arg_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_arg_272_ = lean_ctor_get(v___x_269_, 1);
lean_inc_ref(v_arg_272_);
v___x_273_ = l_Lean_Expr_appFnCleanup___redArg(v___x_269_);
v___x_274_ = l_Lean_Expr_isApp(v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec_ref(v___x_273_);
lean_dec_ref(v_arg_272_);
v___x_275_ = lean_box(0);
return v___x_275_;
}
else
{
lean_object* v_arg_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_arg_276_ = lean_ctor_get(v___x_273_, 1);
lean_inc_ref(v_arg_276_);
v___x_277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_273_);
v___x_278_ = l_Lean_Expr_isApp(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec_ref(v___x_277_);
lean_dec_ref(v_arg_276_);
lean_dec_ref(v_arg_272_);
v___x_279_ = lean_box(0);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_277_);
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2));
v___x_282_ = l_Lean_Expr_isConstOf(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
uint8_t v___x_283_; 
lean_dec_ref(v_arg_276_);
v___x_283_ = l_Lean_Expr_isApp(v___x_280_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec_ref(v___x_280_);
lean_dec_ref(v_arg_272_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_280_);
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7));
v___x_287_ = l_Lean_Expr_isConstOf(v___x_285_, v___x_286_);
lean_dec_ref(v___x_285_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec_ref(v_arg_272_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_arg_272_);
return v___x_289_;
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
lean_dec_ref(v___x_280_);
v___x_290_ = l_Lean_Expr_cleanupAnnotations(v_arg_276_);
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9));
v___x_292_ = l_Lean_Expr_isConstOf(v___x_290_, v___x_291_);
lean_dec_ref(v___x_290_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec_ref(v_arg_272_);
v___x_293_ = lean_box(0);
return v___x_293_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_arg_272_);
return v___x_294_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Rat_ofInt(v_a_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object* v_goal_297_, lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Grind_Goal_getRoot(v_goal_297_, v_e_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_306_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_304_, 1);
v___x_306_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_297_, v_a_305_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v___x_308_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_297_, v_a_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_374_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_374_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_374_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_374_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
if (lean_obj_tag(v_a_309_) == 1)
{
lean_object* v___x_314_; 
lean_dec(v_a_307_);
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
lean_object* v_self_316_; lean_object* v___x_317_; 
lean_del_object(v___x_311_);
lean_dec(v_a_309_);
v_self_316_ = lean_ctor_get(v_a_307_, 0);
lean_inc_ref_n(v_self_316_, 2);
lean_dec(v_a_307_);
v___x_317_ = l_Lean_Meta_getIntValue_x3f(v_self_316_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_365_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_365_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_365_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_365_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
if (lean_obj_tag(v_a_318_) == 1)
{
lean_object* v_val_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v_self_316_);
v_val_322_ = lean_ctor_get(v_a_318_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_333_ == 0)
{
v___x_324_ = v_a_318_;
v_isShared_325_ = v_isSharedCheck_333_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_val_322_);
lean_dec(v_a_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_333_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = l_Rat_ofInt(v_val_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_332_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_328_);
v___x_330_ = v___x_320_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v___x_334_; 
lean_del_object(v___x_320_);
lean_dec(v_a_318_);
v___x_334_ = l_Lean_Meta_getNatValue_x3f(v_self_316_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec_ref(v_self_316_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_356_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_356_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_356_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_356_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
if (lean_obj_tag(v_a_335_) == 1)
{
lean_object* v_val_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_351_; 
v_val_339_ = lean_ctor_get(v_a_335_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_335_);
if (v_isSharedCheck_351_ == 0)
{
v___x_341_ = v_a_335_;
v_isShared_342_ = v_isSharedCheck_351_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_val_339_);
lean_dec(v_a_335_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_351_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_343_ = lean_nat_to_int(v_val_339_);
v___x_344_ = l_Rat_ofInt(v___x_343_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_344_);
v___x_346_ = v___x_341_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_346_);
v___x_348_ = v___x_337_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
lean_dec(v_a_335_);
v___x_352_ = lean_box(0);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_352_);
v___x_354_ = v___x_337_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
v_a_357_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_334_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_334_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_self_316_);
v_a_366_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_317_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_317_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
lean_dec(v_a_307_);
v_a_375_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v___x_308_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_308_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v_ref_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v_ref_379_ = lean_ctor_get(v_a_301_, 5);
v___x_380_ = lean_io_error_to_string(v_a_375_);
v___x_381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = l_Lean_MessageData_ofFormat(v___x_381_);
lean_inc(v_ref_379_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_ref_379_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_383_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_a_388_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_306_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_306_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_396_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_304_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_304_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(lean_object* v_goal_404_, lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_404_, v_e_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec_ref(v_goal_404_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(lean_object* v_goal_412_, lean_object* v_as_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_b_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_b_416_);
return v___x_423_;
}
else
{
lean_object* v_snd_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_473_; 
v_snd_424_ = lean_ctor_get(v_b_416_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_b_416_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v_b_416_, 0);
lean_dec(v_unused_474_);
v___x_426_ = v_b_416_;
v_isShared_427_ = v_isSharedCheck_473_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_424_);
lean_dec(v_b_416_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_473_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_array_uget_borrowed(v_as_413_, v_i_415_);
lean_inc(v_a_428_);
v___x_429_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_412_, v_a_428_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; lean_object* v_a_433_; uint8_t v___x_440_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = lean_box(0);
v___x_440_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_430_);
if (v___x_440_ == 0)
{
lean_dec(v_a_430_);
v_a_433_ = v_snd_424_;
goto v___jp_432_;
}
else
{
lean_object* v___x_441_; 
lean_inc(v_a_430_);
v___x_441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_430_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; uint8_t v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = lean_unbox(v_a_442_);
lean_dec(v_a_442_);
if (v___x_443_ == 0)
{
lean_dec(v_a_430_);
v_a_433_ = v_snd_424_;
goto v___jp_432_;
}
else
{
lean_object* v_self_444_; lean_object* v___x_445_; 
v_self_444_ = lean_ctor_get(v_a_430_, 0);
lean_inc_ref_n(v_self_444_, 2);
lean_dec(v_a_430_);
v___x_445_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_412_, v_self_444_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
if (lean_obj_tag(v_a_446_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_448_; 
v_val_447_ = lean_ctor_get(v_a_446_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_a_446_, 1);
v___x_448_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_412_, v_self_444_, v_val_447_, v_snd_424_);
v_a_433_ = v___x_448_;
goto v___jp_432_;
}
else
{
lean_dec(v_a_446_);
lean_dec_ref(v_self_444_);
v_a_433_ = v_snd_424_;
goto v___jp_432_;
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec_ref(v_self_444_);
lean_del_object(v___x_426_);
lean_dec(v_snd_424_);
v_a_449_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_445_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_445_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_430_);
lean_del_object(v___x_426_);
lean_dec(v_snd_424_);
v_a_457_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_441_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_441_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
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
v___jp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_a_433_);
lean_ctor_set(v___x_426_, 0, v___x_431_);
v___x_435_ = v___x_426_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_a_433_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
size_t v___x_436_; size_t v___x_437_; 
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_415_, v___x_436_);
v_i_415_ = v___x_437_;
v_b_416_ = v___x_435_;
goto _start;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_del_object(v___x_426_);
lean_dec(v_snd_424_);
v_a_465_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_429_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_429_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_goal_475_, lean_object* v_as_476_, lean_object* v_sz_477_, lean_object* v_i_478_, lean_object* v_b_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_sz_boxed_485_ = lean_unbox_usize(v_sz_477_);
lean_dec(v_sz_477_);
v_i_boxed_486_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_475_, v_as_476_, v_sz_boxed_485_, v_i_boxed_486_, v_b_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec_ref(v_as_476_);
lean_dec_ref(v_goal_475_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(lean_object* v_goal_488_, lean_object* v_as_489_, size_t v_sz_490_, size_t v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_usize_dec_lt(v_i_491_, v_sz_490_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_b_492_);
return v___x_499_;
}
else
{
lean_object* v_snd_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_549_; 
v_snd_500_ = lean_ctor_get(v_b_492_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_b_492_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_b_492_, 0);
lean_dec(v_unused_550_);
v___x_502_ = v_b_492_;
v_isShared_503_ = v_isSharedCheck_549_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_snd_500_);
lean_dec(v_b_492_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_549_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_array_uget_borrowed(v_as_489_, v_i_491_);
lean_inc(v_a_504_);
v___x_505_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_488_, v_a_504_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v_a_509_; uint8_t v___x_516_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_box(0);
v___x_516_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_506_);
if (v___x_516_ == 0)
{
lean_dec(v_a_506_);
v_a_509_ = v_snd_500_;
goto v___jp_508_;
}
else
{
lean_object* v___x_517_; 
lean_inc(v_a_506_);
v___x_517_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_506_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; uint8_t v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_519_ == 0)
{
lean_dec(v_a_506_);
v_a_509_ = v_snd_500_;
goto v___jp_508_;
}
else
{
lean_object* v_self_520_; lean_object* v___x_521_; 
v_self_520_ = lean_ctor_get(v_a_506_, 0);
lean_inc_ref_n(v_self_520_, 2);
lean_dec(v_a_506_);
v___x_521_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_488_, v_self_520_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
if (lean_obj_tag(v_a_522_) == 1)
{
lean_object* v_val_523_; lean_object* v___x_524_; 
v_val_523_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v_a_522_, 1);
v___x_524_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_488_, v_self_520_, v_val_523_, v_snd_500_);
v_a_509_ = v___x_524_;
goto v___jp_508_;
}
else
{
lean_dec(v_a_522_);
lean_dec_ref(v_self_520_);
v_a_509_ = v_snd_500_;
goto v___jp_508_;
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_self_520_);
lean_del_object(v___x_502_);
lean_dec(v_snd_500_);
v_a_525_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_521_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_521_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_506_);
lean_del_object(v___x_502_);
lean_dec(v_snd_500_);
v_a_533_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_517_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_517_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
v___jp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v_a_509_);
lean_ctor_set(v___x_502_, 0, v___x_507_);
v___x_511_ = v___x_502_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_a_509_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_491_, v___x_512_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_488_, v_as_489_, v_sz_490_, v___x_513_, v___x_511_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_514_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_del_object(v___x_502_);
lean_dec(v_snd_500_);
v_a_541_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_505_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_505_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(lean_object* v_goal_551_, lean_object* v_as_552_, lean_object* v_sz_553_, lean_object* v_i_554_, lean_object* v_b_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_553_);
lean_dec(v_sz_553_);
v_i_boxed_562_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_551_, v_as_552_, v_sz_boxed_561_, v_i_boxed_562_, v_b_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v_as_552_);
lean_dec_ref(v_goal_551_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(lean_object* v_init_564_, lean_object* v_goal_565_, lean_object* v_n_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
if (lean_obj_tag(v_n_566_) == 0)
{
lean_object* v_cs_573_; lean_object* v___x_574_; lean_object* v___x_575_; size_t v_sz_576_; size_t v___x_577_; lean_object* v___x_578_; 
v_cs_573_ = lean_ctor_get(v_n_566_, 0);
v___x_574_ = lean_box(0);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_b_567_);
v_sz_576_ = lean_array_size(v_cs_573_);
v___x_577_ = ((size_t)0ULL);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_564_, v_goal_565_, v_cs_573_, v_sz_576_, v___x_577_, v___x_575_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_593_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_593_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_593_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_593_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_fst_583_; 
v_fst_583_ = lean_ctor_get(v_a_579_, 0);
if (lean_obj_tag(v_fst_583_) == 0)
{
lean_object* v_snd_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v_snd_584_ = lean_ctor_get(v_a_579_, 1);
lean_inc(v_snd_584_);
lean_dec(v_a_579_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_snd_584_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_585_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v_val_589_; lean_object* v___x_591_; 
lean_inc_ref(v_fst_583_);
lean_dec(v_a_579_);
v_val_589_ = lean_ctor_get(v_fst_583_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_fst_583_, 1);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_val_589_);
v___x_591_ = v___x_581_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_val_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_578_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_578_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_vs_602_; lean_object* v___x_603_; lean_object* v___x_604_; size_t v_sz_605_; size_t v___x_606_; lean_object* v___x_607_; 
v_vs_602_ = lean_ctor_get(v_n_566_, 0);
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v_b_567_);
v_sz_605_ = lean_array_size(v_vs_602_);
v___x_606_ = ((size_t)0ULL);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_565_, v_vs_602_, v_sz_605_, v___x_606_, v___x_604_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_622_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_622_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_fst_612_; 
v_fst_612_ = lean_ctor_get(v_a_608_, 0);
if (lean_obj_tag(v_fst_612_) == 0)
{
lean_object* v_snd_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v_snd_613_ = lean_ctor_get(v_a_608_, 1);
lean_inc(v_snd_613_);
lean_dec(v_a_608_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v_snd_613_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_614_);
v___x_616_ = v___x_610_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v_val_618_; lean_object* v___x_620_; 
lean_inc_ref(v_fst_612_);
lean_dec(v_a_608_);
v_val_618_ = lean_ctor_get(v_fst_612_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v_fst_612_, 1);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_val_618_);
v___x_620_ = v___x_610_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_val_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_607_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_607_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(lean_object* v_init_631_, lean_object* v_goal_632_, lean_object* v_as_633_, size_t v_sz_634_, size_t v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_usize_dec_lt(v_i_635_, v_sz_634_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_b_636_);
return v___x_643_;
}
else
{
lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_678_; 
v_snd_644_ = lean_ctor_get(v_b_636_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_b_636_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v_b_636_, 0);
lean_dec(v_unused_679_);
v___x_646_ = v_b_636_;
v_isShared_647_ = v_isSharedCheck_678_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_dec(v_b_636_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_678_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_array_uget_borrowed(v_as_633_, v_i_635_);
lean_inc(v_snd_644_);
v___x_649_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_631_, v_goal_632_, v_a_648_, v_snd_644_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_669_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_669_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_669_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_669_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
if (lean_obj_tag(v_a_650_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v_a_650_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_654_);
v___x_656_ = v___x_646_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_snd_644_);
v___x_656_ = v_reuseFailAlloc_660_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_658_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_656_);
v___x_658_ = v___x_652_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_del_object(v___x_652_);
lean_dec(v_snd_644_);
v_a_661_ = lean_ctor_get(v_a_650_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v_a_650_, 1);
v___x_662_ = lean_box(0);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v_a_661_);
lean_ctor_set(v___x_646_, 0, v___x_662_);
v___x_664_ = v___x_646_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_a_661_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
size_t v___x_665_; size_t v___x_666_; 
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_635_, v___x_665_);
v_i_635_ = v___x_666_;
v_b_636_ = v___x_664_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_del_object(v___x_646_);
lean_dec(v_snd_644_);
v_a_670_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_649_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_649_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(lean_object* v_init_680_, lean_object* v_goal_681_, lean_object* v_as_682_, lean_object* v_sz_683_, lean_object* v_i_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
size_t v_sz_boxed_691_; size_t v_i_boxed_692_; lean_object* v_res_693_; 
v_sz_boxed_691_ = lean_unbox_usize(v_sz_683_);
lean_dec(v_sz_683_);
v_i_boxed_692_ = lean_unbox_usize(v_i_684_);
lean_dec(v_i_684_);
v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_680_, v_goal_681_, v_as_682_, v_sz_boxed_691_, v_i_boxed_692_, v_b_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_as_682_);
lean_dec_ref(v_goal_681_);
lean_dec_ref(v_init_680_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(lean_object* v_init_694_, lean_object* v_goal_695_, lean_object* v_n_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_694_, v_goal_695_, v_n_696_, v_b_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_n_696_);
lean_dec_ref(v_goal_695_);
lean_dec_ref(v_init_694_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(lean_object* v_goal_704_, lean_object* v_as_705_, size_t v_sz_706_, size_t v_i_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = lean_usize_dec_lt(v_i_707_, v_sz_706_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_b_708_);
return v___x_715_;
}
else
{
lean_object* v_snd_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_765_; 
v_snd_716_ = lean_ctor_get(v_b_708_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_b_708_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_b_708_, 0);
lean_dec(v_unused_766_);
v___x_718_ = v_b_708_;
v_isShared_719_ = v_isSharedCheck_765_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_snd_716_);
lean_dec(v_b_708_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_765_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_a_720_; lean_object* v___x_721_; 
v_a_720_ = lean_array_uget_borrowed(v_as_705_, v_i_707_);
lean_inc(v_a_720_);
v___x_721_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_704_, v_a_720_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v_a_725_; uint8_t v___x_732_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_box(0);
v___x_732_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_722_);
if (v___x_732_ == 0)
{
lean_dec(v_a_722_);
v_a_725_ = v_snd_716_;
goto v___jp_724_;
}
else
{
lean_object* v___x_733_; 
lean_inc(v_a_722_);
v___x_733_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_722_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; uint8_t v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
if (v___x_735_ == 0)
{
lean_dec(v_a_722_);
v_a_725_ = v_snd_716_;
goto v___jp_724_;
}
else
{
lean_object* v_self_736_; lean_object* v___x_737_; 
v_self_736_ = lean_ctor_get(v_a_722_, 0);
lean_inc_ref_n(v_self_736_, 2);
lean_dec(v_a_722_);
v___x_737_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_704_, v_self_736_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
if (lean_obj_tag(v_a_738_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_740_; 
v_val_739_ = lean_ctor_get(v_a_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_a_738_, 1);
v___x_740_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_704_, v_self_736_, v_val_739_, v_snd_716_);
v_a_725_ = v___x_740_;
goto v___jp_724_;
}
else
{
lean_dec(v_a_738_);
lean_dec_ref(v_self_736_);
v_a_725_ = v_snd_716_;
goto v___jp_724_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v_self_736_);
lean_del_object(v___x_718_);
lean_dec(v_snd_716_);
v_a_741_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_737_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_737_);
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
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_722_);
lean_del_object(v___x_718_);
lean_dec(v_snd_716_);
v_a_749_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_733_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_733_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
v___jp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_a_725_);
lean_ctor_set(v___x_718_, 0, v___x_723_);
v___x_727_ = v___x_718_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_725_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
size_t v___x_728_; size_t v___x_729_; 
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_707_, v___x_728_);
v_i_707_ = v___x_729_;
v_b_708_ = v___x_727_;
goto _start;
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_del_object(v___x_718_);
lean_dec(v_snd_716_);
v_a_757_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_721_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_721_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(lean_object* v_goal_767_, lean_object* v_as_768_, lean_object* v_sz_769_, lean_object* v_i_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
size_t v_sz_boxed_777_; size_t v_i_boxed_778_; lean_object* v_res_779_; 
v_sz_boxed_777_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_778_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_767_, v_as_768_, v_sz_boxed_777_, v_i_boxed_778_, v_b_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_as_768_);
lean_dec_ref(v_goal_767_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(lean_object* v_goal_780_, lean_object* v_as_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_b_784_);
return v___x_791_;
}
else
{
lean_object* v_snd_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_841_; 
v_snd_792_ = lean_ctor_get(v_b_784_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_b_784_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v_b_784_, 0);
lean_dec(v_unused_842_);
v___x_794_ = v_b_784_;
v_isShared_795_ = v_isSharedCheck_841_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snd_792_);
lean_dec(v_b_784_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_841_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_array_uget_borrowed(v_as_781_, v_i_783_);
lean_inc(v_a_796_);
v___x_797_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_780_, v_a_796_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v_a_801_; uint8_t v___x_808_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = lean_box(0);
v___x_808_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_798_);
if (v___x_808_ == 0)
{
lean_dec(v_a_798_);
v_a_801_ = v_snd_792_;
goto v___jp_800_;
}
else
{
lean_object* v___x_809_; 
lean_inc(v_a_798_);
v___x_809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_798_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; uint8_t v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
if (v___x_811_ == 0)
{
lean_dec(v_a_798_);
v_a_801_ = v_snd_792_;
goto v___jp_800_;
}
else
{
lean_object* v_self_812_; lean_object* v___x_813_; 
v_self_812_ = lean_ctor_get(v_a_798_, 0);
lean_inc_ref_n(v_self_812_, 2);
lean_dec(v_a_798_);
v___x_813_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v_goal_780_, v_self_812_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
if (lean_obj_tag(v_a_814_) == 1)
{
lean_object* v_val_815_; lean_object* v___x_816_; 
v_val_815_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v_a_814_, 1);
v___x_816_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_780_, v_self_812_, v_val_815_, v_snd_792_);
v_a_801_ = v___x_816_;
goto v___jp_800_;
}
else
{
lean_dec(v_a_814_);
lean_dec_ref(v_self_812_);
v_a_801_ = v_snd_792_;
goto v___jp_800_;
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_self_812_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_817_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_813_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_813_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_a_798_);
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_825_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_809_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_809_);
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
v___jp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_a_801_);
lean_ctor_set(v___x_794_, 0, v___x_799_);
v___x_803_ = v___x_794_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_a_801_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_783_, v___x_804_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_780_, v_as_781_, v_sz_782_, v___x_805_, v___x_803_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_806_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_del_object(v___x_794_);
lean_dec(v_snd_792_);
v_a_833_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_797_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_797_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(lean_object* v_goal_843_, lean_object* v_as_844_, lean_object* v_sz_845_, lean_object* v_i_846_, lean_object* v_b_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
size_t v_sz_boxed_853_; size_t v_i_boxed_854_; lean_object* v_res_855_; 
v_sz_boxed_853_ = lean_unbox_usize(v_sz_845_);
lean_dec(v_sz_845_);
v_i_boxed_854_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_843_, v_as_844_, v_sz_boxed_853_, v_i_boxed_854_, v_b_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v_as_844_);
lean_dec_ref(v_goal_843_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(lean_object* v_goal_856_, lean_object* v_t_857_, lean_object* v_init_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_root_864_; lean_object* v_tail_865_; lean_object* v___x_866_; 
v_root_864_ = lean_ctor_get(v_t_857_, 0);
v_tail_865_ = lean_ctor_get(v_t_857_, 1);
lean_inc_ref(v_init_858_);
v___x_866_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_858_, v_goal_856_, v_root_864_, v_init_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec_ref(v_init_858_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_903_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_903_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_903_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_903_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; 
v_a_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v_a_867_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_a_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; 
lean_del_object(v___x_869_);
v_a_875_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v_a_867_, 1);
v___x_876_ = lean_box(0);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v_a_875_);
v_sz_878_ = lean_array_size(v_tail_865_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_856_, v_tail_865_, v_sz_878_, v___x_879_, v___x_877_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_894_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_894_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_894_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_894_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_fst_885_; 
v_fst_885_ = lean_ctor_get(v_a_881_, 0);
if (lean_obj_tag(v_fst_885_) == 0)
{
lean_object* v_snd_886_; lean_object* v___x_888_; 
v_snd_886_ = lean_ctor_get(v_a_881_, 1);
lean_inc(v_snd_886_);
lean_dec(v_a_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_snd_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_snd_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v_val_890_; lean_object* v___x_892_; 
lean_inc_ref(v_fst_885_);
lean_dec(v_a_881_);
v_val_890_ = lean_ctor_get(v_fst_885_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v_fst_885_, 1);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_val_890_);
v___x_892_ = v___x_883_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_val_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_880_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_880_);
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
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_866_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_866_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(lean_object* v_goal_912_, lean_object* v_t_913_, lean_object* v_init_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_912_, v_t_913_, v_init_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec_ref(v_t_913_);
lean_dec_ref(v_goal_912_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(lean_object* v_a_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_object* v___x_923_; 
v___x_923_ = lean_box(0);
return v___x_923_;
}
else
{
lean_object* v_key_924_; lean_object* v_value_925_; lean_object* v_tail_926_; uint8_t v___x_927_; 
v_key_924_ = lean_ctor_get(v_x_922_, 0);
v_value_925_ = lean_ctor_get(v_x_922_, 1);
v_tail_926_ = lean_ctor_get(v_x_922_, 2);
v___x_927_ = lean_expr_eqv(v_key_924_, v_a_921_);
if (v___x_927_ == 0)
{
v_x_922_ = v_tail_926_;
goto _start;
}
else
{
lean_object* v___x_929_; 
lean_inc(v_value_925_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_value_925_);
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(lean_object* v_a_930_, lean_object* v_x_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_930_, v_x_931_);
lean_dec(v_x_931_);
lean_dec_ref(v_a_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(lean_object* v_m_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_buckets_935_; lean_object* v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; uint64_t v___x_939_; uint64_t v_fold_940_; uint64_t v___x_941_; uint64_t v___x_942_; uint64_t v___x_943_; size_t v___x_944_; size_t v___x_945_; size_t v___x_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_buckets_935_ = lean_ctor_get(v_m_933_, 1);
v___x_936_ = lean_array_get_size(v_buckets_935_);
v___x_937_ = l_Lean_Expr_hash(v_a_934_);
v___x_938_ = 32ULL;
v___x_939_ = lean_uint64_shift_right(v___x_937_, v___x_938_);
v_fold_940_ = lean_uint64_xor(v___x_937_, v___x_939_);
v___x_941_ = 16ULL;
v___x_942_ = lean_uint64_shift_right(v_fold_940_, v___x_941_);
v___x_943_ = lean_uint64_xor(v_fold_940_, v___x_942_);
v___x_944_ = lean_uint64_to_usize(v___x_943_);
v___x_945_ = lean_usize_of_nat(v___x_936_);
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_sub(v___x_945_, v___x_946_);
v___x_948_ = lean_usize_land(v___x_944_, v___x_947_);
v___x_949_ = lean_array_uget_borrowed(v_buckets_935_, v___x_948_);
v___x_950_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_934_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(lean_object* v_m_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_951_, v_a_952_);
lean_dec_ref(v_a_952_);
lean_dec_ref(v_m_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(lean_object* v_goal_954_, lean_object* v_as_955_, size_t v_sz_956_, size_t v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = lean_usize_dec_lt(v_i_957_, v_sz_956_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v_b_958_);
return v___x_965_;
}
else
{
lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_997_; 
v_snd_966_ = lean_ctor_get(v_b_958_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_b_958_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_b_958_, 0);
lean_dec(v_unused_998_);
v___x_968_ = v_b_958_;
v_isShared_969_ = v_isSharedCheck_997_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_dec(v_b_958_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_997_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_array_uget_borrowed(v_as_955_, v_i_957_);
lean_inc(v_a_970_);
v___x_971_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_954_, v_a_970_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v_self_973_; lean_object* v___x_974_; lean_object* v_a_976_; lean_object* v___x_983_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v_self_973_ = lean_ctor_get(v_a_972_, 0);
lean_inc_ref_n(v_self_973_, 2);
lean_dec(v_a_972_);
v___x_974_ = lean_box(0);
v___x_983_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_973_);
if (lean_obj_tag(v___x_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_985_; 
v_val_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_966_, v_val_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_966_, v_self_973_);
lean_dec_ref(v_self_973_);
if (lean_obj_tag(v___x_986_) == 1)
{
lean_object* v_val_987_; lean_object* v___x_988_; 
v_val_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_954_, v_val_984_, v_val_987_, v_snd_966_);
v_a_976_ = v___x_988_;
goto v___jp_975_;
}
else
{
lean_dec(v___x_986_);
lean_dec(v_val_984_);
v_a_976_ = v_snd_966_;
goto v___jp_975_;
}
}
else
{
lean_dec_ref_known(v___x_985_, 1);
lean_dec(v_val_984_);
lean_dec_ref(v_self_973_);
v_a_976_ = v_snd_966_;
goto v___jp_975_;
}
}
else
{
lean_dec(v___x_983_);
lean_dec_ref(v_self_973_);
v_a_976_ = v_snd_966_;
goto v___jp_975_;
}
v___jp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_a_976_);
lean_ctor_set(v___x_968_, 0, v___x_974_);
v___x_978_ = v___x_968_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_a_976_);
v___x_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
size_t v___x_979_; size_t v___x_980_; 
v___x_979_ = ((size_t)1ULL);
v___x_980_ = lean_usize_add(v_i_957_, v___x_979_);
v_i_957_ = v___x_980_;
v_b_958_ = v___x_978_;
goto _start;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_del_object(v___x_968_);
lean_dec(v_snd_966_);
v_a_989_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_971_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_971_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12___boxed(lean_object* v_goal_999_, lean_object* v_as_1000_, lean_object* v_sz_1001_, lean_object* v_i_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
size_t v_sz_boxed_1009_; size_t v_i_boxed_1010_; lean_object* v_res_1011_; 
v_sz_boxed_1009_ = lean_unbox_usize(v_sz_1001_);
lean_dec(v_sz_1001_);
v_i_boxed_1010_ = lean_unbox_usize(v_i_1002_);
lean_dec(v_i_1002_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(v_goal_999_, v_as_1000_, v_sz_boxed_1009_, v_i_boxed_1010_, v_b_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_as_1000_);
lean_dec_ref(v_goal_999_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(lean_object* v_goal_1012_, lean_object* v_as_1013_, size_t v_sz_1014_, size_t v_i_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_usize_dec_lt(v_i_1015_, v_sz_1014_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_b_1016_);
return v___x_1023_;
}
else
{
lean_object* v_snd_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1055_; 
v_snd_1024_ = lean_ctor_get(v_b_1016_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_b_1016_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_b_1016_, 0);
lean_dec(v_unused_1056_);
v___x_1026_ = v_b_1016_;
v_isShared_1027_ = v_isSharedCheck_1055_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_snd_1024_);
lean_dec(v_b_1016_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1055_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_a_1028_; lean_object* v___x_1029_; 
v_a_1028_ = lean_array_uget_borrowed(v_as_1013_, v_i_1015_);
lean_inc(v_a_1028_);
v___x_1029_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1012_, v_a_1028_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v_self_1031_; lean_object* v___x_1032_; lean_object* v_a_1034_; lean_object* v___x_1041_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v_self_1031_ = lean_ctor_get(v_a_1030_, 0);
lean_inc_ref_n(v_self_1031_, 2);
lean_dec(v_a_1030_);
v___x_1032_ = lean_box(0);
v___x_1041_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1031_);
if (lean_obj_tag(v___x_1041_) == 1)
{
lean_object* v_val_1042_; lean_object* v___x_1043_; 
v_val_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1024_, v_val_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1024_, v_self_1031_);
lean_dec_ref(v_self_1031_);
if (lean_obj_tag(v___x_1044_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1012_, v_val_1042_, v_val_1045_, v_snd_1024_);
v_a_1034_ = v___x_1046_;
goto v___jp_1033_;
}
else
{
lean_dec(v___x_1044_);
lean_dec(v_val_1042_);
v_a_1034_ = v_snd_1024_;
goto v___jp_1033_;
}
}
else
{
lean_dec_ref_known(v___x_1043_, 1);
lean_dec(v_val_1042_);
lean_dec_ref(v_self_1031_);
v_a_1034_ = v_snd_1024_;
goto v___jp_1033_;
}
}
else
{
lean_dec(v___x_1041_);
lean_dec_ref(v_self_1031_);
v_a_1034_ = v_snd_1024_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v_a_1034_);
lean_ctor_set(v___x_1026_, 0, v___x_1032_);
v___x_1036_ = v___x_1026_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_a_1034_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_i_1015_, v___x_1037_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(v_goal_1012_, v_as_1013_, v_sz_1014_, v___x_1038_, v___x_1036_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1039_;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_del_object(v___x_1026_);
lean_dec(v_snd_1024_);
v_a_1047_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1029_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1029_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10___boxed(lean_object* v_goal_1057_, lean_object* v_as_1058_, lean_object* v_sz_1059_, lean_object* v_i_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
size_t v_sz_boxed_1067_; size_t v_i_boxed_1068_; lean_object* v_res_1069_; 
v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1059_);
lean_dec(v_sz_1059_);
v_i_boxed_1068_ = lean_unbox_usize(v_i_1060_);
lean_dec(v_i_1060_);
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(v_goal_1057_, v_as_1058_, v_sz_boxed_1067_, v_i_boxed_1068_, v_b_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_as_1058_);
lean_dec_ref(v_goal_1057_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(lean_object* v_init_1070_, lean_object* v_goal_1071_, lean_object* v_n_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
if (lean_obj_tag(v_n_1072_) == 0)
{
lean_object* v_cs_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; size_t v_sz_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v_cs_1079_ = lean_ctor_get(v_n_1072_, 0);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_b_1073_);
v_sz_1082_ = lean_array_size(v_cs_1079_);
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(v_init_1070_, v_goal_1071_, v_cs_1079_, v_sz_1082_, v___x_1083_, v___x_1081_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1099_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1099_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1099_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_fst_1089_; 
v_fst_1089_ = lean_ctor_get(v_a_1085_, 0);
if (lean_obj_tag(v_fst_1089_) == 0)
{
lean_object* v_snd_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_snd_1090_ = lean_ctor_get(v_a_1085_, 1);
lean_inc(v_snd_1090_);
lean_dec(v_a_1085_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_snd_1090_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1091_);
v___x_1093_ = v___x_1087_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
else
{
lean_object* v_val_1095_; lean_object* v___x_1097_; 
lean_inc_ref(v_fst_1089_);
lean_dec(v_a_1085_);
v_val_1095_ = lean_ctor_get(v_fst_1089_, 0);
lean_inc(v_val_1095_);
lean_dec_ref_known(v_fst_1089_, 1);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_val_1095_);
v___x_1097_ = v___x_1087_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_val_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1084_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1084_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_vs_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v_vs_1108_ = lean_ctor_get(v_n_1072_, 0);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_b_1073_);
v_sz_1111_ = lean_array_size(v_vs_1108_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(v_goal_1071_, v_vs_1108_, v_sz_1111_, v___x_1112_, v___x_1110_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1128_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1128_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1128_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_fst_1118_; 
v_fst_1118_ = lean_ctor_get(v_a_1114_, 0);
if (lean_obj_tag(v_fst_1118_) == 0)
{
lean_object* v_snd_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v_snd_1119_ = lean_ctor_get(v_a_1114_, 1);
lean_inc(v_snd_1119_);
lean_dec(v_a_1114_);
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_snd_1119_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1120_);
v___x_1122_ = v___x_1116_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
else
{
lean_object* v_val_1124_; lean_object* v___x_1126_; 
lean_inc_ref(v_fst_1118_);
lean_dec(v_a_1114_);
v_val_1124_ = lean_ctor_get(v_fst_1118_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v_fst_1118_, 1);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v_val_1124_);
v___x_1126_ = v___x_1116_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_val_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
v_a_1129_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1113_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1113_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(lean_object* v_init_1137_, lean_object* v_goal_1138_, lean_object* v_as_1139_, size_t v_sz_1140_, size_t v_i_1141_, lean_object* v_b_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1141_, v_sz_1140_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_b_1142_);
return v___x_1149_;
}
else
{
lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1184_; 
v_snd_1150_ = lean_ctor_get(v_b_1142_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_b_1142_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v_b_1142_, 0);
lean_dec(v_unused_1185_);
v___x_1152_ = v_b_1142_;
v_isShared_1153_ = v_isSharedCheck_1184_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_dec(v_b_1142_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1184_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_a_1154_; lean_object* v___x_1155_; 
v_a_1154_ = lean_array_uget_borrowed(v_as_1139_, v_i_1141_);
lean_inc(v_snd_1150_);
v___x_1155_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_init_1137_, v_goal_1138_, v_a_1154_, v_snd_1150_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1175_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1175_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1175_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
if (lean_obj_tag(v_a_1156_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_a_1156_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1160_);
v___x_1162_ = v___x_1152_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_snd_1150_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1162_);
v___x_1164_ = v___x_1158_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_del_object(v___x_1158_);
lean_dec(v_snd_1150_);
v_a_1167_ = lean_ctor_get(v_a_1156_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v_a_1156_, 1);
v___x_1168_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_a_1167_);
lean_ctor_set(v___x_1152_, 0, v___x_1168_);
v___x_1170_ = v___x_1152_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_a_1167_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
size_t v___x_1171_; size_t v___x_1172_; 
v___x_1171_ = ((size_t)1ULL);
v___x_1172_ = lean_usize_add(v_i_1141_, v___x_1171_);
v_i_1141_ = v___x_1172_;
v_b_1142_ = v___x_1170_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_del_object(v___x_1152_);
lean_dec(v_snd_1150_);
v_a_1176_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1155_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1155_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9___boxed(lean_object* v_init_1186_, lean_object* v_goal_1187_, lean_object* v_as_1188_, lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(v_init_1186_, v_goal_1187_, v_as_1188_, v_sz_boxed_1197_, v_i_boxed_1198_, v_b_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_as_1188_);
lean_dec_ref(v_goal_1187_);
lean_dec_ref(v_init_1186_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5___boxed(lean_object* v_init_1200_, lean_object* v_goal_1201_, lean_object* v_n_1202_, lean_object* v_b_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_init_1200_, v_goal_1201_, v_n_1202_, v_b_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_n_1202_);
lean_dec_ref(v_goal_1201_);
lean_dec_ref(v_init_1200_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(lean_object* v_goal_1210_, lean_object* v_as_1211_, size_t v_sz_1212_, size_t v_i_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = lean_usize_dec_lt(v_i_1213_, v_sz_1212_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_b_1214_);
return v___x_1221_;
}
else
{
lean_object* v_snd_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1253_; 
v_snd_1222_ = lean_ctor_get(v_b_1214_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_b_1214_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v_b_1214_, 0);
lean_dec(v_unused_1254_);
v___x_1224_ = v_b_1214_;
v_isShared_1225_ = v_isSharedCheck_1253_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_snd_1222_);
lean_dec(v_b_1214_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1253_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1226_ = lean_array_uget_borrowed(v_as_1211_, v_i_1213_);
lean_inc(v_a_1226_);
v___x_1227_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1210_, v_a_1226_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v_self_1229_; lean_object* v___x_1230_; lean_object* v_a_1232_; lean_object* v___x_1239_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v_self_1229_ = lean_ctor_get(v_a_1228_, 0);
lean_inc_ref_n(v_self_1229_, 2);
lean_dec(v_a_1228_);
v___x_1230_ = lean_box(0);
v___x_1239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1229_);
if (lean_obj_tag(v___x_1239_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1241_; 
v_val_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1222_, v_val_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1222_, v_self_1229_);
lean_dec_ref(v_self_1229_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1244_; 
v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1210_, v_val_1240_, v_val_1243_, v_snd_1222_);
v_a_1232_ = v___x_1244_;
goto v___jp_1231_;
}
else
{
lean_dec(v___x_1242_);
lean_dec(v_val_1240_);
v_a_1232_ = v_snd_1222_;
goto v___jp_1231_;
}
}
else
{
lean_dec_ref_known(v___x_1241_, 1);
lean_dec(v_val_1240_);
lean_dec_ref(v_self_1229_);
v_a_1232_ = v_snd_1222_;
goto v___jp_1231_;
}
}
else
{
lean_dec(v___x_1239_);
lean_dec_ref(v_self_1229_);
v_a_1232_ = v_snd_1222_;
goto v___jp_1231_;
}
v___jp_1231_:
{
lean_object* v___x_1234_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v_a_1232_);
lean_ctor_set(v___x_1224_, 0, v___x_1230_);
v___x_1234_ = v___x_1224_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_a_1232_);
v___x_1234_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
size_t v___x_1235_; size_t v___x_1236_; 
v___x_1235_ = ((size_t)1ULL);
v___x_1236_ = lean_usize_add(v_i_1213_, v___x_1235_);
v_i_1213_ = v___x_1236_;
v_b_1214_ = v___x_1234_;
goto _start;
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_del_object(v___x_1224_);
lean_dec(v_snd_1222_);
v_a_1245_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1227_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1227_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12___boxed(lean_object* v_goal_1255_, lean_object* v_as_1256_, lean_object* v_sz_1257_, lean_object* v_i_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
size_t v_sz_boxed_1265_; size_t v_i_boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1265_ = lean_unbox_usize(v_sz_1257_);
lean_dec(v_sz_1257_);
v_i_boxed_1266_ = lean_unbox_usize(v_i_1258_);
lean_dec(v_i_1258_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(v_goal_1255_, v_as_1256_, v_sz_boxed_1265_, v_i_boxed_1266_, v_b_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v_as_1256_);
lean_dec_ref(v_goal_1255_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(lean_object* v_goal_1268_, lean_object* v_as_1269_, size_t v_sz_1270_, size_t v_i_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_usize_dec_lt(v_i_1271_, v_sz_1270_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_b_1272_);
return v___x_1279_;
}
else
{
lean_object* v_snd_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1311_; 
v_snd_1280_ = lean_ctor_get(v_b_1272_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_b_1272_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_b_1272_, 0);
lean_dec(v_unused_1312_);
v___x_1282_ = v_b_1272_;
v_isShared_1283_ = v_isSharedCheck_1311_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snd_1280_);
lean_dec(v_b_1272_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1311_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v_a_1284_; lean_object* v___x_1285_; 
v_a_1284_ = lean_array_uget_borrowed(v_as_1269_, v_i_1271_);
lean_inc(v_a_1284_);
v___x_1285_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1268_, v_a_1284_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v_self_1287_; lean_object* v___x_1288_; lean_object* v_a_1290_; lean_object* v___x_1297_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v_self_1287_ = lean_ctor_get(v_a_1286_, 0);
lean_inc_ref_n(v_self_1287_, 2);
lean_dec(v_a_1286_);
v___x_1288_ = lean_box(0);
v___x_1297_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_1287_);
if (lean_obj_tag(v___x_1297_) == 1)
{
lean_object* v_val_1298_; lean_object* v___x_1299_; 
v_val_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1280_, v_val_1298_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_1280_, v_self_1287_);
lean_dec_ref(v_self_1287_);
if (lean_obj_tag(v___x_1300_) == 1)
{
lean_object* v_val_1301_; lean_object* v___x_1302_; 
v_val_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1268_, v_val_1298_, v_val_1301_, v_snd_1280_);
v_a_1290_ = v___x_1302_;
goto v___jp_1289_;
}
else
{
lean_dec(v___x_1300_);
lean_dec(v_val_1298_);
v_a_1290_ = v_snd_1280_;
goto v___jp_1289_;
}
}
else
{
lean_dec_ref_known(v___x_1299_, 1);
lean_dec(v_val_1298_);
lean_dec_ref(v_self_1287_);
v_a_1290_ = v_snd_1280_;
goto v___jp_1289_;
}
}
else
{
lean_dec(v___x_1297_);
lean_dec_ref(v_self_1287_);
v_a_1290_ = v_snd_1280_;
goto v___jp_1289_;
}
v___jp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v_a_1290_);
lean_ctor_set(v___x_1282_, 0, v___x_1288_);
v___x_1292_ = v___x_1282_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_a_1290_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1271_, v___x_1293_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(v_goal_1268_, v_as_1269_, v_sz_1270_, v___x_1294_, v___x_1292_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1295_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_del_object(v___x_1282_);
lean_dec(v_snd_1280_);
v_a_1303_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1285_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1285_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6___boxed(lean_object* v_goal_1313_, lean_object* v_as_1314_, lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
size_t v_sz_boxed_1323_; size_t v_i_boxed_1324_; lean_object* v_res_1325_; 
v_sz_boxed_1323_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1324_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(v_goal_1313_, v_as_1314_, v_sz_boxed_1323_, v_i_boxed_1324_, v_b_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v_as_1314_);
lean_dec_ref(v_goal_1313_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(lean_object* v_goal_1326_, lean_object* v_t_1327_, lean_object* v_init_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_root_1334_; lean_object* v_tail_1335_; lean_object* v___x_1336_; 
v_root_1334_ = lean_ctor_get(v_t_1327_, 0);
v_tail_1335_ = lean_ctor_get(v_t_1327_, 1);
lean_inc_ref(v_init_1328_);
v___x_1336_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_init_1328_, v_goal_1326_, v_root_1334_, v_init_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec_ref(v_init_1328_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1373_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1373_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1373_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
if (lean_obj_tag(v_a_1337_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; 
v_a_1341_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v_a_1337_, 1);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_a_1341_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; size_t v_sz_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
lean_del_object(v___x_1339_);
v_a_1345_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v_a_1337_, 1);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v_a_1345_);
v_sz_1348_ = lean_array_size(v_tail_1335_);
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(v_goal_1326_, v_tail_1335_, v_sz_1348_, v___x_1349_, v___x_1347_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1364_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1364_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1364_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_fst_1355_; 
v_fst_1355_ = lean_ctor_get(v_a_1351_, 0);
if (lean_obj_tag(v_fst_1355_) == 0)
{
lean_object* v_snd_1356_; lean_object* v___x_1358_; 
v_snd_1356_ = lean_ctor_get(v_a_1351_, 1);
lean_inc(v_snd_1356_);
lean_dec(v_a_1351_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v_snd_1356_);
v___x_1358_ = v___x_1353_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_snd_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
lean_object* v_val_1360_; lean_object* v___x_1362_; 
lean_inc_ref(v_fst_1355_);
lean_dec(v_a_1351_);
v_val_1360_ = lean_ctor_get(v_fst_1355_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v_fst_1355_, 1);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v_val_1360_);
v___x_1362_ = v___x_1353_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_val_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1365_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1350_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1350_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1336_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1336_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(lean_object* v_goal_1382_, lean_object* v_t_1383_, lean_object* v_init_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1382_, v_t_1383_, v_init_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec_ref(v_t_1383_);
lean_dec_ref(v_goal_1382_);
return v_res_1390_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_unsigned_to_nat(16u);
v___x_1393_ = lean_mk_array(v___x_1392_, v___x_1391_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_model_1396_; 
v___x_1394_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0);
v___x_1395_ = lean_unsigned_to_nat(0u);
v_model_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_1396_, 0, v___x_1395_);
lean_ctor_set(v_model_1396_, 1, v___x_1394_);
return v_model_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object* v_goal_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_toGoalState_1411_; lean_object* v_exprs_1412_; lean_object* v_model_1413_; lean_object* v___x_1414_; 
v_toGoalState_1411_ = lean_ctor_get(v_goal_1405_, 0);
v_exprs_1412_ = lean_ctor_get(v_toGoalState_1411_, 2);
v_model_1413_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1);
v___x_1414_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_1405_, v_exprs_1412_, v_model_1413_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_1405_, v_exprs_1412_, v_a_1415_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2));
v___x_1419_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1405_, v___x_1418_, v_a_1417_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6));
v___x_1422_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_1421_, v_a_1420_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1422_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v___x_1422_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_a_1420_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1420_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_a_1420_);
v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1422_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1422_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
return v___x_1419_;
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1416_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1416_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1414_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1414_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(lean_object* v_goal_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec_ref(v_goal_1455_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(lean_object* v_00_u03b2_1462_, lean_object* v_m_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_1463_, v_a_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(lean_object* v_00_u03b2_1466_, lean_object* v_m_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(v_00_u03b2_1466_, v_m_1467_, v_a_1468_);
lean_dec_ref(v_a_1468_);
lean_dec_ref(v_m_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(lean_object* v_00_u03b2_1470_, lean_object* v_a_1471_, lean_object* v_x_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_1471_, v_x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1474_, lean_object* v_a_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(v_00_u03b2_1474_, v_a_1475_, v_x_1476_);
lean_dec(v_x_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1477_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

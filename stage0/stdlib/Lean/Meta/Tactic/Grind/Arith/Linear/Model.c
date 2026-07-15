// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Model
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.Types import Lean.Meta.Tactic.Grind.Arith.Linear.Reify import Lean.Meta.Tactic.Grind.Arith.ModelUtil import Init.Grind.Module.Envelope
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSubInst(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isNegInst(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_instInhabitedRat;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 255, 209, 221, 117, 20, 143, 66)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1_, lean_object* v_vals_2_, lean_object* v_i_3_, lean_object* v_k_4_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_17_, lean_object* v_vals_18_, lean_object* v_i_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_17_, v_vals_18_, v_i_19_, v_k_20_);
lean_dec_ref(v_k_20_);
lean_dec_ref(v_vals_18_);
lean_dec_ref(v_keys_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(lean_object* v_x_22_, size_t v_x_23_, lean_object* v_x_24_){
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
v___x_46_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_ks_43_, v_vs_44_, v___x_45_, v_x_24_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
size_t v_x_343__boxed_50_; lean_object* v_res_51_; 
v_x_343__boxed_50_ = lean_unbox_usize(v_x_48_);
lean_dec(v_x_48_);
v_res_51_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_47_, v_x_343__boxed_50_, v_x_49_);
lean_dec_ref(v_x_49_);
lean_dec_ref(v_x_47_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
size_t v___x_54_; size_t v___x_55_; size_t v___x_56_; uint64_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v___x_54_ = lean_ptr_addr(v_x_53_);
v___x_55_ = ((size_t)3ULL);
v___x_56_ = lean_usize_shift_right(v___x_54_, v___x_55_);
v___x_57_ = lean_usize_to_uint64(v___x_56_);
v___x_58_ = lean_uint64_to_usize(v___x_57_);
v___x_59_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_52_, v___x_58_, v_x_53_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg___boxed(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_60_, v_x_61_);
lean_dec_ref(v_x_61_);
lean_dec_ref(v_x_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(lean_object* v_s_63_, lean_object* v_e_64_){
_start:
{
lean_object* v_varMap_65_; lean_object* v_assignment_66_; lean_object* v___x_67_; 
v_varMap_65_ = lean_ctor_get(v_s_63_, 31);
v_assignment_66_ = lean_ctor_get(v_s_63_, 35);
v___x_67_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_varMap_65_, v_e_64_);
if (lean_obj_tag(v___x_67_) == 1)
{
lean_object* v_val_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_80_; 
v_val_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_80_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_val_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_80_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_size_72_; uint8_t v___x_73_; 
v_size_72_ = lean_ctor_get(v_assignment_66_, 2);
v___x_73_ = lean_nat_dec_lt(v_val_68_, v_size_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
lean_del_object(v___x_70_);
lean_dec(v_val_68_);
v___x_74_ = lean_box(0);
return v___x_74_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = l_instInhabitedRat;
v___x_76_ = l_Lean_PersistentArray_get_x21___redArg(v___x_75_, v_assignment_66_, v_val_68_);
lean_dec(v_val_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_76_);
v___x_78_ = v___x_70_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_object* v___x_81_; 
lean_dec(v___x_67_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f___boxed(lean_object* v_s_82_, lean_object* v_e_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_82_, v_e_83_);
lean_dec_ref(v_e_83_);
lean_dec_ref(v_s_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(lean_object* v_00_u03b2_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_86_, v_x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___boxed(lean_object* v_00_u03b2_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(v_00_u03b2_89_, v_x_90_, v_x_91_);
lean_dec_ref(v_x_91_);
lean_dec_ref(v_x_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(lean_object* v_00_u03b2_93_, lean_object* v_x_94_, size_t v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_94_, v_x_95_, v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
size_t v_x_448__boxed_102_; lean_object* v_res_103_; 
v_x_448__boxed_102_ = lean_unbox_usize(v_x_100_);
lean_dec(v_x_100_);
v_res_103_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_98_, v_x_99_, v_x_448__boxed_102_, v_x_101_);
lean_dec_ref(v_x_101_);
lean_dec_ref(v_x_99_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_104_, lean_object* v_keys_105_, lean_object* v_vals_106_, lean_object* v_heq_107_, lean_object* v_i_108_, lean_object* v_k_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_105_, v_vals_106_, v_i_108_, v_k_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_111_, lean_object* v_keys_112_, lean_object* v_vals_113_, lean_object* v_heq_114_, lean_object* v_i_115_, lean_object* v_k_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(v_00_u03b2_111_, v_keys_112_, v_vals_113_, v_heq_114_, v_i_115_, v_k_116_);
lean_dec_ref(v_k_116_);
lean_dec_ref(v_vals_113_);
lean_dec_ref(v_keys_112_);
return v_res_117_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0(void){
_start:
{
uint8_t v___x_118_; uint64_t v___x_119_; 
v___x_118_ = 1;
v___x_119_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object* v_type_120_, lean_object* v_n_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_self_127_; lean_object* v___x_128_; uint8_t v_foApprox_129_; uint8_t v_ctxApprox_130_; uint8_t v_quasiPatternApprox_131_; uint8_t v_constApprox_132_; uint8_t v_isDefEqStuckEx_133_; uint8_t v_unificationHints_134_; uint8_t v_proofIrrelevance_135_; uint8_t v_assignSyntheticOpaque_136_; uint8_t v_offsetCnstrs_137_; uint8_t v_etaStruct_138_; uint8_t v_univApprox_139_; uint8_t v_iota_140_; uint8_t v_beta_141_; uint8_t v_proj_142_; uint8_t v_zeta_143_; uint8_t v_zetaDelta_144_; uint8_t v_zetaUnused_145_; uint8_t v_zetaHave_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_183_; 
v_self_127_ = lean_ctor_get(v_n_121_, 0);
lean_inc_ref(v_self_127_);
lean_dec_ref(v_n_121_);
v___x_128_ = l_Lean_Meta_Context_config(v_a_122_);
v_foApprox_129_ = lean_ctor_get_uint8(v___x_128_, 0);
v_ctxApprox_130_ = lean_ctor_get_uint8(v___x_128_, 1);
v_quasiPatternApprox_131_ = lean_ctor_get_uint8(v___x_128_, 2);
v_constApprox_132_ = lean_ctor_get_uint8(v___x_128_, 3);
v_isDefEqStuckEx_133_ = lean_ctor_get_uint8(v___x_128_, 4);
v_unificationHints_134_ = lean_ctor_get_uint8(v___x_128_, 5);
v_proofIrrelevance_135_ = lean_ctor_get_uint8(v___x_128_, 6);
v_assignSyntheticOpaque_136_ = lean_ctor_get_uint8(v___x_128_, 7);
v_offsetCnstrs_137_ = lean_ctor_get_uint8(v___x_128_, 8);
v_etaStruct_138_ = lean_ctor_get_uint8(v___x_128_, 10);
v_univApprox_139_ = lean_ctor_get_uint8(v___x_128_, 11);
v_iota_140_ = lean_ctor_get_uint8(v___x_128_, 12);
v_beta_141_ = lean_ctor_get_uint8(v___x_128_, 13);
v_proj_142_ = lean_ctor_get_uint8(v___x_128_, 14);
v_zeta_143_ = lean_ctor_get_uint8(v___x_128_, 15);
v_zetaDelta_144_ = lean_ctor_get_uint8(v___x_128_, 16);
v_zetaUnused_145_ = lean_ctor_get_uint8(v___x_128_, 17);
v_zetaHave_146_ = lean_ctor_get_uint8(v___x_128_, 18);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_183_ == 0)
{
v___x_148_ = v___x_128_;
v_isShared_149_ = v_isSharedCheck_183_;
goto v_resetjp_147_;
}
else
{
lean_dec(v___x_128_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_183_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v_trackZetaDelta_150_; lean_object* v_zetaDeltaSet_151_; lean_object* v_lctx_152_; lean_object* v_localInstances_153_; lean_object* v_defEqCtx_x3f_154_; lean_object* v_synthPendingDepth_155_; lean_object* v_canUnfold_x3f_156_; uint8_t v_univApprox_157_; uint8_t v_inTypeClassResolution_158_; uint8_t v_cacheInferType_159_; uint8_t v___x_160_; lean_object* v_config_162_; 
v_trackZetaDelta_150_ = lean_ctor_get_uint8(v_a_122_, sizeof(void*)*7);
v_zetaDeltaSet_151_ = lean_ctor_get(v_a_122_, 1);
v_lctx_152_ = lean_ctor_get(v_a_122_, 2);
v_localInstances_153_ = lean_ctor_get(v_a_122_, 3);
v_defEqCtx_x3f_154_ = lean_ctor_get(v_a_122_, 4);
v_synthPendingDepth_155_ = lean_ctor_get(v_a_122_, 5);
v_canUnfold_x3f_156_ = lean_ctor_get(v_a_122_, 6);
v_univApprox_157_ = lean_ctor_get_uint8(v_a_122_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_158_ = lean_ctor_get_uint8(v_a_122_, sizeof(void*)*7 + 2);
v_cacheInferType_159_ = lean_ctor_get_uint8(v_a_122_, sizeof(void*)*7 + 3);
v___x_160_ = 1;
if (v_isShared_149_ == 0)
{
v_config_162_ = v___x_148_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 0, v_foApprox_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 1, v_ctxApprox_130_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 2, v_quasiPatternApprox_131_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 3, v_constApprox_132_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 4, v_isDefEqStuckEx_133_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 5, v_unificationHints_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 6, v_proofIrrelevance_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 7, v_assignSyntheticOpaque_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 8, v_offsetCnstrs_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 10, v_etaStruct_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 11, v_univApprox_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 12, v_iota_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 13, v_beta_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 14, v_proj_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 15, v_zeta_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 16, v_zetaDelta_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 17, v_zetaUnused_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, 18, v_zetaHave_146_);
v_config_162_ = v_reuseFailAlloc_182_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v_key_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_ctor_set_uint8(v_config_162_, 9, v___x_160_);
v___x_163_ = l_Lean_Meta_Context_configKey(v_a_122_);
v___x_164_ = 3ULL;
v___x_165_ = lean_uint64_shift_right(v___x_163_, v___x_164_);
v___x_166_ = lean_uint64_shift_left(v___x_165_, v___x_164_);
v___x_167_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0);
v_key_168_ = lean_uint64_lor(v___x_166_, v___x_167_);
v___x_169_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_169_, 0, v_config_162_);
lean_ctor_set_uint64(v___x_169_, sizeof(void*)*1, v_key_168_);
lean_inc(v_canUnfold_x3f_156_);
lean_inc(v_synthPendingDepth_155_);
lean_inc(v_defEqCtx_x3f_154_);
lean_inc_ref(v_localInstances_153_);
lean_inc_ref(v_lctx_152_);
lean_inc(v_zetaDeltaSet_151_);
v___x_170_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_zetaDeltaSet_151_);
lean_ctor_set(v___x_170_, 2, v_lctx_152_);
lean_ctor_set(v___x_170_, 3, v_localInstances_153_);
lean_ctor_set(v___x_170_, 4, v_defEqCtx_x3f_154_);
lean_ctor_set(v___x_170_, 5, v_synthPendingDepth_155_);
lean_ctor_set(v___x_170_, 6, v_canUnfold_x3f_156_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*7, v_trackZetaDelta_150_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*7 + 1, v_univApprox_157_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*7 + 2, v_inTypeClassResolution_158_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*7 + 3, v_cacheInferType_159_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
lean_inc_ref(v___x_170_);
v___x_171_ = lean_infer_type(v_self_127_, v___x_170_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
v___x_173_ = l_Lean_Meta_isExprDefEq(v_a_172_, v_type_120_, v___x_170_, v_a_123_, v_a_124_, v_a_125_);
lean_dec_ref_known(v___x_170_, 7);
return v___x_173_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref_known(v___x_170_, 7);
lean_dec_ref(v_type_120_);
v_a_174_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_171_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_171_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object* v_type_184_, lean_object* v_n_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_184_, v_n_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object* v_e_203_){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = l_Lean_Expr_cleanupAnnotations(v_e_203_);
v___x_205_ = l_Lean_Expr_isApp(v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v___x_204_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v_arg_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_arg_207_ = lean_ctor_get(v___x_204_, 1);
lean_inc_ref(v_arg_207_);
v___x_208_ = l_Lean_Expr_appFnCleanup___redArg(v___x_204_);
v___x_209_ = l_Lean_Expr_isApp(v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v___x_208_);
lean_dec_ref(v_arg_207_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = l_Lean_Expr_appFnCleanup___redArg(v___x_208_);
v___x_212_ = l_Lean_Expr_isApp(v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec_ref(v___x_211_);
lean_dec_ref(v_arg_207_);
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_211_);
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_216_ = l_Lean_Expr_isConstOf(v___x_214_, v___x_215_);
lean_dec_ref(v___x_214_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v_arg_207_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v_arg_207_);
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Rat_ofInt(v_a_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_nat_to_int(v_a_221_);
v___x_223_ = l_Rat_ofInt(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_224_, lean_object* v_x_225_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v___x_226_; 
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v_key_227_; lean_object* v_value_228_; lean_object* v_tail_229_; uint8_t v___x_230_; 
v_key_227_ = lean_ctor_get(v_x_225_, 0);
v_value_228_ = lean_ctor_get(v_x_225_, 1);
v_tail_229_ = lean_ctor_get(v_x_225_, 2);
v___x_230_ = lean_expr_eqv(v_key_227_, v_a_224_);
if (v___x_230_ == 0)
{
v_x_225_ = v_tail_229_;
goto _start;
}
else
{
lean_object* v___x_232_; 
lean_inc(v_value_228_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_value_228_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_233_, v_x_234_);
lean_dec(v_x_234_);
lean_dec_ref(v_a_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_buckets_238_; lean_object* v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v_fold_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_buckets_238_ = lean_ctor_get(v_m_236_, 1);
v___x_239_ = lean_array_get_size(v_buckets_238_);
v___x_240_ = l_Lean_Expr_hash(v_a_237_);
v___x_241_ = 32ULL;
v___x_242_ = lean_uint64_shift_right(v___x_240_, v___x_241_);
v_fold_243_ = lean_uint64_xor(v___x_240_, v___x_242_);
v___x_244_ = 16ULL;
v___x_245_ = lean_uint64_shift_right(v_fold_243_, v___x_244_);
v___x_246_ = lean_uint64_xor(v_fold_243_, v___x_245_);
v___x_247_ = lean_uint64_to_usize(v___x_246_);
v___x_248_ = lean_usize_of_nat(v___x_239_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_sub(v___x_248_, v___x_249_);
v___x_251_ = lean_usize_land(v___x_247_, v___x_250_);
v___x_252_ = lean_array_uget_borrowed(v_buckets_238_, v___x_251_);
v___x_253_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_237_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_254_, v_a_255_);
lean_dec_ref(v_a_255_);
lean_dec_ref(v_m_254_);
return v_res_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_296_, lean_object* v_model_297_, lean_object* v_e_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_297_, v_e_298_);
if (lean_obj_tag(v___x_304_) == 1)
{
lean_object* v___x_305_; 
lean_dec_ref(v_e_298_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
lean_dec(v___x_304_);
v___x_306_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_298_, v_a_300_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_560_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_560_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_560_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_560_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = l_Lean_Expr_cleanupAnnotations(v_a_307_);
v___x_317_ = l_Lean_Expr_isApp(v___x_316_);
if (v___x_317_ == 0)
{
lean_dec_ref(v___x_316_);
goto v___jp_311_;
}
else
{
lean_object* v_arg_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_arg_318_ = lean_ctor_get(v___x_316_, 1);
lean_inc_ref(v_arg_318_);
v___x_319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_316_);
v___x_320_ = l_Lean_Expr_isApp(v___x_319_);
if (v___x_320_ == 0)
{
lean_dec_ref(v___x_319_);
lean_dec_ref(v_arg_318_);
goto v___jp_311_;
}
else
{
lean_object* v_arg_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_arg_321_ = lean_ctor_get(v___x_319_, 1);
lean_inc_ref(v_arg_321_);
v___x_322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_319_);
v___x_323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_324_ = l_Lean_Expr_isConstOf(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = l_Lean_Expr_isApp(v___x_322_);
if (v___x_325_ == 0)
{
lean_dec_ref(v___x_322_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
goto v___jp_311_;
}
else
{
lean_object* v_arg_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_arg_326_ = lean_ctor_get(v___x_322_, 1);
lean_inc_ref(v_arg_326_);
v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_322_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_329_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_331_ = l_Lean_Expr_isConstOf(v___x_327_, v___x_330_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; 
v___x_332_ = l_Lean_Expr_isApp(v___x_327_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
goto v___jp_311_;
}
else
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_327_);
v___x_334_ = l_Lean_Expr_isApp(v___x_333_);
if (v___x_334_ == 0)
{
lean_dec_ref(v___x_333_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
goto v___jp_311_;
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_333_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_335_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
goto v___jp_311_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_341_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_345_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_344_);
lean_dec_ref(v___x_337_);
if (v___x_345_ == 0)
{
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
goto v___jp_311_;
}
else
{
uint8_t v___x_346_; 
lean_del_object(v___x_309_);
v___x_346_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_296_, v_arg_326_);
lean_dec_ref(v_arg_326_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_321_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
if (lean_obj_tag(v_a_350_) == 0)
{
lean_dec_ref(v_arg_318_);
return v___x_349_;
}
else
{
lean_object* v_val_351_; lean_object* v___x_352_; 
lean_dec_ref_known(v___x_349_, 1);
v_val_351_ = lean_ctor_get(v_a_350_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v_a_350_, 1);
v___x_352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_318_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
if (lean_obj_tag(v_a_353_) == 0)
{
lean_dec(v_val_351_);
return v___x_352_;
}
else
{
lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_369_; 
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_352_, 0);
lean_dec(v_unused_370_);
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_369_;
goto v_resetjp_354_;
}
else
{
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_369_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_368_; 
v_val_357_ = lean_ctor_get(v_a_353_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_368_ == 0)
{
v___x_359_ = v_a_353_;
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_dec(v_a_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = l_Rat_add(v_val_351_, v_val_357_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_363_);
v___x_365_ = v___x_355_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
else
{
lean_dec(v_val_351_);
return v___x_352_;
}
}
}
else
{
lean_dec_ref(v_arg_318_);
return v___x_349_;
}
}
}
}
else
{
uint8_t v___x_371_; 
lean_dec_ref(v___x_337_);
lean_del_object(v___x_309_);
v___x_371_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_296_, v_arg_326_);
lean_dec_ref(v_arg_326_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_321_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
if (lean_obj_tag(v_a_375_) == 0)
{
lean_dec_ref(v_arg_318_);
return v___x_374_;
}
else
{
lean_object* v_val_376_; lean_object* v___x_377_; 
lean_dec_ref_known(v___x_374_, 1);
v_val_376_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_a_375_, 1);
v___x_377_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_318_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
if (lean_obj_tag(v_a_378_) == 0)
{
lean_dec(v_val_376_);
return v___x_377_;
}
else
{
lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_394_; 
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v___x_377_, 0);
lean_dec(v_unused_395_);
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
else
{
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_val_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_393_; 
v_val_382_ = lean_ctor_get(v_a_378_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_a_378_);
if (v_isSharedCheck_393_ == 0)
{
v___x_384_ = v_a_378_;
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_val_382_);
lean_dec(v_a_378_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = l_Rat_sub(v_val_376_, v_val_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_392_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_388_);
v___x_390_ = v___x_380_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
else
{
lean_dec(v_val_376_);
return v___x_377_;
}
}
}
else
{
lean_dec_ref(v_arg_318_);
return v___x_374_;
}
}
}
}
else
{
uint8_t v___x_396_; 
lean_dec_ref(v___x_337_);
lean_del_object(v___x_309_);
v___x_396_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_296_, v_arg_326_);
lean_dec_ref(v_arg_326_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_321_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
if (lean_obj_tag(v_a_400_) == 0)
{
lean_dec_ref(v_arg_318_);
return v___x_399_;
}
else
{
lean_object* v_val_401_; lean_object* v___x_402_; 
lean_dec_ref_known(v___x_399_, 1);
v_val_401_ = lean_ctor_get(v_a_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v_a_400_, 1);
v___x_402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_318_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
if (lean_obj_tag(v_a_403_) == 0)
{
lean_dec(v_val_401_);
return v___x_402_;
}
else
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_419_; 
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_420_);
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_val_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_418_; 
v_val_407_ = lean_ctor_get(v_a_403_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_418_ == 0)
{
v___x_409_ = v_a_403_;
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_val_407_);
lean_dec(v_a_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = l_Rat_mul(v_val_401_, v_val_407_);
lean_dec(v_val_401_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_413_);
v___x_415_ = v___x_405_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
else
{
lean_dec(v_val_401_);
return v___x_402_;
}
}
}
else
{
lean_dec_ref(v_arg_318_);
return v___x_399_;
}
}
}
}
else
{
uint8_t v___x_421_; 
lean_dec_ref(v___x_337_);
lean_del_object(v___x_309_);
v___x_421_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_296_, v_arg_326_);
if (v___x_421_ == 0)
{
uint8_t v___x_422_; 
v___x_422_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_296_, v_arg_326_);
lean_dec_ref(v_arg_326_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_318_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_getNatValue_x3f(v_arg_321_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec_ref(v_arg_321_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_455_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_455_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_455_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_455_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
if (lean_obj_tag(v_a_426_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec_ref(v_arg_318_);
v___x_430_ = lean_box(0);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v_val_434_; lean_object* v___x_435_; 
lean_del_object(v___x_428_);
v_val_434_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v_a_426_, 1);
v___x_435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_318_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
if (lean_obj_tag(v_a_436_) == 0)
{
lean_dec(v_val_434_);
return v___x_435_;
}
else
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_453_; 
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v___x_435_, 0);
lean_dec(v_unused_454_);
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_453_;
goto v_resetjp_437_;
}
else
{
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_453_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_val_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_452_; 
v_val_440_ = lean_ctor_get(v_a_436_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v_a_436_);
if (v_isSharedCheck_452_ == 0)
{
v___x_442_ = v_a_436_;
v_isShared_443_ = v_isSharedCheck_452_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_val_440_);
lean_dec(v_a_436_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_452_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_434_);
v___x_445_ = l_Rat_mul(v___x_444_, v_val_440_);
lean_dec_ref(v___x_444_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_447_ = v___x_442_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_447_);
v___x_449_ = v___x_438_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
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
}
}
else
{
lean_dec(v_val_434_);
return v___x_435_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec_ref(v_arg_318_);
v_a_456_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_425_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_425_);
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
else
{
lean_object* v___x_464_; 
lean_dec_ref(v_arg_326_);
v___x_464_ = l_Lean_Meta_getIntValue_x3f(v_arg_321_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_494_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_494_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_494_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_494_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
if (lean_obj_tag(v_a_465_) == 0)
{
lean_object* v___x_469_; lean_object* v___x_471_; 
lean_dec_ref(v_arg_318_);
v___x_469_ = lean_box(0);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
else
{
lean_object* v_val_473_; lean_object* v___x_474_; 
lean_del_object(v___x_467_);
v_val_473_ = lean_ctor_get(v_a_465_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v_a_465_, 1);
v___x_474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_318_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
if (lean_obj_tag(v_a_475_) == 0)
{
lean_dec(v_val_473_);
return v___x_474_;
}
else
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_492_; 
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v___x_474_, 0);
lean_dec(v_unused_493_);
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_492_;
goto v_resetjp_476_;
}
else
{
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_492_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_val_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_491_; 
v_val_479_ = lean_ctor_get(v_a_475_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_a_475_);
if (v_isSharedCheck_491_ == 0)
{
v___x_481_ = v_a_475_;
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_val_479_);
lean_dec(v_a_475_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = l_Rat_ofInt(v_val_473_);
v___x_484_ = l_Rat_mul(v___x_483_, v_val_479_);
lean_dec_ref(v___x_483_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_486_);
v___x_488_ = v___x_477_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
else
{
lean_dec(v_val_473_);
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v_arg_318_);
v_a_495_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_464_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_464_);
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
}
}
}
}
}
else
{
uint8_t v___x_503_; 
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_326_);
lean_del_object(v___x_309_);
v___x_503_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_296_, v_arg_321_);
lean_dec_ref(v_arg_321_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref(v_arg_318_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_296_, v_model_297_, v_arg_318_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
if (lean_obj_tag(v_a_507_) == 0)
{
return v___x_506_;
}
else
{
lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_506_, 0);
lean_dec(v_unused_524_);
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_523_;
goto v_resetjp_508_;
}
else
{
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_523_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_val_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_522_; 
v_val_511_ = lean_ctor_get(v_a_507_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_522_ == 0)
{
v___x_513_ = v_a_507_;
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_val_511_);
lean_dec(v_a_507_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = l_Rat_neg(v_val_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_517_);
v___x_519_ = v___x_509_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
}
else
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v___x_525_; 
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_326_);
lean_dec_ref(v_arg_318_);
lean_del_object(v___x_309_);
v___x_525_ = l_Lean_Meta_getNatValue_x3f(v_arg_321_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec_ref(v_arg_321_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_546_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_546_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_546_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_546_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
if (lean_obj_tag(v_a_526_) == 0)
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = lean_box(0);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v_val_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
v_val_534_ = lean_ctor_get(v_a_526_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_536_ = v_a_526_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_val_534_);
lean_dec(v_a_526_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_540_);
v___x_542_ = v___x_528_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_525_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_525_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
else
{
uint8_t v___x_555_; 
lean_dec_ref(v___x_322_);
lean_dec_ref(v_arg_321_);
lean_del_object(v___x_309_);
v___x_555_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_296_, v_arg_318_);
lean_dec_ref(v_arg_318_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
}
}
v___jp_311_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_box(0);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_306_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_306_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_569_, lean_object* v_model_570_, lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_569_, v_model_570_, v_e_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec_ref(v_model_570_);
lean_dec_ref(v_s_569_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_578_, lean_object* v_m_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_579_, v_a_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_582_, lean_object* v_m_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_582_, v_m_583_, v_a_584_);
lean_dec_ref(v_a_584_);
lean_dec_ref(v_m_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_nat_to_int(v_a_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_588_, lean_object* v_a_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_589_, v_x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_592_, lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_592_, v_a_593_, v_x_594_);
lean_dec(v_x_594_);
lean_dec_ref(v_a_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_596_, lean_object* v_s_597_, lean_object* v_model_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_597_, v_model_598_, v_e_596_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_605_, lean_object* v_s_606_, lean_object* v_model_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_605_, v_s_606_, v_model_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec_ref(v_model_607_);
lean_dec_ref(v_s_606_);
return v_res_613_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
else
{
lean_object* v_key_617_; lean_object* v_tail_618_; uint8_t v___x_619_; 
v_key_617_ = lean_ctor_get(v_x_615_, 0);
v_tail_618_ = lean_ctor_get(v_x_615_, 2);
v___x_619_ = lean_expr_eqv(v_key_617_, v_a_614_);
if (v___x_619_ == 0)
{
v_x_615_ = v_tail_618_;
goto _start;
}
else
{
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_621_, lean_object* v_x_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_621_, v_x_622_);
lean_dec(v_x_622_);
lean_dec_ref(v_a_621_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_buckets_627_; lean_object* v___x_628_; uint64_t v___x_629_; uint64_t v___x_630_; uint64_t v___x_631_; uint64_t v_fold_632_; uint64_t v___x_633_; uint64_t v___x_634_; uint64_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_buckets_627_ = lean_ctor_get(v_m_625_, 1);
v___x_628_ = lean_array_get_size(v_buckets_627_);
v___x_629_ = l_Lean_Expr_hash(v_a_626_);
v___x_630_ = 32ULL;
v___x_631_ = lean_uint64_shift_right(v___x_629_, v___x_630_);
v_fold_632_ = lean_uint64_xor(v___x_629_, v___x_631_);
v___x_633_ = 16ULL;
v___x_634_ = lean_uint64_shift_right(v_fold_632_, v___x_633_);
v___x_635_ = lean_uint64_xor(v_fold_632_, v___x_634_);
v___x_636_ = lean_uint64_to_usize(v___x_635_);
v___x_637_ = lean_usize_of_nat(v___x_628_);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_sub(v___x_637_, v___x_638_);
v___x_640_ = lean_usize_land(v___x_636_, v___x_639_);
v___x_641_ = lean_array_uget_borrowed(v_buckets_627_, v___x_640_);
v___x_642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_626_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_643_, lean_object* v_a_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_643_, v_a_644_);
lean_dec_ref(v_a_644_);
lean_dec_ref(v_m_643_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v___x_647_, lean_object* v_goal_648_, lean_object* v_structId_649_, lean_object* v_as_650_, size_t v_sz_651_, size_t v_i_652_, lean_object* v_b_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_b_653_);
return v___x_660_;
}
else
{
lean_object* v_snd_661_; lean_object* v_a_662_; lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_693_; 
v_snd_661_ = lean_ctor_get(v_b_653_, 1);
lean_inc(v_snd_661_);
lean_dec_ref(v_b_653_);
v_a_662_ = lean_array_uget(v_as_650_, v_i_652_);
v_fst_663_ = lean_ctor_get(v_a_662_, 0);
v_snd_664_ = lean_ctor_get(v_a_662_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_a_662_);
if (v_isSharedCheck_693_ == 0)
{
v___x_666_ = v_a_662_;
v_isShared_667_ = v_isSharedCheck_693_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_snd_664_);
lean_inc(v_fst_663_);
lean_dec(v_a_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_693_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_a_670_; uint8_t v___y_678_; uint8_t v___x_691_; 
v___x_668_ = lean_box(0);
v___x_691_ = lean_nat_dec_eq(v_structId_649_, v_snd_664_);
lean_dec(v_snd_664_);
if (v___x_691_ == 0)
{
v___y_678_ = v___x_691_;
goto v___jp_677_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_661_, v_fst_663_);
if (v___x_692_ == 0)
{
v___y_678_ = v___x_691_;
goto v___jp_677_;
}
else
{
lean_dec(v_fst_663_);
v_a_670_ = v_snd_661_;
goto v___jp_669_;
}
}
v___jp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_a_670_);
lean_ctor_set(v___x_666_, 0, v___x_668_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_a_670_);
v___x_672_ = v_reuseFailAlloc_676_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
size_t v___x_673_; size_t v___x_674_; 
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_652_, v___x_673_);
v_i_652_ = v___x_674_;
v_b_653_ = v___x_672_;
goto _start;
}
}
v___jp_677_:
{
if (v___y_678_ == 0)
{
lean_dec(v_fst_663_);
v_a_670_ = v_snd_661_;
goto v___jp_669_;
}
else
{
lean_object* v___x_679_; 
lean_inc(v_fst_663_);
v___x_679_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_647_, v_snd_661_, v_fst_663_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
if (lean_obj_tag(v_a_680_) == 1)
{
lean_object* v_val_681_; lean_object* v___x_682_; 
v_val_681_ = lean_ctor_get(v_a_680_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v_a_680_, 1);
v___x_682_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_648_, v_fst_663_, v_val_681_, v_snd_661_);
v_a_670_ = v___x_682_;
goto v___jp_669_;
}
else
{
lean_dec(v_a_680_);
lean_dec(v_fst_663_);
v_a_670_ = v_snd_661_;
goto v___jp_669_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_del_object(v___x_666_);
lean_dec(v_fst_663_);
lean_dec(v_snd_661_);
v_a_683_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_679_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_679_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v___x_694_, lean_object* v_goal_695_, lean_object* v_structId_696_, lean_object* v_as_697_, lean_object* v_sz_698_, lean_object* v_i_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
size_t v_sz_boxed_706_; size_t v_i_boxed_707_; lean_object* v_res_708_; 
v_sz_boxed_706_ = lean_unbox_usize(v_sz_698_);
lean_dec(v_sz_698_);
v_i_boxed_707_ = lean_unbox_usize(v_i_699_);
lean_dec(v_i_699_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_694_, v_goal_695_, v_structId_696_, v_as_697_, v_sz_boxed_706_, v_i_boxed_707_, v_b_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v_as_697_);
lean_dec(v_structId_696_);
lean_dec_ref(v_goal_695_);
lean_dec_ref(v___x_694_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v___x_709_, lean_object* v_goal_710_, lean_object* v_structId_711_, lean_object* v_as_712_, size_t v_sz_713_, size_t v_i_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_714_, v_sz_713_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_b_715_);
return v___x_722_;
}
else
{
lean_object* v_snd_723_; lean_object* v_a_724_; lean_object* v_fst_725_; lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_755_; 
v_snd_723_ = lean_ctor_get(v_b_715_, 1);
lean_inc(v_snd_723_);
lean_dec_ref(v_b_715_);
v_a_724_ = lean_array_uget(v_as_712_, v_i_714_);
v_fst_725_ = lean_ctor_get(v_a_724_, 0);
v_snd_726_ = lean_ctor_get(v_a_724_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_755_ == 0)
{
v___x_728_ = v_a_724_;
v_isShared_729_ = v_isSharedCheck_755_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_inc(v_fst_725_);
lean_dec(v_a_724_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_755_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v_a_732_; uint8_t v___y_740_; uint8_t v___x_753_; 
v___x_730_ = lean_box(0);
v___x_753_ = lean_nat_dec_eq(v_structId_711_, v_snd_726_);
lean_dec(v_snd_726_);
if (v___x_753_ == 0)
{
v___y_740_ = v___x_753_;
goto v___jp_739_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_723_, v_fst_725_);
if (v___x_754_ == 0)
{
v___y_740_ = v___x_753_;
goto v___jp_739_;
}
else
{
lean_dec(v_fst_725_);
v_a_732_ = v_snd_723_;
goto v___jp_731_;
}
}
v___jp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_a_732_);
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_734_ = v___x_728_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_732_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_714_, v___x_735_);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_709_, v_goal_710_, v_structId_711_, v_as_712_, v_sz_713_, v___x_736_, v___x_734_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
return v___x_737_;
}
}
v___jp_739_:
{
if (v___y_740_ == 0)
{
lean_dec(v_fst_725_);
v_a_732_ = v_snd_723_;
goto v___jp_731_;
}
else
{
lean_object* v___x_741_; 
lean_inc(v_fst_725_);
v___x_741_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_709_, v_snd_723_, v_fst_725_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
if (lean_obj_tag(v_a_742_) == 1)
{
lean_object* v_val_743_; lean_object* v___x_744_; 
v_val_743_ = lean_ctor_get(v_a_742_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v_a_742_, 1);
v___x_744_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_710_, v_fst_725_, v_val_743_, v_snd_723_);
v_a_732_ = v___x_744_;
goto v___jp_731_;
}
else
{
lean_dec(v_a_742_);
lean_dec(v_fst_725_);
v_a_732_ = v_snd_723_;
goto v___jp_731_;
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_del_object(v___x_728_);
lean_dec(v_fst_725_);
lean_dec(v_snd_723_);
v_a_745_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_741_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_741_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v___x_756_, lean_object* v_goal_757_, lean_object* v_structId_758_, lean_object* v_as_759_, lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v_sz_boxed_768_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_769_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_756_, v_goal_757_, v_structId_758_, v_as_759_, v_sz_boxed_768_, v_i_boxed_769_, v_b_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_as_759_);
lean_dec(v_structId_758_);
lean_dec_ref(v_goal_757_);
lean_dec_ref(v___x_756_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_771_, lean_object* v___x_772_, lean_object* v_goal_773_, lean_object* v_structId_774_, lean_object* v_n_775_, lean_object* v_b_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
if (lean_obj_tag(v_n_775_) == 0)
{
lean_object* v_cs_782_; lean_object* v___x_783_; lean_object* v___x_784_; size_t v_sz_785_; size_t v___x_786_; lean_object* v___x_787_; 
v_cs_782_ = lean_ctor_get(v_n_775_, 0);
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v_b_776_);
v_sz_785_ = lean_array_size(v_cs_782_);
v___x_786_ = ((size_t)0ULL);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_771_, v___x_772_, v_goal_773_, v_structId_774_, v_cs_782_, v_sz_785_, v___x_786_, v___x_784_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_802_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_802_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_802_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_802_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_fst_792_; 
v_fst_792_ = lean_ctor_get(v_a_788_, 0);
if (lean_obj_tag(v_fst_792_) == 0)
{
lean_object* v_snd_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v_snd_793_ = lean_ctor_get(v_a_788_, 1);
lean_inc(v_snd_793_);
lean_dec(v_a_788_);
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v_snd_793_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_794_);
v___x_796_ = v___x_790_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
lean_object* v_val_798_; lean_object* v___x_800_; 
lean_inc_ref(v_fst_792_);
lean_dec(v_a_788_);
v_val_798_ = lean_ctor_get(v_fst_792_, 0);
lean_inc(v_val_798_);
lean_dec_ref_known(v_fst_792_, 1);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v_val_798_);
v___x_800_ = v___x_790_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_val_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v_a_803_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___x_787_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_787_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_vs_811_; lean_object* v___x_812_; lean_object* v___x_813_; size_t v_sz_814_; size_t v___x_815_; lean_object* v___x_816_; 
v_vs_811_ = lean_ctor_get(v_n_775_, 0);
v___x_812_ = lean_box(0);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_b_776_);
v_sz_814_ = lean_array_size(v_vs_811_);
v___x_815_ = ((size_t)0ULL);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_772_, v_goal_773_, v_structId_774_, v_vs_811_, v_sz_814_, v___x_815_, v___x_813_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_831_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_831_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_831_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_831_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_fst_821_; 
v_fst_821_ = lean_ctor_get(v_a_817_, 0);
if (lean_obj_tag(v_fst_821_) == 0)
{
lean_object* v_snd_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v_snd_822_ = lean_ctor_get(v_a_817_, 1);
lean_inc(v_snd_822_);
lean_dec(v_a_817_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_snd_822_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_823_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v_val_827_; lean_object* v___x_829_; 
lean_inc_ref(v_fst_821_);
lean_dec(v_a_817_);
v_val_827_ = lean_ctor_get(v_fst_821_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v_fst_821_, 1);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v_val_827_);
v___x_829_ = v___x_819_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_val_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_816_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_816_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_840_, lean_object* v___x_841_, lean_object* v_goal_842_, lean_object* v_structId_843_, lean_object* v_as_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_b_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_b_847_);
return v___x_854_;
}
else
{
lean_object* v_snd_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_889_; 
v_snd_855_ = lean_ctor_get(v_b_847_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_b_847_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_b_847_, 0);
lean_dec(v_unused_890_);
v___x_857_ = v_b_847_;
v_isShared_858_ = v_isSharedCheck_889_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_snd_855_);
lean_dec(v_b_847_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_889_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_array_uget_borrowed(v_as_844_, v_i_846_);
lean_inc(v_snd_855_);
v___x_860_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_840_, v___x_841_, v_goal_842_, v_structId_843_, v_a_859_, v_snd_855_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_880_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_880_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
if (lean_obj_tag(v_a_861_) == 0)
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_a_861_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_865_);
v___x_867_ = v___x_857_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_855_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_867_);
v___x_869_ = v___x_863_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
lean_del_object(v___x_863_);
lean_dec(v_snd_855_);
v_a_872_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v_a_861_, 1);
v___x_873_ = lean_box(0);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v_a_872_);
lean_ctor_set(v___x_857_, 0, v___x_873_);
v___x_875_ = v___x_857_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_a_872_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
size_t v___x_876_; size_t v___x_877_; 
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_846_, v___x_876_);
v_i_846_ = v___x_877_;
v_b_847_ = v___x_875_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_del_object(v___x_857_);
lean_dec(v_snd_855_);
v_a_881_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_860_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_860_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_891_, lean_object* v___x_892_, lean_object* v_goal_893_, lean_object* v_structId_894_, lean_object* v_as_895_, lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_b_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_sz_boxed_904_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_905_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_891_, v___x_892_, v_goal_893_, v_structId_894_, v_as_895_, v_sz_boxed_904_, v_i_boxed_905_, v_b_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec_ref(v_as_895_);
lean_dec(v_structId_894_);
lean_dec_ref(v_goal_893_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v_init_891_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_907_, lean_object* v___x_908_, lean_object* v_goal_909_, lean_object* v_structId_910_, lean_object* v_n_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_907_, v___x_908_, v_goal_909_, v_structId_910_, v_n_911_, v_b_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_n_911_);
lean_dec(v_structId_910_);
lean_dec_ref(v_goal_909_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v_init_907_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v___x_919_, lean_object* v_goal_920_, lean_object* v_structId_921_, lean_object* v_as_922_, size_t v_sz_923_, size_t v_i_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_lt(v_i_924_, v_sz_923_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_b_925_);
return v___x_932_;
}
else
{
lean_object* v_snd_933_; lean_object* v_a_934_; lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_965_; 
v_snd_933_ = lean_ctor_get(v_b_925_, 1);
lean_inc(v_snd_933_);
lean_dec_ref(v_b_925_);
v_a_934_ = lean_array_uget(v_as_922_, v_i_924_);
v_fst_935_ = lean_ctor_get(v_a_934_, 0);
v_snd_936_ = lean_ctor_get(v_a_934_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_934_);
if (v_isSharedCheck_965_ == 0)
{
v___x_938_ = v_a_934_;
v_isShared_939_ = v_isSharedCheck_965_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snd_936_);
lean_inc(v_fst_935_);
lean_dec(v_a_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_965_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v_a_942_; uint8_t v___y_950_; uint8_t v___x_963_; 
v___x_940_ = lean_box(0);
v___x_963_ = lean_nat_dec_eq(v_structId_921_, v_snd_936_);
lean_dec(v_snd_936_);
if (v___x_963_ == 0)
{
v___y_950_ = v___x_963_;
goto v___jp_949_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_933_, v_fst_935_);
if (v___x_964_ == 0)
{
v___y_950_ = v___x_963_;
goto v___jp_949_;
}
else
{
lean_dec(v_fst_935_);
v_a_942_ = v_snd_933_;
goto v___jp_941_;
}
}
v___jp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_a_942_);
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_a_942_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
size_t v___x_945_; size_t v___x_946_; 
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_add(v_i_924_, v___x_945_);
v_i_924_ = v___x_946_;
v_b_925_ = v___x_944_;
goto _start;
}
}
v___jp_949_:
{
if (v___y_950_ == 0)
{
lean_dec(v_fst_935_);
v_a_942_ = v_snd_933_;
goto v___jp_941_;
}
else
{
lean_object* v___x_951_; 
lean_inc(v_fst_935_);
v___x_951_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_919_, v_snd_933_, v_fst_935_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
if (lean_obj_tag(v_a_952_) == 1)
{
lean_object* v_val_953_; lean_object* v___x_954_; 
v_val_953_ = lean_ctor_get(v_a_952_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v_a_952_, 1);
v___x_954_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_920_, v_fst_935_, v_val_953_, v_snd_933_);
v_a_942_ = v___x_954_;
goto v___jp_941_;
}
else
{
lean_dec(v_a_952_);
lean_dec(v_fst_935_);
v_a_942_ = v_snd_933_;
goto v___jp_941_;
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_938_);
lean_dec(v_fst_935_);
lean_dec(v_snd_933_);
v_a_955_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_951_);
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
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v___x_966_, lean_object* v_goal_967_, lean_object* v_structId_968_, lean_object* v_as_969_, lean_object* v_sz_970_, lean_object* v_i_971_, lean_object* v_b_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
size_t v_sz_boxed_978_; size_t v_i_boxed_979_; lean_object* v_res_980_; 
v_sz_boxed_978_ = lean_unbox_usize(v_sz_970_);
lean_dec(v_sz_970_);
v_i_boxed_979_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_res_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_966_, v_goal_967_, v_structId_968_, v_as_969_, v_sz_boxed_978_, v_i_boxed_979_, v_b_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_as_969_);
lean_dec(v_structId_968_);
lean_dec_ref(v_goal_967_);
lean_dec_ref(v___x_966_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v___x_981_, lean_object* v_goal_982_, lean_object* v_structId_983_, lean_object* v_as_984_, size_t v_sz_985_, size_t v_i_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_lt(v_i_986_, v_sz_985_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_b_987_);
return v___x_994_;
}
else
{
lean_object* v_snd_995_; lean_object* v_a_996_; lean_object* v_fst_997_; lean_object* v_snd_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1027_; 
v_snd_995_ = lean_ctor_get(v_b_987_, 1);
lean_inc(v_snd_995_);
lean_dec_ref(v_b_987_);
v_a_996_ = lean_array_uget(v_as_984_, v_i_986_);
v_fst_997_ = lean_ctor_get(v_a_996_, 0);
v_snd_998_ = lean_ctor_get(v_a_996_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_a_996_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1000_ = v_a_996_;
v_isShared_1001_ = v_isSharedCheck_1027_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snd_998_);
lean_inc(v_fst_997_);
lean_dec(v_a_996_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1027_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v_a_1004_; uint8_t v___y_1012_; uint8_t v___x_1025_; 
v___x_1002_ = lean_box(0);
v___x_1025_ = lean_nat_dec_eq(v_structId_983_, v_snd_998_);
lean_dec(v_snd_998_);
if (v___x_1025_ == 0)
{
v___y_1012_ = v___x_1025_;
goto v___jp_1011_;
}
else
{
uint8_t v___x_1026_; 
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_995_, v_fst_997_);
if (v___x_1026_ == 0)
{
v___y_1012_ = v___x_1025_;
goto v___jp_1011_;
}
else
{
lean_dec(v_fst_997_);
v_a_1004_ = v_snd_995_;
goto v___jp_1003_;
}
}
v___jp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v_a_1004_);
lean_ctor_set(v___x_1000_, 0, v___x_1002_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_a_1004_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_986_, v___x_1007_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_981_, v_goal_982_, v_structId_983_, v_as_984_, v_sz_985_, v___x_1008_, v___x_1006_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
return v___x_1009_;
}
}
v___jp_1011_:
{
if (v___y_1012_ == 0)
{
lean_dec(v_fst_997_);
v_a_1004_ = v_snd_995_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1013_; 
lean_inc(v_fst_997_);
v___x_1013_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_981_, v_snd_995_, v_fst_997_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
if (lean_obj_tag(v_a_1014_) == 1)
{
lean_object* v_val_1015_; lean_object* v___x_1016_; 
v_val_1015_ = lean_ctor_get(v_a_1014_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v_a_1014_, 1);
v___x_1016_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_982_, v_fst_997_, v_val_1015_, v_snd_995_);
v_a_1004_ = v___x_1016_;
goto v___jp_1003_;
}
else
{
lean_dec(v_a_1014_);
lean_dec(v_fst_997_);
v_a_1004_ = v_snd_995_;
goto v___jp_1003_;
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_del_object(v___x_1000_);
lean_dec(v_fst_997_);
lean_dec(v_snd_995_);
v_a_1017_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1013_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v___x_1028_, lean_object* v_goal_1029_, lean_object* v_structId_1030_, lean_object* v_as_1031_, lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
size_t v_sz_boxed_1040_; size_t v_i_boxed_1041_; lean_object* v_res_1042_; 
v_sz_boxed_1040_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1028_, v_goal_1029_, v_structId_1030_, v_as_1031_, v_sz_boxed_1040_, v_i_boxed_1041_, v_b_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v_as_1031_);
lean_dec(v_structId_1030_);
lean_dec_ref(v_goal_1029_);
lean_dec_ref(v___x_1028_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v___x_1043_, lean_object* v_goal_1044_, lean_object* v_structId_1045_, lean_object* v_t_1046_, lean_object* v_init_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_root_1053_; lean_object* v_tail_1054_; lean_object* v___x_1055_; 
v_root_1053_ = lean_ctor_get(v_t_1046_, 0);
v_tail_1054_ = lean_ctor_get(v_t_1046_, 1);
lean_inc_ref(v_init_1047_);
v___x_1055_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1047_, v___x_1043_, v_goal_1044_, v_structId_1045_, v_root_1053_, v_init_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec_ref(v_init_1047_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1092_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1092_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1092_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
if (lean_obj_tag(v_a_1056_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v_a_1056_, 1);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_a_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; size_t v_sz_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
lean_del_object(v___x_1058_);
v_a_1064_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v_a_1056_, 1);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_a_1064_);
v_sz_1067_ = lean_array_size(v_tail_1054_);
v___x_1068_ = ((size_t)0ULL);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_1043_, v_goal_1044_, v_structId_1045_, v_tail_1054_, v_sz_1067_, v___x_1068_, v___x_1066_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1083_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1083_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1083_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_fst_1074_; 
v_fst_1074_ = lean_ctor_get(v_a_1070_, 0);
if (lean_obj_tag(v_fst_1074_) == 0)
{
lean_object* v_snd_1075_; lean_object* v___x_1077_; 
v_snd_1075_ = lean_ctor_get(v_a_1070_, 1);
lean_inc(v_snd_1075_);
lean_dec(v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_snd_1075_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_snd_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
else
{
lean_object* v_val_1079_; lean_object* v___x_1081_; 
lean_inc_ref(v_fst_1074_);
lean_dec(v_a_1070_);
v_val_1079_ = lean_ctor_get(v_fst_1074_, 0);
lean_inc(v_val_1079_);
lean_dec_ref_known(v_fst_1074_, 1);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_val_1079_);
v___x_1081_ = v___x_1072_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_val_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v_a_1084_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1069_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1069_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1055_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1055_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v___x_1101_, lean_object* v_goal_1102_, lean_object* v_structId_1103_, lean_object* v_t_1104_, lean_object* v_init_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1101_, v_goal_1102_, v_structId_1103_, v_t_1104_, v_init_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_t_1104_);
lean_dec(v_structId_1103_);
lean_dec_ref(v_goal_1102_);
lean_dec_ref(v___x_1101_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1112_, lean_object* v_structId_1113_, lean_object* v_model_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1121_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1120_, v_goal_1112_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_structs_1123_; lean_object* v_exprToStructIdEntries_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v_structs_1123_ = lean_ctor_get(v_a_1122_, 0);
lean_inc_ref(v_structs_1123_);
v_exprToStructIdEntries_1124_ = lean_ctor_get(v_a_1122_, 3);
lean_inc_ref(v_exprToStructIdEntries_1124_);
lean_dec(v_a_1122_);
v___x_1125_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1126_ = lean_array_get(v___x_1125_, v_structs_1123_, v_structId_1113_);
lean_dec_ref(v_structs_1123_);
v___x_1127_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1126_, v_goal_1112_, v_structId_1113_, v_exprToStructIdEntries_1124_, v_model_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec_ref(v_exprToStructIdEntries_1124_);
lean_dec(v___x_1126_);
return v___x_1127_;
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_model_1114_);
v_a_1128_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1130_ = v___x_1121_;
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1121_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_ref_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v_ref_1132_ = lean_ctor_get(v_a_1117_, 5);
v___x_1133_ = lean_io_error_to_string(v_a_1128_);
v___x_1134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofFormat(v___x_1134_);
lean_inc(v_ref_1132_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_ref_1132_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1136_);
v___x_1138_ = v___x_1130_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1141_, lean_object* v_structId_1142_, lean_object* v_model_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1141_, v_structId_1142_, v_model_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_structId_1142_);
lean_dec_ref(v_goal_1141_);
return v_res_1149_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1150_, lean_object* v_m_1151_, lean_object* v_a_1152_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1151_, v_a_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_m_1155_, lean_object* v_a_1156_){
_start:
{
uint8_t v_res_1157_; lean_object* v_r_1158_; 
v_res_1157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1154_, v_m_1155_, v_a_1156_);
lean_dec_ref(v_a_1156_);
lean_dec_ref(v_m_1155_);
v_r_1158_ = lean_box(v_res_1157_);
return v_r_1158_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1159_, lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1160_, v_x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1163_, lean_object* v_a_1164_, lean_object* v_x_1165_){
_start:
{
uint8_t v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1163_, v_a_1164_, v_x_1165_);
lean_dec(v_x_1165_);
lean_dec_ref(v_a_1164_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1168_, lean_object* v___x_1169_, lean_object* v_as_1170_, size_t v_sz_1171_, size_t v_i_1172_, lean_object* v_b_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_lt(v_i_1172_, v_sz_1171_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_dec_ref(v___x_1169_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_b_1173_);
return v___x_1180_;
}
else
{
lean_object* v_snd_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1222_; 
v_snd_1181_ = lean_ctor_get(v_b_1173_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_b_1173_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_b_1173_, 0);
lean_dec(v_unused_1223_);
v___x_1183_ = v_b_1173_;
v_isShared_1184_ = v_isSharedCheck_1222_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_snd_1181_);
lean_dec(v_b_1173_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1222_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_a_1185_; lean_object* v___x_1186_; 
v_a_1185_ = lean_array_uget_borrowed(v_as_1170_, v_i_1172_);
lean_inc(v_a_1185_);
v___x_1186_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1168_, v_a_1185_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; lean_object* v_a_1190_; uint8_t v___x_1197_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1188_ = lean_box(0);
v___x_1197_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1187_);
if (v___x_1197_ == 0)
{
lean_dec(v_a_1187_);
v_a_1190_ = v_snd_1181_;
goto v___jp_1189_;
}
else
{
lean_object* v_type_1198_; lean_object* v___x_1199_; 
v_type_1198_ = lean_ctor_get(v___x_1169_, 2);
lean_inc(v_a_1187_);
lean_inc_ref(v_type_1198_);
v___x_1199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1198_, v_a_1187_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; uint8_t v___x_1201_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = lean_unbox(v_a_1200_);
lean_dec(v_a_1200_);
if (v___x_1201_ == 0)
{
lean_dec(v_a_1187_);
v_a_1190_ = v_snd_1181_;
goto v___jp_1189_;
}
else
{
lean_object* v_self_1202_; lean_object* v___x_1203_; 
v_self_1202_ = lean_ctor_get(v_a_1187_, 0);
lean_inc_ref(v_self_1202_);
lean_dec(v_a_1187_);
v___x_1203_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1169_, v_self_1202_);
if (lean_obj_tag(v___x_1203_) == 1)
{
lean_object* v_val_1204_; lean_object* v___x_1205_; 
v_val_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1205_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1168_, v_self_1202_, v_val_1204_, v_snd_1181_);
v_a_1190_ = v___x_1205_;
goto v___jp_1189_;
}
else
{
lean_dec(v___x_1203_);
lean_dec_ref(v_self_1202_);
v_a_1190_ = v_snd_1181_;
goto v___jp_1189_;
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1187_);
lean_del_object(v___x_1183_);
lean_dec(v_snd_1181_);
lean_dec_ref(v___x_1169_);
v_a_1206_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1199_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1199_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
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
v___jp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_a_1190_);
lean_ctor_set(v___x_1183_, 0, v___x_1188_);
v___x_1192_ = v___x_1183_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_a_1190_);
v___x_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
size_t v___x_1193_; size_t v___x_1194_; 
v___x_1193_ = ((size_t)1ULL);
v___x_1194_ = lean_usize_add(v_i_1172_, v___x_1193_);
v_i_1172_ = v___x_1194_;
v_b_1173_ = v___x_1192_;
goto _start;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_del_object(v___x_1183_);
lean_dec(v_snd_1181_);
lean_dec_ref(v___x_1169_);
v_a_1214_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1186_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1186_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1224_, lean_object* v___x_1225_, lean_object* v_as_1226_, lean_object* v_sz_1227_, lean_object* v_i_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
size_t v_sz_boxed_1235_; size_t v_i_boxed_1236_; lean_object* v_res_1237_; 
v_sz_boxed_1235_ = lean_unbox_usize(v_sz_1227_);
lean_dec(v_sz_1227_);
v_i_boxed_1236_ = lean_unbox_usize(v_i_1228_);
lean_dec(v_i_1228_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1224_, v___x_1225_, v_as_1226_, v_sz_boxed_1235_, v_i_boxed_1236_, v_b_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_as_1226_);
lean_dec_ref(v_goal_1224_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1238_, lean_object* v___x_1239_, lean_object* v_as_1240_, size_t v_sz_1241_, size_t v_i_1242_, lean_object* v_b_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_usize_dec_lt(v_i_1242_, v_sz_1241_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; 
lean_dec_ref(v___x_1239_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_b_1243_);
return v___x_1250_;
}
else
{
lean_object* v_snd_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1292_; 
v_snd_1251_ = lean_ctor_get(v_b_1243_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_b_1243_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v_b_1243_, 0);
lean_dec(v_unused_1293_);
v___x_1253_ = v_b_1243_;
v_isShared_1254_ = v_isSharedCheck_1292_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_snd_1251_);
lean_dec(v_b_1243_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1292_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_a_1255_; lean_object* v___x_1256_; 
v_a_1255_ = lean_array_uget_borrowed(v_as_1240_, v_i_1242_);
lean_inc(v_a_1255_);
v___x_1256_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1238_, v_a_1255_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v_a_1260_; uint8_t v___x_1267_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = lean_box(0);
v___x_1267_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1257_);
if (v___x_1267_ == 0)
{
lean_dec(v_a_1257_);
v_a_1260_ = v_snd_1251_;
goto v___jp_1259_;
}
else
{
lean_object* v_type_1268_; lean_object* v___x_1269_; 
v_type_1268_ = lean_ctor_get(v___x_1239_, 2);
lean_inc(v_a_1257_);
lean_inc_ref(v_type_1268_);
v___x_1269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1268_, v_a_1257_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = lean_unbox(v_a_1270_);
lean_dec(v_a_1270_);
if (v___x_1271_ == 0)
{
lean_dec(v_a_1257_);
v_a_1260_ = v_snd_1251_;
goto v___jp_1259_;
}
else
{
lean_object* v_self_1272_; lean_object* v___x_1273_; 
v_self_1272_ = lean_ctor_get(v_a_1257_, 0);
lean_inc_ref(v_self_1272_);
lean_dec(v_a_1257_);
v___x_1273_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1239_, v_self_1272_);
if (lean_obj_tag(v___x_1273_) == 1)
{
lean_object* v_val_1274_; lean_object* v___x_1275_; 
v_val_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1275_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1238_, v_self_1272_, v_val_1274_, v_snd_1251_);
v_a_1260_ = v___x_1275_;
goto v___jp_1259_;
}
else
{
lean_dec(v___x_1273_);
lean_dec_ref(v_self_1272_);
v_a_1260_ = v_snd_1251_;
goto v___jp_1259_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_a_1257_);
lean_del_object(v___x_1253_);
lean_dec(v_snd_1251_);
lean_dec_ref(v___x_1239_);
v_a_1276_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1269_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1269_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
v___jp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v_a_1260_);
lean_ctor_set(v___x_1253_, 0, v___x_1258_);
v___x_1262_ = v___x_1253_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_a_1260_);
v___x_1262_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_i_1242_, v___x_1263_);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1238_, v___x_1239_, v_as_1240_, v_sz_1241_, v___x_1264_, v___x_1262_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1265_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_del_object(v___x_1253_);
lean_dec(v_snd_1251_);
lean_dec_ref(v___x_1239_);
v_a_1284_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1256_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1256_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1294_, lean_object* v___x_1295_, lean_object* v_as_1296_, lean_object* v_sz_1297_, lean_object* v_i_1298_, lean_object* v_b_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
size_t v_sz_boxed_1305_; size_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1297_);
lean_dec(v_sz_1297_);
v_i_boxed_1306_ = lean_unbox_usize(v_i_1298_);
lean_dec(v_i_1298_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1294_, v___x_1295_, v_as_1296_, v_sz_boxed_1305_, v_i_boxed_1306_, v_b_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec_ref(v_as_1296_);
lean_dec_ref(v_goal_1294_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1308_, lean_object* v_goal_1309_, lean_object* v___x_1310_, lean_object* v_n_1311_, lean_object* v_b_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
if (lean_obj_tag(v_n_1311_) == 0)
{
lean_object* v_cs_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v_cs_1318_ = lean_ctor_get(v_n_1311_, 0);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_b_1312_);
v_sz_1321_ = lean_array_size(v_cs_1318_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1308_, v_goal_1309_, v___x_1310_, v_cs_1318_, v_sz_1321_, v___x_1322_, v___x_1320_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1338_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1338_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_fst_1328_; 
v_fst_1328_ = lean_ctor_get(v_a_1324_, 0);
if (lean_obj_tag(v_fst_1328_) == 0)
{
lean_object* v_snd_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v_snd_1329_ = lean_ctor_get(v_a_1324_, 1);
lean_inc(v_snd_1329_);
lean_dec(v_a_1324_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_snd_1329_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1330_);
v___x_1332_ = v___x_1326_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v_val_1334_; lean_object* v___x_1336_; 
lean_inc_ref(v_fst_1328_);
lean_dec(v_a_1324_);
v_val_1334_ = lean_ctor_get(v_fst_1328_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v_fst_1328_, 1);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_val_1334_);
v___x_1336_ = v___x_1326_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_val_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
v_a_1339_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1323_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1323_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_vs_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v_vs_1347_ = lean_ctor_get(v_n_1311_, 0);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v_b_1312_);
v_sz_1350_ = lean_array_size(v_vs_1347_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1309_, v___x_1310_, v_vs_1347_, v_sz_1350_, v___x_1351_, v___x_1349_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1367_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_fst_1357_; 
v_fst_1357_ = lean_ctor_get(v_a_1353_, 0);
if (lean_obj_tag(v_fst_1357_) == 0)
{
lean_object* v_snd_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v_snd_1358_ = lean_ctor_get(v_a_1353_, 1);
lean_inc(v_snd_1358_);
lean_dec(v_a_1353_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_snd_1358_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1361_ = v___x_1355_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
else
{
lean_object* v_val_1363_; lean_object* v___x_1365_; 
lean_inc_ref(v_fst_1357_);
lean_dec(v_a_1353_);
v_val_1363_ = lean_ctor_get(v_fst_1357_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v_fst_1357_, 1);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_val_1363_);
v___x_1365_ = v___x_1355_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_val_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1352_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1352_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1376_, lean_object* v_goal_1377_, lean_object* v___x_1378_, lean_object* v_as_1379_, size_t v_sz_1380_, size_t v_i_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_lt(v_i_1381_, v_sz_1380_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref(v___x_1378_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_b_1382_);
return v___x_1389_;
}
else
{
lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1424_; 
v_snd_1390_ = lean_ctor_get(v_b_1382_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_b_1382_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v_b_1382_, 0);
lean_dec(v_unused_1425_);
v___x_1392_ = v_b_1382_;
v_isShared_1393_ = v_isSharedCheck_1424_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_dec(v_b_1382_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1424_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_array_uget_borrowed(v_as_1379_, v_i_1381_);
lean_inc(v_snd_1390_);
lean_inc_ref(v___x_1378_);
v___x_1395_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1376_, v_goal_1377_, v___x_1378_, v_a_1394_, v_snd_1390_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1415_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1415_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1415_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
if (lean_obj_tag(v_a_1396_) == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_dec_ref(v___x_1378_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1396_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1400_);
v___x_1402_ = v___x_1392_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_snd_1390_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1402_);
v___x_1404_ = v___x_1398_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_del_object(v___x_1398_);
lean_dec(v_snd_1390_);
v_a_1407_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v_a_1396_, 1);
v___x_1408_ = lean_box(0);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v_a_1407_);
lean_ctor_set(v___x_1392_, 0, v___x_1408_);
v___x_1410_ = v___x_1392_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_a_1407_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
size_t v___x_1411_; size_t v___x_1412_; 
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_add(v_i_1381_, v___x_1411_);
v_i_1381_ = v___x_1412_;
v_b_1382_ = v___x_1410_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_del_object(v___x_1392_);
lean_dec(v_snd_1390_);
lean_dec_ref(v___x_1378_);
v_a_1416_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1395_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1395_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1426_, lean_object* v_goal_1427_, lean_object* v___x_1428_, lean_object* v_as_1429_, lean_object* v_sz_1430_, lean_object* v_i_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
size_t v_sz_boxed_1438_; size_t v_i_boxed_1439_; lean_object* v_res_1440_; 
v_sz_boxed_1438_ = lean_unbox_usize(v_sz_1430_);
lean_dec(v_sz_1430_);
v_i_boxed_1439_ = lean_unbox_usize(v_i_1431_);
lean_dec(v_i_1431_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1426_, v_goal_1427_, v___x_1428_, v_as_1429_, v_sz_boxed_1438_, v_i_boxed_1439_, v_b_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v_as_1429_);
lean_dec_ref(v_goal_1427_);
lean_dec_ref(v_init_1426_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1441_, lean_object* v_goal_1442_, lean_object* v___x_1443_, lean_object* v_n_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1441_, v_goal_1442_, v___x_1443_, v_n_1444_, v_b_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v_n_1444_);
lean_dec_ref(v_goal_1442_);
lean_dec_ref(v_init_1441_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1452_, lean_object* v___x_1453_, lean_object* v_as_1454_, size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v___x_1463_; 
v___x_1463_ = lean_usize_dec_lt(v_i_1456_, v_sz_1455_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
lean_dec_ref(v___x_1453_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_b_1457_);
return v___x_1464_;
}
else
{
lean_object* v_snd_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1506_; 
v_snd_1465_ = lean_ctor_get(v_b_1457_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_b_1457_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_b_1457_, 0);
lean_dec(v_unused_1507_);
v___x_1467_ = v_b_1457_;
v_isShared_1468_ = v_isSharedCheck_1506_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snd_1465_);
lean_dec(v_b_1457_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1506_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_array_uget_borrowed(v_as_1454_, v_i_1456_);
lean_inc(v_a_1469_);
v___x_1470_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1452_, v_a_1469_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v_a_1474_; uint8_t v___x_1481_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = lean_box(0);
v___x_1481_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1471_);
if (v___x_1481_ == 0)
{
lean_dec(v_a_1471_);
v_a_1474_ = v_snd_1465_;
goto v___jp_1473_;
}
else
{
lean_object* v_type_1482_; lean_object* v___x_1483_; 
v_type_1482_ = lean_ctor_get(v___x_1453_, 2);
lean_inc(v_a_1471_);
lean_inc_ref(v_type_1482_);
v___x_1483_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1482_, v_a_1471_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; uint8_t v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = lean_unbox(v_a_1484_);
lean_dec(v_a_1484_);
if (v___x_1485_ == 0)
{
lean_dec(v_a_1471_);
v_a_1474_ = v_snd_1465_;
goto v___jp_1473_;
}
else
{
lean_object* v_self_1486_; lean_object* v___x_1487_; 
v_self_1486_ = lean_ctor_get(v_a_1471_, 0);
lean_inc_ref(v_self_1486_);
lean_dec(v_a_1471_);
v___x_1487_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1453_, v_self_1486_);
if (lean_obj_tag(v___x_1487_) == 1)
{
lean_object* v_val_1488_; lean_object* v___x_1489_; 
v_val_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1452_, v_self_1486_, v_val_1488_, v_snd_1465_);
v_a_1474_ = v___x_1489_;
goto v___jp_1473_;
}
else
{
lean_dec(v___x_1487_);
lean_dec_ref(v_self_1486_);
v_a_1474_ = v_snd_1465_;
goto v___jp_1473_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_a_1471_);
lean_del_object(v___x_1467_);
lean_dec(v_snd_1465_);
lean_dec_ref(v___x_1453_);
v_a_1490_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1483_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1483_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
v___jp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v_a_1474_);
lean_ctor_set(v___x_1467_, 0, v___x_1472_);
v___x_1476_ = v___x_1467_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_a_1474_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
size_t v___x_1477_; size_t v___x_1478_; 
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_add(v_i_1456_, v___x_1477_);
v_i_1456_ = v___x_1478_;
v_b_1457_ = v___x_1476_;
goto _start;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_del_object(v___x_1467_);
lean_dec(v_snd_1465_);
lean_dec_ref(v___x_1453_);
v_a_1498_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1470_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1470_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1508_, lean_object* v___x_1509_, lean_object* v_as_1510_, lean_object* v_sz_1511_, lean_object* v_i_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
size_t v_sz_boxed_1519_; size_t v_i_boxed_1520_; lean_object* v_res_1521_; 
v_sz_boxed_1519_ = lean_unbox_usize(v_sz_1511_);
lean_dec(v_sz_1511_);
v_i_boxed_1520_ = lean_unbox_usize(v_i_1512_);
lean_dec(v_i_1512_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1508_, v___x_1509_, v_as_1510_, v_sz_boxed_1519_, v_i_boxed_1520_, v_b_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_as_1510_);
lean_dec_ref(v_goal_1508_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1522_, lean_object* v___x_1523_, lean_object* v_as_1524_, size_t v_sz_1525_, size_t v_i_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_usize_dec_lt(v_i_1526_, v_sz_1525_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_dec_ref(v___x_1523_);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_b_1527_);
return v___x_1534_;
}
else
{
lean_object* v_snd_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1576_; 
v_snd_1535_ = lean_ctor_get(v_b_1527_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_b_1527_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v_b_1527_, 0);
lean_dec(v_unused_1577_);
v___x_1537_ = v_b_1527_;
v_isShared_1538_ = v_isSharedCheck_1576_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snd_1535_);
lean_dec(v_b_1527_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1576_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_array_uget_borrowed(v_as_1524_, v_i_1526_);
lean_inc(v_a_1539_);
v___x_1540_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1522_, v_a_1539_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; lean_object* v_a_1544_; uint8_t v___x_1551_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = lean_box(0);
v___x_1551_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1541_);
if (v___x_1551_ == 0)
{
lean_dec(v_a_1541_);
v_a_1544_ = v_snd_1535_;
goto v___jp_1543_;
}
else
{
lean_object* v_type_1552_; lean_object* v___x_1553_; 
v_type_1552_ = lean_ctor_get(v___x_1523_, 2);
lean_inc(v_a_1541_);
lean_inc_ref(v_type_1552_);
v___x_1553_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1552_, v_a_1541_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; uint8_t v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = lean_unbox(v_a_1554_);
lean_dec(v_a_1554_);
if (v___x_1555_ == 0)
{
lean_dec(v_a_1541_);
v_a_1544_ = v_snd_1535_;
goto v___jp_1543_;
}
else
{
lean_object* v_self_1556_; lean_object* v___x_1557_; 
v_self_1556_ = lean_ctor_get(v_a_1541_, 0);
lean_inc_ref(v_self_1556_);
lean_dec(v_a_1541_);
v___x_1557_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1523_, v_self_1556_);
if (lean_obj_tag(v___x_1557_) == 1)
{
lean_object* v_val_1558_; lean_object* v___x_1559_; 
v_val_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1522_, v_self_1556_, v_val_1558_, v_snd_1535_);
v_a_1544_ = v___x_1559_;
goto v___jp_1543_;
}
else
{
lean_dec(v___x_1557_);
lean_dec_ref(v_self_1556_);
v_a_1544_ = v_snd_1535_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_a_1541_);
lean_del_object(v___x_1537_);
lean_dec(v_snd_1535_);
lean_dec_ref(v___x_1523_);
v_a_1560_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1553_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1553_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
v___jp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v_a_1544_);
lean_ctor_set(v___x_1537_, 0, v___x_1542_);
v___x_1546_ = v___x_1537_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_a_1544_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1526_, v___x_1547_);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1522_, v___x_1523_, v_as_1524_, v_sz_1525_, v___x_1548_, v___x_1546_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_del_object(v___x_1537_);
lean_dec(v_snd_1535_);
lean_dec_ref(v___x_1523_);
v_a_1568_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1540_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1540_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1578_, lean_object* v___x_1579_, lean_object* v_as_1580_, lean_object* v_sz_1581_, lean_object* v_i_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
size_t v_sz_boxed_1589_; size_t v_i_boxed_1590_; lean_object* v_res_1591_; 
v_sz_boxed_1589_ = lean_unbox_usize(v_sz_1581_);
lean_dec(v_sz_1581_);
v_i_boxed_1590_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1578_, v___x_1579_, v_as_1580_, v_sz_boxed_1589_, v_i_boxed_1590_, v_b_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec_ref(v_as_1580_);
lean_dec_ref(v_goal_1578_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1592_, lean_object* v___x_1593_, lean_object* v_t_1594_, lean_object* v_init_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_root_1601_; lean_object* v_tail_1602_; lean_object* v___x_1603_; 
v_root_1601_ = lean_ctor_get(v_t_1594_, 0);
v_tail_1602_ = lean_ctor_get(v_t_1594_, 1);
lean_inc_ref(v___x_1593_);
lean_inc_ref(v_init_1595_);
v___x_1603_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1595_, v_goal_1592_, v___x_1593_, v_root_1601_, v_init_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec_ref(v_init_1595_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1640_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1640_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1640_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
if (lean_obj_tag(v_a_1604_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; 
lean_dec_ref(v___x_1593_);
v_a_1608_ = lean_ctor_get(v_a_1604_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v_a_1604_, 1);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v_a_1608_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; size_t v_sz_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
lean_del_object(v___x_1606_);
v_a_1612_ = lean_ctor_get(v_a_1604_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v_a_1604_, 1);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v_a_1612_);
v_sz_1615_ = lean_array_size(v_tail_1602_);
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1592_, v___x_1593_, v_tail_1602_, v_sz_1615_, v___x_1616_, v___x_1614_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1631_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1631_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_fst_1622_; 
v_fst_1622_ = lean_ctor_get(v_a_1618_, 0);
if (lean_obj_tag(v_fst_1622_) == 0)
{
lean_object* v_snd_1623_; lean_object* v___x_1625_; 
v_snd_1623_ = lean_ctor_get(v_a_1618_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_a_1618_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_snd_1623_);
v___x_1625_ = v___x_1620_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_snd_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v_val_1627_; lean_object* v___x_1629_; 
lean_inc_ref(v_fst_1622_);
lean_dec(v_a_1618_);
v_val_1627_ = lean_ctor_get(v_fst_1622_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v_fst_1622_, 1);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_val_1627_);
v___x_1629_ = v___x_1620_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_val_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1617_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1617_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___x_1593_);
v_a_1641_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1603_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1603_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1649_, lean_object* v___x_1650_, lean_object* v_t_1651_, lean_object* v_init_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1649_, v___x_1650_, v_t_1651_, v_init_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_t_1651_);
lean_dec_ref(v_goal_1649_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1659_, lean_object* v_as_1660_, size_t v_sz_1661_, size_t v_i_1662_, lean_object* v_b_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_usize_dec_lt(v_i_1662_, v_sz_1661_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_b_1663_);
return v___x_1670_;
}
else
{
lean_object* v_snd_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1702_; 
v_snd_1671_ = lean_ctor_get(v_b_1663_, 1);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_b_1663_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v_b_1663_, 0);
lean_dec(v_unused_1703_);
v___x_1673_ = v_b_1663_;
v_isShared_1674_ = v_isSharedCheck_1702_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_snd_1671_);
lean_dec(v_b_1663_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1702_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_a_1675_; lean_object* v___x_1676_; 
v_a_1675_ = lean_array_uget_borrowed(v_as_1660_, v_i_1662_);
lean_inc(v_a_1675_);
v___x_1676_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1659_, v_a_1675_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v_self_1678_; lean_object* v___x_1679_; lean_object* v_a_1681_; lean_object* v___x_1688_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v_self_1678_ = lean_ctor_get(v_a_1677_, 0);
lean_inc_ref_n(v_self_1678_, 2);
lean_dec(v_a_1677_);
v___x_1679_ = lean_box(0);
v___x_1688_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1678_);
if (lean_obj_tag(v___x_1688_) == 1)
{
lean_object* v_val_1689_; lean_object* v___x_1690_; 
v_val_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1671_, v_val_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1671_, v_self_1678_);
lean_dec_ref(v_self_1678_);
if (lean_obj_tag(v___x_1691_) == 1)
{
lean_object* v_val_1692_; lean_object* v___x_1693_; 
v_val_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1659_, v_val_1689_, v_val_1692_, v_snd_1671_);
v_a_1681_ = v___x_1693_;
goto v___jp_1680_;
}
else
{
lean_dec(v___x_1691_);
lean_dec(v_val_1689_);
v_a_1681_ = v_snd_1671_;
goto v___jp_1680_;
}
}
else
{
lean_dec_ref_known(v___x_1690_, 1);
lean_dec(v_val_1689_);
lean_dec_ref(v_self_1678_);
v_a_1681_ = v_snd_1671_;
goto v___jp_1680_;
}
}
else
{
lean_dec(v___x_1688_);
lean_dec_ref(v_self_1678_);
v_a_1681_ = v_snd_1671_;
goto v___jp_1680_;
}
v___jp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v_a_1681_);
lean_ctor_set(v___x_1673_, 0, v___x_1679_);
v___x_1683_ = v___x_1673_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1681_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
size_t v___x_1684_; size_t v___x_1685_; 
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1662_, v___x_1684_);
v_i_1662_ = v___x_1685_;
v_b_1663_ = v___x_1683_;
goto _start;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_del_object(v___x_1673_);
lean_dec(v_snd_1671_);
v_a_1694_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1676_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1676_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1704_, lean_object* v_as_1705_, lean_object* v_sz_1706_, lean_object* v_i_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
size_t v_sz_boxed_1714_; size_t v_i_boxed_1715_; lean_object* v_res_1716_; 
v_sz_boxed_1714_ = lean_unbox_usize(v_sz_1706_);
lean_dec(v_sz_1706_);
v_i_boxed_1715_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1704_, v_as_1705_, v_sz_boxed_1714_, v_i_boxed_1715_, v_b_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v_as_1705_);
lean_dec_ref(v_goal_1704_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1717_, lean_object* v_as_1718_, size_t v_sz_1719_, size_t v_i_1720_, lean_object* v_b_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_lt(v_i_1720_, v_sz_1719_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_b_1721_);
return v___x_1728_;
}
else
{
lean_object* v_snd_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1760_; 
v_snd_1729_ = lean_ctor_get(v_b_1721_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_b_1721_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_b_1721_, 0);
lean_dec(v_unused_1761_);
v___x_1731_ = v_b_1721_;
v_isShared_1732_ = v_isSharedCheck_1760_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_snd_1729_);
lean_dec(v_b_1721_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1760_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_a_1733_; lean_object* v___x_1734_; 
v_a_1733_ = lean_array_uget_borrowed(v_as_1718_, v_i_1720_);
lean_inc(v_a_1733_);
v___x_1734_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1717_, v_a_1733_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v_self_1736_; lean_object* v___x_1737_; lean_object* v_a_1739_; lean_object* v___x_1746_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v_self_1736_ = lean_ctor_get(v_a_1735_, 0);
lean_inc_ref_n(v_self_1736_, 2);
lean_dec(v_a_1735_);
v___x_1737_ = lean_box(0);
v___x_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1736_);
if (lean_obj_tag(v___x_1746_) == 1)
{
lean_object* v_val_1747_; lean_object* v___x_1748_; 
v_val_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_val_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1729_, v_val_1747_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1729_, v_self_1736_);
lean_dec_ref(v_self_1736_);
if (lean_obj_tag(v___x_1749_) == 1)
{
lean_object* v_val_1750_; lean_object* v___x_1751_; 
v_val_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_val_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1717_, v_val_1747_, v_val_1750_, v_snd_1729_);
v_a_1739_ = v___x_1751_;
goto v___jp_1738_;
}
else
{
lean_dec(v___x_1749_);
lean_dec(v_val_1747_);
v_a_1739_ = v_snd_1729_;
goto v___jp_1738_;
}
}
else
{
lean_dec_ref_known(v___x_1748_, 1);
lean_dec(v_val_1747_);
lean_dec_ref(v_self_1736_);
v_a_1739_ = v_snd_1729_;
goto v___jp_1738_;
}
}
else
{
lean_dec(v___x_1746_);
lean_dec_ref(v_self_1736_);
v_a_1739_ = v_snd_1729_;
goto v___jp_1738_;
}
v___jp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v_a_1739_);
lean_ctor_set(v___x_1731_, 0, v___x_1737_);
v___x_1741_ = v___x_1731_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1739_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
size_t v___x_1742_; size_t v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1720_, v___x_1742_);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1717_, v_as_1718_, v_sz_1719_, v___x_1743_, v___x_1741_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_del_object(v___x_1731_);
lean_dec(v_snd_1729_);
v_a_1752_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1734_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1734_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1762_, lean_object* v_as_1763_, lean_object* v_sz_1764_, lean_object* v_i_1765_, lean_object* v_b_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
size_t v_sz_boxed_1772_; size_t v_i_boxed_1773_; lean_object* v_res_1774_; 
v_sz_boxed_1772_ = lean_unbox_usize(v_sz_1764_);
lean_dec(v_sz_1764_);
v_i_boxed_1773_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1762_, v_as_1763_, v_sz_boxed_1772_, v_i_boxed_1773_, v_b_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v_as_1763_);
lean_dec_ref(v_goal_1762_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1775_, lean_object* v_as_1776_, size_t v_sz_1777_, size_t v_i_1778_, lean_object* v_b_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_usize_dec_lt(v_i_1778_, v_sz_1777_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_b_1779_);
return v___x_1786_;
}
else
{
lean_object* v_snd_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1818_; 
v_snd_1787_ = lean_ctor_get(v_b_1779_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_b_1779_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v_b_1779_, 0);
lean_dec(v_unused_1819_);
v___x_1789_ = v_b_1779_;
v_isShared_1790_ = v_isSharedCheck_1818_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_snd_1787_);
lean_dec(v_b_1779_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1818_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_array_uget_borrowed(v_as_1776_, v_i_1778_);
lean_inc(v_a_1791_);
v___x_1792_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1775_, v_a_1791_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v_self_1794_; lean_object* v___x_1795_; lean_object* v_a_1797_; lean_object* v___x_1804_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v_self_1794_ = lean_ctor_get(v_a_1793_, 0);
lean_inc_ref_n(v_self_1794_, 2);
lean_dec(v_a_1793_);
v___x_1795_ = lean_box(0);
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1794_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v___x_1806_; 
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1787_, v_val_1805_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1787_, v_self_1794_);
lean_dec_ref(v_self_1794_);
if (lean_obj_tag(v___x_1807_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1809_; 
v_val_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1775_, v_val_1805_, v_val_1808_, v_snd_1787_);
v_a_1797_ = v___x_1809_;
goto v___jp_1796_;
}
else
{
lean_dec(v___x_1807_);
lean_dec(v_val_1805_);
v_a_1797_ = v_snd_1787_;
goto v___jp_1796_;
}
}
else
{
lean_dec_ref_known(v___x_1806_, 1);
lean_dec(v_val_1805_);
lean_dec_ref(v_self_1794_);
v_a_1797_ = v_snd_1787_;
goto v___jp_1796_;
}
}
else
{
lean_dec(v___x_1804_);
lean_dec_ref(v_self_1794_);
v_a_1797_ = v_snd_1787_;
goto v___jp_1796_;
}
v___jp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v_a_1797_);
lean_ctor_set(v___x_1789_, 0, v___x_1795_);
v___x_1799_ = v___x_1789_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_a_1797_);
v___x_1799_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
size_t v___x_1800_; size_t v___x_1801_; 
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_add(v_i_1778_, v___x_1800_);
v_i_1778_ = v___x_1801_;
v_b_1779_ = v___x_1799_;
goto _start;
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_del_object(v___x_1789_);
lean_dec(v_snd_1787_);
v_a_1810_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1792_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1792_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1820_, lean_object* v_as_1821_, lean_object* v_sz_1822_, lean_object* v_i_1823_, lean_object* v_b_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
size_t v_sz_boxed_1830_; size_t v_i_boxed_1831_; lean_object* v_res_1832_; 
v_sz_boxed_1830_ = lean_unbox_usize(v_sz_1822_);
lean_dec(v_sz_1822_);
v_i_boxed_1831_ = lean_unbox_usize(v_i_1823_);
lean_dec(v_i_1823_);
v_res_1832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1820_, v_as_1821_, v_sz_boxed_1830_, v_i_boxed_1831_, v_b_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v_as_1821_);
lean_dec_ref(v_goal_1820_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1833_, lean_object* v_as_1834_, size_t v_sz_1835_, size_t v_i_1836_, lean_object* v_b_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_usize_dec_lt(v_i_1836_, v_sz_1835_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_b_1837_);
return v___x_1844_;
}
else
{
lean_object* v_snd_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1876_; 
v_snd_1845_ = lean_ctor_get(v_b_1837_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_b_1837_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v_b_1837_, 0);
lean_dec(v_unused_1877_);
v___x_1847_ = v_b_1837_;
v_isShared_1848_ = v_isSharedCheck_1876_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_snd_1845_);
lean_dec(v_b_1837_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1876_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_array_uget_borrowed(v_as_1834_, v_i_1836_);
lean_inc(v_a_1849_);
v___x_1850_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1833_, v_a_1849_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v_self_1852_; lean_object* v___x_1853_; lean_object* v_a_1855_; lean_object* v___x_1862_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v_self_1852_ = lean_ctor_get(v_a_1851_, 0);
lean_inc_ref_n(v_self_1852_, 2);
lean_dec(v_a_1851_);
v___x_1853_ = lean_box(0);
v___x_1862_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1852_);
if (lean_obj_tag(v___x_1862_) == 1)
{
lean_object* v_val_1863_; lean_object* v___x_1864_; 
v_val_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_val_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1845_, v_val_1863_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1845_, v_self_1852_);
lean_dec_ref(v_self_1852_);
if (lean_obj_tag(v___x_1865_) == 1)
{
lean_object* v_val_1866_; lean_object* v___x_1867_; 
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1833_, v_val_1863_, v_val_1866_, v_snd_1845_);
v_a_1855_ = v___x_1867_;
goto v___jp_1854_;
}
else
{
lean_dec(v___x_1865_);
lean_dec(v_val_1863_);
v_a_1855_ = v_snd_1845_;
goto v___jp_1854_;
}
}
else
{
lean_dec_ref_known(v___x_1864_, 1);
lean_dec(v_val_1863_);
lean_dec_ref(v_self_1852_);
v_a_1855_ = v_snd_1845_;
goto v___jp_1854_;
}
}
else
{
lean_dec(v___x_1862_);
lean_dec_ref(v_self_1852_);
v_a_1855_ = v_snd_1845_;
goto v___jp_1854_;
}
v___jp_1854_:
{
lean_object* v___x_1857_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v_a_1855_);
lean_ctor_set(v___x_1847_, 0, v___x_1853_);
v___x_1857_ = v___x_1847_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_a_1855_);
v___x_1857_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
size_t v___x_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = ((size_t)1ULL);
v___x_1859_ = lean_usize_add(v_i_1836_, v___x_1858_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1833_, v_as_1834_, v_sz_1835_, v___x_1859_, v___x_1857_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_del_object(v___x_1847_);
lean_dec(v_snd_1845_);
v_a_1868_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1850_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1850_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1878_, lean_object* v_as_1879_, lean_object* v_sz_1880_, lean_object* v_i_1881_, lean_object* v_b_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
size_t v_sz_boxed_1888_; size_t v_i_boxed_1889_; lean_object* v_res_1890_; 
v_sz_boxed_1888_ = lean_unbox_usize(v_sz_1880_);
lean_dec(v_sz_1880_);
v_i_boxed_1889_ = lean_unbox_usize(v_i_1881_);
lean_dec(v_i_1881_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1878_, v_as_1879_, v_sz_boxed_1888_, v_i_boxed_1889_, v_b_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v_as_1879_);
lean_dec_ref(v_goal_1878_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1891_, lean_object* v_goal_1892_, lean_object* v_n_1893_, lean_object* v_b_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
if (lean_obj_tag(v_n_1893_) == 0)
{
lean_object* v_cs_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; size_t v_sz_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v_cs_1900_ = lean_ctor_get(v_n_1893_, 0);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v_b_1894_);
v_sz_1903_ = lean_array_size(v_cs_1900_);
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1891_, v_goal_1892_, v_cs_1900_, v_sz_1903_, v___x_1904_, v___x_1902_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1920_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1920_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1920_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_fst_1910_; 
v_fst_1910_ = lean_ctor_get(v_a_1906_, 0);
if (lean_obj_tag(v_fst_1910_) == 0)
{
lean_object* v_snd_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v_snd_1911_ = lean_ctor_get(v_a_1906_, 1);
lean_inc(v_snd_1911_);
lean_dec(v_a_1906_);
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_snd_1911_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1912_);
v___x_1914_ = v___x_1908_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
else
{
lean_object* v_val_1916_; lean_object* v___x_1918_; 
lean_inc_ref(v_fst_1910_);
lean_dec(v_a_1906_);
v_val_1916_ = lean_ctor_get(v_fst_1910_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_fst_1910_, 1);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v_val_1916_);
v___x_1918_ = v___x_1908_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_val_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_a_1921_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1905_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1905_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_vs_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; size_t v_sz_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
v_vs_1929_ = lean_ctor_get(v_n_1893_, 0);
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v_b_1894_);
v_sz_1932_ = lean_array_size(v_vs_1929_);
v___x_1933_ = ((size_t)0ULL);
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1892_, v_vs_1929_, v_sz_1932_, v___x_1933_, v___x_1931_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1949_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1949_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1949_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_fst_1939_; 
v_fst_1939_ = lean_ctor_get(v_a_1935_, 0);
if (lean_obj_tag(v_fst_1939_) == 0)
{
lean_object* v_snd_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v_snd_1940_ = lean_ctor_get(v_a_1935_, 1);
lean_inc(v_snd_1940_);
lean_dec(v_a_1935_);
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_snd_1940_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1941_);
v___x_1943_ = v___x_1937_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
else
{
lean_object* v_val_1945_; lean_object* v___x_1947_; 
lean_inc_ref(v_fst_1939_);
lean_dec(v_a_1935_);
v_val_1945_ = lean_ctor_get(v_fst_1939_, 0);
lean_inc(v_val_1945_);
lean_dec_ref_known(v_fst_1939_, 1);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v_val_1945_);
v___x_1947_ = v___x_1937_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_val_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v_a_1950_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1934_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1934_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1958_, lean_object* v_goal_1959_, lean_object* v_as_1960_, size_t v_sz_1961_, size_t v_i_1962_, lean_object* v_b_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_usize_dec_lt(v_i_1962_, v_sz_1961_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_b_1963_);
return v___x_1970_;
}
else
{
lean_object* v_snd_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2005_; 
v_snd_1971_ = lean_ctor_get(v_b_1963_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_b_1963_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v_b_1963_, 0);
lean_dec(v_unused_2006_);
v___x_1973_ = v_b_1963_;
v_isShared_1974_ = v_isSharedCheck_2005_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snd_1971_);
lean_dec(v_b_1963_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2005_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_a_1975_; lean_object* v___x_1976_; 
v_a_1975_ = lean_array_uget_borrowed(v_as_1960_, v_i_1962_);
lean_inc(v_snd_1971_);
v___x_1976_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1958_, v_goal_1959_, v_a_1975_, v_snd_1971_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1996_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1996_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1996_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_a_1977_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1981_);
v___x_1983_ = v___x_1973_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_snd_1971_);
v___x_1983_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1983_);
v___x_1985_ = v___x_1979_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_del_object(v___x_1979_);
lean_dec(v_snd_1971_);
v_a_1988_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v_a_1977_, 1);
v___x_1989_ = lean_box(0);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v_a_1988_);
lean_ctor_set(v___x_1973_, 0, v___x_1989_);
v___x_1991_ = v___x_1973_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_a_1988_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
size_t v___x_1992_; size_t v___x_1993_; 
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1962_, v___x_1992_);
v_i_1962_ = v___x_1993_;
v_b_1963_ = v___x_1991_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_del_object(v___x_1973_);
lean_dec(v_snd_1971_);
v_a_1997_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1976_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1976_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_2007_, lean_object* v_goal_2008_, lean_object* v_as_2009_, lean_object* v_sz_2010_, lean_object* v_i_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
size_t v_sz_boxed_2018_; size_t v_i_boxed_2019_; lean_object* v_res_2020_; 
v_sz_boxed_2018_ = lean_unbox_usize(v_sz_2010_);
lean_dec(v_sz_2010_);
v_i_boxed_2019_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_2007_, v_goal_2008_, v_as_2009_, v_sz_boxed_2018_, v_i_boxed_2019_, v_b_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v_as_2009_);
lean_dec_ref(v_goal_2008_);
lean_dec_ref(v_init_2007_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_2021_, lean_object* v_goal_2022_, lean_object* v_n_2023_, lean_object* v_b_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2021_, v_goal_2022_, v_n_2023_, v_b_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v_n_2023_);
lean_dec_ref(v_goal_2022_);
lean_dec_ref(v_init_2021_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2031_, lean_object* v_t_2032_, lean_object* v_init_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_root_2039_; lean_object* v_tail_2040_; lean_object* v___x_2041_; 
v_root_2039_ = lean_ctor_get(v_t_2032_, 0);
v_tail_2040_ = lean_ctor_get(v_t_2032_, 1);
lean_inc_ref(v_init_2033_);
v___x_2041_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2033_, v_goal_2031_, v_root_2039_, v_init_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec_ref(v_init_2033_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2078_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2078_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2078_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
if (lean_obj_tag(v_a_2042_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; 
v_a_2046_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v_a_2042_, 1);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_a_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; size_t v_sz_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
lean_del_object(v___x_2044_);
v_a_2050_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v_a_2042_, 1);
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v_a_2050_);
v_sz_2053_ = lean_array_size(v_tail_2040_);
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2031_, v_tail_2040_, v_sz_2053_, v___x_2054_, v___x_2052_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2069_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2069_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2069_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v_fst_2060_; 
v_fst_2060_ = lean_ctor_get(v_a_2056_, 0);
if (lean_obj_tag(v_fst_2060_) == 0)
{
lean_object* v_snd_2061_; lean_object* v___x_2063_; 
v_snd_2061_ = lean_ctor_get(v_a_2056_, 1);
lean_inc(v_snd_2061_);
lean_dec(v_a_2056_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_snd_2061_);
v___x_2063_ = v___x_2058_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_snd_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
else
{
lean_object* v_val_2065_; lean_object* v___x_2067_; 
lean_inc_ref(v_fst_2060_);
lean_dec(v_a_2056_);
v_val_2065_ = lean_ctor_get(v_fst_2060_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v_fst_2060_, 1);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_val_2065_);
v___x_2067_ = v___x_2058_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_a_2070_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2055_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2055_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
v_a_2079_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2041_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2041_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2087_, lean_object* v_t_2088_, lean_object* v_init_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2087_, v_t_2088_, v_init_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec_ref(v_t_2088_);
lean_dec_ref(v_goal_2087_);
return v_res_2095_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_unsigned_to_nat(16u);
v___x_2098_ = lean_mk_array(v___x_2097_, v___x_2096_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_model_2101_; 
v___x_2099_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2100_ = lean_unsigned_to_nat(0u);
v_model_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_2101_, 0, v___x_2100_);
lean_ctor_set(v_model_2101_, 1, v___x_2099_);
return v_model_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2109_, lean_object* v_structId_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2117_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2116_, v_goal_2109_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v_toGoalState_2119_; lean_object* v_structs_2120_; lean_object* v_exprs_2121_; lean_object* v___x_2122_; lean_object* v_model_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v_toGoalState_2119_ = lean_ctor_get(v_goal_2109_, 0);
v_structs_2120_ = lean_ctor_get(v_a_2118_, 0);
lean_inc_ref(v_structs_2120_);
lean_dec(v_a_2118_);
v_exprs_2121_ = lean_ctor_get(v_toGoalState_2119_, 2);
v___x_2122_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2123_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2124_ = lean_array_get(v___x_2122_, v_structs_2120_, v_structId_2110_);
lean_dec_ref(v_structs_2120_);
lean_inc(v___x_2124_);
v___x_2125_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2109_, v___x_2124_, v_exprs_2121_, v_model_2123_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2109_, v_structId_2110_, v_a_2126_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2109_, v_exprs_2121_, v_a_2128_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v_type_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v_type_2131_ = lean_ctor_get(v___x_2124_, 2);
lean_inc_ref(v_type_2131_);
lean_dec(v___x_2124_);
v___x_2132_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2132_, 0, v_type_2131_);
v___x_2133_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2109_, v___x_2132_, v_a_2130_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v___x_2135_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2136_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2135_, v_a_2134_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v___x_2136_, 0);
lean_dec(v_unused_2144_);
v___x_2138_ = v___x_2136_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_dec(v___x_2136_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v_a_2134_);
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2134_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_a_2134_);
v_a_2145_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2136_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2136_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
return v___x_2133_;
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v___x_2124_);
v_a_2153_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2129_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2129_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v___x_2124_);
v_a_2161_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2127_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2127_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v___x_2124_);
v_a_2169_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2125_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2125_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2189_; 
v_a_2177_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2179_ = v___x_2117_;
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2117_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_ref_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v_ref_2181_ = lean_ctor_get(v_a_2113_, 5);
v___x_2182_ = lean_io_error_to_string(v_a_2177_);
v___x_2183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
v___x_2184_ = l_Lean_MessageData_ofFormat(v___x_2183_);
lean_inc(v_ref_2181_);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_ref_2181_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2185_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2190_, lean_object* v_structId_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2190_, v_structId_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_structId_2191_);
lean_dec_ref(v_goal_2190_);
return v_res_2197_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
}
#ifdef __cplusplus
}
#endif

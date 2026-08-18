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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_instInhabitedRat;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSubInst(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isNegInst(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value),LEAN_SCALAR_PTR_LITERAL(44, 255, 209, 221, 117, 20, 143, 66)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(lean_object* v_type_118_, lean_object* v_n_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_self_125_; lean_object* v_keyedConfig_126_; uint8_t v_trackZetaDelta_127_; lean_object* v_zetaDeltaSet_128_; lean_object* v_lctx_129_; lean_object* v_localInstances_130_; lean_object* v_defEqCtx_x3f_131_; lean_object* v_synthPendingDepth_132_; lean_object* v_customCanUnfoldPredicate_x3f_133_; uint8_t v_univApprox_134_; uint8_t v_inTypeClassResolution_135_; uint8_t v_cacheInferType_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_self_125_ = lean_ctor_get(v_n_119_, 0);
lean_inc_ref(v_self_125_);
lean_dec_ref(v_n_119_);
v_keyedConfig_126_ = lean_ctor_get(v_a_120_, 0);
v_trackZetaDelta_127_ = lean_ctor_get_uint8(v_a_120_, sizeof(void*)*7);
v_zetaDeltaSet_128_ = lean_ctor_get(v_a_120_, 1);
v_lctx_129_ = lean_ctor_get(v_a_120_, 2);
v_localInstances_130_ = lean_ctor_get(v_a_120_, 3);
v_defEqCtx_x3f_131_ = lean_ctor_get(v_a_120_, 4);
v_synthPendingDepth_132_ = lean_ctor_get(v_a_120_, 5);
v_customCanUnfoldPredicate_x3f_133_ = lean_ctor_get(v_a_120_, 6);
v_univApprox_134_ = lean_ctor_get_uint8(v_a_120_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_135_ = lean_ctor_get_uint8(v_a_120_, sizeof(void*)*7 + 2);
v_cacheInferType_136_ = lean_ctor_get_uint8(v_a_120_, sizeof(void*)*7 + 3);
v___x_137_ = 1;
lean_inc_ref(v_keyedConfig_126_);
v___x_138_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_137_, v_keyedConfig_126_);
lean_inc(v_customCanUnfoldPredicate_x3f_133_);
lean_inc(v_synthPendingDepth_132_);
lean_inc(v_defEqCtx_x3f_131_);
lean_inc_ref(v_localInstances_130_);
lean_inc_ref(v_lctx_129_);
lean_inc(v_zetaDeltaSet_128_);
v___x_139_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_zetaDeltaSet_128_);
lean_ctor_set(v___x_139_, 2, v_lctx_129_);
lean_ctor_set(v___x_139_, 3, v_localInstances_130_);
lean_ctor_set(v___x_139_, 4, v_defEqCtx_x3f_131_);
lean_ctor_set(v___x_139_, 5, v_synthPendingDepth_132_);
lean_ctor_set(v___x_139_, 6, v_customCanUnfoldPredicate_x3f_133_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7, v_trackZetaDelta_127_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7 + 1, v_univApprox_134_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7 + 2, v_inTypeClassResolution_135_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7 + 3, v_cacheInferType_136_);
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v_a_121_);
lean_inc_ref(v___x_139_);
v___x_140_ = lean_infer_type(v_self_125_, v___x_139_, v_a_121_, v_a_122_, v_a_123_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = l_Lean_Meta_isExprDefEq(v_a_141_, v_type_118_, v___x_139_, v_a_121_, v_a_122_, v_a_123_);
lean_dec_ref_known(v___x_139_, 7);
return v___x_142_;
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref_known(v___x_139_, 7);
lean_dec_ref(v_type_118_);
v_a_143_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_140_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_140_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(lean_object* v_type_151_, lean_object* v_n_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_151_, v_n_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(lean_object* v_e_170_){
_start:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = l_Lean_Expr_cleanupAnnotations(v_e_170_);
v___x_172_ = l_Lean_Expr_isApp(v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_dec_ref(v___x_171_);
v___x_173_ = lean_box(0);
return v___x_173_;
}
else
{
lean_object* v_arg_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_arg_174_ = lean_ctor_get(v___x_171_, 1);
lean_inc_ref(v_arg_174_);
v___x_175_ = l_Lean_Expr_appFnCleanup___redArg(v___x_171_);
v___x_176_ = l_Lean_Expr_isApp(v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec_ref(v___x_175_);
lean_dec_ref(v_arg_174_);
v___x_177_ = lean_box(0);
return v___x_177_;
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_175_);
v___x_179_ = l_Lean_Expr_isApp(v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec_ref(v___x_178_);
lean_dec_ref(v_arg_174_);
v___x_180_ = lean_box(0);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_178_);
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5));
v___x_183_ = l_Lean_Expr_isConstOf(v___x_181_, v___x_182_);
lean_dec_ref(v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec_ref(v_arg_174_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v_arg_174_);
return v___x_185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Rat_ofInt(v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_nat_to_int(v_a_188_);
v___x_190_ = l_Rat_ofInt(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_m_191_, lean_object* v_query_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
lean_object* v_zero_196_; uint8_t v_isZero_197_; 
v_zero_196_ = lean_unsigned_to_nat(0u);
v_isZero_197_ = lean_nat_dec_eq(v_x_194_, v_zero_196_);
if (v_isZero_197_ == 1)
{
lean_dec(v_x_195_);
lean_dec(v_x_194_);
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(2);
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_val_199_ = lean_ctor_get(v_x_193_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v_x_193_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_val_199_);
lean_dec(v_x_193_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_val_199_);
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
lean_object* v_keyArray_207_; lean_object* v_valueArray_208_; lean_object* v___x_209_; uint8_t v_isSome_210_; 
v_keyArray_207_ = lean_ctor_get(v_m_191_, 1);
v_valueArray_208_ = lean_ctor_get(v_m_191_, 2);
v___x_209_ = lean_array_fget_borrowed(v_keyArray_207_, v_x_195_);
v_isSome_210_ = lean_noption_is_some(v___x_209_);
if (v_isSome_210_ == 0)
{
lean_dec(v_x_194_);
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v_x_195_);
return v___x_211_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_x_195_);
v_val_212_ = lean_ctor_get(v_x_193_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_193_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v_x_193_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_dec(v_x_193_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_val_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_object* v_one_220_; lean_object* v_n_221_; lean_object* v___y_223_; 
v_one_220_ = lean_unsigned_to_nat(1u);
v_n_221_ = lean_nat_sub(v_x_194_, v_one_220_);
lean_dec(v_x_194_);
if (v_isSome_210_ == 0)
{
goto v___jp_229_;
}
else
{
lean_object* v___x_231_; uint8_t v_isSome_232_; 
v___x_231_ = lean_array_fget_borrowed(v_valueArray_208_, v_x_195_);
v_isSome_232_ = lean_noption_is_some(v___x_231_);
if (v_isSome_232_ == 0)
{
goto v___jp_229_;
}
else
{
lean_object* v_val_233_; uint8_t v___x_234_; 
lean_inc(v___x_209_);
v_val_233_ = lean_noption_get(v___x_209_);
v___x_234_ = lean_expr_eqv(v_val_233_, v_query_192_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
lean_dec(v_val_233_);
v___x_235_ = lean_array_get_size(v_keyArray_207_);
v___x_236_ = lean_nat_add(v_x_195_, v_one_220_);
lean_dec(v_x_195_);
v___x_237_ = lean_nat_dec_lt(v___x_236_, v___x_235_);
if (v___x_237_ == 0)
{
lean_dec(v___x_236_);
v_x_194_ = v_n_221_;
v_x_195_ = v_zero_196_;
goto _start;
}
else
{
v_x_194_ = v_n_221_;
v_x_195_ = v___x_236_;
goto _start;
}
}
else
{
lean_object* v_val_240_; lean_object* v___x_241_; 
lean_dec(v_n_221_);
lean_dec(v_x_193_);
lean_inc(v___x_231_);
v_val_240_ = lean_noption_get(v___x_231_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_x_195_);
lean_ctor_set(v___x_241_, 1, v_val_233_);
lean_ctor_set(v___x_241_, 2, v_val_240_);
return v___x_241_;
}
}
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = lean_array_get_size(v_keyArray_207_);
v___x_225_ = lean_nat_add(v_x_195_, v_one_220_);
lean_dec(v_x_195_);
v___x_226_ = lean_nat_dec_lt(v___x_225_, v___x_224_);
if (v___x_226_ == 0)
{
lean_dec(v___x_225_);
v_x_193_ = v___y_223_;
v_x_194_ = v_n_221_;
v_x_195_ = v_zero_196_;
goto _start;
}
else
{
v_x_193_ = v___y_223_;
v_x_194_ = v_n_221_;
v_x_195_ = v___x_225_;
goto _start;
}
}
v___jp_229_:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v___x_230_; 
lean_inc(v_x_195_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_x_195_);
v___y_223_ = v___x_230_;
goto v___jp_222_;
}
else
{
v___y_223_ = v_x_193_;
goto v___jp_222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_242_, lean_object* v_query_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___redArg(v_m_242_, v_query_243_, v_x_244_, v_x_245_, v_x_246_);
lean_dec_ref(v_query_243_);
lean_dec_ref(v_m_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___redArg(lean_object* v_m_248_, lean_object* v_query_249_){
_start:
{
lean_object* v_keyArray_250_; lean_object* v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v_fold_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_keyArray_250_ = lean_ctor_get(v_m_248_, 1);
v___x_251_ = lean_array_get_size(v_keyArray_250_);
v___x_252_ = l_Lean_Expr_hash(v_query_249_);
v___x_253_ = 32ULL;
v___x_254_ = lean_uint64_shift_right(v___x_252_, v___x_253_);
v_fold_255_ = lean_uint64_xor(v___x_252_, v___x_254_);
v___x_256_ = 16ULL;
v___x_257_ = lean_uint64_shift_right(v_fold_255_, v___x_256_);
v___x_258_ = lean_uint64_xor(v_fold_255_, v___x_257_);
v___x_259_ = lean_uint64_to_usize(v___x_258_);
v___x_260_ = lean_usize_of_nat(v___x_251_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_sub(v___x_260_, v___x_261_);
v___x_263_ = lean_usize_land(v___x_259_, v___x_262_);
v___x_264_ = lean_usize_to_nat(v___x_263_);
v___x_265_ = lean_box(0);
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___redArg(v_m_248_, v_query_249_, v___x_265_, v___x_251_, v___x_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_267_, lean_object* v_query_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___redArg(v_m_267_, v_query_268_);
lean_dec_ref(v_query_268_);
lean_dec_ref(v_m_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_m_270_, lean_object* v_query_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___redArg(v_m_270_, v_query_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_index_273_; lean_object* v_key_274_; lean_object* v_value_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_index_273_ = lean_ctor_get(v___x_272_, 0);
v_key_274_ = lean_ctor_get(v___x_272_, 1);
v_value_275_ = lean_ctor_get(v___x_272_, 2);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_272_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_value_275_);
lean_inc(v_key_274_);
lean_inc(v_index_273_);
lean_dec(v___x_272_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_index_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_key_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_value_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v___x_283_; 
lean_dec(v___x_272_);
v___x_283_ = lean_box(1);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_284_, lean_object* v_query_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_m_284_, v_query_285_);
lean_dec_ref(v_query_285_);
lean_dec_ref(v_m_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_m_287_, v_a_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_value_290_; lean_object* v___x_291_; 
v_value_290_ = lean_ctor_get(v___x_289_, 2);
lean_inc(v_value_290_);
lean_dec_ref_known(v___x_289_, 3);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v_value_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_box(0);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_293_, v_a_294_);
lean_dec_ref(v_a_294_);
lean_dec_ref(v_m_293_);
return v_res_295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_335_, lean_object* v_model_336_, lean_object* v_e_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_336_, v_e_337_);
if (lean_obj_tag(v___x_343_) == 1)
{
lean_object* v___x_344_; 
lean_dec_ref(v_e_337_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; 
lean_dec(v___x_343_);
v___x_345_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_337_, v_a_339_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_599_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_599_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_599_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_599_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = l_Lean_Expr_cleanupAnnotations(v_a_346_);
v___x_356_ = l_Lean_Expr_isApp(v___x_355_);
if (v___x_356_ == 0)
{
lean_dec_ref(v___x_355_);
goto v___jp_350_;
}
else
{
lean_object* v_arg_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_arg_357_ = lean_ctor_get(v___x_355_, 1);
lean_inc_ref(v_arg_357_);
v___x_358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_355_);
v___x_359_ = l_Lean_Expr_isApp(v___x_358_);
if (v___x_359_ == 0)
{
lean_dec_ref(v___x_358_);
lean_dec_ref(v_arg_357_);
goto v___jp_350_;
}
else
{
lean_object* v_arg_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_arg_360_ = lean_ctor_get(v___x_358_, 1);
lean_inc_ref(v_arg_360_);
v___x_361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_358_);
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_Expr_isApp(v___x_361_);
if (v___x_364_ == 0)
{
lean_dec_ref(v___x_361_);
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
goto v___jp_350_;
}
else
{
lean_object* v_arg_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_arg_365_ = lean_ctor_get(v___x_361_, 1);
lean_inc_ref(v_arg_365_);
v___x_366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_361_);
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_368_ = l_Lean_Expr_isConstOf(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_370_ = l_Lean_Expr_isConstOf(v___x_366_, v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
v___x_371_ = l_Lean_Expr_isApp(v___x_366_);
if (v___x_371_ == 0)
{
lean_dec_ref(v___x_366_);
lean_dec_ref(v_arg_365_);
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
goto v___jp_350_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_366_);
v___x_373_ = l_Lean_Expr_isApp(v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v___x_372_);
lean_dec_ref(v_arg_365_);
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
goto v___jp_350_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_372_);
v___x_375_ = l_Lean_Expr_isApp(v___x_374_);
if (v___x_375_ == 0)
{
lean_dec_ref(v___x_374_);
lean_dec_ref(v_arg_365_);
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
goto v___jp_350_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_374_);
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_378_ = l_Lean_Expr_isConstOf(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_380_ = l_Lean_Expr_isConstOf(v___x_376_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_382_ = l_Lean_Expr_isConstOf(v___x_376_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_384_ = l_Lean_Expr_isConstOf(v___x_376_, v___x_383_);
lean_dec_ref(v___x_376_);
if (v___x_384_ == 0)
{
lean_dec_ref(v_arg_365_);
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
goto v___jp_350_;
}
else
{
uint8_t v___x_385_; 
lean_del_object(v___x_348_);
v___x_385_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_335_, v_arg_365_);
lean_dec_ref(v_arg_365_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; 
v___x_388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_360_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
if (lean_obj_tag(v_a_389_) == 0)
{
lean_dec_ref(v_arg_357_);
return v___x_388_;
}
else
{
lean_object* v_val_390_; lean_object* v___x_391_; 
lean_dec_ref_known(v___x_388_, 1);
v_val_390_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v_a_389_, 1);
v___x_391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_357_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
if (lean_obj_tag(v_a_392_) == 0)
{
lean_dec(v_val_390_);
return v___x_391_;
}
else
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_408_; 
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_409_);
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
else
{
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_407_; 
v_val_396_ = lean_ctor_get(v_a_392_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_a_392_);
if (v_isSharedCheck_407_ == 0)
{
v___x_398_ = v_a_392_;
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v_a_392_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = l_Rat_add(v_val_390_, v_val_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
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
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_402_);
v___x_404_ = v___x_394_;
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
}
}
else
{
lean_dec(v_val_390_);
return v___x_391_;
}
}
}
else
{
lean_dec_ref(v_arg_357_);
return v___x_388_;
}
}
}
}
else
{
uint8_t v___x_410_; 
lean_dec_ref(v___x_376_);
lean_del_object(v___x_348_);
v___x_410_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_335_, v_arg_365_);
lean_dec_ref(v_arg_365_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
v___x_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_360_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
if (lean_obj_tag(v_a_414_) == 0)
{
lean_dec_ref(v_arg_357_);
return v___x_413_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_416_; 
lean_dec_ref_known(v___x_413_, 1);
v_val_415_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v_a_414_, 1);
v___x_416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_357_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
if (lean_obj_tag(v_a_417_) == 0)
{
lean_dec(v_val_415_);
return v___x_416_;
}
else
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_433_; 
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v___x_416_, 0);
lean_dec(v_unused_434_);
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_433_;
goto v_resetjp_418_;
}
else
{
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_433_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
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
v___x_425_ = l_Rat_sub(v_val_415_, v_val_421_);
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
}
}
else
{
lean_dec(v_val_415_);
return v___x_416_;
}
}
}
else
{
lean_dec_ref(v_arg_357_);
return v___x_413_;
}
}
}
}
else
{
uint8_t v___x_435_; 
lean_dec_ref(v___x_376_);
lean_del_object(v___x_348_);
v___x_435_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_335_, v_arg_365_);
lean_dec_ref(v_arg_365_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; 
v___x_438_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_360_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
if (lean_obj_tag(v_a_439_) == 0)
{
lean_dec_ref(v_arg_357_);
return v___x_438_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_441_; 
lean_dec_ref_known(v___x_438_, 1);
v_val_440_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_a_439_, 1);
v___x_441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_357_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
if (lean_obj_tag(v_a_442_) == 0)
{
lean_dec(v_val_440_);
return v___x_441_;
}
else
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_458_; 
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___x_441_, 0);
lean_dec(v_unused_459_);
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
else
{
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_458_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_457_; 
v_val_446_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_457_ == 0)
{
v___x_448_ = v_a_442_;
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_a_442_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = l_Rat_mul(v_val_440_, v_val_446_);
lean_dec(v_val_440_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_452_);
v___x_454_ = v___x_444_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
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
}
else
{
lean_dec(v_val_440_);
return v___x_441_;
}
}
}
else
{
lean_dec_ref(v_arg_357_);
return v___x_438_;
}
}
}
}
else
{
uint8_t v___x_460_; 
lean_dec_ref(v___x_376_);
lean_del_object(v___x_348_);
v___x_460_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_335_, v_arg_365_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_335_, v_arg_365_);
lean_dec_ref(v_arg_365_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_357_);
v___x_462_ = lean_box(0);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_getNatValue_x3f(v_arg_360_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec_ref(v_arg_360_);
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
lean_dec_ref(v_arg_357_);
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
v___x_474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_357_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
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
v___x_483_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_473_);
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
lean_dec_ref(v_arg_357_);
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
else
{
lean_object* v___x_503_; 
lean_dec_ref(v_arg_365_);
v___x_503_ = l_Lean_Meta_getIntValue_x3f(v_arg_360_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_533_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_533_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_533_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_533_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
if (lean_obj_tag(v_a_504_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec_ref(v_arg_357_);
v___x_508_ = lean_box(0);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
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
lean_object* v_val_512_; lean_object* v___x_513_; 
lean_del_object(v___x_506_);
v_val_512_ = lean_ctor_get(v_a_504_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_a_504_, 1);
v___x_513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_357_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
if (lean_obj_tag(v_a_514_) == 0)
{
lean_dec(v_val_512_);
return v___x_513_;
}
else
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_531_; 
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_513_, 0);
lean_dec(v_unused_532_);
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_531_;
goto v_resetjp_515_;
}
else
{
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_531_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_val_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_530_; 
v_val_518_ = lean_ctor_get(v_a_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_520_ = v_a_514_;
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_val_518_);
lean_dec(v_a_514_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_522_ = l_Rat_ofInt(v_val_512_);
v___x_523_ = l_Rat_mul(v___x_522_, v_val_518_);
lean_dec_ref(v___x_522_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_523_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_525_);
v___x_527_ = v___x_516_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
else
{
lean_dec(v_val_512_);
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_arg_357_);
v_a_534_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_503_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_503_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
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
uint8_t v___x_542_; 
lean_dec_ref(v___x_366_);
lean_dec_ref(v_arg_365_);
lean_del_object(v___x_348_);
v___x_542_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_335_, v_arg_360_);
lean_dec_ref(v_arg_360_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_arg_357_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_335_, v_model_336_, v_arg_357_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
if (lean_obj_tag(v_a_546_) == 0)
{
return v___x_545_;
}
else
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_562_; 
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_545_, 0);
lean_dec(v_unused_563_);
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_562_;
goto v_resetjp_547_;
}
else
{
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_562_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_val_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
v_val_550_ = lean_ctor_get(v_a_546_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_561_ == 0)
{
v___x_552_ = v_a_546_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_val_550_);
lean_dec(v_a_546_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = l_Rat_neg(v_val_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_556_);
v___x_558_ = v___x_548_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
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
}
else
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v___x_564_; 
lean_dec_ref(v___x_366_);
lean_dec_ref(v_arg_365_);
lean_dec_ref(v_arg_357_);
lean_del_object(v___x_348_);
v___x_564_ = l_Lean_Meta_getNatValue_x3f(v_arg_360_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec_ref(v_arg_360_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_585_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_585_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_585_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_585_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
else
{
lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_584_; 
v_val_573_ = lean_ctor_get(v_a_565_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_584_ == 0)
{
v___x_575_ = v_a_565_;
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v_a_565_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_577_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_579_);
v___x_581_ = v___x_567_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_564_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_564_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
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
}
}
else
{
uint8_t v___x_594_; 
lean_dec_ref(v___x_361_);
lean_dec_ref(v_arg_360_);
lean_del_object(v___x_348_);
v___x_594_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_335_, v_arg_357_);
lean_dec_ref(v_arg_357_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
}
}
v___jp_350_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_box(0);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_351_);
v___x_353_ = v___x_348_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_345_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_345_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_608_, lean_object* v_model_609_, lean_object* v_e_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_608_, v_model_609_, v_e_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec_ref(v_model_609_);
lean_dec_ref(v_s_608_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_617_, lean_object* v_m_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_618_, v_a_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_621_, lean_object* v_m_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_621_, v_m_622_, v_a_623_);
lean_dec_ref(v_a_623_);
lean_dec_ref(v_m_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_nat_to_int(v_a_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_627_, lean_object* v_m_628_, lean_object* v_query_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_m_628_, v_query_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_631_, lean_object* v_m_632_, lean_object* v_query_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_631_, v_m_632_, v_query_633_);
lean_dec_ref(v_query_633_);
lean_dec_ref(v_m_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_635_, lean_object* v_m_636_, lean_object* v_query_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___redArg(v_m_636_, v_query_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_639_, lean_object* v_m_640_, lean_object* v_query_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2(v_00_u03b2_639_, v_m_640_, v_query_641_);
lean_dec_ref(v_query_641_);
lean_dec_ref(v_m_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_643_, lean_object* v_m_644_, lean_object* v_query_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___redArg(v_m_644_, v_query_645_, v_x_646_, v_x_647_, v_x_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_651_, lean_object* v_m_652_, lean_object* v_query_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_651_, v_m_652_, v_query_653_, v_x_654_, v_x_655_, v_x_656_, v_x_657_);
lean_dec_ref(v_query_653_);
lean_dec_ref(v_m_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_659_, lean_object* v_s_660_, lean_object* v_model_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_660_, v_model_661_, v_e_659_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_668_, lean_object* v_s_669_, lean_object* v_model_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_668_, v_s_669_, v_model_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec_ref(v_model_670_);
lean_dec_ref(v_s_669_);
return v_res_676_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_m_677_, v_a_678_);
if (lean_obj_tag(v___x_679_) == 0)
{
uint8_t v___x_680_; 
lean_dec_ref_known(v___x_679_, 3);
v___x_680_ = 1;
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = 0;
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_682_, lean_object* v_a_683_){
_start:
{
uint8_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_682_, v_a_683_);
lean_dec_ref(v_a_683_);
lean_dec_ref(v_m_682_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3_spec__4(lean_object* v___x_686_, lean_object* v_goal_687_, lean_object* v_structId_688_, lean_object* v_as_689_, size_t v_sz_690_, size_t v_i_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
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
lean_object* v_snd_700_; lean_object* v_a_701_; lean_object* v_fst_702_; lean_object* v_snd_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_732_; 
v_snd_700_ = lean_ctor_get(v_b_692_, 1);
lean_inc(v_snd_700_);
lean_dec_ref(v_b_692_);
v_a_701_ = lean_array_uget(v_as_689_, v_i_691_);
v_fst_702_ = lean_ctor_get(v_a_701_, 0);
v_snd_703_ = lean_ctor_get(v_a_701_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_701_);
if (v_isSharedCheck_732_ == 0)
{
v___x_705_ = v_a_701_;
v_isShared_706_ = v_isSharedCheck_732_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_snd_703_);
lean_inc(v_fst_702_);
lean_dec(v_a_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_732_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v_a_709_; uint8_t v___y_717_; uint8_t v___x_730_; 
v___x_707_ = lean_box(0);
v___x_730_ = lean_nat_dec_eq(v_structId_688_, v_snd_703_);
lean_dec(v_snd_703_);
if (v___x_730_ == 0)
{
v___y_717_ = v___x_730_;
goto v___jp_716_;
}
else
{
uint8_t v___x_731_; 
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_700_, v_fst_702_);
if (v___x_731_ == 0)
{
v___y_717_ = v___x_730_;
goto v___jp_716_;
}
else
{
lean_dec(v_fst_702_);
v_a_709_ = v_snd_700_;
goto v___jp_708_;
}
}
v___jp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v_a_709_);
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_a_709_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
size_t v___x_712_; size_t v___x_713_; 
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_i_691_, v___x_712_);
v_i_691_ = v___x_713_;
v_b_692_ = v___x_711_;
goto _start;
}
}
v___jp_716_:
{
if (v___y_717_ == 0)
{
lean_dec(v_fst_702_);
v_a_709_ = v_snd_700_;
goto v___jp_708_;
}
else
{
lean_object* v___x_718_; 
lean_inc(v_fst_702_);
v___x_718_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_686_, v_snd_700_, v_fst_702_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
if (lean_obj_tag(v_a_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_721_; 
v_val_720_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v_a_719_, 1);
v___x_721_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_687_, v_fst_702_, v_val_720_, v_snd_700_);
v_a_709_ = v___x_721_;
goto v___jp_708_;
}
else
{
lean_dec(v_a_719_);
lean_dec(v_fst_702_);
v_a_709_ = v_snd_700_;
goto v___jp_708_;
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_del_object(v___x_705_);
lean_dec(v_fst_702_);
lean_dec(v_snd_700_);
v_a_722_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_718_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_718_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3_spec__4___boxed(lean_object* v___x_733_, lean_object* v_goal_734_, lean_object* v_structId_735_, lean_object* v_as_736_, lean_object* v_sz_737_, lean_object* v_i_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
size_t v_sz_boxed_745_; size_t v_i_boxed_746_; lean_object* v_res_747_; 
v_sz_boxed_745_ = lean_unbox_usize(v_sz_737_);
lean_dec(v_sz_737_);
v_i_boxed_746_ = lean_unbox_usize(v_i_738_);
lean_dec(v_i_738_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3_spec__4(v___x_733_, v_goal_734_, v_structId_735_, v_as_736_, v_sz_boxed_745_, v_i_boxed_746_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec_ref(v_as_736_);
lean_dec(v_structId_735_);
lean_dec_ref(v_goal_734_);
lean_dec_ref(v___x_733_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3(lean_object* v___x_748_, lean_object* v_goal_749_, lean_object* v_structId_750_, lean_object* v_as_751_, size_t v_sz_752_, size_t v_i_753_, lean_object* v_b_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_lt(v_i_753_, v_sz_752_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v_b_754_);
return v___x_761_;
}
else
{
lean_object* v_snd_762_; lean_object* v_a_763_; lean_object* v_fst_764_; lean_object* v_snd_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_794_; 
v_snd_762_ = lean_ctor_get(v_b_754_, 1);
lean_inc(v_snd_762_);
lean_dec_ref(v_b_754_);
v_a_763_ = lean_array_uget(v_as_751_, v_i_753_);
v_fst_764_ = lean_ctor_get(v_a_763_, 0);
v_snd_765_ = lean_ctor_get(v_a_763_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_763_);
if (v_isSharedCheck_794_ == 0)
{
v___x_767_ = v_a_763_;
v_isShared_768_ = v_isSharedCheck_794_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snd_765_);
lean_inc(v_fst_764_);
lean_dec(v_a_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_794_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v_a_771_; uint8_t v___y_779_; uint8_t v___x_792_; 
v___x_769_ = lean_box(0);
v___x_792_ = lean_nat_dec_eq(v_structId_750_, v_snd_765_);
lean_dec(v_snd_765_);
if (v___x_792_ == 0)
{
v___y_779_ = v___x_792_;
goto v___jp_778_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_762_, v_fst_764_);
if (v___x_793_ == 0)
{
v___y_779_ = v___x_792_;
goto v___jp_778_;
}
else
{
lean_dec(v_fst_764_);
v_a_771_ = v_snd_762_;
goto v___jp_770_;
}
}
v___jp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_a_771_);
lean_ctor_set(v___x_767_, 0, v___x_769_);
v___x_773_ = v___x_767_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_a_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_753_, v___x_774_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3_spec__4(v___x_748_, v_goal_749_, v_structId_750_, v_as_751_, v_sz_752_, v___x_775_, v___x_773_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_776_;
}
}
v___jp_778_:
{
if (v___y_779_ == 0)
{
lean_dec(v_fst_764_);
v_a_771_ = v_snd_762_;
goto v___jp_770_;
}
else
{
lean_object* v___x_780_; 
lean_inc(v_fst_764_);
v___x_780_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_748_, v_snd_762_, v_fst_764_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
if (lean_obj_tag(v_a_781_) == 1)
{
lean_object* v_val_782_; lean_object* v___x_783_; 
v_val_782_ = lean_ctor_get(v_a_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v_a_781_, 1);
v___x_783_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_749_, v_fst_764_, v_val_782_, v_snd_762_);
v_a_771_ = v___x_783_;
goto v___jp_770_;
}
else
{
lean_dec(v_a_781_);
lean_dec(v_fst_764_);
v_a_771_ = v_snd_762_;
goto v___jp_770_;
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_767_);
lean_dec(v_fst_764_);
lean_dec(v_snd_762_);
v_a_784_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_780_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3___boxed(lean_object* v___x_795_, lean_object* v_goal_796_, lean_object* v_structId_797_, lean_object* v_as_798_, lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
size_t v_sz_boxed_807_; size_t v_i_boxed_808_; lean_object* v_res_809_; 
v_sz_boxed_807_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_808_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3(v___x_795_, v_goal_796_, v_structId_797_, v_as_798_, v_sz_boxed_807_, v_i_boxed_808_, v_b_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_as_798_);
lean_dec(v_structId_797_);
lean_dec_ref(v_goal_796_);
lean_dec_ref(v___x_795_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1(lean_object* v_init_810_, lean_object* v___x_811_, lean_object* v_goal_812_, lean_object* v_structId_813_, lean_object* v_n_814_, lean_object* v_b_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
if (lean_obj_tag(v_n_814_) == 0)
{
lean_object* v_cs_821_; lean_object* v___x_822_; lean_object* v___x_823_; size_t v_sz_824_; size_t v___x_825_; lean_object* v___x_826_; 
v_cs_821_ = lean_ctor_get(v_n_814_, 0);
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_b_815_);
v_sz_824_ = lean_array_size(v_cs_821_);
v___x_825_ = ((size_t)0ULL);
v___x_826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__2(v_init_810_, v___x_811_, v_goal_812_, v_structId_813_, v_cs_821_, v_sz_824_, v___x_825_, v___x_823_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_841_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_841_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_841_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_841_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_fst_831_; 
v_fst_831_ = lean_ctor_get(v_a_827_, 0);
if (lean_obj_tag(v_fst_831_) == 0)
{
lean_object* v_snd_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v_snd_832_ = lean_ctor_get(v_a_827_, 1);
lean_inc(v_snd_832_);
lean_dec(v_a_827_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_snd_832_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_833_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v_val_837_; lean_object* v___x_839_; 
lean_inc_ref(v_fst_831_);
lean_dec(v_a_827_);
v_val_837_ = lean_ctor_get(v_fst_831_, 0);
lean_inc(v_val_837_);
lean_dec_ref_known(v_fst_831_, 1);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v_val_837_);
v___x_839_ = v___x_829_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_val_837_);
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
v_a_842_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_826_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_826_);
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
else
{
lean_object* v_vs_850_; lean_object* v___x_851_; lean_object* v___x_852_; size_t v_sz_853_; size_t v___x_854_; lean_object* v___x_855_; 
v_vs_850_ = lean_ctor_get(v_n_814_, 0);
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v_b_815_);
v_sz_853_ = lean_array_size(v_vs_850_);
v___x_854_ = ((size_t)0ULL);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__3(v___x_811_, v_goal_812_, v_structId_813_, v_vs_850_, v_sz_853_, v___x_854_, v___x_852_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_870_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_870_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_870_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_870_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_fst_860_; 
v_fst_860_ = lean_ctor_get(v_a_856_, 0);
if (lean_obj_tag(v_fst_860_) == 0)
{
lean_object* v_snd_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v_snd_861_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_861_);
lean_dec(v_a_856_);
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v_snd_861_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_862_);
v___x_864_ = v___x_858_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v_val_866_; lean_object* v___x_868_; 
lean_inc_ref(v_fst_860_);
lean_dec(v_a_856_);
v_val_866_ = lean_ctor_get(v_fst_860_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v_fst_860_, 1);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v_val_866_);
v___x_868_ = v___x_858_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_val_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_a_871_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_855_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_855_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__2(lean_object* v_init_879_, lean_object* v___x_880_, lean_object* v_goal_881_, lean_object* v_structId_882_, lean_object* v_as_883_, size_t v_sz_884_, size_t v_i_885_, lean_object* v_b_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = lean_usize_dec_lt(v_i_885_, v_sz_884_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_b_886_);
return v___x_893_;
}
else
{
lean_object* v_snd_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_928_; 
v_snd_894_ = lean_ctor_get(v_b_886_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_b_886_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_b_886_, 0);
lean_dec(v_unused_929_);
v___x_896_ = v_b_886_;
v_isShared_897_ = v_isSharedCheck_928_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_snd_894_);
lean_dec(v_b_886_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_928_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_array_uget_borrowed(v_as_883_, v_i_885_);
lean_inc(v_snd_894_);
v___x_899_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1(v_init_879_, v___x_880_, v_goal_881_, v_structId_882_, v_a_898_, v_snd_894_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_919_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_919_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_919_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_919_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
if (lean_obj_tag(v_a_900_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v_a_900_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_904_);
v___x_906_ = v___x_896_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_snd_894_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_906_);
v___x_908_ = v___x_902_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_del_object(v___x_902_);
lean_dec(v_snd_894_);
v_a_911_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v_a_900_, 1);
v___x_912_ = lean_box(0);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v_a_911_);
lean_ctor_set(v___x_896_, 0, v___x_912_);
v___x_914_ = v___x_896_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_a_911_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
size_t v___x_915_; size_t v___x_916_; 
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_885_, v___x_915_);
v_i_885_ = v___x_916_;
v_b_886_ = v___x_914_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_del_object(v___x_896_);
lean_dec(v_snd_894_);
v_a_920_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_899_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_899_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__2___boxed(lean_object* v_init_930_, lean_object* v___x_931_, lean_object* v_goal_932_, lean_object* v_structId_933_, lean_object* v_as_934_, lean_object* v_sz_935_, lean_object* v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
size_t v_sz_boxed_943_; size_t v_i_boxed_944_; lean_object* v_res_945_; 
v_sz_boxed_943_ = lean_unbox_usize(v_sz_935_);
lean_dec(v_sz_935_);
v_i_boxed_944_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1_spec__2(v_init_930_, v___x_931_, v_goal_932_, v_structId_933_, v_as_934_, v_sz_boxed_943_, v_i_boxed_944_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_as_934_);
lean_dec(v_structId_933_);
lean_dec_ref(v_goal_932_);
lean_dec_ref(v___x_931_);
lean_dec_ref(v_init_930_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1___boxed(lean_object* v_init_946_, lean_object* v___x_947_, lean_object* v_goal_948_, lean_object* v_structId_949_, lean_object* v_n_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1(v_init_946_, v___x_947_, v_goal_948_, v_structId_949_, v_n_950_, v_b_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v_n_950_);
lean_dec(v_structId_949_);
lean_dec_ref(v_goal_948_);
lean_dec_ref(v___x_947_);
lean_dec_ref(v_init_946_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__5(lean_object* v___x_958_, lean_object* v_goal_959_, lean_object* v_structId_960_, lean_object* v_as_961_, size_t v_sz_962_, size_t v_i_963_, lean_object* v_b_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = lean_usize_dec_lt(v_i_963_, v_sz_962_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_b_964_);
return v___x_971_;
}
else
{
lean_object* v_snd_972_; lean_object* v_a_973_; lean_object* v_fst_974_; lean_object* v_snd_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1004_; 
v_snd_972_ = lean_ctor_get(v_b_964_, 1);
lean_inc(v_snd_972_);
lean_dec_ref(v_b_964_);
v_a_973_ = lean_array_uget(v_as_961_, v_i_963_);
v_fst_974_ = lean_ctor_get(v_a_973_, 0);
v_snd_975_ = lean_ctor_get(v_a_973_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_973_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_977_ = v_a_973_;
v_isShared_978_ = v_isSharedCheck_1004_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snd_975_);
lean_inc(v_fst_974_);
lean_dec(v_a_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1004_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v_a_981_; uint8_t v___y_989_; uint8_t v___x_1002_; 
v___x_979_ = lean_box(0);
v___x_1002_ = lean_nat_dec_eq(v_structId_960_, v_snd_975_);
lean_dec(v_snd_975_);
if (v___x_1002_ == 0)
{
v___y_989_ = v___x_1002_;
goto v___jp_988_;
}
else
{
uint8_t v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_972_, v_fst_974_);
if (v___x_1003_ == 0)
{
v___y_989_ = v___x_1002_;
goto v___jp_988_;
}
else
{
lean_dec(v_fst_974_);
v_a_981_ = v_snd_972_;
goto v___jp_980_;
}
}
v___jp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v_a_981_);
lean_ctor_set(v___x_977_, 0, v___x_979_);
v___x_983_ = v___x_977_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_a_981_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
size_t v___x_984_; size_t v___x_985_; 
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_add(v_i_963_, v___x_984_);
v_i_963_ = v___x_985_;
v_b_964_ = v___x_983_;
goto _start;
}
}
v___jp_988_:
{
if (v___y_989_ == 0)
{
lean_dec(v_fst_974_);
v_a_981_ = v_snd_972_;
goto v___jp_980_;
}
else
{
lean_object* v___x_990_; 
lean_inc(v_fst_974_);
v___x_990_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_958_, v_snd_972_, v_fst_974_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
if (lean_obj_tag(v_a_991_) == 1)
{
lean_object* v_val_992_; lean_object* v___x_993_; 
v_val_992_ = lean_ctor_get(v_a_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_a_991_, 1);
v___x_993_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_959_, v_fst_974_, v_val_992_, v_snd_972_);
v_a_981_ = v___x_993_;
goto v___jp_980_;
}
else
{
lean_dec(v_a_991_);
lean_dec(v_fst_974_);
v_a_981_ = v_snd_972_;
goto v___jp_980_;
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_del_object(v___x_977_);
lean_dec(v_fst_974_);
lean_dec(v_snd_972_);
v_a_994_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_990_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_990_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__5___boxed(lean_object* v___x_1005_, lean_object* v_goal_1006_, lean_object* v_structId_1007_, lean_object* v_as_1008_, lean_object* v_sz_1009_, lean_object* v_i_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
size_t v_sz_boxed_1017_; size_t v_i_boxed_1018_; lean_object* v_res_1019_; 
v_sz_boxed_1017_ = lean_unbox_usize(v_sz_1009_);
lean_dec(v_sz_1009_);
v_i_boxed_1018_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__5(v___x_1005_, v_goal_1006_, v_structId_1007_, v_as_1008_, v_sz_boxed_1017_, v_i_boxed_1018_, v_b_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_as_1008_);
lean_dec(v_structId_1007_);
lean_dec_ref(v_goal_1006_);
lean_dec_ref(v___x_1005_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v___x_1020_, lean_object* v_goal_1021_, lean_object* v_structId_1022_, lean_object* v_as_1023_, size_t v_sz_1024_, size_t v_i_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_lt(v_i_1025_, v_sz_1024_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_b_1026_);
return v___x_1033_;
}
else
{
lean_object* v_snd_1034_; lean_object* v_a_1035_; lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1066_; 
v_snd_1034_ = lean_ctor_get(v_b_1026_, 1);
lean_inc(v_snd_1034_);
lean_dec_ref(v_b_1026_);
v_a_1035_ = lean_array_uget(v_as_1023_, v_i_1025_);
v_fst_1036_ = lean_ctor_get(v_a_1035_, 0);
v_snd_1037_ = lean_ctor_get(v_a_1035_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_a_1035_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1039_ = v_a_1035_;
v_isShared_1040_ = v_isSharedCheck_1066_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_snd_1037_);
lean_inc(v_fst_1036_);
lean_dec(v_a_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1066_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v_a_1043_; uint8_t v___y_1051_; uint8_t v___x_1064_; 
v___x_1041_ = lean_box(0);
v___x_1064_ = lean_nat_dec_eq(v_structId_1022_, v_snd_1037_);
lean_dec(v_snd_1037_);
if (v___x_1064_ == 0)
{
v___y_1051_ = v___x_1064_;
goto v___jp_1050_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_1034_, v_fst_1036_);
if (v___x_1065_ == 0)
{
v___y_1051_ = v___x_1064_;
goto v___jp_1050_;
}
else
{
lean_dec(v_fst_1036_);
v_a_1043_ = v_snd_1034_;
goto v___jp_1042_;
}
}
v___jp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v_a_1043_);
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1045_ = v___x_1039_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_a_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_add(v_i_1025_, v___x_1046_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__5(v___x_1020_, v_goal_1021_, v_structId_1022_, v_as_1023_, v_sz_1024_, v___x_1047_, v___x_1045_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1048_;
}
}
v___jp_1050_:
{
if (v___y_1051_ == 0)
{
lean_dec(v_fst_1036_);
v_a_1043_ = v_snd_1034_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1052_; 
lean_inc(v_fst_1036_);
v___x_1052_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_1020_, v_snd_1034_, v_fst_1036_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
if (lean_obj_tag(v_a_1053_) == 1)
{
lean_object* v_val_1054_; lean_object* v___x_1055_; 
v_val_1054_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v_a_1053_, 1);
v___x_1055_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1021_, v_fst_1036_, v_val_1054_, v_snd_1034_);
v_a_1043_ = v___x_1055_;
goto v___jp_1042_;
}
else
{
lean_dec(v_a_1053_);
lean_dec(v_fst_1036_);
v_a_1043_ = v_snd_1034_;
goto v___jp_1042_;
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_1039_);
lean_dec(v_fst_1036_);
lean_dec(v_snd_1034_);
v_a_1056_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1052_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1052_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v___x_1067_, lean_object* v_goal_1068_, lean_object* v_structId_1069_, lean_object* v_as_1070_, lean_object* v_sz_1071_, lean_object* v_i_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
size_t v_sz_boxed_1079_; size_t v_i_boxed_1080_; lean_object* v_res_1081_; 
v_sz_boxed_1079_ = lean_unbox_usize(v_sz_1071_);
lean_dec(v_sz_1071_);
v_i_boxed_1080_ = lean_unbox_usize(v_i_1072_);
lean_dec(v_i_1072_);
v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v___x_1067_, v_goal_1068_, v_structId_1069_, v_as_1070_, v_sz_boxed_1079_, v_i_boxed_1080_, v_b_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec_ref(v_as_1070_);
lean_dec(v_structId_1069_);
lean_dec_ref(v_goal_1068_);
lean_dec_ref(v___x_1067_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v___x_1082_, lean_object* v_goal_1083_, lean_object* v_structId_1084_, lean_object* v_t_1085_, lean_object* v_init_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_root_1092_; lean_object* v_tail_1093_; lean_object* v___x_1094_; 
v_root_1092_ = lean_ctor_get(v_t_1085_, 0);
v_tail_1093_ = lean_ctor_get(v_t_1085_, 1);
lean_inc_ref(v_init_1086_);
v___x_1094_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__1(v_init_1086_, v___x_1082_, v_goal_1083_, v_structId_1084_, v_root_1092_, v_init_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec_ref(v_init_1086_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1131_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1131_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1131_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
if (lean_obj_tag(v_a_1095_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; 
v_a_1099_ = lean_ctor_get(v_a_1095_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v_a_1095_, 1);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v_a_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; size_t v_sz_1106_; size_t v___x_1107_; lean_object* v___x_1108_; 
lean_del_object(v___x_1097_);
v_a_1103_ = lean_ctor_get(v_a_1095_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v_a_1095_, 1);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_a_1103_);
v_sz_1106_ = lean_array_size(v_tail_1093_);
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v___x_1082_, v_goal_1083_, v_structId_1084_, v_tail_1093_, v_sz_1106_, v___x_1107_, v___x_1105_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1122_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1122_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1122_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_fst_1113_; 
v_fst_1113_ = lean_ctor_get(v_a_1109_, 0);
if (lean_obj_tag(v_fst_1113_) == 0)
{
lean_object* v_snd_1114_; lean_object* v___x_1116_; 
v_snd_1114_ = lean_ctor_get(v_a_1109_, 1);
lean_inc(v_snd_1114_);
lean_dec(v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v_snd_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_snd_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1120_; 
lean_inc_ref(v_fst_1113_);
lean_dec(v_a_1109_);
v_val_1118_ = lean_ctor_get(v_fst_1113_, 0);
lean_inc(v_val_1118_);
lean_dec_ref_known(v_fst_1113_, 1);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v_val_1118_);
v___x_1120_ = v___x_1111_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_val_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1123_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1108_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1108_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1094_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1094_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v___x_1140_, lean_object* v_goal_1141_, lean_object* v_structId_1142_, lean_object* v_t_1143_, lean_object* v_init_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1140_, v_goal_1141_, v_structId_1142_, v_t_1143_, v_init_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_t_1143_);
lean_dec(v_structId_1142_);
lean_dec_ref(v_goal_1141_);
lean_dec_ref(v___x_1140_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1151_, lean_object* v_structId_1152_, lean_object* v_model_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1160_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1159_, v_goal_1151_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_structs_1162_; lean_object* v_exprToStructIdEntries_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v_structs_1162_ = lean_ctor_get(v_a_1161_, 0);
lean_inc_ref(v_structs_1162_);
v_exprToStructIdEntries_1163_ = lean_ctor_get(v_a_1161_, 3);
lean_inc_ref(v_exprToStructIdEntries_1163_);
lean_dec(v_a_1161_);
v___x_1164_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1165_ = lean_array_get(v___x_1164_, v_structs_1162_, v_structId_1152_);
lean_dec_ref(v_structs_1162_);
v___x_1166_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_1165_, v_goal_1151_, v_structId_1152_, v_exprToStructIdEntries_1163_, v_model_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec_ref(v_exprToStructIdEntries_1163_);
lean_dec(v___x_1165_);
return v___x_1166_;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v_model_1153_);
v_a_1167_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1169_ = v___x_1160_;
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1160_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_ref_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v_ref_1171_ = lean_ctor_get(v_a_1156_, 5);
v___x_1172_ = lean_io_error_to_string(v_a_1167_);
v___x_1173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = l_Lean_MessageData_ofFormat(v___x_1173_);
lean_inc(v_ref_1171_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_ref_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1175_);
v___x_1177_ = v___x_1169_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1180_, lean_object* v_structId_1181_, lean_object* v_model_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1180_, v_structId_1181_, v_model_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_structId_1181_);
lean_dec_ref(v_goal_1180_);
return v_res_1188_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1189_, lean_object* v_m_1190_, lean_object* v_a_1191_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1190_, v_a_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1193_, lean_object* v_m_1194_, lean_object* v_a_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1193_, v_m_1194_, v_a_1195_);
lean_dec_ref(v_a_1195_);
lean_dec_ref(v_m_1194_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1198_, lean_object* v___x_1199_, lean_object* v_as_1200_, size_t v_sz_1201_, size_t v_i_1202_, lean_object* v_b_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_usize_dec_lt(v_i_1202_, v_sz_1201_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v___x_1199_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_b_1203_);
return v___x_1210_;
}
else
{
lean_object* v_snd_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1252_; 
v_snd_1211_ = lean_ctor_get(v_b_1203_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_b_1203_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_b_1203_, 0);
lean_dec(v_unused_1253_);
v___x_1213_ = v_b_1203_;
v_isShared_1214_ = v_isSharedCheck_1252_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_snd_1211_);
lean_dec(v_b_1203_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1252_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_array_uget_borrowed(v_as_1200_, v_i_1202_);
lean_inc(v_a_1215_);
v___x_1216_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1198_, v_a_1215_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v_a_1220_; uint8_t v___x_1227_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = lean_box(0);
v___x_1227_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1217_);
if (v___x_1227_ == 0)
{
lean_dec(v_a_1217_);
v_a_1220_ = v_snd_1211_;
goto v___jp_1219_;
}
else
{
lean_object* v_type_1228_; lean_object* v___x_1229_; 
v_type_1228_ = lean_ctor_get(v___x_1199_, 2);
lean_inc(v_a_1217_);
lean_inc_ref(v_type_1228_);
v___x_1229_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1228_, v_a_1217_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; uint8_t v___x_1231_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = lean_unbox(v_a_1230_);
lean_dec(v_a_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_a_1217_);
v_a_1220_ = v_snd_1211_;
goto v___jp_1219_;
}
else
{
lean_object* v_self_1232_; lean_object* v___x_1233_; 
v_self_1232_ = lean_ctor_get(v_a_1217_, 0);
lean_inc_ref(v_self_1232_);
lean_dec(v_a_1217_);
v___x_1233_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1199_, v_self_1232_);
if (lean_obj_tag(v___x_1233_) == 1)
{
lean_object* v_val_1234_; lean_object* v___x_1235_; 
v_val_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v___x_1235_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1198_, v_self_1232_, v_val_1234_, v_snd_1211_);
v_a_1220_ = v___x_1235_;
goto v___jp_1219_;
}
else
{
lean_dec(v___x_1233_);
lean_dec_ref(v_self_1232_);
v_a_1220_ = v_snd_1211_;
goto v___jp_1219_;
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec(v_a_1217_);
lean_del_object(v___x_1213_);
lean_dec(v_snd_1211_);
lean_dec_ref(v___x_1199_);
v_a_1236_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1229_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1229_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
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
v___jp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v_a_1220_);
lean_ctor_set(v___x_1213_, 0, v___x_1218_);
v___x_1222_ = v___x_1213_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1220_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
size_t v___x_1223_; size_t v___x_1224_; 
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1202_, v___x_1223_);
v_i_1202_ = v___x_1224_;
v_b_1203_ = v___x_1222_;
goto _start;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_del_object(v___x_1213_);
lean_dec(v_snd_1211_);
lean_dec_ref(v___x_1199_);
v_a_1244_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1216_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1216_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1254_, lean_object* v___x_1255_, lean_object* v_as_1256_, lean_object* v_sz_1257_, lean_object* v_i_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
size_t v_sz_boxed_1265_; size_t v_i_boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1265_ = lean_unbox_usize(v_sz_1257_);
lean_dec(v_sz_1257_);
v_i_boxed_1266_ = lean_unbox_usize(v_i_1258_);
lean_dec(v_i_1258_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1254_, v___x_1255_, v_as_1256_, v_sz_boxed_1265_, v_i_boxed_1266_, v_b_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v_as_1256_);
lean_dec_ref(v_goal_1254_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1268_, lean_object* v___x_1269_, lean_object* v_as_1270_, size_t v_sz_1271_, size_t v_i_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_lt(v_i_1272_, v_sz_1271_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref(v___x_1269_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_b_1273_);
return v___x_1280_;
}
else
{
lean_object* v_snd_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1322_; 
v_snd_1281_ = lean_ctor_get(v_b_1273_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_b_1273_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_b_1273_, 0);
lean_dec(v_unused_1323_);
v___x_1283_ = v_b_1273_;
v_isShared_1284_ = v_isSharedCheck_1322_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_snd_1281_);
lean_dec(v_b_1273_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1322_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1285_ = lean_array_uget_borrowed(v_as_1270_, v_i_1272_);
lean_inc(v_a_1285_);
v___x_1286_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1268_, v_a_1285_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v_a_1290_; uint8_t v___x_1297_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_box(0);
v___x_1297_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1287_);
if (v___x_1297_ == 0)
{
lean_dec(v_a_1287_);
v_a_1290_ = v_snd_1281_;
goto v___jp_1289_;
}
else
{
lean_object* v_type_1298_; lean_object* v___x_1299_; 
v_type_1298_ = lean_ctor_get(v___x_1269_, 2);
lean_inc(v_a_1287_);
lean_inc_ref(v_type_1298_);
v___x_1299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1298_, v_a_1287_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; uint8_t v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = lean_unbox(v_a_1300_);
lean_dec(v_a_1300_);
if (v___x_1301_ == 0)
{
lean_dec(v_a_1287_);
v_a_1290_ = v_snd_1281_;
goto v___jp_1289_;
}
else
{
lean_object* v_self_1302_; lean_object* v___x_1303_; 
v_self_1302_ = lean_ctor_get(v_a_1287_, 0);
lean_inc_ref(v_self_1302_);
lean_dec(v_a_1287_);
v___x_1303_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1269_, v_self_1302_);
if (lean_obj_tag(v___x_1303_) == 1)
{
lean_object* v_val_1304_; lean_object* v___x_1305_; 
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1268_, v_self_1302_, v_val_1304_, v_snd_1281_);
v_a_1290_ = v___x_1305_;
goto v___jp_1289_;
}
else
{
lean_dec(v___x_1303_);
lean_dec_ref(v_self_1302_);
v_a_1290_ = v_snd_1281_;
goto v___jp_1289_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1287_);
lean_del_object(v___x_1283_);
lean_dec(v_snd_1281_);
lean_dec_ref(v___x_1269_);
v_a_1306_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1299_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1299_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
v___jp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v_a_1290_);
lean_ctor_set(v___x_1283_, 0, v___x_1288_);
v___x_1292_ = v___x_1283_;
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
v___x_1294_ = lean_usize_add(v_i_1272_, v___x_1293_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1268_, v___x_1269_, v_as_1270_, v_sz_1271_, v___x_1294_, v___x_1292_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1295_;
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1283_);
lean_dec(v_snd_1281_);
lean_dec_ref(v___x_1269_);
v_a_1314_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1286_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1286_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1324_, lean_object* v___x_1325_, lean_object* v_as_1326_, lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
size_t v_sz_boxed_1335_; size_t v_i_boxed_1336_; lean_object* v_res_1337_; 
v_sz_boxed_1335_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1336_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1324_, v___x_1325_, v_as_1326_, v_sz_boxed_1335_, v_i_boxed_1336_, v_b_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v_as_1326_);
lean_dec_ref(v_goal_1324_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1338_, lean_object* v_goal_1339_, lean_object* v___x_1340_, lean_object* v_n_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
if (lean_obj_tag(v_n_1341_) == 0)
{
lean_object* v_cs_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; size_t v_sz_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v_cs_1348_ = lean_ctor_get(v_n_1341_, 0);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_b_1342_);
v_sz_1351_ = lean_array_size(v_cs_1348_);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1338_, v_goal_1339_, v___x_1340_, v_cs_1348_, v_sz_1351_, v___x_1352_, v___x_1350_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1368_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_fst_1358_; 
v_fst_1358_ = lean_ctor_get(v_a_1354_, 0);
if (lean_obj_tag(v_fst_1358_) == 0)
{
lean_object* v_snd_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v_snd_1359_ = lean_ctor_get(v_a_1354_, 1);
lean_inc(v_snd_1359_);
lean_dec(v_a_1354_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_snd_1359_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1360_);
v___x_1362_ = v___x_1356_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v_val_1364_; lean_object* v___x_1366_; 
lean_inc_ref(v_fst_1358_);
lean_dec(v_a_1354_);
v_val_1364_ = lean_ctor_get(v_fst_1358_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v_fst_1358_, 1);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_val_1364_);
v___x_1366_ = v___x_1356_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_val_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_a_1369_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1353_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1353_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_vs_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; size_t v_sz_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v_vs_1377_ = lean_ctor_get(v_n_1341_, 0);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v_b_1342_);
v_sz_1380_ = lean_array_size(v_vs_1377_);
v___x_1381_ = ((size_t)0ULL);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1339_, v___x_1340_, v_vs_1377_, v_sz_1380_, v___x_1381_, v___x_1379_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1397_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1397_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1397_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_fst_1387_; 
v_fst_1387_ = lean_ctor_get(v_a_1383_, 0);
if (lean_obj_tag(v_fst_1387_) == 0)
{
lean_object* v_snd_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v_snd_1388_ = lean_ctor_get(v_a_1383_, 1);
lean_inc(v_snd_1388_);
lean_dec(v_a_1383_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_snd_1388_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1389_);
v___x_1391_ = v___x_1385_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
lean_object* v_val_1393_; lean_object* v___x_1395_; 
lean_inc_ref(v_fst_1387_);
lean_dec(v_a_1383_);
v_val_1393_ = lean_ctor_get(v_fst_1387_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v_fst_1387_, 1);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_val_1393_);
v___x_1395_ = v___x_1385_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_val_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1382_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1382_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1406_, lean_object* v_goal_1407_, lean_object* v___x_1408_, lean_object* v_as_1409_, size_t v_sz_1410_, size_t v_i_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_usize_dec_lt(v_i_1411_, v_sz_1410_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref(v___x_1408_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_b_1412_);
return v___x_1419_;
}
else
{
lean_object* v_snd_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1454_; 
v_snd_1420_ = lean_ctor_get(v_b_1412_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_b_1412_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_b_1412_, 0);
lean_dec(v_unused_1455_);
v___x_1422_ = v_b_1412_;
v_isShared_1423_ = v_isSharedCheck_1454_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_snd_1420_);
lean_dec(v_b_1412_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1454_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_array_uget_borrowed(v_as_1409_, v_i_1411_);
lean_inc(v_snd_1420_);
lean_inc_ref(v___x_1408_);
v___x_1425_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1406_, v_goal_1407_, v___x_1408_, v_a_1424_, v_snd_1420_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1445_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1445_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1445_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
if (lean_obj_tag(v_a_1426_) == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_dec_ref(v___x_1408_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1426_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1430_);
v___x_1432_ = v___x_1422_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_snd_1420_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1432_);
v___x_1434_ = v___x_1428_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_del_object(v___x_1428_);
lean_dec(v_snd_1420_);
v_a_1437_ = lean_ctor_get(v_a_1426_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v_a_1426_, 1);
v___x_1438_ = lean_box(0);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v_a_1437_);
lean_ctor_set(v___x_1422_, 0, v___x_1438_);
v___x_1440_ = v___x_1422_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_a_1437_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
size_t v___x_1441_; size_t v___x_1442_; 
v___x_1441_ = ((size_t)1ULL);
v___x_1442_ = lean_usize_add(v_i_1411_, v___x_1441_);
v_i_1411_ = v___x_1442_;
v_b_1412_ = v___x_1440_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1422_);
lean_dec(v_snd_1420_);
lean_dec_ref(v___x_1408_);
v_a_1446_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1425_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1425_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1456_, lean_object* v_goal_1457_, lean_object* v___x_1458_, lean_object* v_as_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
size_t v_sz_boxed_1468_; size_t v_i_boxed_1469_; lean_object* v_res_1470_; 
v_sz_boxed_1468_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1469_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1456_, v_goal_1457_, v___x_1458_, v_as_1459_, v_sz_boxed_1468_, v_i_boxed_1469_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v_as_1459_);
lean_dec_ref(v_goal_1457_);
lean_dec_ref(v_init_1456_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1471_, lean_object* v_goal_1472_, lean_object* v___x_1473_, lean_object* v_n_1474_, lean_object* v_b_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1471_, v_goal_1472_, v___x_1473_, v_n_1474_, v_b_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v_n_1474_);
lean_dec_ref(v_goal_1472_);
lean_dec_ref(v_init_1471_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1482_, lean_object* v___x_1483_, lean_object* v_as_1484_, size_t v_sz_1485_, size_t v_i_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_usize_dec_lt(v_i_1486_, v_sz_1485_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_dec_ref(v___x_1483_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_b_1487_);
return v___x_1494_;
}
else
{
lean_object* v_snd_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1536_; 
v_snd_1495_ = lean_ctor_get(v_b_1487_, 1);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_b_1487_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_b_1487_, 0);
lean_dec(v_unused_1537_);
v___x_1497_ = v_b_1487_;
v_isShared_1498_ = v_isSharedCheck_1536_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_snd_1495_);
lean_dec(v_b_1487_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1536_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_array_uget_borrowed(v_as_1484_, v_i_1486_);
lean_inc(v_a_1499_);
v___x_1500_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1482_, v_a_1499_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; lean_object* v_a_1504_; uint8_t v___x_1511_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = lean_box(0);
v___x_1511_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1501_);
if (v___x_1511_ == 0)
{
lean_dec(v_a_1501_);
v_a_1504_ = v_snd_1495_;
goto v___jp_1503_;
}
else
{
lean_object* v_type_1512_; lean_object* v___x_1513_; 
v_type_1512_ = lean_ctor_get(v___x_1483_, 2);
lean_inc(v_a_1501_);
lean_inc_ref(v_type_1512_);
v___x_1513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1512_, v_a_1501_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; uint8_t v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_unbox(v_a_1514_);
lean_dec(v_a_1514_);
if (v___x_1515_ == 0)
{
lean_dec(v_a_1501_);
v_a_1504_ = v_snd_1495_;
goto v___jp_1503_;
}
else
{
lean_object* v_self_1516_; lean_object* v___x_1517_; 
v_self_1516_ = lean_ctor_get(v_a_1501_, 0);
lean_inc_ref(v_self_1516_);
lean_dec(v_a_1501_);
v___x_1517_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1483_, v_self_1516_);
if (lean_obj_tag(v___x_1517_) == 1)
{
lean_object* v_val_1518_; lean_object* v___x_1519_; 
v_val_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1482_, v_self_1516_, v_val_1518_, v_snd_1495_);
v_a_1504_ = v___x_1519_;
goto v___jp_1503_;
}
else
{
lean_dec(v___x_1517_);
lean_dec_ref(v_self_1516_);
v_a_1504_ = v_snd_1495_;
goto v___jp_1503_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1501_);
lean_del_object(v___x_1497_);
lean_dec(v_snd_1495_);
lean_dec_ref(v___x_1483_);
v_a_1520_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1513_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1513_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
v___jp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_a_1504_);
lean_ctor_set(v___x_1497_, 0, v___x_1502_);
v___x_1506_ = v___x_1497_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_a_1504_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
size_t v___x_1507_; size_t v___x_1508_; 
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1486_, v___x_1507_);
v_i_1486_ = v___x_1508_;
v_b_1487_ = v___x_1506_;
goto _start;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_del_object(v___x_1497_);
lean_dec(v_snd_1495_);
lean_dec_ref(v___x_1483_);
v_a_1528_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1500_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1500_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1538_, lean_object* v___x_1539_, lean_object* v_as_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
size_t v_sz_boxed_1549_; size_t v_i_boxed_1550_; lean_object* v_res_1551_; 
v_sz_boxed_1549_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1550_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1538_, v___x_1539_, v_as_1540_, v_sz_boxed_1549_, v_i_boxed_1550_, v_b_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_as_1540_);
lean_dec_ref(v_goal_1538_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1552_, lean_object* v___x_1553_, lean_object* v_as_1554_, size_t v_sz_1555_, size_t v_i_1556_, lean_object* v_b_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_usize_dec_lt(v_i_1556_, v_sz_1555_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_dec_ref(v___x_1553_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_b_1557_);
return v___x_1564_;
}
else
{
lean_object* v_snd_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1606_; 
v_snd_1565_ = lean_ctor_get(v_b_1557_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_b_1557_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_b_1557_, 0);
lean_dec(v_unused_1607_);
v___x_1567_ = v_b_1557_;
v_isShared_1568_ = v_isSharedCheck_1606_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_snd_1565_);
lean_dec(v_b_1557_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1606_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_array_uget_borrowed(v_as_1554_, v_i_1556_);
lean_inc(v_a_1569_);
v___x_1570_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1552_, v_a_1569_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v_a_1574_; uint8_t v___x_1581_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = lean_box(0);
v___x_1581_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1571_);
if (v___x_1581_ == 0)
{
lean_dec(v_a_1571_);
v_a_1574_ = v_snd_1565_;
goto v___jp_1573_;
}
else
{
lean_object* v_type_1582_; lean_object* v___x_1583_; 
v_type_1582_ = lean_ctor_get(v___x_1553_, 2);
lean_inc(v_a_1571_);
lean_inc_ref(v_type_1582_);
v___x_1583_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1582_, v_a_1571_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; uint8_t v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_unbox(v_a_1584_);
lean_dec(v_a_1584_);
if (v___x_1585_ == 0)
{
lean_dec(v_a_1571_);
v_a_1574_ = v_snd_1565_;
goto v___jp_1573_;
}
else
{
lean_object* v_self_1586_; lean_object* v___x_1587_; 
v_self_1586_ = lean_ctor_get(v_a_1571_, 0);
lean_inc_ref(v_self_1586_);
lean_dec(v_a_1571_);
v___x_1587_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1553_, v_self_1586_);
if (lean_obj_tag(v___x_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v___x_1589_; 
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1552_, v_self_1586_, v_val_1588_, v_snd_1565_);
v_a_1574_ = v___x_1589_;
goto v___jp_1573_;
}
else
{
lean_dec(v___x_1587_);
lean_dec_ref(v_self_1586_);
v_a_1574_ = v_snd_1565_;
goto v___jp_1573_;
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_a_1571_);
lean_del_object(v___x_1567_);
lean_dec(v_snd_1565_);
lean_dec_ref(v___x_1553_);
v_a_1590_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1583_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1583_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
v___jp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v_a_1574_);
lean_ctor_set(v___x_1567_, 0, v___x_1572_);
v___x_1576_ = v___x_1567_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_a_1574_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = ((size_t)1ULL);
v___x_1578_ = lean_usize_add(v_i_1556_, v___x_1577_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1552_, v___x_1553_, v_as_1554_, v_sz_1555_, v___x_1578_, v___x_1576_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v___x_1579_;
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_del_object(v___x_1567_);
lean_dec(v_snd_1565_);
lean_dec_ref(v___x_1553_);
v_a_1598_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1570_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1570_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1608_, lean_object* v___x_1609_, lean_object* v_as_1610_, lean_object* v_sz_1611_, lean_object* v_i_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
size_t v_sz_boxed_1619_; size_t v_i_boxed_1620_; lean_object* v_res_1621_; 
v_sz_boxed_1619_ = lean_unbox_usize(v_sz_1611_);
lean_dec(v_sz_1611_);
v_i_boxed_1620_ = lean_unbox_usize(v_i_1612_);
lean_dec(v_i_1612_);
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1608_, v___x_1609_, v_as_1610_, v_sz_boxed_1619_, v_i_boxed_1620_, v_b_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_as_1610_);
lean_dec_ref(v_goal_1608_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1622_, lean_object* v___x_1623_, lean_object* v_t_1624_, lean_object* v_init_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_root_1631_; lean_object* v_tail_1632_; lean_object* v___x_1633_; 
v_root_1631_ = lean_ctor_get(v_t_1624_, 0);
v_tail_1632_ = lean_ctor_get(v_t_1624_, 1);
lean_inc_ref(v___x_1623_);
lean_inc_ref(v_init_1625_);
v___x_1633_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1625_, v_goal_1622_, v___x_1623_, v_root_1631_, v_init_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v_init_1625_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1670_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1670_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1670_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
if (lean_obj_tag(v_a_1634_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; 
lean_dec_ref(v___x_1623_);
v_a_1638_ = lean_ctor_get(v_a_1634_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v_a_1634_, 1);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_a_1638_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; size_t v_sz_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
lean_del_object(v___x_1636_);
v_a_1642_ = lean_ctor_get(v_a_1634_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v_a_1634_, 1);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_a_1642_);
v_sz_1645_ = lean_array_size(v_tail_1632_);
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1622_, v___x_1623_, v_tail_1632_, v_sz_1645_, v___x_1646_, v___x_1644_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1661_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1661_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1661_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_fst_1652_; 
v_fst_1652_ = lean_ctor_get(v_a_1648_, 0);
if (lean_obj_tag(v_fst_1652_) == 0)
{
lean_object* v_snd_1653_; lean_object* v___x_1655_; 
v_snd_1653_ = lean_ctor_get(v_a_1648_, 1);
lean_inc(v_snd_1653_);
lean_dec(v_a_1648_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v_snd_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_snd_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
else
{
lean_object* v_val_1657_; lean_object* v___x_1659_; 
lean_inc_ref(v_fst_1652_);
lean_dec(v_a_1648_);
v_val_1657_ = lean_ctor_get(v_fst_1652_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v_fst_1652_, 1);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v_val_1657_);
v___x_1659_ = v___x_1650_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_val_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1647_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1647_);
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
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v___x_1623_);
v_a_1671_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1633_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1633_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1679_, lean_object* v___x_1680_, lean_object* v_t_1681_, lean_object* v_init_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1679_, v___x_1680_, v_t_1681_, v_init_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v_t_1681_);
lean_dec_ref(v_goal_1679_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1689_, lean_object* v_as_1690_, size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_b_1693_);
return v___x_1700_;
}
else
{
lean_object* v_snd_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1732_; 
v_snd_1701_ = lean_ctor_get(v_b_1693_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_b_1693_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v_b_1693_, 0);
lean_dec(v_unused_1733_);
v___x_1703_ = v_b_1693_;
v_isShared_1704_ = v_isSharedCheck_1732_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snd_1701_);
lean_dec(v_b_1693_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1732_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_a_1705_; lean_object* v___x_1706_; 
v_a_1705_ = lean_array_uget_borrowed(v_as_1690_, v_i_1692_);
lean_inc(v_a_1705_);
v___x_1706_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1689_, v_a_1705_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v_self_1708_; lean_object* v___x_1709_; lean_object* v_a_1711_; lean_object* v___x_1718_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v_self_1708_ = lean_ctor_get(v_a_1707_, 0);
lean_inc_ref_n(v_self_1708_, 2);
lean_dec(v_a_1707_);
v___x_1709_ = lean_box(0);
v___x_1718_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1708_);
if (lean_obj_tag(v___x_1718_) == 1)
{
lean_object* v_val_1719_; lean_object* v___x_1720_; 
v_val_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1701_, v_val_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1701_, v_self_1708_);
lean_dec_ref(v_self_1708_);
if (lean_obj_tag(v___x_1721_) == 1)
{
lean_object* v_val_1722_; lean_object* v___x_1723_; 
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1689_, v_val_1719_, v_val_1722_, v_snd_1701_);
v_a_1711_ = v___x_1723_;
goto v___jp_1710_;
}
else
{
lean_dec(v___x_1721_);
lean_dec(v_val_1719_);
v_a_1711_ = v_snd_1701_;
goto v___jp_1710_;
}
}
else
{
lean_dec_ref_known(v___x_1720_, 1);
lean_dec(v_val_1719_);
lean_dec_ref(v_self_1708_);
v_a_1711_ = v_snd_1701_;
goto v___jp_1710_;
}
}
else
{
lean_dec(v___x_1718_);
lean_dec_ref(v_self_1708_);
v_a_1711_ = v_snd_1701_;
goto v___jp_1710_;
}
v___jp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_a_1711_);
lean_ctor_set(v___x_1703_, 0, v___x_1709_);
v___x_1713_ = v___x_1703_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_a_1711_);
v___x_1713_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
size_t v___x_1714_; size_t v___x_1715_; 
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_i_1692_, v___x_1714_);
v_i_1692_ = v___x_1715_;
v_b_1693_ = v___x_1713_;
goto _start;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_del_object(v___x_1703_);
lean_dec(v_snd_1701_);
v_a_1724_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1706_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1706_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1734_, lean_object* v_as_1735_, lean_object* v_sz_1736_, lean_object* v_i_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
size_t v_sz_boxed_1744_; size_t v_i_boxed_1745_; lean_object* v_res_1746_; 
v_sz_boxed_1744_ = lean_unbox_usize(v_sz_1736_);
lean_dec(v_sz_1736_);
v_i_boxed_1745_ = lean_unbox_usize(v_i_1737_);
lean_dec(v_i_1737_);
v_res_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1734_, v_as_1735_, v_sz_boxed_1744_, v_i_boxed_1745_, v_b_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v_as_1735_);
lean_dec_ref(v_goal_1734_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1747_, lean_object* v_as_1748_, size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_lt(v_i_1750_, v_sz_1749_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_b_1751_);
return v___x_1758_;
}
else
{
lean_object* v_snd_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1790_; 
v_snd_1759_ = lean_ctor_get(v_b_1751_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_b_1751_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_b_1751_, 0);
lean_dec(v_unused_1791_);
v___x_1761_ = v_b_1751_;
v_isShared_1762_ = v_isSharedCheck_1790_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_snd_1759_);
lean_dec(v_b_1751_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1790_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_array_uget_borrowed(v_as_1748_, v_i_1750_);
lean_inc(v_a_1763_);
v___x_1764_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1747_, v_a_1763_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_self_1766_; lean_object* v___x_1767_; lean_object* v_a_1769_; lean_object* v___x_1776_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v_self_1766_ = lean_ctor_get(v_a_1765_, 0);
lean_inc_ref_n(v_self_1766_, 2);
lean_dec(v_a_1765_);
v___x_1767_ = lean_box(0);
v___x_1776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1766_);
if (lean_obj_tag(v___x_1776_) == 1)
{
lean_object* v_val_1777_; lean_object* v___x_1778_; 
v_val_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1759_, v_val_1777_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1759_, v_self_1766_);
lean_dec_ref(v_self_1766_);
if (lean_obj_tag(v___x_1779_) == 1)
{
lean_object* v_val_1780_; lean_object* v___x_1781_; 
v_val_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1747_, v_val_1777_, v_val_1780_, v_snd_1759_);
v_a_1769_ = v___x_1781_;
goto v___jp_1768_;
}
else
{
lean_dec(v___x_1779_);
lean_dec(v_val_1777_);
v_a_1769_ = v_snd_1759_;
goto v___jp_1768_;
}
}
else
{
lean_dec_ref_known(v___x_1778_, 1);
lean_dec(v_val_1777_);
lean_dec_ref(v_self_1766_);
v_a_1769_ = v_snd_1759_;
goto v___jp_1768_;
}
}
else
{
lean_dec(v___x_1776_);
lean_dec_ref(v_self_1766_);
v_a_1769_ = v_snd_1759_;
goto v___jp_1768_;
}
v___jp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v_a_1769_);
lean_ctor_set(v___x_1761_, 0, v___x_1767_);
v___x_1771_ = v___x_1761_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_a_1769_);
v___x_1771_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_add(v_i_1750_, v___x_1772_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1747_, v_as_1748_, v_sz_1749_, v___x_1773_, v___x_1771_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1774_;
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_del_object(v___x_1761_);
lean_dec(v_snd_1759_);
v_a_1782_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1764_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1764_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1792_, lean_object* v_as_1793_, lean_object* v_sz_1794_, lean_object* v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1794_);
lean_dec(v_sz_1794_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1792_, v_as_1793_, v_sz_boxed_1802_, v_i_boxed_1803_, v_b_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v_as_1793_);
lean_dec_ref(v_goal_1792_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1805_, lean_object* v_as_1806_, size_t v_sz_1807_, size_t v_i_1808_, lean_object* v_b_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_usize_dec_lt(v_i_1808_, v_sz_1807_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_b_1809_);
return v___x_1816_;
}
else
{
lean_object* v_snd_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1848_; 
v_snd_1817_ = lean_ctor_get(v_b_1809_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_b_1809_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v_b_1809_, 0);
lean_dec(v_unused_1849_);
v___x_1819_ = v_b_1809_;
v_isShared_1820_ = v_isSharedCheck_1848_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snd_1817_);
lean_dec(v_b_1809_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1848_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_a_1821_; lean_object* v___x_1822_; 
v_a_1821_ = lean_array_uget_borrowed(v_as_1806_, v_i_1808_);
lean_inc(v_a_1821_);
v___x_1822_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1805_, v_a_1821_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v_self_1824_; lean_object* v___x_1825_; lean_object* v_a_1827_; lean_object* v___x_1834_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v_self_1824_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref_n(v_self_1824_, 2);
lean_dec(v_a_1823_);
v___x_1825_ = lean_box(0);
v___x_1834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1824_);
if (lean_obj_tag(v___x_1834_) == 1)
{
lean_object* v_val_1835_; lean_object* v___x_1836_; 
v_val_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1817_, v_val_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1817_, v_self_1824_);
lean_dec_ref(v_self_1824_);
if (lean_obj_tag(v___x_1837_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1839_; 
v_val_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1805_, v_val_1835_, v_val_1838_, v_snd_1817_);
v_a_1827_ = v___x_1839_;
goto v___jp_1826_;
}
else
{
lean_dec(v___x_1837_);
lean_dec(v_val_1835_);
v_a_1827_ = v_snd_1817_;
goto v___jp_1826_;
}
}
else
{
lean_dec_ref_known(v___x_1836_, 1);
lean_dec(v_val_1835_);
lean_dec_ref(v_self_1824_);
v_a_1827_ = v_snd_1817_;
goto v___jp_1826_;
}
}
else
{
lean_dec(v___x_1834_);
lean_dec_ref(v_self_1824_);
v_a_1827_ = v_snd_1817_;
goto v___jp_1826_;
}
v___jp_1826_:
{
lean_object* v___x_1829_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v_a_1827_);
lean_ctor_set(v___x_1819_, 0, v___x_1825_);
v___x_1829_ = v___x_1819_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_a_1827_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
size_t v___x_1830_; size_t v___x_1831_; 
v___x_1830_ = ((size_t)1ULL);
v___x_1831_ = lean_usize_add(v_i_1808_, v___x_1830_);
v_i_1808_ = v___x_1831_;
v_b_1809_ = v___x_1829_;
goto _start;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1840_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1822_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1822_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1850_, lean_object* v_as_1851_, lean_object* v_sz_1852_, lean_object* v_i_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
size_t v_sz_boxed_1860_; size_t v_i_boxed_1861_; lean_object* v_res_1862_; 
v_sz_boxed_1860_ = lean_unbox_usize(v_sz_1852_);
lean_dec(v_sz_1852_);
v_i_boxed_1861_ = lean_unbox_usize(v_i_1853_);
lean_dec(v_i_1853_);
v_res_1862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1850_, v_as_1851_, v_sz_boxed_1860_, v_i_boxed_1861_, v_b_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec_ref(v_as_1851_);
lean_dec_ref(v_goal_1850_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1863_, lean_object* v_as_1864_, size_t v_sz_1865_, size_t v_i_1866_, lean_object* v_b_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_usize_dec_lt(v_i_1866_, v_sz_1865_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_b_1867_);
return v___x_1874_;
}
else
{
lean_object* v_snd_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1906_; 
v_snd_1875_ = lean_ctor_get(v_b_1867_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_b_1867_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; 
v_unused_1907_ = lean_ctor_get(v_b_1867_, 0);
lean_dec(v_unused_1907_);
v___x_1877_ = v_b_1867_;
v_isShared_1878_ = v_isSharedCheck_1906_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_snd_1875_);
lean_dec(v_b_1867_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1906_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_array_uget_borrowed(v_as_1864_, v_i_1866_);
lean_inc(v_a_1879_);
v___x_1880_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1863_, v_a_1879_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_self_1882_; lean_object* v___x_1883_; lean_object* v_a_1885_; lean_object* v___x_1892_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_self_1882_ = lean_ctor_get(v_a_1881_, 0);
lean_inc_ref_n(v_self_1882_, 2);
lean_dec(v_a_1881_);
v___x_1883_ = lean_box(0);
v___x_1892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1882_);
if (lean_obj_tag(v___x_1892_) == 1)
{
lean_object* v_val_1893_; lean_object* v___x_1894_; 
v_val_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_val_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1875_, v_val_1893_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1875_, v_self_1882_);
lean_dec_ref(v_self_1882_);
if (lean_obj_tag(v___x_1895_) == 1)
{
lean_object* v_val_1896_; lean_object* v___x_1897_; 
v_val_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_val_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1863_, v_val_1893_, v_val_1896_, v_snd_1875_);
v_a_1885_ = v___x_1897_;
goto v___jp_1884_;
}
else
{
lean_dec(v___x_1895_);
lean_dec(v_val_1893_);
v_a_1885_ = v_snd_1875_;
goto v___jp_1884_;
}
}
else
{
lean_dec_ref_known(v___x_1894_, 1);
lean_dec(v_val_1893_);
lean_dec_ref(v_self_1882_);
v_a_1885_ = v_snd_1875_;
goto v___jp_1884_;
}
}
else
{
lean_dec(v___x_1892_);
lean_dec_ref(v_self_1882_);
v_a_1885_ = v_snd_1875_;
goto v___jp_1884_;
}
v___jp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v_a_1885_);
lean_ctor_set(v___x_1877_, 0, v___x_1883_);
v___x_1887_ = v___x_1877_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_a_1885_);
v___x_1887_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
size_t v___x_1888_; size_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = ((size_t)1ULL);
v___x_1889_ = lean_usize_add(v_i_1866_, v___x_1888_);
v___x_1890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1863_, v_as_1864_, v_sz_1865_, v___x_1889_, v___x_1887_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1890_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_del_object(v___x_1877_);
lean_dec(v_snd_1875_);
v_a_1898_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1880_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1880_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1908_, lean_object* v_as_1909_, lean_object* v_sz_1910_, lean_object* v_i_1911_, lean_object* v_b_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
size_t v_sz_boxed_1918_; size_t v_i_boxed_1919_; lean_object* v_res_1920_; 
v_sz_boxed_1918_ = lean_unbox_usize(v_sz_1910_);
lean_dec(v_sz_1910_);
v_i_boxed_1919_ = lean_unbox_usize(v_i_1911_);
lean_dec(v_i_1911_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1908_, v_as_1909_, v_sz_boxed_1918_, v_i_boxed_1919_, v_b_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v_as_1909_);
lean_dec_ref(v_goal_1908_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1921_, lean_object* v_goal_1922_, lean_object* v_n_1923_, lean_object* v_b_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
if (lean_obj_tag(v_n_1923_) == 0)
{
lean_object* v_cs_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; size_t v_sz_1933_; size_t v___x_1934_; lean_object* v___x_1935_; 
v_cs_1930_ = lean_ctor_get(v_n_1923_, 0);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v_b_1924_);
v_sz_1933_ = lean_array_size(v_cs_1930_);
v___x_1934_ = ((size_t)0ULL);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1921_, v_goal_1922_, v_cs_1930_, v_sz_1933_, v___x_1934_, v___x_1932_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1950_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1950_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1950_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_fst_1940_; 
v_fst_1940_ = lean_ctor_get(v_a_1936_, 0);
if (lean_obj_tag(v_fst_1940_) == 0)
{
lean_object* v_snd_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v_snd_1941_ = lean_ctor_get(v_a_1936_, 1);
lean_inc(v_snd_1941_);
lean_dec(v_a_1936_);
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_snd_1941_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1942_);
v___x_1944_ = v___x_1938_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
else
{
lean_object* v_val_1946_; lean_object* v___x_1948_; 
lean_inc_ref(v_fst_1940_);
lean_dec(v_a_1936_);
v_val_1946_ = lean_ctor_get(v_fst_1940_, 0);
lean_inc(v_val_1946_);
lean_dec_ref_known(v_fst_1940_, 1);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v_val_1946_);
v___x_1948_ = v___x_1938_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_val_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1935_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1935_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_object* v_vs_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; 
v_vs_1959_ = lean_ctor_get(v_n_1923_, 0);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v_b_1924_);
v_sz_1962_ = lean_array_size(v_vs_1959_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1922_, v_vs_1959_, v_sz_1962_, v___x_1963_, v___x_1961_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1979_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_fst_1969_; 
v_fst_1969_ = lean_ctor_get(v_a_1965_, 0);
if (lean_obj_tag(v_fst_1969_) == 0)
{
lean_object* v_snd_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v_snd_1970_ = lean_ctor_get(v_a_1965_, 1);
lean_inc(v_snd_1970_);
lean_dec(v_a_1965_);
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_snd_1970_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1971_);
v___x_1973_ = v___x_1967_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
else
{
lean_object* v_val_1975_; lean_object* v___x_1977_; 
lean_inc_ref(v_fst_1969_);
lean_dec(v_a_1965_);
v_val_1975_ = lean_ctor_get(v_fst_1969_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_fst_1969_, 1);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_val_1975_);
v___x_1977_ = v___x_1967_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_val_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1964_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1964_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1988_, lean_object* v_goal_1989_, lean_object* v_as_1990_, size_t v_sz_1991_, size_t v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_b_1993_);
return v___x_2000_;
}
else
{
lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2035_; 
v_snd_2001_ = lean_ctor_get(v_b_1993_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_b_1993_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_b_1993_, 0);
lean_dec(v_unused_2036_);
v___x_2003_ = v_b_1993_;
v_isShared_2004_ = v_isSharedCheck_2035_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_dec(v_b_1993_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2035_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_array_uget_borrowed(v_as_1990_, v_i_1992_);
lean_inc(v_snd_2001_);
v___x_2006_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1988_, v_goal_1989_, v_a_2005_, v_snd_2001_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2026_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2026_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2026_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
if (lean_obj_tag(v_a_2007_) == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_a_2007_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2011_);
v___x_2013_ = v___x_2003_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_snd_2001_);
v___x_2013_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2013_);
v___x_2015_ = v___x_2009_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_del_object(v___x_2009_);
lean_dec(v_snd_2001_);
v_a_2018_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v_a_2007_, 1);
v___x_2019_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_a_2018_);
lean_ctor_set(v___x_2003_, 0, v___x_2019_);
v___x_2021_ = v___x_2003_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_a_2018_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
size_t v___x_2022_; size_t v___x_2023_; 
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_1992_, v___x_2022_);
v_i_1992_ = v___x_2023_;
v_b_1993_ = v___x_2021_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_del_object(v___x_2003_);
lean_dec(v_snd_2001_);
v_a_2027_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2006_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2006_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_2037_, lean_object* v_goal_2038_, lean_object* v_as_2039_, lean_object* v_sz_2040_, lean_object* v_i_2041_, lean_object* v_b_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
size_t v_sz_boxed_2048_; size_t v_i_boxed_2049_; lean_object* v_res_2050_; 
v_sz_boxed_2048_ = lean_unbox_usize(v_sz_2040_);
lean_dec(v_sz_2040_);
v_i_boxed_2049_ = lean_unbox_usize(v_i_2041_);
lean_dec(v_i_2041_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_2037_, v_goal_2038_, v_as_2039_, v_sz_boxed_2048_, v_i_boxed_2049_, v_b_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec_ref(v_as_2039_);
lean_dec_ref(v_goal_2038_);
lean_dec_ref(v_init_2037_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_2051_, lean_object* v_goal_2052_, lean_object* v_n_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2051_, v_goal_2052_, v_n_2053_, v_b_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_n_2053_);
lean_dec_ref(v_goal_2052_);
lean_dec_ref(v_init_2051_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_2061_, lean_object* v_t_2062_, lean_object* v_init_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_root_2069_; lean_object* v_tail_2070_; lean_object* v___x_2071_; 
v_root_2069_ = lean_ctor_get(v_t_2062_, 0);
v_tail_2070_ = lean_ctor_get(v_t_2062_, 1);
lean_inc_ref(v_init_2063_);
v___x_2071_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_2063_, v_goal_2061_, v_root_2069_, v_init_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec_ref(v_init_2063_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2108_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2108_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2108_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
if (lean_obj_tag(v_a_2072_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; 
v_a_2076_ = lean_ctor_get(v_a_2072_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v_a_2072_, 1);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v_a_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; size_t v_sz_2083_; size_t v___x_2084_; lean_object* v___x_2085_; 
lean_del_object(v___x_2074_);
v_a_2080_ = lean_ctor_get(v_a_2072_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v_a_2072_, 1);
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v_a_2080_);
v_sz_2083_ = lean_array_size(v_tail_2070_);
v___x_2084_ = ((size_t)0ULL);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_2061_, v_tail_2070_, v_sz_2083_, v___x_2084_, v___x_2082_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2099_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2099_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2099_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_fst_2090_; 
v_fst_2090_ = lean_ctor_get(v_a_2086_, 0);
if (lean_obj_tag(v_fst_2090_) == 0)
{
lean_object* v_snd_2091_; lean_object* v___x_2093_; 
v_snd_2091_ = lean_ctor_get(v_a_2086_, 1);
lean_inc(v_snd_2091_);
lean_dec(v_a_2086_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v_snd_2091_);
v___x_2093_ = v___x_2088_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_snd_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2097_; 
lean_inc_ref(v_fst_2090_);
lean_dec(v_a_2086_);
v_val_2095_ = lean_ctor_get(v_fst_2090_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v_fst_2090_, 1);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v_val_2095_);
v___x_2097_ = v___x_2088_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_val_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
v_a_2100_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2085_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2085_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_a_2109_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2071_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2071_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2117_, lean_object* v_t_2118_, lean_object* v_init_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2117_, v_t_2118_, v_init_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_t_2118_);
lean_dec_ref(v_goal_2117_);
return v_res_2125_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v_cellCount_2126_; lean_object* v___x_2127_; 
v_cellCount_2126_ = lean_unsigned_to_nat(16u);
v___x_2127_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v_cellCount_2128_; lean_object* v___x_2129_; 
v_cellCount_2128_ = lean_unsigned_to_nat(16u);
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2128_);
return v___x_2129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v_model_2133_; 
v___x_2130_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2131_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2132_ = lean_unsigned_to_nat(0u);
v_model_2133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_model_2133_, 0, v___x_2132_);
lean_ctor_set(v_model_2133_, 1, v___x_2131_);
lean_ctor_set(v_model_2133_, 2, v___x_2130_);
return v_model_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2141_, lean_object* v_structId_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2149_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2148_, v_goal_2141_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v_toGoalState_2151_; lean_object* v_structs_2152_; lean_object* v_exprs_2153_; lean_object* v___x_2154_; lean_object* v_model_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v_toGoalState_2151_ = lean_ctor_get(v_goal_2141_, 0);
v_structs_2152_ = lean_ctor_get(v_a_2150_, 0);
lean_inc_ref(v_structs_2152_);
lean_dec(v_a_2150_);
v_exprs_2153_ = lean_ctor_get(v_toGoalState_2151_, 2);
v___x_2154_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2155_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2);
v___x_2156_ = lean_array_get(v___x_2154_, v_structs_2152_, v_structId_2142_);
lean_dec_ref(v_structs_2152_);
lean_inc(v___x_2156_);
v___x_2157_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2141_, v___x_2156_, v_exprs_2153_, v_model_2155_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2159_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2141_, v_structId_2142_, v_a_2158_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2141_, v_exprs_2153_, v_a_2160_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v_type_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v_type_2163_ = lean_ctor_get(v___x_2156_, 2);
lean_inc_ref(v_type_2163_);
lean_dec(v___x_2156_);
v___x_2164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2164_, 0, v_type_2163_);
v___x_2165_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2141_, v___x_2164_, v_a_2162_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__6));
v___x_2168_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2167_, v_a_2166_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; 
v_unused_2176_ = lean_ctor_get(v___x_2168_, 0);
lean_dec(v_unused_2176_);
v___x_2170_ = v___x_2168_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_dec(v___x_2168_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v_a_2166_);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2166_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_a_2166_);
v_a_2177_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2168_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2168_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
return v___x_2165_;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v___x_2156_);
v_a_2185_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2161_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2161_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v___x_2156_);
v_a_2193_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2159_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2159_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v___x_2156_);
v_a_2201_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2157_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2157_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2221_; 
v_a_2209_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2211_ = v___x_2149_;
v_isShared_2212_ = v_isSharedCheck_2221_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2149_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2221_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v_ref_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v_ref_2213_ = lean_ctor_get(v_a_2145_, 5);
v___x_2214_ = lean_io_error_to_string(v_a_2209_);
v___x_2215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
v___x_2216_ = l_Lean_MessageData_ofFormat(v___x_2215_);
lean_inc(v_ref_2213_);
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_ref_2213_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2217_);
v___x_2219_ = v___x_2211_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2222_, lean_object* v_structId_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2222_, v_structId_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_structId_2223_);
lean_dec_ref(v_goal_2222_);
return v_res_2229_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
size_t v_x_358__boxed_50_; lean_object* v_res_51_; 
v_x_358__boxed_50_ = lean_unbox_usize(v_x_48_);
lean_dec(v_x_48_);
v_res_51_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_47_, v_x_358__boxed_50_, v_x_49_);
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
size_t v_x_463__boxed_102_; lean_object* v_res_103_; 
v_x_463__boxed_102_ = lean_unbox_usize(v_x_100_);
lean_dec(v_x_100_);
v_res_103_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_98_, v_x_99_, v_x_463__boxed_102_, v_x_101_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v_key_194_; lean_object* v_value_195_; lean_object* v_tail_196_; uint8_t v___x_197_; 
v_key_194_ = lean_ctor_get(v_x_192_, 0);
v_value_195_ = lean_ctor_get(v_x_192_, 1);
v_tail_196_ = lean_ctor_get(v_x_192_, 2);
v___x_197_ = lean_expr_eqv(v_key_194_, v_a_191_);
if (v___x_197_ == 0)
{
v_x_192_ = v_tail_196_;
goto _start;
}
else
{
lean_object* v___x_199_; 
lean_inc(v_value_195_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_value_195_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_200_, lean_object* v_x_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_200_, v_x_201_);
lean_dec(v_x_201_);
lean_dec_ref(v_a_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(lean_object* v_m_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_buckets_205_; lean_object* v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v_fold_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_buckets_205_ = lean_ctor_get(v_m_203_, 1);
v___x_206_ = lean_array_get_size(v_buckets_205_);
v___x_207_ = l_Lean_Expr_hash(v_a_204_);
v___x_208_ = 32ULL;
v___x_209_ = lean_uint64_shift_right(v___x_207_, v___x_208_);
v_fold_210_ = lean_uint64_xor(v___x_207_, v___x_209_);
v___x_211_ = 16ULL;
v___x_212_ = lean_uint64_shift_right(v_fold_210_, v___x_211_);
v___x_213_ = lean_uint64_xor(v_fold_210_, v___x_212_);
v___x_214_ = lean_uint64_to_usize(v___x_213_);
v___x_215_ = lean_usize_of_nat(v___x_206_);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_sub(v___x_215_, v___x_216_);
v___x_218_ = lean_usize_land(v___x_214_, v___x_217_);
v___x_219_ = lean_array_uget_borrowed(v_buckets_205_, v___x_218_);
v___x_220_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_204_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(lean_object* v_m_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_221_, v_a_222_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_m_221_);
return v_res_223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(lean_object* v_s_263_, lean_object* v_model_264_, lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_264_, v_e_265_);
if (lean_obj_tag(v___x_271_) == 1)
{
lean_object* v___x_272_; 
lean_dec_ref(v_e_265_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; 
lean_dec(v___x_271_);
v___x_273_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_265_, v_a_267_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_527_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_527_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_527_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_527_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = l_Lean_Expr_cleanupAnnotations(v_a_274_);
v___x_284_ = l_Lean_Expr_isApp(v___x_283_);
if (v___x_284_ == 0)
{
lean_dec_ref(v___x_283_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_arg_285_ = lean_ctor_get(v___x_283_, 1);
lean_inc_ref(v_arg_285_);
v___x_286_ = l_Lean_Expr_appFnCleanup___redArg(v___x_283_);
v___x_287_ = l_Lean_Expr_isApp(v___x_286_);
if (v___x_287_ == 0)
{
lean_dec_ref(v___x_286_);
lean_dec_ref(v_arg_285_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_arg_288_ = lean_ctor_get(v___x_286_, 1);
lean_inc_ref(v_arg_288_);
v___x_289_ = l_Lean_Expr_appFnCleanup___redArg(v___x_286_);
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2));
v___x_291_ = l_Lean_Expr_isConstOf(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_Expr_isApp(v___x_289_);
if (v___x_292_ == 0)
{
lean_dec_ref(v___x_289_);
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
goto v___jp_278_;
}
else
{
lean_object* v_arg_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_arg_293_ = lean_ctor_get(v___x_289_, 1);
lean_inc_ref(v_arg_293_);
v___x_294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_289_);
v___x_295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5));
v___x_296_ = l_Lean_Expr_isConstOf(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8));
v___x_298_ = l_Lean_Expr_isConstOf(v___x_294_, v___x_297_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_Expr_isApp(v___x_294_);
if (v___x_299_ == 0)
{
lean_dec_ref(v___x_294_);
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
goto v___jp_278_;
}
else
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_294_);
v___x_301_ = l_Lean_Expr_isApp(v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref(v___x_300_);
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
goto v___jp_278_;
}
else
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = l_Lean_Expr_appFnCleanup___redArg(v___x_300_);
v___x_303_ = l_Lean_Expr_isApp(v___x_302_);
if (v___x_303_ == 0)
{
lean_dec_ref(v___x_302_);
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
goto v___jp_278_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_302_);
v___x_305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11));
v___x_306_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14));
v___x_308_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17));
v___x_310_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20));
v___x_312_ = l_Lean_Expr_isConstOf(v___x_304_, v___x_311_);
lean_dec_ref(v___x_304_);
if (v___x_312_ == 0)
{
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
goto v___jp_278_;
}
else
{
uint8_t v___x_313_; 
lean_del_object(v___x_276_);
v___x_313_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_263_, v_arg_293_);
lean_dec_ref(v_arg_293_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_288_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
if (lean_obj_tag(v_a_317_) == 0)
{
lean_dec_ref(v_arg_285_);
return v___x_316_;
}
else
{
lean_object* v_val_318_; lean_object* v___x_319_; 
lean_dec_ref_known(v___x_316_, 1);
v_val_318_ = lean_ctor_get(v_a_317_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v_a_317_, 1);
v___x_319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_285_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
if (lean_obj_tag(v_a_320_) == 0)
{
lean_dec(v_val_318_);
return v___x_319_;
}
else
{
lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_336_; 
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___x_319_, 0);
lean_dec(v_unused_337_);
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_336_;
goto v_resetjp_321_;
}
else
{
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_336_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_val_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_335_; 
v_val_324_ = lean_ctor_get(v_a_320_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_a_320_);
if (v_isSharedCheck_335_ == 0)
{
v___x_326_ = v_a_320_;
v_isShared_327_ = v_isSharedCheck_335_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_val_324_);
lean_dec(v_a_320_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_335_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = l_Rat_add(v_val_318_, v_val_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_330_);
v___x_332_ = v___x_322_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
else
{
lean_dec(v_val_318_);
return v___x_319_;
}
}
}
else
{
lean_dec_ref(v_arg_285_);
return v___x_316_;
}
}
}
}
else
{
uint8_t v___x_338_; 
lean_dec_ref(v___x_304_);
lean_del_object(v___x_276_);
v___x_338_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_263_, v_arg_293_);
lean_dec_ref(v_arg_293_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_288_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
if (lean_obj_tag(v_a_342_) == 0)
{
lean_dec_ref(v_arg_285_);
return v___x_341_;
}
else
{
lean_object* v_val_343_; lean_object* v___x_344_; 
lean_dec_ref_known(v___x_341_, 1);
v_val_343_ = lean_ctor_get(v_a_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_a_342_, 1);
v___x_344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_285_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
if (lean_obj_tag(v_a_345_) == 0)
{
lean_dec(v_val_343_);
return v___x_344_;
}
else
{
lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_361_; 
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v___x_344_, 0);
lean_dec(v_unused_362_);
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_361_;
goto v_resetjp_346_;
}
else
{
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_361_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_val_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_360_; 
v_val_349_ = lean_ctor_get(v_a_345_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v_a_345_);
if (v_isSharedCheck_360_ == 0)
{
v___x_351_ = v_a_345_;
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_val_349_);
lean_dec(v_a_345_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = l_Rat_sub(v_val_343_, v_val_349_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_355_);
v___x_357_ = v___x_347_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
else
{
lean_dec(v_val_343_);
return v___x_344_;
}
}
}
else
{
lean_dec_ref(v_arg_285_);
return v___x_341_;
}
}
}
}
else
{
uint8_t v___x_363_; 
lean_dec_ref(v___x_304_);
lean_del_object(v___x_276_);
v___x_363_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_263_, v_arg_293_);
lean_dec_ref(v_arg_293_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_288_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
if (lean_obj_tag(v_a_367_) == 0)
{
lean_dec_ref(v_arg_285_);
return v___x_366_;
}
else
{
lean_object* v_val_368_; lean_object* v___x_369_; 
lean_dec_ref_known(v___x_366_, 1);
v_val_368_ = lean_ctor_get(v_a_367_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v_a_367_, 1);
v___x_369_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_285_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
if (lean_obj_tag(v_a_370_) == 0)
{
lean_dec(v_val_368_);
return v___x_369_;
}
else
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_386_; 
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v___x_369_, 0);
lean_dec(v_unused_387_);
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_val_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_385_; 
v_val_374_ = lean_ctor_get(v_a_370_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_a_370_);
if (v_isSharedCheck_385_ == 0)
{
v___x_376_ = v_a_370_;
v_isShared_377_ = v_isSharedCheck_385_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_val_374_);
lean_dec(v_a_370_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_385_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = l_Rat_mul(v_val_368_, v_val_374_);
lean_dec(v_val_368_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_384_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_380_);
v___x_382_ = v___x_372_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
else
{
lean_dec(v_val_368_);
return v___x_369_;
}
}
}
else
{
lean_dec_ref(v_arg_285_);
return v___x_366_;
}
}
}
}
else
{
uint8_t v___x_388_; 
lean_dec_ref(v___x_304_);
lean_del_object(v___x_276_);
v___x_388_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_263_, v_arg_293_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
v___x_389_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_263_, v_arg_293_);
lean_dec_ref(v_arg_293_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref(v_arg_288_);
lean_dec_ref(v_arg_285_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_getNatValue_x3f(v_arg_288_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec_ref(v_arg_288_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_422_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_422_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_422_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_422_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
if (lean_obj_tag(v_a_393_) == 0)
{
lean_object* v___x_397_; lean_object* v___x_399_; 
lean_dec_ref(v_arg_285_);
v___x_397_ = lean_box(0);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v_val_401_; lean_object* v___x_402_; 
lean_del_object(v___x_395_);
v_val_401_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v_a_393_, 1);
v___x_402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_285_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
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
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_420_; 
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_421_);
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_420_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_420_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_val_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_419_; 
v_val_407_ = lean_ctor_get(v_a_403_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_403_);
if (v_isSharedCheck_419_ == 0)
{
v___x_409_ = v_a_403_;
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_val_407_);
lean_dec(v_a_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_411_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_401_);
v___x_412_ = l_Rat_mul(v___x_411_, v_val_407_);
lean_dec_ref(v___x_411_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_414_);
v___x_416_ = v___x_405_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
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
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_arg_285_);
v_a_423_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_392_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_392_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_object* v___x_431_; 
lean_dec_ref(v_arg_293_);
v___x_431_ = l_Lean_Meta_getIntValue_x3f(v_arg_288_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_461_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_461_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_461_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_461_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
if (lean_obj_tag(v_a_432_) == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_dec_ref(v_arg_285_);
v___x_436_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
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
else
{
lean_object* v_val_440_; lean_object* v___x_441_; 
lean_del_object(v___x_434_);
v_val_440_ = lean_ctor_get(v_a_432_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_a_432_, 1);
v___x_441_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_285_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
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
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_459_; 
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v___x_441_, 0);
lean_dec(v_unused_460_);
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_459_;
goto v_resetjp_443_;
}
else
{
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_459_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_458_; 
v_val_446_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_458_ == 0)
{
v___x_448_ = v_a_442_;
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_a_442_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = l_Rat_ofInt(v_val_440_);
v___x_451_ = l_Rat_mul(v___x_450_, v_val_446_);
lean_dec_ref(v___x_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_457_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_453_);
v___x_455_ = v___x_444_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
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
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v_arg_285_);
v_a_462_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_431_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_431_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
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
uint8_t v___x_470_; 
lean_dec_ref(v___x_294_);
lean_dec_ref(v_arg_293_);
lean_del_object(v___x_276_);
v___x_470_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(v_s_263_, v_arg_288_);
lean_dec_ref(v_arg_288_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec_ref(v_arg_285_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_263_, v_model_264_, v_arg_285_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
if (lean_obj_tag(v_a_474_) == 0)
{
return v___x_473_;
}
else
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_490_; 
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v___x_473_, 0);
lean_dec(v_unused_491_);
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_490_;
goto v_resetjp_475_;
}
else
{
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_490_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v_val_478_ = lean_ctor_get(v_a_474_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_474_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v_a_474_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v_a_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = l_Rat_neg(v_val_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_488_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_484_);
v___x_486_ = v___x_476_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
else
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v___x_492_; 
lean_dec_ref(v___x_294_);
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_arg_285_);
lean_del_object(v___x_276_);
v___x_492_ = l_Lean_Meta_getNatValue_x3f(v_arg_288_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec_ref(v_arg_288_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_513_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_513_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_513_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_513_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_a_493_) == 0)
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v_val_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_val_501_ = lean_ctor_get(v_a_493_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_512_ == 0)
{
v___x_503_ = v_a_493_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_val_501_);
lean_dec(v_a_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_507_);
v___x_509_ = v___x_495_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_492_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_492_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
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
uint8_t v___x_522_; 
lean_dec_ref(v___x_289_);
lean_dec_ref(v_arg_288_);
lean_del_object(v___x_276_);
v___x_522_ = l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_263_, v_arg_285_);
lean_dec_ref(v_arg_285_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
}
}
v___jp_278_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = lean_box(0);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_279_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_a_528_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_273_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_273_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(lean_object* v_s_536_, lean_object* v_model_537_, lean_object* v_e_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_536_, v_model_537_, v_e_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec_ref(v_model_537_);
lean_dec_ref(v_s_536_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(lean_object* v_00_u03b2_545_, lean_object* v_m_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_546_, v_a_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_549_, lean_object* v_m_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_549_, v_m_550_, v_a_551_);
lean_dec_ref(v_a_551_);
lean_dec_ref(v_m_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_nat_to_int(v_a_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_555_, lean_object* v_a_556_, lean_object* v_x_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_556_, v_x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_559_, lean_object* v_a_560_, lean_object* v_x_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_559_, v_a_560_, v_x_561_);
lean_dec(v_x_561_);
lean_dec_ref(v_a_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(lean_object* v_e_563_, lean_object* v_s_564_, lean_object* v_model_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_564_, v_model_565_, v_e_563_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(lean_object* v_e_572_, lean_object* v_s_573_, lean_object* v_model_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_572_, v_s_573_, v_model_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec_ref(v_model_574_);
lean_dec_ref(v_s_573_);
return v_res_580_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
uint8_t v___x_583_; 
v___x_583_ = 0;
return v___x_583_;
}
else
{
lean_object* v_key_584_; lean_object* v_tail_585_; uint8_t v___x_586_; 
v_key_584_ = lean_ctor_get(v_x_582_, 0);
v_tail_585_ = lean_ctor_get(v_x_582_, 2);
v___x_586_ = lean_expr_eqv(v_key_584_, v_a_581_);
if (v___x_586_ == 0)
{
v_x_582_ = v_tail_585_;
goto _start;
}
else
{
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
uint8_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_588_, v_x_589_);
lean_dec(v_x_589_);
lean_dec_ref(v_a_588_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(lean_object* v_m_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_buckets_594_; lean_object* v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v_fold_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_buckets_594_ = lean_ctor_get(v_m_592_, 1);
v___x_595_ = lean_array_get_size(v_buckets_594_);
v___x_596_ = l_Lean_Expr_hash(v_a_593_);
v___x_597_ = 32ULL;
v___x_598_ = lean_uint64_shift_right(v___x_596_, v___x_597_);
v_fold_599_ = lean_uint64_xor(v___x_596_, v___x_598_);
v___x_600_ = 16ULL;
v___x_601_ = lean_uint64_shift_right(v_fold_599_, v___x_600_);
v___x_602_ = lean_uint64_xor(v_fold_599_, v___x_601_);
v___x_603_ = lean_uint64_to_usize(v___x_602_);
v___x_604_ = lean_usize_of_nat(v___x_595_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_sub(v___x_604_, v___x_605_);
v___x_607_ = lean_usize_land(v___x_603_, v___x_606_);
v___x_608_ = lean_array_uget_borrowed(v_buckets_594_, v___x_607_);
v___x_609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_593_, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(lean_object* v_m_610_, lean_object* v_a_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_610_, v_a_611_);
lean_dec_ref(v_a_611_);
lean_dec_ref(v_m_610_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(lean_object* v_structId_614_, lean_object* v___x_615_, lean_object* v_goal_616_, lean_object* v_as_617_, size_t v_sz_618_, size_t v_i_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_b_620_);
return v___x_627_;
}
else
{
lean_object* v_snd_628_; lean_object* v_a_629_; lean_object* v_fst_630_; lean_object* v_snd_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_658_; 
v_snd_628_ = lean_ctor_get(v_b_620_, 1);
lean_inc(v_snd_628_);
lean_dec_ref(v_b_620_);
v_a_629_ = lean_array_uget(v_as_617_, v_i_619_);
v_fst_630_ = lean_ctor_get(v_a_629_, 0);
v_snd_631_ = lean_ctor_get(v_a_629_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_a_629_);
if (v_isSharedCheck_658_ == 0)
{
v___x_633_ = v_a_629_;
v_isShared_634_ = v_isSharedCheck_658_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_snd_631_);
lean_inc(v_fst_630_);
lean_dec(v_a_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_658_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v_a_637_; uint8_t v___x_644_; 
v___x_635_ = lean_box(0);
v___x_644_ = lean_nat_dec_eq(v_structId_614_, v_snd_631_);
lean_dec(v_snd_631_);
if (v___x_644_ == 0)
{
lean_dec(v_fst_630_);
v_a_637_ = v_snd_628_;
goto v___jp_636_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_628_, v_fst_630_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_inc(v_fst_630_);
v___x_646_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_615_, v_snd_628_, v_fst_630_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
if (lean_obj_tag(v_a_647_) == 1)
{
lean_object* v_val_648_; lean_object* v___x_649_; 
v_val_648_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v_a_647_, 1);
v___x_649_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_616_, v_fst_630_, v_val_648_, v_snd_628_);
v_a_637_ = v___x_649_;
goto v___jp_636_;
}
else
{
lean_dec(v_a_647_);
lean_dec(v_fst_630_);
v_a_637_ = v_snd_628_;
goto v___jp_636_;
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_del_object(v___x_633_);
lean_dec(v_fst_630_);
lean_dec(v_snd_628_);
v_a_650_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_646_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_646_);
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
lean_dec(v_fst_630_);
v_a_637_ = v_snd_628_;
goto v___jp_636_;
}
}
v___jp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_a_637_);
lean_ctor_set(v___x_633_, 0, v___x_635_);
v___x_639_ = v___x_633_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_a_637_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
size_t v___x_640_; size_t v___x_641_; 
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_619_, v___x_640_);
v_i_619_ = v___x_641_;
v_b_620_ = v___x_639_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_structId_659_, lean_object* v___x_660_, lean_object* v_goal_661_, lean_object* v_as_662_, lean_object* v_sz_663_, lean_object* v_i_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v_i_boxed_672_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_659_, v___x_660_, v_goal_661_, v_as_662_, v_sz_boxed_671_, v_i_boxed_672_, v_b_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v_as_662_);
lean_dec_ref(v_goal_661_);
lean_dec_ref(v___x_660_);
lean_dec(v_structId_659_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(lean_object* v_structId_674_, lean_object* v___x_675_, lean_object* v_goal_676_, lean_object* v_as_677_, size_t v_sz_678_, size_t v_i_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_lt(v_i_679_, v_sz_678_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v_b_680_);
return v___x_687_;
}
else
{
lean_object* v_snd_688_; lean_object* v_a_689_; lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_718_; 
v_snd_688_ = lean_ctor_get(v_b_680_, 1);
lean_inc(v_snd_688_);
lean_dec_ref(v_b_680_);
v_a_689_ = lean_array_uget(v_as_677_, v_i_679_);
v_fst_690_ = lean_ctor_get(v_a_689_, 0);
v_snd_691_ = lean_ctor_get(v_a_689_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_a_689_);
if (v_isSharedCheck_718_ == 0)
{
v___x_693_ = v_a_689_;
v_isShared_694_ = v_isSharedCheck_718_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_691_);
lean_inc(v_fst_690_);
lean_dec(v_a_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_718_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v_a_697_; uint8_t v___x_704_; 
v___x_695_ = lean_box(0);
v___x_704_ = lean_nat_dec_eq(v_structId_674_, v_snd_691_);
lean_dec(v_snd_691_);
if (v___x_704_ == 0)
{
lean_dec(v_fst_690_);
v_a_697_ = v_snd_688_;
goto v___jp_696_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_688_, v_fst_690_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_inc(v_fst_690_);
v___x_706_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_675_, v_snd_688_, v_fst_690_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
if (lean_obj_tag(v_a_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_709_; 
v_val_708_ = lean_ctor_get(v_a_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v_a_707_, 1);
v___x_709_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_676_, v_fst_690_, v_val_708_, v_snd_688_);
v_a_697_ = v___x_709_;
goto v___jp_696_;
}
else
{
lean_dec(v_a_707_);
lean_dec(v_fst_690_);
v_a_697_ = v_snd_688_;
goto v___jp_696_;
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_del_object(v___x_693_);
lean_dec(v_fst_690_);
lean_dec(v_snd_688_);
v_a_710_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_706_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_706_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_dec(v_fst_690_);
v_a_697_ = v_snd_688_;
goto v___jp_696_;
}
}
v___jp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_a_697_);
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_a_697_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; 
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_add(v_i_679_, v___x_700_);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v_structId_674_, v___x_675_, v_goal_676_, v_as_677_, v_sz_678_, v___x_701_, v___x_699_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v___x_702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(lean_object* v_structId_719_, lean_object* v___x_720_, lean_object* v_goal_721_, lean_object* v_as_722_, lean_object* v_sz_723_, lean_object* v_i_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v_sz_boxed_731_ = lean_unbox_usize(v_sz_723_);
lean_dec(v_sz_723_);
v_i_boxed_732_ = lean_unbox_usize(v_i_724_);
lean_dec(v_i_724_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_719_, v___x_720_, v_goal_721_, v_as_722_, v_sz_boxed_731_, v_i_boxed_732_, v_b_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec_ref(v_as_722_);
lean_dec_ref(v_goal_721_);
lean_dec_ref(v___x_720_);
lean_dec(v_structId_719_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(lean_object* v_init_734_, lean_object* v_structId_735_, lean_object* v___x_736_, lean_object* v_goal_737_, lean_object* v_n_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
if (lean_obj_tag(v_n_738_) == 0)
{
lean_object* v_cs_745_; lean_object* v___x_746_; lean_object* v___x_747_; size_t v_sz_748_; size_t v___x_749_; lean_object* v___x_750_; 
v_cs_745_ = lean_ctor_get(v_n_738_, 0);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_b_739_);
v_sz_748_ = lean_array_size(v_cs_745_);
v___x_749_ = ((size_t)0ULL);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_734_, v_structId_735_, v___x_736_, v_goal_737_, v_cs_745_, v_sz_748_, v___x_749_, v___x_747_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_765_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_765_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_765_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_765_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_fst_755_; 
v_fst_755_ = lean_ctor_get(v_a_751_, 0);
if (lean_obj_tag(v_fst_755_) == 0)
{
lean_object* v_snd_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v_snd_756_ = lean_ctor_get(v_a_751_, 1);
lean_inc(v_snd_756_);
lean_dec(v_a_751_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v_snd_756_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_757_);
v___x_759_ = v___x_753_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_object* v_val_761_; lean_object* v___x_763_; 
lean_inc_ref(v_fst_755_);
lean_dec(v_a_751_);
v_val_761_ = lean_ctor_get(v_fst_755_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v_fst_755_, 1);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v_val_761_);
v___x_763_ = v___x_753_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_val_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_750_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_750_);
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
else
{
lean_object* v_vs_774_; lean_object* v___x_775_; lean_object* v___x_776_; size_t v_sz_777_; size_t v___x_778_; lean_object* v___x_779_; 
v_vs_774_ = lean_ctor_get(v_n_738_, 0);
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v_b_739_);
v_sz_777_ = lean_array_size(v_vs_774_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v_structId_735_, v___x_736_, v_goal_737_, v_vs_774_, v_sz_777_, v___x_778_, v___x_776_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_794_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_794_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_794_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_794_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_fst_784_; 
v_fst_784_ = lean_ctor_get(v_a_780_, 0);
if (lean_obj_tag(v_fst_784_) == 0)
{
lean_object* v_snd_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v_snd_785_ = lean_ctor_get(v_a_780_, 1);
lean_inc(v_snd_785_);
lean_dec(v_a_780_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v_snd_785_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_786_);
v___x_788_ = v___x_782_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
else
{
lean_object* v_val_790_; lean_object* v___x_792_; 
lean_inc_ref(v_fst_784_);
lean_dec(v_a_780_);
v_val_790_ = lean_ctor_get(v_fst_784_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v_fst_784_, 1);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v_val_790_);
v___x_792_ = v___x_782_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_val_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_a_795_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_779_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_779_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(lean_object* v_init_803_, lean_object* v_structId_804_, lean_object* v___x_805_, lean_object* v_goal_806_, lean_object* v_as_807_, size_t v_sz_808_, size_t v_i_809_, lean_object* v_b_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = lean_usize_dec_lt(v_i_809_, v_sz_808_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v_b_810_);
return v___x_817_;
}
else
{
lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_852_; 
v_snd_818_ = lean_ctor_get(v_b_810_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_b_810_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_b_810_, 0);
lean_dec(v_unused_853_);
v___x_820_ = v_b_810_;
v_isShared_821_ = v_isSharedCheck_852_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_dec(v_b_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_852_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_array_uget_borrowed(v_as_807_, v_i_809_);
lean_inc(v_snd_818_);
v___x_823_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_803_, v_structId_804_, v___x_805_, v_goal_806_, v_a_822_, v_snd_818_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_843_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_843_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_843_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_843_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
if (lean_obj_tag(v_a_824_) == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v_a_824_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_828_);
v___x_830_ = v___x_820_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_snd_818_);
v___x_830_ = v_reuseFailAlloc_834_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_830_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
lean_del_object(v___x_826_);
lean_dec(v_snd_818_);
v_a_835_ = lean_ctor_get(v_a_824_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v_a_824_, 1);
v___x_836_ = lean_box(0);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_a_835_);
lean_ctor_set(v___x_820_, 0, v___x_836_);
v___x_838_ = v___x_820_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_a_835_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
size_t v___x_839_; size_t v___x_840_; 
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_i_809_, v___x_839_);
v_i_809_ = v___x_840_;
v_b_810_ = v___x_838_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_del_object(v___x_820_);
lean_dec(v_snd_818_);
v_a_844_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_823_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_823_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(lean_object* v_init_854_, lean_object* v_structId_855_, lean_object* v___x_856_, lean_object* v_goal_857_, lean_object* v_as_858_, lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_868_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_854_, v_structId_855_, v___x_856_, v_goal_857_, v_as_858_, v_sz_boxed_867_, v_i_boxed_868_, v_b_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_as_858_);
lean_dec_ref(v_goal_857_);
lean_dec_ref(v___x_856_);
lean_dec(v_structId_855_);
lean_dec_ref(v_init_854_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(lean_object* v_init_870_, lean_object* v_structId_871_, lean_object* v___x_872_, lean_object* v_goal_873_, lean_object* v_n_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_870_, v_structId_871_, v___x_872_, v_goal_873_, v_n_874_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_n_874_);
lean_dec_ref(v_goal_873_);
lean_dec_ref(v___x_872_);
lean_dec(v_structId_871_);
lean_dec_ref(v_init_870_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(lean_object* v_structId_882_, lean_object* v___x_883_, lean_object* v_goal_884_, lean_object* v_as_885_, size_t v_sz_886_, size_t v_i_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
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
lean_object* v_snd_896_; lean_object* v_a_897_; lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_926_; 
v_snd_896_ = lean_ctor_get(v_b_888_, 1);
lean_inc(v_snd_896_);
lean_dec_ref(v_b_888_);
v_a_897_ = lean_array_uget(v_as_885_, v_i_887_);
v_fst_898_ = lean_ctor_get(v_a_897_, 0);
v_snd_899_ = lean_ctor_get(v_a_897_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_a_897_);
if (v_isSharedCheck_926_ == 0)
{
v___x_901_ = v_a_897_;
v_isShared_902_ = v_isSharedCheck_926_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_inc(v_fst_898_);
lean_dec(v_a_897_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_926_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v_a_905_; uint8_t v___x_912_; 
v___x_903_ = lean_box(0);
v___x_912_ = lean_nat_dec_eq(v_structId_882_, v_snd_899_);
lean_dec(v_snd_899_);
if (v___x_912_ == 0)
{
lean_dec(v_fst_898_);
v_a_905_ = v_snd_896_;
goto v___jp_904_;
}
else
{
uint8_t v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_896_, v_fst_898_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_inc(v_fst_898_);
v___x_914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_883_, v_snd_896_, v_fst_898_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
if (lean_obj_tag(v_a_915_) == 1)
{
lean_object* v_val_916_; lean_object* v___x_917_; 
v_val_916_ = lean_ctor_get(v_a_915_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v_a_915_, 1);
v___x_917_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_884_, v_fst_898_, v_val_916_, v_snd_896_);
v_a_905_ = v___x_917_;
goto v___jp_904_;
}
else
{
lean_dec(v_a_915_);
lean_dec(v_fst_898_);
v_a_905_ = v_snd_896_;
goto v___jp_904_;
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_del_object(v___x_901_);
lean_dec(v_fst_898_);
lean_dec(v_snd_896_);
v_a_918_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_914_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_914_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_dec(v_fst_898_);
v_a_905_ = v_snd_896_;
goto v___jp_904_;
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
size_t v___x_908_; size_t v___x_909_; 
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_add(v_i_887_, v___x_908_);
v_i_887_ = v___x_909_;
v_b_888_ = v___x_907_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(lean_object* v_structId_927_, lean_object* v___x_928_, lean_object* v_goal_929_, lean_object* v_as_930_, lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
size_t v_sz_boxed_939_; size_t v_i_boxed_940_; lean_object* v_res_941_; 
v_sz_boxed_939_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_940_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_927_, v___x_928_, v_goal_929_, v_as_930_, v_sz_boxed_939_, v_i_boxed_940_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec_ref(v_as_930_);
lean_dec_ref(v_goal_929_);
lean_dec_ref(v___x_928_);
lean_dec(v_structId_927_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(lean_object* v_structId_942_, lean_object* v___x_943_, lean_object* v_goal_944_, lean_object* v_as_945_, size_t v_sz_946_, size_t v_i_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_lt(v_i_947_, v_sz_946_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_b_948_);
return v___x_955_;
}
else
{
lean_object* v_snd_956_; lean_object* v_a_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_986_; 
v_snd_956_ = lean_ctor_get(v_b_948_, 1);
lean_inc(v_snd_956_);
lean_dec_ref(v_b_948_);
v_a_957_ = lean_array_uget(v_as_945_, v_i_947_);
v_fst_958_ = lean_ctor_get(v_a_957_, 0);
v_snd_959_ = lean_ctor_get(v_a_957_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_986_ == 0)
{
v___x_961_ = v_a_957_;
v_isShared_962_ = v_isSharedCheck_986_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_958_);
lean_dec(v_a_957_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_986_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v_a_965_; uint8_t v___x_972_; 
v___x_963_ = lean_box(0);
v___x_972_ = lean_nat_dec_eq(v_structId_942_, v_snd_959_);
lean_dec(v_snd_959_);
if (v___x_972_ == 0)
{
lean_dec(v_fst_958_);
v_a_965_ = v_snd_956_;
goto v___jp_964_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_956_, v_fst_958_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_inc(v_fst_958_);
v___x_974_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_943_, v_snd_956_, v_fst_958_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
if (lean_obj_tag(v_a_975_) == 1)
{
lean_object* v_val_976_; lean_object* v___x_977_; 
v_val_976_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v_a_975_, 1);
v___x_977_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_944_, v_fst_958_, v_val_976_, v_snd_956_);
v_a_965_ = v___x_977_;
goto v___jp_964_;
}
else
{
lean_dec(v_a_975_);
lean_dec(v_fst_958_);
v_a_965_ = v_snd_956_;
goto v___jp_964_;
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_del_object(v___x_961_);
lean_dec(v_fst_958_);
lean_dec(v_snd_956_);
v_a_978_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_974_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_dec(v_fst_958_);
v_a_965_ = v_snd_956_;
goto v___jp_964_;
}
}
v___jp_964_:
{
lean_object* v___x_967_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v_a_965_);
lean_ctor_set(v___x_961_, 0, v___x_963_);
v___x_967_ = v___x_961_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_a_965_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; 
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_add(v_i_947_, v___x_968_);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v_structId_942_, v___x_943_, v_goal_944_, v_as_945_, v_sz_946_, v___x_969_, v___x_967_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(lean_object* v_structId_987_, lean_object* v___x_988_, lean_object* v_goal_989_, lean_object* v_as_990_, lean_object* v_sz_991_, lean_object* v_i_992_, lean_object* v_b_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
size_t v_sz_boxed_999_; size_t v_i_boxed_1000_; lean_object* v_res_1001_; 
v_sz_boxed_999_ = lean_unbox_usize(v_sz_991_);
lean_dec(v_sz_991_);
v_i_boxed_1000_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_987_, v___x_988_, v_goal_989_, v_as_990_, v_sz_boxed_999_, v_i_boxed_1000_, v_b_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec_ref(v_as_990_);
lean_dec_ref(v_goal_989_);
lean_dec_ref(v___x_988_);
lean_dec(v_structId_987_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(lean_object* v_structId_1002_, lean_object* v___x_1003_, lean_object* v_goal_1004_, lean_object* v_t_1005_, lean_object* v_init_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_root_1012_; lean_object* v_tail_1013_; lean_object* v___x_1014_; 
v_root_1012_ = lean_ctor_get(v_t_1005_, 0);
v_tail_1013_ = lean_ctor_get(v_t_1005_, 1);
lean_inc_ref(v_init_1006_);
v___x_1014_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_1006_, v_structId_1002_, v___x_1003_, v_goal_1004_, v_root_1012_, v_init_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec_ref(v_init_1006_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1051_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1051_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1051_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
if (lean_obj_tag(v_a_1015_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; 
v_a_1019_ = lean_ctor_get(v_a_1015_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v_a_1015_, 1);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v_a_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; size_t v_sz_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
lean_del_object(v___x_1017_);
v_a_1023_ = lean_ctor_get(v_a_1015_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_a_1015_, 1);
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v_a_1023_);
v_sz_1026_ = lean_array_size(v_tail_1013_);
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v_structId_1002_, v___x_1003_, v_goal_1004_, v_tail_1013_, v_sz_1026_, v___x_1027_, v___x_1025_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1042_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_fst_1033_; 
v_fst_1033_ = lean_ctor_get(v_a_1029_, 0);
if (lean_obj_tag(v_fst_1033_) == 0)
{
lean_object* v_snd_1034_; lean_object* v___x_1036_; 
v_snd_1034_ = lean_ctor_get(v_a_1029_, 1);
lean_inc(v_snd_1034_);
lean_dec(v_a_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_snd_1034_);
v___x_1036_ = v___x_1031_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_snd_1034_);
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
lean_object* v_val_1038_; lean_object* v___x_1040_; 
lean_inc_ref(v_fst_1033_);
lean_dec(v_a_1029_);
v_val_1038_ = lean_ctor_get(v_fst_1033_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v_fst_1033_, 1);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_val_1038_);
v___x_1040_ = v___x_1031_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_val_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1028_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1028_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1014_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1014_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(lean_object* v_structId_1060_, lean_object* v___x_1061_, lean_object* v_goal_1062_, lean_object* v_t_1063_, lean_object* v_init_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1060_, v___x_1061_, v_goal_1062_, v_t_1063_, v_init_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v_t_1063_);
lean_dec_ref(v_goal_1062_);
lean_dec_ref(v___x_1061_);
lean_dec(v_structId_1060_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(lean_object* v_goal_1071_, lean_object* v_structId_1072_, lean_object* v_model_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1080_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1079_, v_goal_1071_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_structs_1082_; lean_object* v_exprToStructIdEntries_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v_structs_1082_ = lean_ctor_get(v_a_1081_, 0);
lean_inc_ref(v_structs_1082_);
v_exprToStructIdEntries_1083_ = lean_ctor_get(v_a_1081_, 3);
lean_inc_ref(v_exprToStructIdEntries_1083_);
lean_dec(v_a_1081_);
v___x_1084_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v___x_1085_ = lean_array_get(v___x_1084_, v_structs_1082_, v_structId_1072_);
lean_dec_ref(v_structs_1082_);
v___x_1086_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v_structId_1072_, v___x_1085_, v_goal_1071_, v_exprToStructIdEntries_1083_, v_model_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec_ref(v_exprToStructIdEntries_1083_);
lean_dec(v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_model_1073_);
v_a_1087_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1089_ = v___x_1080_;
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1080_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_ref_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v_ref_1091_ = lean_ctor_get(v_a_1076_, 5);
v___x_1092_ = lean_io_error_to_string(v_a_1087_);
v___x_1093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
v___x_1094_ = l_Lean_MessageData_ofFormat(v___x_1093_);
lean_inc(v_ref_1091_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_ref_1091_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1095_);
v___x_1097_ = v___x_1089_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(lean_object* v_goal_1100_, lean_object* v_structId_1101_, lean_object* v_model_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_1100_, v_structId_1101_, v_model_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_structId_1101_);
lean_dec_ref(v_goal_1100_);
return v_res_1108_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(lean_object* v_00_u03b2_1109_, lean_object* v_m_1110_, lean_object* v_a_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_1110_, v_a_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_m_1114_, lean_object* v_a_1115_){
_start:
{
uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_res_1116_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_1113_, v_m_1114_, v_a_1115_);
lean_dec_ref(v_a_1115_);
lean_dec_ref(v_m_1114_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(lean_object* v_00_u03b2_1118_, lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_1119_, v_x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1122_, lean_object* v_a_1123_, lean_object* v_x_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_1122_, v_a_1123_, v_x_1124_);
lean_dec(v_x_1124_);
lean_dec_ref(v_a_1123_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(lean_object* v_goal_1127_, lean_object* v___x_1128_, lean_object* v_as_1129_, size_t v_sz_1130_, size_t v_i_1131_, lean_object* v_b_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_usize_dec_lt(v_i_1131_, v_sz_1130_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v___x_1128_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_b_1132_);
return v___x_1139_;
}
else
{
lean_object* v_snd_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1181_; 
v_snd_1140_ = lean_ctor_get(v_b_1132_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_b_1132_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_b_1132_, 0);
lean_dec(v_unused_1182_);
v___x_1142_ = v_b_1132_;
v_isShared_1143_ = v_isSharedCheck_1181_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snd_1140_);
lean_dec(v_b_1132_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1181_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_array_uget_borrowed(v_as_1129_, v_i_1131_);
lean_inc(v_a_1144_);
v___x_1145_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1127_, v_a_1144_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; lean_object* v_a_1149_; uint8_t v___x_1156_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_box(0);
v___x_1156_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1146_);
if (v___x_1156_ == 0)
{
lean_dec(v_a_1146_);
v_a_1149_ = v_snd_1140_;
goto v___jp_1148_;
}
else
{
lean_object* v_type_1157_; lean_object* v___x_1158_; 
v_type_1157_ = lean_ctor_get(v___x_1128_, 2);
lean_inc(v_a_1146_);
lean_inc_ref(v_type_1157_);
v___x_1158_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1157_, v_a_1146_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; uint8_t v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_unbox(v_a_1159_);
lean_dec(v_a_1159_);
if (v___x_1160_ == 0)
{
lean_dec(v_a_1146_);
v_a_1149_ = v_snd_1140_;
goto v___jp_1148_;
}
else
{
lean_object* v_self_1161_; lean_object* v___x_1162_; 
v_self_1161_ = lean_ctor_get(v_a_1146_, 0);
lean_inc_ref(v_self_1161_);
lean_dec(v_a_1146_);
v___x_1162_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1128_, v_self_1161_);
if (lean_obj_tag(v___x_1162_) == 1)
{
lean_object* v_val_1163_; lean_object* v___x_1164_; 
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1127_, v_self_1161_, v_val_1163_, v_snd_1140_);
v_a_1149_ = v___x_1164_;
goto v___jp_1148_;
}
else
{
lean_dec(v___x_1162_);
lean_dec_ref(v_self_1161_);
v_a_1149_ = v_snd_1140_;
goto v___jp_1148_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_a_1146_);
lean_del_object(v___x_1142_);
lean_dec(v_snd_1140_);
lean_dec_ref(v___x_1128_);
v_a_1165_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1158_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1158_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
v___jp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_a_1149_);
lean_ctor_set(v___x_1142_, 0, v___x_1147_);
v___x_1151_ = v___x_1142_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_a_1149_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
size_t v___x_1152_; size_t v___x_1153_; 
v___x_1152_ = ((size_t)1ULL);
v___x_1153_ = lean_usize_add(v_i_1131_, v___x_1152_);
v_i_1131_ = v___x_1153_;
v_b_1132_ = v___x_1151_;
goto _start;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_del_object(v___x_1142_);
lean_dec(v_snd_1140_);
lean_dec_ref(v___x_1128_);
v_a_1173_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1145_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1145_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_goal_1183_, lean_object* v___x_1184_, lean_object* v_as_1185_, lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_b_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
size_t v_sz_boxed_1194_; size_t v_i_boxed_1195_; lean_object* v_res_1196_; 
v_sz_boxed_1194_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1195_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1183_, v___x_1184_, v_as_1185_, v_sz_boxed_1194_, v_i_boxed_1195_, v_b_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec_ref(v_as_1185_);
lean_dec_ref(v_goal_1183_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(lean_object* v_goal_1197_, lean_object* v___x_1198_, lean_object* v_as_1199_, size_t v_sz_1200_, size_t v_i_1201_, lean_object* v_b_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_usize_dec_lt(v_i_1201_, v_sz_1200_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref(v___x_1198_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_b_1202_);
return v___x_1209_;
}
else
{
lean_object* v_snd_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1251_; 
v_snd_1210_ = lean_ctor_get(v_b_1202_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_b_1202_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v_b_1202_, 0);
lean_dec(v_unused_1252_);
v___x_1212_ = v_b_1202_;
v_isShared_1213_ = v_isSharedCheck_1251_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_snd_1210_);
lean_dec(v_b_1202_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1251_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_a_1214_; lean_object* v___x_1215_; 
v_a_1214_ = lean_array_uget_borrowed(v_as_1199_, v_i_1201_);
lean_inc(v_a_1214_);
v___x_1215_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1197_, v_a_1214_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v_a_1219_; uint8_t v___x_1226_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = lean_box(0);
v___x_1226_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1216_);
if (v___x_1226_ == 0)
{
lean_dec(v_a_1216_);
v_a_1219_ = v_snd_1210_;
goto v___jp_1218_;
}
else
{
lean_object* v_type_1227_; lean_object* v___x_1228_; 
v_type_1227_ = lean_ctor_get(v___x_1198_, 2);
lean_inc(v_a_1216_);
lean_inc_ref(v_type_1227_);
v___x_1228_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1227_, v_a_1216_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; uint8_t v___x_1230_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = lean_unbox(v_a_1229_);
lean_dec(v_a_1229_);
if (v___x_1230_ == 0)
{
lean_dec(v_a_1216_);
v_a_1219_ = v_snd_1210_;
goto v___jp_1218_;
}
else
{
lean_object* v_self_1231_; lean_object* v___x_1232_; 
v_self_1231_ = lean_ctor_get(v_a_1216_, 0);
lean_inc_ref(v_self_1231_);
lean_dec(v_a_1216_);
v___x_1232_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1198_, v_self_1231_);
if (lean_obj_tag(v___x_1232_) == 1)
{
lean_object* v_val_1233_; lean_object* v___x_1234_; 
v_val_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1197_, v_self_1231_, v_val_1233_, v_snd_1210_);
v_a_1219_ = v___x_1234_;
goto v___jp_1218_;
}
else
{
lean_dec(v___x_1232_);
lean_dec_ref(v_self_1231_);
v_a_1219_ = v_snd_1210_;
goto v___jp_1218_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_a_1216_);
lean_del_object(v___x_1212_);
lean_dec(v_snd_1210_);
lean_dec_ref(v___x_1198_);
v_a_1235_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1228_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1228_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
v___jp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v_a_1219_);
lean_ctor_set(v___x_1212_, 0, v___x_1217_);
v___x_1221_ = v___x_1212_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_a_1219_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1201_, v___x_1222_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_1197_, v___x_1198_, v_as_1199_, v_sz_1200_, v___x_1223_, v___x_1221_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_del_object(v___x_1212_);
lean_dec(v_snd_1210_);
lean_dec_ref(v___x_1198_);
v_a_1243_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1215_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1215_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(lean_object* v_goal_1253_, lean_object* v___x_1254_, lean_object* v_as_1255_, lean_object* v_sz_1256_, lean_object* v_i_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
size_t v_sz_boxed_1264_; size_t v_i_boxed_1265_; lean_object* v_res_1266_; 
v_sz_boxed_1264_ = lean_unbox_usize(v_sz_1256_);
lean_dec(v_sz_1256_);
v_i_boxed_1265_ = lean_unbox_usize(v_i_1257_);
lean_dec(v_i_1257_);
v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1253_, v___x_1254_, v_as_1255_, v_sz_boxed_1264_, v_i_boxed_1265_, v_b_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v_as_1255_);
lean_dec_ref(v_goal_1253_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(lean_object* v_init_1267_, lean_object* v_goal_1268_, lean_object* v___x_1269_, lean_object* v_n_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
if (lean_obj_tag(v_n_1270_) == 0)
{
lean_object* v_cs_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; size_t v_sz_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v_cs_1277_ = lean_ctor_get(v_n_1270_, 0);
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_b_1271_);
v_sz_1280_ = lean_array_size(v_cs_1277_);
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1267_, v_goal_1268_, v___x_1269_, v_cs_1277_, v_sz_1280_, v___x_1281_, v___x_1279_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1297_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1297_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1297_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_fst_1287_; 
v_fst_1287_ = lean_ctor_get(v_a_1283_, 0);
if (lean_obj_tag(v_fst_1287_) == 0)
{
lean_object* v_snd_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v_snd_1288_ = lean_ctor_get(v_a_1283_, 1);
lean_inc(v_snd_1288_);
lean_dec(v_a_1283_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_snd_1288_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1289_);
v___x_1291_ = v___x_1285_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
else
{
lean_object* v_val_1293_; lean_object* v___x_1295_; 
lean_inc_ref(v_fst_1287_);
lean_dec(v_a_1283_);
v_val_1293_ = lean_ctor_get(v_fst_1287_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v_fst_1287_, 1);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_val_1293_);
v___x_1295_ = v___x_1285_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_val_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_a_1298_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1282_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1282_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_vs_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; size_t v_sz_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v_vs_1306_ = lean_ctor_get(v_n_1270_, 0);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_b_1271_);
v_sz_1309_ = lean_array_size(v_vs_1306_);
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_1268_, v___x_1269_, v_vs_1306_, v_sz_1309_, v___x_1310_, v___x_1308_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1326_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1326_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1326_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_fst_1316_; 
v_fst_1316_ = lean_ctor_get(v_a_1312_, 0);
if (lean_obj_tag(v_fst_1316_) == 0)
{
lean_object* v_snd_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v_snd_1317_ = lean_ctor_get(v_a_1312_, 1);
lean_inc(v_snd_1317_);
lean_dec(v_a_1312_);
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_snd_1317_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1318_);
v___x_1320_ = v___x_1314_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v_val_1322_; lean_object* v___x_1324_; 
lean_inc_ref(v_fst_1316_);
lean_dec(v_a_1312_);
v_val_1322_ = lean_ctor_get(v_fst_1316_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v_fst_1316_, 1);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v_val_1322_);
v___x_1324_ = v___x_1314_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_val_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_a_1327_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1311_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1311_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(lean_object* v_init_1335_, lean_object* v_goal_1336_, lean_object* v___x_1337_, lean_object* v_as_1338_, size_t v_sz_1339_, size_t v_i_1340_, lean_object* v_b_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_usize_dec_lt(v_i_1340_, v_sz_1339_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec_ref(v___x_1337_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v_b_1341_);
return v___x_1348_;
}
else
{
lean_object* v_snd_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1383_; 
v_snd_1349_ = lean_ctor_get(v_b_1341_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_b_1341_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; 
v_unused_1384_ = lean_ctor_get(v_b_1341_, 0);
lean_dec(v_unused_1384_);
v___x_1351_ = v_b_1341_;
v_isShared_1352_ = v_isSharedCheck_1383_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_snd_1349_);
lean_dec(v_b_1341_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1383_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1353_ = lean_array_uget_borrowed(v_as_1338_, v_i_1340_);
lean_inc(v_snd_1349_);
lean_inc_ref(v___x_1337_);
v___x_1354_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1335_, v_goal_1336_, v___x_1337_, v_a_1353_, v_snd_1349_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1374_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1374_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1374_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
if (lean_obj_tag(v_a_1355_) == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_dec_ref(v___x_1337_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_a_1355_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1359_);
v___x_1361_ = v___x_1351_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1349_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1361_);
v___x_1363_ = v___x_1357_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_del_object(v___x_1357_);
lean_dec(v_snd_1349_);
v_a_1366_ = lean_ctor_get(v_a_1355_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v_a_1355_, 1);
v___x_1367_ = lean_box(0);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v_a_1366_);
lean_ctor_set(v___x_1351_, 0, v___x_1367_);
v___x_1369_ = v___x_1351_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_a_1366_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
size_t v___x_1370_; size_t v___x_1371_; 
v___x_1370_ = ((size_t)1ULL);
v___x_1371_ = lean_usize_add(v_i_1340_, v___x_1370_);
v_i_1340_ = v___x_1371_;
v_b_1341_ = v___x_1369_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_del_object(v___x_1351_);
lean_dec(v_snd_1349_);
lean_dec_ref(v___x_1337_);
v_a_1375_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1354_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1354_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1385_, lean_object* v_goal_1386_, lean_object* v___x_1387_, lean_object* v_as_1388_, lean_object* v_sz_1389_, lean_object* v_i_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1389_);
lean_dec(v_sz_1389_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_1385_, v_goal_1386_, v___x_1387_, v_as_1388_, v_sz_boxed_1397_, v_i_boxed_1398_, v_b_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec_ref(v_as_1388_);
lean_dec_ref(v_goal_1386_);
lean_dec_ref(v_init_1385_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(lean_object* v_init_1400_, lean_object* v_goal_1401_, lean_object* v___x_1402_, lean_object* v_n_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1400_, v_goal_1401_, v___x_1402_, v_n_1403_, v_b_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec_ref(v_n_1403_);
lean_dec_ref(v_goal_1401_);
lean_dec_ref(v_init_1400_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(lean_object* v_goal_1411_, lean_object* v___x_1412_, lean_object* v_as_1413_, size_t v_sz_1414_, size_t v_i_1415_, lean_object* v_b_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_usize_dec_lt(v_i_1415_, v_sz_1414_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v___x_1412_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_b_1416_);
return v___x_1423_;
}
else
{
lean_object* v_snd_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1465_; 
v_snd_1424_ = lean_ctor_get(v_b_1416_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_b_1416_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_b_1416_, 0);
lean_dec(v_unused_1466_);
v___x_1426_ = v_b_1416_;
v_isShared_1427_ = v_isSharedCheck_1465_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_snd_1424_);
lean_dec(v_b_1416_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1465_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1428_ = lean_array_uget_borrowed(v_as_1413_, v_i_1415_);
lean_inc(v_a_1428_);
v___x_1429_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1411_, v_a_1428_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; lean_object* v_a_1433_; uint8_t v___x_1440_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = lean_box(0);
v___x_1440_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1430_);
if (v___x_1440_ == 0)
{
lean_dec(v_a_1430_);
v_a_1433_ = v_snd_1424_;
goto v___jp_1432_;
}
else
{
lean_object* v_type_1441_; lean_object* v___x_1442_; 
v_type_1441_ = lean_ctor_get(v___x_1412_, 2);
lean_inc(v_a_1430_);
lean_inc_ref(v_type_1441_);
v___x_1442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1441_, v_a_1430_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; uint8_t v___x_1444_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = lean_unbox(v_a_1443_);
lean_dec(v_a_1443_);
if (v___x_1444_ == 0)
{
lean_dec(v_a_1430_);
v_a_1433_ = v_snd_1424_;
goto v___jp_1432_;
}
else
{
lean_object* v_self_1445_; lean_object* v___x_1446_; 
v_self_1445_ = lean_ctor_get(v_a_1430_, 0);
lean_inc_ref(v_self_1445_);
lean_dec(v_a_1430_);
v___x_1446_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1412_, v_self_1445_);
if (lean_obj_tag(v___x_1446_) == 1)
{
lean_object* v_val_1447_; lean_object* v___x_1448_; 
v_val_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1411_, v_self_1445_, v_val_1447_, v_snd_1424_);
v_a_1433_ = v___x_1448_;
goto v___jp_1432_;
}
else
{
lean_dec(v___x_1446_);
lean_dec_ref(v_self_1445_);
v_a_1433_ = v_snd_1424_;
goto v___jp_1432_;
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_a_1430_);
lean_del_object(v___x_1426_);
lean_dec(v_snd_1424_);
lean_dec_ref(v___x_1412_);
v_a_1449_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1442_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1442_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
v___jp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_a_1433_);
lean_ctor_set(v___x_1426_, 0, v___x_1431_);
v___x_1435_ = v___x_1426_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_a_1433_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
size_t v___x_1436_; size_t v___x_1437_; 
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_i_1415_, v___x_1436_);
v_i_1415_ = v___x_1437_;
v_b_1416_ = v___x_1435_;
goto _start;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_del_object(v___x_1426_);
lean_dec(v_snd_1424_);
lean_dec_ref(v___x_1412_);
v_a_1457_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1429_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1429_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(lean_object* v_goal_1467_, lean_object* v___x_1468_, lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
size_t v_sz_boxed_1478_; size_t v_i_boxed_1479_; lean_object* v_res_1480_; 
v_sz_boxed_1478_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1479_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1467_, v___x_1468_, v_as_1469_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec_ref(v_as_1469_);
lean_dec_ref(v_goal_1467_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(lean_object* v_goal_1481_, lean_object* v___x_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec_ref(v___x_1482_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_b_1486_);
return v___x_1493_;
}
else
{
lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1535_; 
v_snd_1494_ = lean_ctor_get(v_b_1486_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_b_1486_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v_b_1486_, 0);
lean_dec(v_unused_1536_);
v___x_1496_ = v_b_1486_;
v_isShared_1497_ = v_isSharedCheck_1535_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_dec(v_b_1486_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1535_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_array_uget_borrowed(v_as_1483_, v_i_1485_);
lean_inc(v_a_1498_);
v___x_1499_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1481_, v_a_1498_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v_a_1503_; uint8_t v___x_1510_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = lean_box(0);
v___x_1510_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1500_);
if (v___x_1510_ == 0)
{
lean_dec(v_a_1500_);
v_a_1503_ = v_snd_1494_;
goto v___jp_1502_;
}
else
{
lean_object* v_type_1511_; lean_object* v___x_1512_; 
v_type_1511_ = lean_ctor_get(v___x_1482_, 2);
lean_inc(v_a_1500_);
lean_inc_ref(v_type_1511_);
v___x_1512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_1511_, v_a_1500_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; uint8_t v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = lean_unbox(v_a_1513_);
lean_dec(v_a_1513_);
if (v___x_1514_ == 0)
{
lean_dec(v_a_1500_);
v_a_1503_ = v_snd_1494_;
goto v___jp_1502_;
}
else
{
lean_object* v_self_1515_; lean_object* v___x_1516_; 
v_self_1515_ = lean_ctor_get(v_a_1500_, 0);
lean_inc_ref(v_self_1515_);
lean_dec(v_a_1500_);
v___x_1516_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v___x_1482_, v_self_1515_);
if (lean_obj_tag(v___x_1516_) == 1)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; 
v_val_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1481_, v_self_1515_, v_val_1517_, v_snd_1494_);
v_a_1503_ = v___x_1518_;
goto v___jp_1502_;
}
else
{
lean_dec(v___x_1516_);
lean_dec_ref(v_self_1515_);
v_a_1503_ = v_snd_1494_;
goto v___jp_1502_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1500_);
lean_del_object(v___x_1496_);
lean_dec(v_snd_1494_);
lean_dec_ref(v___x_1482_);
v_a_1519_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1512_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1512_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
v___jp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v_a_1503_);
lean_ctor_set(v___x_1496_, 0, v___x_1501_);
v___x_1505_ = v___x_1496_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_a_1503_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = lean_usize_add(v_i_1485_, v___x_1506_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_1481_, v___x_1482_, v_as_1483_, v_sz_1484_, v___x_1507_, v___x_1505_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_del_object(v___x_1496_);
lean_dec(v_snd_1494_);
lean_dec_ref(v___x_1482_);
v_a_1527_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1499_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1499_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(lean_object* v_goal_1537_, lean_object* v___x_1538_, lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1537_, v___x_1538_, v_as_1539_, v_sz_boxed_1548_, v_i_boxed_1549_, v_b_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_as_1539_);
lean_dec_ref(v_goal_1537_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(lean_object* v_goal_1551_, lean_object* v___x_1552_, lean_object* v_t_1553_, lean_object* v_init_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_root_1560_; lean_object* v_tail_1561_; lean_object* v___x_1562_; 
v_root_1560_ = lean_ctor_get(v_t_1553_, 0);
v_tail_1561_ = lean_ctor_get(v_t_1553_, 1);
lean_inc_ref(v___x_1552_);
lean_inc_ref(v_init_1554_);
v___x_1562_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_1554_, v_goal_1551_, v___x_1552_, v_root_1560_, v_init_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec_ref(v_init_1554_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1599_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1599_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1599_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
if (lean_obj_tag(v_a_1563_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; 
lean_dec_ref(v___x_1552_);
v_a_1567_ = lean_ctor_get(v_a_1563_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v_a_1563_, 1);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_a_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
lean_del_object(v___x_1565_);
v_a_1571_ = lean_ctor_get(v_a_1563_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v_a_1563_, 1);
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v_a_1571_);
v_sz_1574_ = lean_array_size(v_tail_1561_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_1551_, v___x_1552_, v_tail_1561_, v_sz_1574_, v___x_1575_, v___x_1573_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1590_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_fst_1581_; 
v_fst_1581_ = lean_ctor_get(v_a_1577_, 0);
if (lean_obj_tag(v_fst_1581_) == 0)
{
lean_object* v_snd_1582_; lean_object* v___x_1584_; 
v_snd_1582_ = lean_ctor_get(v_a_1577_, 1);
lean_inc(v_snd_1582_);
lean_dec(v_a_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_snd_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_snd_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
else
{
lean_object* v_val_1586_; lean_object* v___x_1588_; 
lean_inc_ref(v_fst_1581_);
lean_dec(v_a_1577_);
v_val_1586_ = lean_ctor_get(v_fst_1581_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v_fst_1581_, 1);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_val_1586_);
v___x_1588_ = v___x_1579_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_val_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_a_1591_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1576_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1576_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v___x_1552_);
v_a_1600_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1562_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1562_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(lean_object* v_goal_1608_, lean_object* v___x_1609_, lean_object* v_t_1610_, lean_object* v_init_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_1608_, v___x_1609_, v_t_1610_, v_init_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec_ref(v_t_1610_);
lean_dec_ref(v_goal_1608_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(lean_object* v_goal_1618_, lean_object* v_as_1619_, size_t v_sz_1620_, size_t v_i_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_usize_dec_lt(v_i_1621_, v_sz_1620_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_b_1622_);
return v___x_1629_;
}
else
{
lean_object* v_snd_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1661_; 
v_snd_1630_ = lean_ctor_get(v_b_1622_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_b_1622_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v_b_1622_, 0);
lean_dec(v_unused_1662_);
v___x_1632_ = v_b_1622_;
v_isShared_1633_ = v_isSharedCheck_1661_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_snd_1630_);
lean_dec(v_b_1622_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1661_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_array_uget_borrowed(v_as_1619_, v_i_1621_);
lean_inc(v_a_1634_);
v___x_1635_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1618_, v_a_1634_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v_self_1637_; lean_object* v___x_1638_; lean_object* v_a_1640_; lean_object* v___x_1647_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v_self_1637_ = lean_ctor_get(v_a_1636_, 0);
lean_inc_ref_n(v_self_1637_, 2);
lean_dec(v_a_1636_);
v___x_1638_ = lean_box(0);
v___x_1647_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1637_);
if (lean_obj_tag(v___x_1647_) == 1)
{
lean_object* v_val_1648_; lean_object* v___x_1649_; 
v_val_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_val_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1630_, v_val_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1630_, v_self_1637_);
lean_dec_ref(v_self_1637_);
if (lean_obj_tag(v___x_1650_) == 1)
{
lean_object* v_val_1651_; lean_object* v___x_1652_; 
v_val_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1618_, v_val_1648_, v_val_1651_, v_snd_1630_);
v_a_1640_ = v___x_1652_;
goto v___jp_1639_;
}
else
{
lean_dec(v___x_1650_);
lean_dec(v_val_1648_);
v_a_1640_ = v_snd_1630_;
goto v___jp_1639_;
}
}
else
{
lean_dec_ref_known(v___x_1649_, 1);
lean_dec(v_val_1648_);
lean_dec_ref(v_self_1637_);
v_a_1640_ = v_snd_1630_;
goto v___jp_1639_;
}
}
else
{
lean_dec(v___x_1647_);
lean_dec_ref(v_self_1637_);
v_a_1640_ = v_snd_1630_;
goto v___jp_1639_;
}
v___jp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v_a_1640_);
lean_ctor_set(v___x_1632_, 0, v___x_1638_);
v___x_1642_ = v___x_1632_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_a_1640_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
size_t v___x_1643_; size_t v___x_1644_; 
v___x_1643_ = ((size_t)1ULL);
v___x_1644_ = lean_usize_add(v_i_1621_, v___x_1643_);
v_i_1621_ = v___x_1644_;
v_b_1622_ = v___x_1642_;
goto _start;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_del_object(v___x_1632_);
lean_dec(v_snd_1630_);
v_a_1653_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1635_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1635_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(lean_object* v_goal_1663_, lean_object* v_as_1664_, lean_object* v_sz_1665_, lean_object* v_i_1666_, lean_object* v_b_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
size_t v_sz_boxed_1673_; size_t v_i_boxed_1674_; lean_object* v_res_1675_; 
v_sz_boxed_1673_ = lean_unbox_usize(v_sz_1665_);
lean_dec(v_sz_1665_);
v_i_boxed_1674_ = lean_unbox_usize(v_i_1666_);
lean_dec(v_i_1666_);
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1663_, v_as_1664_, v_sz_boxed_1673_, v_i_boxed_1674_, v_b_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v_as_1664_);
lean_dec_ref(v_goal_1663_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(lean_object* v_goal_1676_, lean_object* v_as_1677_, size_t v_sz_1678_, size_t v_i_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_usize_dec_lt(v_i_1679_, v_sz_1678_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_b_1680_);
return v___x_1687_;
}
else
{
lean_object* v_snd_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1719_; 
v_snd_1688_ = lean_ctor_get(v_b_1680_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_b_1680_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v_b_1680_, 0);
lean_dec(v_unused_1720_);
v___x_1690_ = v_b_1680_;
v_isShared_1691_ = v_isSharedCheck_1719_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_snd_1688_);
lean_dec(v_b_1680_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1719_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_a_1692_; lean_object* v___x_1693_; 
v_a_1692_ = lean_array_uget_borrowed(v_as_1677_, v_i_1679_);
lean_inc(v_a_1692_);
v___x_1693_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1676_, v_a_1692_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v_self_1695_; lean_object* v___x_1696_; lean_object* v_a_1698_; lean_object* v___x_1705_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v_self_1695_ = lean_ctor_get(v_a_1694_, 0);
lean_inc_ref_n(v_self_1695_, 2);
lean_dec(v_a_1694_);
v___x_1696_ = lean_box(0);
v___x_1705_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1695_);
if (lean_obj_tag(v___x_1705_) == 1)
{
lean_object* v_val_1706_; lean_object* v___x_1707_; 
v_val_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_val_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1688_, v_val_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1688_, v_self_1695_);
lean_dec_ref(v_self_1695_);
if (lean_obj_tag(v___x_1708_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1710_; 
v_val_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1676_, v_val_1706_, v_val_1709_, v_snd_1688_);
v_a_1698_ = v___x_1710_;
goto v___jp_1697_;
}
else
{
lean_dec(v___x_1708_);
lean_dec(v_val_1706_);
v_a_1698_ = v_snd_1688_;
goto v___jp_1697_;
}
}
else
{
lean_dec_ref_known(v___x_1707_, 1);
lean_dec(v_val_1706_);
lean_dec_ref(v_self_1695_);
v_a_1698_ = v_snd_1688_;
goto v___jp_1697_;
}
}
else
{
lean_dec(v___x_1705_);
lean_dec_ref(v_self_1695_);
v_a_1698_ = v_snd_1688_;
goto v___jp_1697_;
}
v___jp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v_a_1698_);
lean_ctor_set(v___x_1690_, 0, v___x_1696_);
v___x_1700_ = v___x_1690_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_a_1698_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1679_, v___x_1701_);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_1676_, v_as_1677_, v_sz_1678_, v___x_1702_, v___x_1700_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1703_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_del_object(v___x_1690_);
lean_dec(v_snd_1688_);
v_a_1711_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1693_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1693_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(lean_object* v_goal_1721_, lean_object* v_as_1722_, lean_object* v_sz_1723_, lean_object* v_i_1724_, lean_object* v_b_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
size_t v_sz_boxed_1731_; size_t v_i_boxed_1732_; lean_object* v_res_1733_; 
v_sz_boxed_1731_ = lean_unbox_usize(v_sz_1723_);
lean_dec(v_sz_1723_);
v_i_boxed_1732_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1721_, v_as_1722_, v_sz_boxed_1731_, v_i_boxed_1732_, v_b_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec_ref(v_as_1722_);
lean_dec_ref(v_goal_1721_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(lean_object* v_goal_1734_, lean_object* v_as_1735_, size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_b_1738_);
return v___x_1745_;
}
else
{
lean_object* v_snd_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1777_; 
v_snd_1746_ = lean_ctor_get(v_b_1738_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_b_1738_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v_b_1738_, 0);
lean_dec(v_unused_1778_);
v___x_1748_ = v_b_1738_;
v_isShared_1749_ = v_isSharedCheck_1777_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snd_1746_);
lean_dec(v_b_1738_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1777_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_a_1750_; lean_object* v___x_1751_; 
v_a_1750_ = lean_array_uget_borrowed(v_as_1735_, v_i_1737_);
lean_inc(v_a_1750_);
v___x_1751_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1734_, v_a_1750_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v_self_1753_; lean_object* v___x_1754_; lean_object* v_a_1756_; lean_object* v___x_1763_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v_self_1753_ = lean_ctor_get(v_a_1752_, 0);
lean_inc_ref_n(v_self_1753_, 2);
lean_dec(v_a_1752_);
v___x_1754_ = lean_box(0);
v___x_1763_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1753_);
if (lean_obj_tag(v___x_1763_) == 1)
{
lean_object* v_val_1764_; lean_object* v___x_1765_; 
v_val_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_val_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1746_, v_val_1764_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1746_, v_self_1753_);
lean_dec_ref(v_self_1753_);
if (lean_obj_tag(v___x_1766_) == 1)
{
lean_object* v_val_1767_; lean_object* v___x_1768_; 
v_val_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1734_, v_val_1764_, v_val_1767_, v_snd_1746_);
v_a_1756_ = v___x_1768_;
goto v___jp_1755_;
}
else
{
lean_dec(v___x_1766_);
lean_dec(v_val_1764_);
v_a_1756_ = v_snd_1746_;
goto v___jp_1755_;
}
}
else
{
lean_dec_ref_known(v___x_1765_, 1);
lean_dec(v_val_1764_);
lean_dec_ref(v_self_1753_);
v_a_1756_ = v_snd_1746_;
goto v___jp_1755_;
}
}
else
{
lean_dec(v___x_1763_);
lean_dec_ref(v_self_1753_);
v_a_1756_ = v_snd_1746_;
goto v___jp_1755_;
}
v___jp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v_a_1756_);
lean_ctor_set(v___x_1748_, 0, v___x_1754_);
v___x_1758_ = v___x_1748_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_a_1756_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
size_t v___x_1759_; size_t v___x_1760_; 
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_add(v_i_1737_, v___x_1759_);
v_i_1737_ = v___x_1760_;
v_b_1738_ = v___x_1758_;
goto _start;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_del_object(v___x_1748_);
lean_dec(v_snd_1746_);
v_a_1769_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1751_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1751_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v_goal_1779_, lean_object* v_as_1780_, lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_b_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1779_, v_as_1780_, v_sz_boxed_1789_, v_i_boxed_1790_, v_b_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v_as_1780_);
lean_dec_ref(v_goal_1779_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(lean_object* v_goal_1792_, lean_object* v_as_1793_, size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_b_1796_);
return v___x_1803_;
}
else
{
lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1835_; 
v_snd_1804_ = lean_ctor_get(v_b_1796_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_b_1796_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v_b_1796_, 0);
lean_dec(v_unused_1836_);
v___x_1806_ = v_b_1796_;
v_isShared_1807_ = v_isSharedCheck_1835_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_dec(v_b_1796_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1835_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_array_uget_borrowed(v_as_1793_, v_i_1795_);
lean_inc(v_a_1808_);
v___x_1809_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1792_, v_a_1808_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v_self_1811_; lean_object* v___x_1812_; lean_object* v_a_1814_; lean_object* v___x_1821_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v_self_1811_ = lean_ctor_get(v_a_1810_, 0);
lean_inc_ref_n(v_self_1811_, 2);
lean_dec(v_a_1810_);
v___x_1812_ = lean_box(0);
v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_1811_);
if (lean_obj_tag(v___x_1821_) == 1)
{
lean_object* v_val_1822_; lean_object* v___x_1823_; 
v_val_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_val_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1804_, v_val_1822_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_1804_, v_self_1811_);
lean_dec_ref(v_self_1811_);
if (lean_obj_tag(v___x_1824_) == 1)
{
lean_object* v_val_1825_; lean_object* v___x_1826_; 
v_val_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1792_, v_val_1822_, v_val_1825_, v_snd_1804_);
v_a_1814_ = v___x_1826_;
goto v___jp_1813_;
}
else
{
lean_dec(v___x_1824_);
lean_dec(v_val_1822_);
v_a_1814_ = v_snd_1804_;
goto v___jp_1813_;
}
}
else
{
lean_dec_ref_known(v___x_1823_, 1);
lean_dec(v_val_1822_);
lean_dec_ref(v_self_1811_);
v_a_1814_ = v_snd_1804_;
goto v___jp_1813_;
}
}
else
{
lean_dec(v___x_1821_);
lean_dec_ref(v_self_1811_);
v_a_1814_ = v_snd_1804_;
goto v___jp_1813_;
}
v___jp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v_a_1814_);
lean_ctor_set(v___x_1806_, 0, v___x_1812_);
v___x_1816_ = v___x_1806_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_a_1814_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_add(v_i_1795_, v___x_1817_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_1792_, v_as_1793_, v_sz_1794_, v___x_1818_, v___x_1816_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_del_object(v___x_1806_);
lean_dec(v_snd_1804_);
v_a_1827_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1809_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1809_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(lean_object* v_goal_1837_, lean_object* v_as_1838_, lean_object* v_sz_1839_, lean_object* v_i_1840_, lean_object* v_b_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
size_t v_sz_boxed_1847_; size_t v_i_boxed_1848_; lean_object* v_res_1849_; 
v_sz_boxed_1847_ = lean_unbox_usize(v_sz_1839_);
lean_dec(v_sz_1839_);
v_i_boxed_1848_ = lean_unbox_usize(v_i_1840_);
lean_dec(v_i_1840_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1837_, v_as_1838_, v_sz_boxed_1847_, v_i_boxed_1848_, v_b_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec_ref(v_as_1838_);
lean_dec_ref(v_goal_1837_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(lean_object* v_init_1850_, lean_object* v_goal_1851_, lean_object* v_n_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
if (lean_obj_tag(v_n_1852_) == 0)
{
lean_object* v_cs_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; size_t v_sz_1862_; size_t v___x_1863_; lean_object* v___x_1864_; 
v_cs_1859_ = lean_ctor_get(v_n_1852_, 0);
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v_b_1853_);
v_sz_1862_ = lean_array_size(v_cs_1859_);
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1850_, v_goal_1851_, v_cs_1859_, v_sz_1862_, v___x_1863_, v___x_1861_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1879_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1879_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1879_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_fst_1869_; 
v_fst_1869_ = lean_ctor_get(v_a_1865_, 0);
if (lean_obj_tag(v_fst_1869_) == 0)
{
lean_object* v_snd_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v_snd_1870_ = lean_ctor_get(v_a_1865_, 1);
lean_inc(v_snd_1870_);
lean_dec(v_a_1865_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_snd_1870_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1871_);
v___x_1873_ = v___x_1867_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
else
{
lean_object* v_val_1875_; lean_object* v___x_1877_; 
lean_inc_ref(v_fst_1869_);
lean_dec(v_a_1865_);
v_val_1875_ = lean_ctor_get(v_fst_1869_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_fst_1869_, 1);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_val_1875_);
v___x_1877_ = v___x_1867_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_val_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1864_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1864_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_vs_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; size_t v_sz_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
v_vs_1888_ = lean_ctor_get(v_n_1852_, 0);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v_b_1853_);
v_sz_1891_ = lean_array_size(v_vs_1888_);
v___x_1892_ = ((size_t)0ULL);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_1851_, v_vs_1888_, v_sz_1891_, v___x_1892_, v___x_1890_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1908_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_fst_1898_; 
v_fst_1898_ = lean_ctor_get(v_a_1894_, 0);
if (lean_obj_tag(v_fst_1898_) == 0)
{
lean_object* v_snd_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v_snd_1899_ = lean_ctor_get(v_a_1894_, 1);
lean_inc(v_snd_1899_);
lean_dec(v_a_1894_);
v___x_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1900_, 0, v_snd_1899_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1900_);
v___x_1902_ = v___x_1896_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
else
{
lean_object* v_val_1904_; lean_object* v___x_1906_; 
lean_inc_ref(v_fst_1898_);
lean_dec(v_a_1894_);
v_val_1904_ = lean_ctor_get(v_fst_1898_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v_fst_1898_, 1);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v_val_1904_);
v___x_1906_ = v___x_1896_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_val_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1893_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1893_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(lean_object* v_init_1917_, lean_object* v_goal_1918_, lean_object* v_as_1919_, size_t v_sz_1920_, size_t v_i_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v___x_1928_; 
v___x_1928_ = lean_usize_dec_lt(v_i_1921_, v_sz_1920_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_b_1922_);
return v___x_1929_;
}
else
{
lean_object* v_snd_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1964_; 
v_snd_1930_ = lean_ctor_get(v_b_1922_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_b_1922_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v_b_1922_, 0);
lean_dec(v_unused_1965_);
v___x_1932_ = v_b_1922_;
v_isShared_1933_ = v_isSharedCheck_1964_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_snd_1930_);
lean_dec(v_b_1922_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1964_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v_a_1934_; lean_object* v___x_1935_; 
v_a_1934_ = lean_array_uget_borrowed(v_as_1919_, v_i_1921_);
lean_inc(v_snd_1930_);
v___x_1935_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1917_, v_goal_1918_, v_a_1934_, v_snd_1930_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1955_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1955_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1955_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
if (lean_obj_tag(v_a_1936_) == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1936_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1940_);
v___x_1942_ = v___x_1932_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_snd_1930_);
v___x_1942_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
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
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
lean_del_object(v___x_1938_);
lean_dec(v_snd_1930_);
v_a_1947_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v_a_1936_, 1);
v___x_1948_ = lean_box(0);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v_a_1947_);
lean_ctor_set(v___x_1932_, 0, v___x_1948_);
v___x_1950_ = v___x_1932_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_a_1947_);
v___x_1950_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
size_t v___x_1951_; size_t v___x_1952_; 
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_add(v_i_1921_, v___x_1951_);
v_i_1921_ = v___x_1952_;
v_b_1922_ = v___x_1950_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1932_);
lean_dec(v_snd_1930_);
v_a_1956_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1935_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1935_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(lean_object* v_init_1966_, lean_object* v_goal_1967_, lean_object* v_as_1968_, lean_object* v_sz_1969_, lean_object* v_i_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
size_t v_sz_boxed_1977_; size_t v_i_boxed_1978_; lean_object* v_res_1979_; 
v_sz_boxed_1977_ = lean_unbox_usize(v_sz_1969_);
lean_dec(v_sz_1969_);
v_i_boxed_1978_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_1966_, v_goal_1967_, v_as_1968_, v_sz_boxed_1977_, v_i_boxed_1978_, v_b_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v_as_1968_);
lean_dec_ref(v_goal_1967_);
lean_dec_ref(v_init_1966_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(lean_object* v_init_1980_, lean_object* v_goal_1981_, lean_object* v_n_1982_, lean_object* v_b_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1980_, v_goal_1981_, v_n_1982_, v_b_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec_ref(v_n_1982_);
lean_dec_ref(v_goal_1981_);
lean_dec_ref(v_init_1980_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(lean_object* v_goal_1990_, lean_object* v_t_1991_, lean_object* v_init_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_root_1998_; lean_object* v_tail_1999_; lean_object* v___x_2000_; 
v_root_1998_ = lean_ctor_get(v_t_1991_, 0);
v_tail_1999_ = lean_ctor_get(v_t_1991_, 1);
lean_inc_ref(v_init_1992_);
v___x_2000_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_1992_, v_goal_1990_, v_root_1998_, v_init_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec_ref(v_init_1992_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2037_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2037_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2037_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
if (lean_obj_tag(v_a_2001_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; 
v_a_2005_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v_a_2001_, 1);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v_a_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; size_t v_sz_2012_; size_t v___x_2013_; lean_object* v___x_2014_; 
lean_del_object(v___x_2003_);
v_a_2009_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v_a_2001_, 1);
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v_a_2009_);
v_sz_2012_ = lean_array_size(v_tail_1999_);
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_1990_, v_tail_1999_, v_sz_2012_, v___x_2013_, v___x_2011_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2028_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2028_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2028_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_fst_2019_; 
v_fst_2019_ = lean_ctor_get(v_a_2015_, 0);
if (lean_obj_tag(v_fst_2019_) == 0)
{
lean_object* v_snd_2020_; lean_object* v___x_2022_; 
v_snd_2020_ = lean_ctor_get(v_a_2015_, 1);
lean_inc(v_snd_2020_);
lean_dec(v_a_2015_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_snd_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_snd_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
else
{
lean_object* v_val_2024_; lean_object* v___x_2026_; 
lean_inc_ref(v_fst_2019_);
lean_dec(v_a_2015_);
v_val_2024_ = lean_ctor_get(v_fst_2019_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v_fst_2019_, 1);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_val_2024_);
v___x_2026_ = v___x_2017_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_val_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2014_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2014_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_a_2038_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2000_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2000_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(lean_object* v_goal_2046_, lean_object* v_t_2047_, lean_object* v_init_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2046_, v_t_2047_, v_init_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_t_2047_);
lean_dec_ref(v_goal_2046_);
return v_res_2054_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_unsigned_to_nat(16u);
v___x_2057_ = lean_mk_array(v___x_2056_, v___x_2055_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v_model_2060_; 
v___x_2058_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0);
v___x_2059_ = lean_unsigned_to_nat(0u);
v_model_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_model_2060_, 0, v___x_2059_);
lean_ctor_set(v_model_2060_, 1, v___x_2058_);
return v_model_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel(lean_object* v_goal_2068_, lean_object* v_structId_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2076_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2075_, v_goal_2068_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v_toGoalState_2078_; lean_object* v_structs_2079_; lean_object* v_exprs_2080_; lean_object* v___x_2081_; lean_object* v_model_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v_toGoalState_2078_ = lean_ctor_get(v_goal_2068_, 0);
v_structs_2079_ = lean_ctor_get(v_a_2077_, 0);
lean_inc_ref(v_structs_2079_);
lean_dec(v_a_2077_);
v_exprs_2080_ = lean_ctor_get(v_toGoalState_2078_, 2);
v___x_2081_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
v_model_2082_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1, &l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1);
v___x_2083_ = lean_array_get(v___x_2081_, v_structs_2079_, v_structId_2069_);
lean_dec_ref(v_structs_2079_);
lean_inc(v___x_2083_);
v___x_2084_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_2068_, v___x_2083_, v_exprs_2080_, v_model_2082_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_2068_, v_structId_2069_, v_a_2085_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_2068_, v_exprs_2080_, v_a_2087_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v_type_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v_type_2090_ = lean_ctor_get(v___x_2083_, 2);
lean_inc_ref(v_type_2090_);
lean_dec(v___x_2083_);
v___x_2091_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed), 7, 1);
lean_closure_set(v___x_2091_, 0, v_type_2090_);
v___x_2092_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_2068_, v___x_2091_, v_a_2089_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5));
v___x_2095_ = l_Lean_Meta_Grind_Arith_traceModel(v___x_2094_, v_a_2093_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; 
v_unused_2103_ = lean_ctor_get(v___x_2095_, 0);
lean_dec(v_unused_2103_);
v___x_2097_ = v___x_2095_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_dec(v___x_2095_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v_a_2093_);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2093_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_a_2093_);
v_a_2104_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2095_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2095_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
return v___x_2092_;
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v___x_2083_);
v_a_2112_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2088_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2088_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v___x_2083_);
v_a_2120_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2086_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2086_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v___x_2083_);
v_a_2128_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2084_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2084_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2148_; 
v_a_2136_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2138_ = v___x_2076_;
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2076_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2148_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_ref_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v_ref_2140_ = lean_ctor_get(v_a_2072_, 5);
v___x_2141_ = lean_io_error_to_string(v_a_2136_);
v___x_2142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
v___x_2143_ = l_Lean_MessageData_ofFormat(v___x_2142_);
lean_inc(v_ref_2140_);
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v_ref_2140_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2144_);
v___x_2146_ = v___x_2138_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(lean_object* v_goal_2149_, lean_object* v_structId_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(v_goal_2149_, v_structId_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_structId_2150_);
lean_dec_ref(v_goal_2149_);
return v_res_2156_;
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
